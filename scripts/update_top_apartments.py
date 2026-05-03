#!/usr/bin/env python3
from __future__ import annotations

import json
import math
import re
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from urllib.parse import quote_plus

from curl_cffi import requests as cf


ROOT = Path(__file__).resolve().parents[1]
INDEX_HTML = ROOT / "index.html"
OUTPUT_JSON = ROOT / "data" / "top_apartments.json"
MAPS_DESTINATION = "1 Manhattan West, 395 9th Ave, New York, NY 10001"

TARGET_RENT = 2350
STRETCH_RENT = 2600
OUTPUT_COUNT = 5
REQUEST_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
        "Chrome/124.0.0.0 Safari/537.36"
    ),
    "Accept-Language": "en-US,en;q=0.9",
}
LAUNDRY_RE = re.compile(
    r"(?i)"
    r"(washer/dryer(?: in unit)?|washer in unit|dryer in unit|"
    r"in[- ]unit laundry|in[- ]unit washer|laundry in building|laundry room)"
)
EXCLUDE_RE = re.compile(r"(?i)room for rent|shared apartment|co-?living|sublet")
NO_FEE_RE = re.compile(r"(?i)no.?fee")
PRICE_RE = re.compile(r"\$([\d,]+)\s*/mo")

STREETEASY_PATHS = {
    "Astoria": "astoria",
    "Jersey City (Journal Sq)": "journal-square",
    "Hoboken": "hoboken",
    "Jackson Heights": "jackson-heights",
    "Sunnyside": "sunnyside-queens",
    "Washington Heights": "washington-heights",
    "Elmhurst": "elmhurst",
    "Flushing": "flushing",
    "Hamilton Heights": "hamilton-heights",
    "Central Harlem": "central-harlem",
    "Upper East Side": "upper-east-side",
    "Forest Hills": "forest-hills",
    "Inwood": "inwood",
    "Harlem (127-155)": "harlem",
    "East Harlem": "east-harlem",
}

ALLOWED_LOCALITIES = {
    "astoria": {"astoria"},
    "journal-square": {"journal square", "jersey city", "mcginley square"},
    "hoboken": {"hoboken"},
    "jackson-heights": {"jackson heights"},
    "sunnyside-queens": {"sunnyside"},
    "washington-heights": {"washington heights"},
    "elmhurst": {"elmhurst"},
    "flushing": {"flushing", "east flushing"},
    "hamilton-heights": {"hamilton heights"},
    "central-harlem": {"central harlem", "harlem"},
    "upper-east-side": {"upper east side", "yorkville", "carnegie hill"},
    "forest-hills": {"forest hills"},
    "inwood": {"inwood"},
    "harlem": {"harlem"},
    "east-harlem": {"east harlem", "harlem"},
}


@dataclass
class Candidate:
    neighborhood: str
    search_slug: str
    search_url: str
    listing_url: str
    address: str
    locality: str
    beds: str
    price: int | None
    available: str


def get(url: str, timeout: int = 18) -> str:
    last_error: Exception | None = None
    for browser in ("chrome124", "safari17_0", "chrome120"):
        try:
            response = cf.get(
                url,
                headers=REQUEST_HEADERS,
                impersonate=browser,
                timeout=timeout,
            )
            response.raise_for_status()
            return response.text
        except Exception as exc:  # pragma: no cover - network fallback
            last_error = exc
    if last_error:
        raise last_error
    raise RuntimeError(f"Unable to fetch {url}")


def load_neighborhoods() -> list[dict[str, Any]]:
    html = INDEX_HTML.read_text()
    prefix = "const results = "
    suffix = "\nconst precincts = "
    start = html.find(prefix)
    if start < 0:
        raise RuntimeError("Could not find results array in index.html")
    start += len(prefix)
    end = html.find(suffix, start)
    if end < 0:
        raise RuntimeError("Could not find precincts marker after results array")
    return json.loads(html[start:end].strip())


def extract_price(item: dict[str, Any], events: dict[str, dict[str, Any]]) -> int | None:
    url = (item.get("url") or item.get("@id") or "").split("?")[0]
    event_price = events.get(url, {}).get("price")
    if event_price:
        return event_price
    for prop in item.get("additionalProperty") or []:
        if not isinstance(prop, dict):
            continue
        if (prop.get("name") or "").lower() == "monthly rent":
            match = PRICE_RE.search(str(prop.get("value") or ""))
            if match:
                return int(match.group(1).replace(",", ""))
    return None


def listing_graph(search_html: str) -> list[dict[str, Any]]:
    blocks = re.findall(
        r"<script[^>]+type=[\"']application/ld\+json[\"'][^>]*>(.*?)</script>",
        search_html,
        re.S,
    )
    items: list[dict[str, Any]] = []
    for block in blocks:
        try:
            data = json.loads(block)
        except json.JSONDecodeError:
            continue
        graph = data.get("@graph", data if isinstance(data, list) else [data])
        if not isinstance(graph, list):
            graph = [graph]
        for item in graph:
            if isinstance(item, dict):
                items.append(item)
    return items


def fetch_search_candidates(neighborhood: dict[str, Any]) -> list[Candidate]:
    slug = STREETEASY_PATHS.get(neighborhood["name"])
    if not slug:
        return []
    search_url = f"https://streeteasy.com/for-rent/{slug}?beds=0,1&price=-{STRETCH_RENT}"
    try:
        graph = listing_graph(get(search_url))
    except Exception:
        return []
    events: dict[str, dict[str, Any]] = {}
    for item in graph:
        if item.get("@type") != "Event":
            continue
        offers = item.get("offers") or {}
        url = (offers.get("url") or "").split("?")[0]
        if not url:
            continue
        try:
            price = int(str(offers.get("price")).replace(",", ""))
        except (TypeError, ValueError):
            price = None
        events[url] = {
            "price": price,
            "available": (item.get("startDate") or "check listing")[:10],
        }

    allowed = ALLOWED_LOCALITIES.get(slug, set())
    candidates: list[Candidate] = []
    seen: set[str] = set()
    for item in graph:
        if item.get("@type") not in {"Apartment", "House", "Residence"}:
            continue
        beds = item.get("numberOfBedrooms")
        if beds not in (0, 1):
            continue
        url = (item.get("url") or item.get("@id") or "").split("?")[0]
        if not url or url in seen:
            continue
        seen.add(url)
        address = item.get("address") or {}
        locality = (address.get("addressLocality") or "").strip()
        if allowed and locality.lower() not in allowed:
            continue
        price = extract_price(item, events)
        if price and price > STRETCH_RENT:
            continue
        candidates.append(
            Candidate(
                neighborhood=neighborhood["name"],
                search_slug=slug,
                search_url=search_url,
                listing_url=url,
                address=address.get("streetAddress", ""),
                locality=locality,
                beds="Studio" if beds == 0 else "1BR",
                price=price,
                available=events.get(url, {}).get("available", "check listing"),
            )
        )
    return candidates


def compact_text(html: str) -> str:
    return re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", html)).strip()


def enrich_candidate(candidate: Candidate, by_name: dict[str, dict[str, Any]]) -> dict[str, Any] | None:
    try:
        html = get(candidate.listing_url, timeout=12)
    except Exception:
        html = ""
    text = compact_text(html)
    if text and EXCLUDE_RE.search(text):
        return None

    laundry_match = LAUNDRY_RE.search(text) if text else None
    no_fee = bool(NO_FEE_RE.search(text)) if text else False
    price = candidate.price
    if not price:
        price_match = PRICE_RE.search(text)
        if price_match:
            price = int(price_match.group(1).replace(",", ""))
    if not price or price > STRETCH_RENT:
        return None

    hood = by_name[candidate.neighborhood]
    commute = int(hood["min"])
    transit_cost = int(hood.get("transit_cost") or 0)
    tax_credit = 246 if hood.get("tax") == "NJ" else 0
    effective_cost = price + transit_cost - tax_credit
    state = "NJ" if hood.get("tax") == "NJ" else "NY"
    origin = f"{candidate.address}, {candidate.locality}, {state}"
    route_url = (
        "https://www.google.com/maps/dir/?api=1"
        f"&origin={quote_plus(origin)}"
        f"&destination={quote_plus(MAPS_DESTINATION)}"
        "&travelmode=transit"
    )
    confidence = (hood.get("data_confidence") or "medium").lower()
    fit_status = "target" if price <= TARGET_RENT else "stretch"
    laundry_text = laundry_match.group(1) if laundry_match else "verify on listing"

    summary_parts = [
        f"{candidate.beds} in {candidate.neighborhood}",
        f"출근 약 {commute}분",
        "세탁 확인" if laundry_match else "세탁은 매물 페이지 확인 필요",
        "무중개수수료 표기" if no_fee else "수수료 조건 확인 필요",
    ]

    listing_score = (
        float(hood.get("composite") or 0)
        + (18 if laundry_match else 0)
        + (12 if price <= TARGET_RENT else 5)
        + (4 if no_fee else 0)
        - max(0, commute - 45) * 2.5
        - (10 if confidence == "low" else 0)
    )

    return {
        "neighborhood": candidate.neighborhood,
        "address": candidate.address,
        "locality": candidate.locality,
        "beds": candidate.beds,
        "price": price,
        "rent_status": fit_status,
        "laundry": laundry_text,
        "laundry_confirmed": bool(laundry_match),
        "no_fee": no_fee,
        "commute_minutes": commute,
        "effective_cost": effective_cost,
        "transit_cost": transit_cost,
        "tax_credit": tax_credit,
        "score": round(listing_score, 1),
        "neighborhood_score": float(hood.get("composite") or 0),
        "fit_status": hood.get("data_confidence", "medium"),
        "source_confidence": confidence,
        "summary": " · ".join(summary_parts),
        "listing_url": candidate.listing_url,
        "search_url": candidate.search_url,
        "route_url": route_url,
        "available": candidate.available,
    }


def rank_key(item: dict[str, Any]) -> tuple[Any, ...]:
    confidence_rank = {"high": 0, "medium": 1, "low": 2}.get(item["source_confidence"], 1)
    return (
        0 if item["laundry_confirmed"] else 1,
        0 if item["rent_status"] == "target" else 1,
        0 if item["commute_minutes"] <= 45 else 1,
        confidence_rank,
        item["price"],
        item["commute_minutes"],
        -item["neighborhood_score"],
        item["address"],
    )


def unique_best(items: list[dict[str, Any]]) -> list[dict[str, Any]]:
    seen_urls: set[str] = set()
    seen_addresses: set[tuple[str, str]] = set()
    unique: list[dict[str, Any]] = []
    for item in sorted(items, key=rank_key):
        if item["listing_url"] in seen_urls:
            continue
        address_key = (item["neighborhood"], item["address"])
        if address_key in seen_addresses:
            continue
        seen_urls.add(item["listing_url"])
        seen_addresses.add(address_key)
        unique.append(item)
    return unique


def build_output(items: list[dict[str, Any]]) -> dict[str, Any]:
    top = unique_best(items)[:OUTPUT_COUNT]
    for idx, item in enumerate(top, start=1):
        item["rank"] = idx
    return {
        "updated_at": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
        "criteria": {
            "target_rent": TARGET_RENT,
            "stretch_rent": STRETCH_RENT,
            "beds": ["Studio", "1BR"],
            "ranking_note": (
                "세탁 확인된 매물을 우선하고, 그다음 40x 기준($2,350) 충족 여부와 "
                "통근 시간, 동네 점수를 함께 반영합니다."
            ),
            "fallback_note": (
                "매일 공급이 적을 수 있어 $2,600까지의 스트레치 매물도 포함합니다."
            ),
        },
        "apartments": top,
    }


def main() -> None:
    neighborhoods = load_neighborhoods()
    by_name = {item["name"]: item for item in neighborhoods}
    candidates: list[Candidate] = []
    for hood in neighborhoods:
        candidates.extend(fetch_search_candidates(hood))

    enriched: list[dict[str, Any]] = []
    with ThreadPoolExecutor(max_workers=6) as pool:
        futures = [pool.submit(enrich_candidate, candidate, by_name) for candidate in candidates]
        for future in as_completed(futures):
            record = future.result()
            if record:
                enriched.append(record)

    payload = build_output(enriched)
    OUTPUT_JSON.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n")
    print(f"Wrote {len(payload['apartments'])} apartments to {OUTPUT_JSON}")


if __name__ == "__main__":
    main()
