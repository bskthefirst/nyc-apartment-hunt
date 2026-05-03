#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from urllib.parse import quote_plus

import requests as pyrequests
from curl_cffi import requests as cf
from scrapling.parser import Selector

ROOT = Path(__file__).resolve().parents[1]
INDEX_HTML = ROOT / "index.html"
OUTPUT_JSON = ROOT / "data" / "top_apartments.json"
MAPS_DESTINATION = "1 Manhattan West, 395 9th Ave, New York, NY 10001"

TARGET_RENT = 2350
STRETCH_RENT = 2800
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
BLOCKED_PAGE_RE = re.compile(
    r"(?i)access to this page has been denied|please enable javascript|verify you are human|captcha"
)
HARD_AVOID_NEIGHBORHOODS = {"Washington Heights"}
SEARCH_MODES = ("0,1", "0", "1")

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


@dataclass(slots=True)
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


def compact_text(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def slug_for_neighborhood(name: str) -> str | None:
    return STREETEASY_PATHS.get(name)


def allowed_localities_for(slug: str) -> set[str]:
    return ALLOWED_LOCALITIES.get(slug, set())


class StreetEasyAPI:
    def __init__(
        self,
        index_html: Path = INDEX_HTML,
        output_json: Path = OUTPUT_JSON,
        cache_dir: Path | None = None,
        target_rent: int = TARGET_RENT,
        stretch_rent: int = STRETCH_RENT,
        output_count: int = OUTPUT_COUNT,
        cache_ttl_seconds: int = 12 * 60 * 60,
        max_workers: int = 6,
    ) -> None:
        self.index_html = index_html
        self.output_json = output_json
        self.target_rent = target_rent
        self.stretch_rent = stretch_rent
        self.output_count = output_count
        self.cache_ttl_seconds = cache_ttl_seconds
        self.max_workers = max_workers
        self.cache_dir = cache_dir or (ROOT / ".cache" / "streeteasy")
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        self._neighborhoods: list[dict[str, Any]] | None = None

    def load_neighborhoods(self) -> list[dict[str, Any]]:
        if self._neighborhoods is not None:
            return self._neighborhoods
        html = self.index_html.read_text()
        prefix = "const results = "
        suffix = "\nconst precincts = "
        start = html.find(prefix)
        if start < 0:
            raise RuntimeError("Could not find results array in index.html")
        start += len(prefix)
        end = html.find(suffix, start)
        if end < 0:
            raise RuntimeError("Could not find precincts marker after results array")
        self._neighborhoods = json.loads(html[start:end].strip())
        return self._neighborhoods

    def _cache_path(self, url: str) -> Path:
        digest = hashlib.sha1(url.encode("utf-8")).hexdigest()
        return self.cache_dir / f"{digest}.txt"

    def _read_cache(self, url: str) -> str | None:
        path = self._cache_path(url)
        if not path.exists():
            return None
        age = time.time() - path.stat().st_mtime
        if age > self.cache_ttl_seconds:
            return None
        try:
            return path.read_text()
        except Exception:
            return None

    def _write_cache(self, url: str, text: str) -> None:
        try:
            self._cache_path(url).write_text(text)
        except Exception:
            pass

    def fetch_text(self, url: str, timeout: int = 18, allow_jina: bool = True) -> str:
        cached = self._read_cache(url)
        if cached is not None:
            return cached

        last_error: Exception | None = None
        for browser in ("chrome124", "safari17_0", "chrome120"):
            try:
                response = cf.get(
                    url,
                    headers=REQUEST_HEADERS,
                    impersonate=browser,
                    timeout=timeout,
                    allow_redirects=True,
                )
                status = getattr(response, "status_code", None) or getattr(response, "status", None)
                text = response.text or ""
                if status and int(status) >= 400:
                    last_error = RuntimeError(f"{url} returned {status}")
                    continue
                if text and not BLOCKED_PAGE_RE.search(text):
                    self._write_cache(url, text)
                    return text
                last_error = RuntimeError(f"{url} returned blocked content")
            except Exception as exc:  # pragma: no cover - network fallback
                last_error = exc

        if allow_jina:
            for delay in (0, 2, 5):
                if delay:
                    time.sleep(delay)
                try:
                    response = pyrequests.get(f"https://r.jina.ai/{url}", timeout=timeout)
                    response.raise_for_status()
                    text = response.text or ""
                    if text:
                        self._write_cache(url, text)
                        return text
                except Exception as exc:  # pragma: no cover - network fallback
                    last_error = exc

        if last_error:
            raise last_error
        raise RuntimeError(f"Unable to fetch {url}")

    def _jsonld_blocks(self, html: str) -> list[str]:
        blocks: list[str] = []
        selector = Selector(html)
        for script in selector.find_all("script", type="application/ld+json"):
            block = (script.text or "").strip()
            if block:
                blocks.append(block)
        if blocks:
            return blocks
        blocks.extend(
            re.findall(
                r"<script[^>]+type=[\"']application/ld\+json[\"'][^>]*>(.*?)</script>",
                html,
                re.S,
            )
        )
        return blocks

    def _listing_graph(self, search_html: str) -> list[dict[str, Any]]:
        items: list[dict[str, Any]] = []
        for block in self._jsonld_blocks(search_html):
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

    def _extract_price(self, item: dict[str, Any], events: dict[str, dict[str, Any]]) -> int | None:
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

    def _search_urls(self, slug: str, max_rent: int) -> list[str]:
        base = f"https://streeteasy.com/for-rent/{slug}"
        urls = [f"{base}?beds={beds}&price=-{max_rent}" for beds in SEARCH_MODES]
        # Preserve ordering but avoid duplicate entries if a slug ever maps oddly.
        return list(dict.fromkeys(urls))

    def _parse_search_html(self, neighborhood: dict[str, Any], search_url: str, search_html: str) -> list[Candidate]:
        slug = STREETEASY_PATHS.get(neighborhood["name"])
        if not slug:
            return []
        graph = self._listing_graph(search_html)
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

        allowed = allowed_localities_for(slug)
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
            price = self._extract_price(item, events)
            if price and price > self.stretch_rent:
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

    def _parse_search_jina(self, neighborhood: dict[str, Any], search_url: str) -> list[Candidate]:
        markdown = self.fetch_text(search_url)
        lines = [line.rstrip() for line in markdown.splitlines()]
        records: list[Candidate] = []
        current_price: int | None = None
        current_beds: str | None = None

        def add_candidate(title: str, url: str) -> None:
            if not current_price or not current_beds:
                return
            records.append(
                Candidate(
                    neighborhood=neighborhood["name"],
                    search_slug=STREETEASY_PATHS.get(neighborhood["name"], ""),
                    search_url=search_url,
                    listing_url=url,
                    address=title,
                    locality=neighborhood["name"],
                    beds=current_beds,
                    price=current_price,
                    available="check listing",
                )
            )

        for raw_line in lines:
            line = raw_line.strip()
            price_match = re.match(r"^\$([\d,]+)\s*$", line)
            if price_match and current_price is None:
                current_price = int(price_match.group(1).replace(",", ""))
                continue
            if current_beds is None:
                if re.search(r"(?i)^\*\s+studio\s*$", line):
                    current_beds = "Studio"
                    continue
                if re.search(r"(?i)^\*\s+1 bed\s*$", line):
                    current_beds = "1BR"
                    continue
            match = re.search(
                r"\[!\[Image \d+: ([^\]]+?) image 1 of \d+\]\([^)]+\)\]\((https://streeteasy\.com/building/[^)]+)\)",
                line,
            )
            if match:
                add_candidate(match.group(1).strip(), match.group(2))
                current_price = None
                current_beds = None

        seen: set[str] = set()
        unique: list[Candidate] = []
        for rec in records:
            if rec.listing_url in seen:
                continue
            seen.add(rec.listing_url)
            if rec.price and rec.price <= self.stretch_rent:
                unique.append(rec)
        return unique

    def fetch_search_candidates(self, neighborhood: dict[str, Any], min_candidates: int = 2) -> list[Candidate]:
        slug = STREETEASY_PATHS.get(neighborhood["name"])
        if not slug:
            return []

        candidates: list[Candidate] = []
        for max_rent in (self.stretch_rent,):
            for idx, search_url in enumerate(self._search_urls(slug, max_rent)):
                try:
                    search_html = self.fetch_text(search_url)
                except Exception:
                    search_html = ""
                found: list[Candidate] = []
                if search_html and not search_html.lstrip().startswith("Access to this page"):
                    found = self._parse_search_html(neighborhood, search_url, search_html)
                if not found:
                    try:
                        found = self._parse_search_jina(neighborhood, search_url)
                    except Exception:
                        found = []
                candidates.extend(found)
                if idx == 0:
                    seen = {candidate.listing_url for candidate in candidates}
                    if len(seen) >= min_candidates:
                        break

        seen_urls: set[str] = set()
        unique: list[Candidate] = []
        for candidate in candidates:
            if candidate.listing_url in seen_urls:
                continue
            seen_urls.add(candidate.listing_url)
            unique.append(candidate)
        return unique

    def _fetch_detail_text(self, listing_url: str) -> str:
        html = ""
        try:
            html = self.fetch_text(listing_url, timeout=12)
        except Exception:
            html = ""
        if html and BLOCKED_PAGE_RE.search(html):
            html = ""
        if not html:
            try:
                html = self.fetch_text(listing_url, timeout=12, allow_jina=True)
            except Exception:
                html = ""
        if not html:
            return ""
        try:
            return compact_text(Selector(html).get_all_text())
        except Exception:
            return compact_text(re.sub(r"<[^>]+>", " ", html))

    def enrich_candidate(self, candidate: Candidate, by_name: dict[str, dict[str, Any]]) -> dict[str, Any] | None:
        text = self._fetch_detail_text(candidate.listing_url)
        if text and EXCLUDE_RE.search(text):
            return None

        laundry_match = LAUNDRY_RE.search(text) if text else None
        no_fee = bool(NO_FEE_RE.search(text)) if text else False
        price = candidate.price
        if not price:
            price_match = PRICE_RE.search(text)
            if price_match:
                price = int(price_match.group(1).replace(",", ""))
        if not price or price > self.stretch_rent:
            return None

        hood = by_name[candidate.neighborhood]
        hood_note = str(hood.get("note") or "")
        station_safety = str(hood.get("station_safety") or "")
        if candidate.neighborhood in HARD_AVOID_NEIGHBORHOODS:
            return None
        if "강력 제외" in hood_note or "Hard Avoid" in hood_note or "강력 제외" in station_safety:
            return None
        if not laundry_match:
            return None

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
        fit_status = "target" if price <= self.target_rent else "stretch"
        laundry_text = laundry_match.group(1) if laundry_match else "verify on listing"

        summary_parts = [
            f"{candidate.beds} in {candidate.neighborhood}",
            f"출근 약 {commute}분",
            "세탁 확인",
            "무중개수수료 표기" if no_fee else "수수료 조건 확인 필요",
        ]
        listing_score = (
            float(hood.get("composite") or 0)
            + (18 if laundry_match else 0)
            + (12 if price <= self.target_rent else 5)
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
            "laundry_confirmed": True,
            "no_fee": no_fee,
            "commute_minutes": commute,
            "effective_cost": effective_cost,
            "transit_cost": transit_cost,
            "tax_credit": tax_credit,
            "score": round(listing_score, 1),
            "neighborhood_score": float(hood.get("composite") or 0),
            "source_confidence": confidence,
            "summary": " · ".join(summary_parts),
            "listing_url": candidate.listing_url,
            "search_url": candidate.search_url,
            "route_url": route_url,
            "available": candidate.available,
        }

    @staticmethod
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

    def unique_best(self, items: list[dict[str, Any]]) -> list[dict[str, Any]]:
        seen_urls: set[str] = set()
        seen_addresses: set[tuple[str, str]] = set()
        unique: list[dict[str, Any]] = []
        for item in sorted(items, key=self.rank_key):
            if item["listing_url"] in seen_urls:
                continue
            address_key = (item["neighborhood"], item["address"])
            if address_key in seen_addresses:
                continue
            seen_urls.add(item["listing_url"])
            seen_addresses.add(address_key)
            unique.append(item)
        return unique

    def build_output(self, items: list[dict[str, Any]]) -> dict[str, Any]:
        top = self.unique_best(items)[: self.output_count]
        for idx, item in enumerate(top, start=1):
            item["rank"] = idx
        return {
            "updated_at": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
            "criteria": {
                "target_rent": self.target_rent,
                "stretch_rent": self.stretch_rent,
                "beds": ["Studio", "1BR"],
                "ranking_note": (
                    "세탁이 확인된 매물만 남기고 강력 제외 동네를 배제한 뒤, "
                    "40x 기준($2,350) 충족 여부와 통근 시간, 동네 점수를 함께 반영합니다."
                ),
                "fallback_note": (
                    "매일 공급이 적을 수 있어 $2,800까지의 차순위 매물도 확인하지만, "
                    "검증되지 않은 매물로 5개를 억지로 채우지는 않습니다."
                ),
            },
            "apartments": top,
        }

    def search_neighborhood(self, neighborhood_name: str, count: int = 3) -> dict[str, Any]:
        neighborhoods = self.load_neighborhoods()
        hood = next((item for item in neighborhoods if item["name"] == neighborhood_name), None)
        if not hood:
            raise KeyError(f"Unknown neighborhood: {neighborhood_name}")

        candidates = self.fetch_search_candidates(hood, min_candidates=max(count, 2))
        by_name = {item["name"]: item for item in neighborhoods}
        enriched: list[dict[str, Any]] = []
        with ThreadPoolExecutor(max_workers=self.max_workers) as pool:
            futures = [pool.submit(self.enrich_candidate, candidate, by_name) for candidate in candidates]
            for future in as_completed(futures):
                record = future.result()
                if record:
                    enriched.append(record)

        top = self.unique_best(enriched)[:count]
        for idx, item in enumerate(top, start=1):
            item["rank"] = idx
        return {
            "neighborhood": neighborhood_name,
            "search_urls": self._search_urls(STREETEASY_PATHS[neighborhood_name], self.stretch_rent),
            "count": len(top),
            "results": top,
        }

    def build_feed(self) -> dict[str, Any]:
        neighborhoods = sorted(
            self.load_neighborhoods(),
            key=lambda item: float(item.get("composite") or 0),
            reverse=True,
        )
        by_name = {item["name"]: item for item in neighborhoods}
        enriched: list[dict[str, Any]] = []
        for hood in neighborhoods:
            candidates = self.fetch_search_candidates(hood)
            if not candidates:
                continue
            with ThreadPoolExecutor(max_workers=self.max_workers) as pool:
                futures = [pool.submit(self.enrich_candidate, candidate, by_name) for candidate in candidates]
                for future in as_completed(futures):
                    record = future.result()
                    if record:
                        enriched.append(record)
            if len(enriched) >= self.output_count * 2:
                break

        return self.build_output(enriched)

    def write_feed(self) -> dict[str, Any] | None:
        payload = self.build_feed()
        if not payload["apartments"]:
            print("No verified apartments found; leaving existing feed untouched")
            return None
        self.output_json.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n")
        print(f"Wrote {len(payload['apartments'])} apartments to {self.output_json}")
        return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="StreetEasy apartment scraping API")
    sub = parser.add_subparsers(dest="command", required=True)

    top = sub.add_parser("top", help="Build the daily Top Apartments feed")
    top.add_argument("--json", action="store_true", help="Print compact JSON to stdout")

    search = sub.add_parser("search", help="Search one neighborhood")
    search.add_argument("--neighborhood", required=True)
    search.add_argument("--count", type=int, default=3)
    search.add_argument("--json", action="store_true", help="Print compact JSON to stdout")

    args = parser.parse_args(argv)
    api = StreetEasyAPI()

    if args.command == "top":
        payload = api.build_feed()
        if not payload["apartments"]:
            print("No verified apartments found; leaving existing feed untouched")
            return 0
        if args.json:
            print(json.dumps(payload, ensure_ascii=False, separators=(",", ":")))
        else:
            api.output_json.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n")
            print(f"Wrote {len(payload['apartments'])} apartments to {api.output_json}")
        return 0

    if args.command == "search":
        payload = api.search_neighborhood(args.neighborhood, count=args.count)
        if args.json:
            print(json.dumps(payload, ensure_ascii=False, separators=(",", ":")))
        else:
            print(json.dumps(payload, ensure_ascii=False, indent=2))
        return 0

    return 1


if __name__ == "__main__":
    raise SystemExit(main())
