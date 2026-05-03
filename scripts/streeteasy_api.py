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

IN_UNIT_LAUNDRY_RE = re.compile(
    r"(?i)(washer/dryer(?: in unit)?|washer in unit|dryer in unit|in[- ]unit laundry|in[- ]unit washer)"
)
BUILDING_LAUNDRY_RE = re.compile(r"(?i)(laundry in building|laundry room)")
EXCLUDE_RE = re.compile(r"(?i)room for rent|shared apartment|co-?living|sublet")
NO_FEE_RE = re.compile(r"(?i)no.?fee")
PRICE_RE = re.compile(r"\$([\d,]+)\s*/mo")
BLOCKED_PAGE_RE = re.compile(
    r"(?i)access to this page has been denied|please enable javascript|verify you are human|captcha"
)
HARD_AVOID_NEIGHBORHOODS = {"Washington Heights"}
HARD_AVOID_ROB_RATE = 2.0
SEARCH_MODES = ("0,1", "0", "1")
MAX_SHORTLIST_EFFECTIVE = 2900
MAX_VIABLE_EFFECTIVE = 3200
MAX_WATCH_EFFECTIVE = 3450

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


def is_hard_avoid_neighborhood(hood: dict[str, Any]) -> bool:
    name = str(hood.get("name") or "")
    note = str(hood.get("note") or "")
    station_safety = str(hood.get("station_safety") or "")
    rob_rate = float(hood.get("rob_rate") or 0)
    return (
        name in HARD_AVOID_NEIGHBORHOODS
        or rob_rate > HARD_AVOID_ROB_RATE
        or "강력 제외" in note
        or "Hard Avoid" in note
        or "강력 제외" in station_safety
        or "Hard Avoid" in station_safety
    )


def normalize_confidence(value: Any) -> str:
    raw = str(value or "").lower()
    return raw if raw in {"high", "medium", "low"} else "medium"


def station_risk_level(hood: dict[str, Any]) -> str:
    if hood.get("station_risk"):
        raw = str(hood.get("station_risk")).lower()
        return raw if raw in {"low", "moderate", "high"} else "moderate"
    text = str(hood.get("station_safety") or "").lower()
    if hood.get("tax") == "NJ" or text == "n/a":
        return "moderate"
    if "elevated" in text or "높음" in text:
        return "high"
    if "moderate" in text or "보통" in text:
        return "moderate"
    if "low" in text or "낮음" in text:
        return "low"
    return "moderate"


def safe_station(hood: dict[str, Any]) -> bool:
    return station_risk_level(hood) != "high"


def calc_price_score(rent: int) -> int:
    if rent <= 2400:
        return 100
    if rent <= 2600:
        return 80
    if rent <= 2800:
        return 55
    if rent <= 3000:
        return 30
    if rent <= 3200:
        return 10
    return 0


def calc_commute_score(mins: int) -> float:
    penalty = max(0, mins - 18) * 2.35
    rush_penalty = (mins - 45) * 2 if mins > 45 else 0
    return max(0.0, min(100.0, 100.0 - penalty - rush_penalty))


def calc_hood_safety_score(hood: dict[str, Any]) -> float:
    return max(0.0, min(100.0, 100.0 - (float(hood.get("rob_rate") or 0) * 18) - (float(hood.get("burg_rate") or 0) * 6)))


def calc_transit_safety_score(hood: dict[str, Any]) -> int:
    risk = station_risk_level(hood)
    if risk == "low":
        return 85
    if risk == "high":
        return 20
    return 60


def calc_laundry_score(value: str) -> int:
    if value == "Common":
        return 100
    if value == "Mixed":
        return 60
    return 10


def calc_late_score(value: Any) -> int:
    return max(0, min(100, int(value or 0)))


def calc_building_score(value: Any) -> int:
    return max(0, min(100, int(value or 0)))


def derive_scores(hood: dict[str, Any]) -> dict[str, Any]:
    return {
        "price": calc_price_score(int(rent_basis(hood))),
        "hood_safety": calc_hood_safety_score(hood),
        "transit_safety": calc_transit_safety_score(hood),
        "commute": calc_commute_score(int(hood.get("min") or 0)),
        "laundry": calc_laundry_score(str(hood.get("ltxt") or "")),
        "late": calc_late_score(hood.get("late")),
        "bldg": calc_building_score(hood.get("bldg")),
    }


def rent_basis(hood: dict[str, Any]) -> int:
    studio = int(hood.get("studio") or 0)
    if studio > 0:
        return studio
    return int(hood.get("rent") or 0)


def effective_cost_for_hood(hood: dict[str, Any]) -> int:
    transit_cost = int(hood.get("transit_cost") or 0)
    tax_credit = 246 if hood.get("tax") == "NJ" else 0
    return rent_basis(hood) + transit_cost - tax_credit


def laundry_pass(hood: dict[str, Any]) -> bool:
    return str(hood.get("ltxt") or "") != "Rare"


def classify_laundry_text(text: str) -> tuple[str, str] | None:
    if IN_UNIT_LAUNDRY_RE.search(text):
        return "방 안 세탁기 있음", "in_unit"
    if BUILDING_LAUNDRY_RE.search(text):
        return "아파트 공용 세탁기 있음", "building"
    return None


def solo_rent_fit(hood: dict[str, Any]) -> dict[str, bool]:
    studio = int(hood.get("studio") or 0)
    one_br = int(hood.get("one_br") or 0)
    return {
        "studio": studio <= TARGET_RENT,
        "onebr": one_br <= TARGET_RENT,
        "studioStretch": studio <= STRETCH_RENT,
        "onebrStretch": one_br <= STRETCH_RENT,
    }


def fit_info(hood: dict[str, Any]) -> dict[str, str]:
    eff = effective_cost_for_hood(hood)
    laundry = laundry_pass(hood)
    commute = int(hood.get("min") or 0) <= 45
    safe_night = safe_station(hood)
    composite = float(hood.get("composite") or 0)
    if is_hard_avoid_neighborhood(hood):
        return {
            "status": "Hard Avoid",
            "reason": "강력 제외: 168th St A 역 관련 위험이 여전히 큽니다",
        }
    if not laundry:
        return {
            "status": "Laundry Gate",
            "reason": "세탁 미충족: 건물 내 세탁 선택지가 거의 없습니다",
        }
    if eff <= MAX_SHORTLIST_EFFECTIVE and commute and safe_night and composite >= 48:
        return {
            "status": "Shortlist",
            "reason": "실질비용, 통근, 역 주변 체감 안전의 균형이 좋습니다",
        }
    if eff <= MAX_VIABLE_EFFECTIVE and int(hood.get("min") or 0) <= 52:
        return {
            "status": "Viable",
            "reason": "비용과 통근은 대체로 괜찮고 세탁 조건도 무난합니다",
        }
    if eff <= MAX_WATCH_EFFECTIVE and int(hood.get("min") or 0) <= 60:
        return {
            "status": "Watch",
            "reason": "검토는 가능하지만 실질비용이나 통근이 조금 아쉽습니다",
        }
    return {
        "status": "Avoid",
        "reason": "가격이나 핵심 조건이 기준에 많이 못 미칩니다",
    }


def solo_rent_status(hood: dict[str, Any]) -> dict[str, str]:
    fit = solo_rent_fit(hood)
    eff = effective_cost_for_hood(hood)
    laundry = laundry_pass(hood)
    commute = int(hood.get("min") or 0) <= 45
    safe_night = safe_station(hood)
    composite = float(hood.get("composite") or 0)
    if is_hard_avoid_neighborhood(hood):
        return {
            "status": "Hard Avoid",
            "reason": "강력 제외: 168th St A 역 관련 위험이 여전히 큽니다",
        }
    if not laundry:
        return {
            "status": "Laundry Gate",
            "reason": "세탁 미충족: 건물 내 세탁 선택지가 거의 없습니다",
        }
    if (fit["studio"] or fit["onebr"]) and commute and safe_night and composite >= 48:
        if fit["studio"] and fit["onebr"]:
            reason = "스튜디오와 1BR 모두 $2,350 이내입니다"
        elif fit["studio"]:
            reason = "스튜디오가 $2,350 이내입니다"
        else:
            reason = "1BR이 $2,350 이내입니다"
        return {"status": "Target", "reason": reason}
    if (fit["studioStretch"] or fit["onebrStretch"]) and commute and safe_night and eff <= MAX_SHORTLIST_EFFECTIVE:
        return {
            "status": "Stretch",
            "reason": "예산은 조금 넘지만 통근과 전체 조건은 아직 괜찮습니다",
        }
    if fit["studio"] or fit["onebr"]:
        return {
            "status": "Watch",
            "reason": "월세는 맞지만 통근이나 역 주변 체감 안전이 아쉽습니다",
        }
    return {
        "status": "No 40x Solo",
        "reason": "Studio와 1BR 모두 $2,350을 넘습니다",
    }


def recommendation_tier(hood: dict[str, Any]) -> int:
    fit = fit_info(hood)["status"]
    solo = solo_rent_status(hood)["status"]
    reliable = normalize_confidence(hood.get("data_confidence")) != "low"
    if reliable and fit == "Shortlist" and solo == "Target":
        return 0
    if reliable and fit == "Viable" and solo in {"Target", "Stretch"}:
        return 1
    if reliable and fit == "Shortlist" and solo == "Stretch":
        return 2
    if reliable and fit == "Watch" and solo in {"Target", "Stretch"}:
        return 3
    if reliable and fit == "Viable":
        return 4
    if fit == "Laundry Gate":
        return 7
    if fit == "Hard Avoid":
        return 9
    return 6


def recommendation_label(tier: int) -> str:
    if tier <= 1:
        return "우선 검토"
    if tier <= 3:
        return "다음 후보"
    return "조건 재검토"


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

    def _cache_path(self, url: str, source: str) -> Path:
        digest = hashlib.sha1(f"{source}:{url}".encode("utf-8")).hexdigest()
        return self.cache_dir / f"{digest}.txt"

    def _read_cache(self, url: str, source: str) -> str | None:
        path = self._cache_path(url, source)
        if not path.exists():
            return None
        age = time.time() - path.stat().st_mtime
        if age > self.cache_ttl_seconds:
            return None
        try:
            return path.read_text()
        except Exception:
            return None

    def _write_cache(self, url: str, text: str, source: str) -> None:
        try:
            self._cache_path(url, source).write_text(text)
        except Exception:
            pass

    def fetch_text(self, url: str, timeout: int = 18, allow_jina: bool = True) -> str:
        cached = self._read_cache(url, "direct")
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
                    self._write_cache(url, text, "direct")
                    return text
                last_error = RuntimeError(f"{url} returned blocked content")
            except Exception as exc:  # pragma: no cover - network fallback
                last_error = exc

        if allow_jina:
            cached_jina = self._read_cache(url, "jina")
            if cached_jina is not None:
                return cached_jina
            for delay in (0, 2, 5):
                if delay:
                    time.sleep(delay)
                try:
                    response = pyrequests.get(f"https://r.jina.ai/{url}", timeout=timeout)
                    response.raise_for_status()
                    text = response.text or ""
                    if text:
                        self._write_cache(url, text, "jina")
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

    def _canonical_search_url(self, slug: str, beds: str, max_rent: int) -> str:
        bed_code = "0" if beds == "Studio" else "1"
        return f"https://streeteasy.com/for-rent/{slug}?beds={bed_code}&price=-{max_rent}"

    def neighborhood_priority_key(self, hood: dict[str, Any]) -> tuple[Any, ...]:
        fit = fit_info(hood)["status"]
        solo = solo_rent_status(hood)["status"]
        reliable = normalize_confidence(hood.get("data_confidence")) != "low"
        tier = recommendation_tier(hood)
        fit_rank = {"Shortlist": 0, "Viable": 1, "Watch": 2, "Avoid": 3, "Laundry Gate": 4, "Hard Avoid": 5}.get(fit, 9)
        solo_rank = {"Target": 0, "Stretch": 1, "Watch": 2, "No 40x Solo": 3, "Laundry Gate": 4, "Hard Avoid": 5}.get(solo, 9)
        confidence_rank = {"high": 0, "medium": 1, "low": 2}.get(normalize_confidence(hood.get("data_confidence")), 1)
        return (
            tier,
            fit_rank,
            solo_rank,
            0 if reliable else 1,
            confidence_rank,
            -float(hood.get("composite") or 0),
            effective_cost_for_hood(hood),
            int(hood.get("min") or 0),
            str(hood.get("name") or ""),
        )

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
        markdown = self.fetch_text(search_url, allow_jina=True)
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

        laundry_info = classify_laundry_text(text) if text else None
        no_fee = bool(NO_FEE_RE.search(text)) if text else False
        price = candidate.price
        if not price:
            price_match = PRICE_RE.search(text)
            if price_match:
                price = int(price_match.group(1).replace(",", ""))
        if not price or price > self.stretch_rent:
            return None

        hood = by_name[candidate.neighborhood]
        if is_hard_avoid_neighborhood(hood):
            return None
        if not laundry_info:
            return None

        hood_fit = fit_info(hood)
        hood_solo = solo_rent_status(hood)
        hood_tier = recommendation_tier(hood)

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
        laundry_text, laundry_kind = laundry_info
        canonical_search_url = self._canonical_search_url(candidate.search_slug, candidate.beds, self.stretch_rent)

        summary_parts = [
            f"{candidate.beds} in {candidate.neighborhood}",
            f"출근 약 {commute}분",
            laundry_text,
            "무중개수수료 표기" if no_fee else "수수료 조건 확인 필요",
        ]
        listing_score = (
            float(hood.get("composite") or 0)
            + 18
            + (12 if price <= self.target_rent else 5)
            + (4 if no_fee else 0)
            - max(0, commute - 45) * 2.5
            - (10 if confidence == "low" else 0)
        )

        return {
            "neighborhood": candidate.neighborhood,
            "neighborhood_fit_status": hood_fit["status"],
            "neighborhood_fit_reason": hood_fit["reason"],
            "neighborhood_solo_status": hood_solo["status"],
            "neighborhood_solo_reason": hood_solo["reason"],
            "neighborhood_tier": hood_tier,
            "neighborhood_tier_label": recommendation_label(hood_tier),
            "address": candidate.address,
            "locality": candidate.locality,
            "beds": candidate.beds,
            "price": price,
            "rent_status": fit_status,
            "laundry": laundry_text,
            "laundry_kind": laundry_kind,
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
            "search_url": canonical_search_url,
            "route_url": route_url,
            "available": candidate.available,
        }

    @staticmethod
    def rank_key(item: dict[str, Any]) -> tuple[Any, ...]:
        confidence_rank = {"high": 0, "medium": 1, "low": 2}.get(item["source_confidence"], 1)
        return (
            int(item.get("neighborhood_tier") or 9),
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
                    "세탁기 있음이 확인된 매물만 남기고 강력 제외 동네를 배제한 뒤, "
                    "웹사이트와 같은 동네 tier 순서로 40x 기준($2,350) 충족 여부, 통근 시간, 신뢰도를 함께 반영합니다."
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
        if is_hard_avoid_neighborhood(hood):
            return {
                "neighborhood": neighborhood_name,
                "search_urls": self._search_urls(STREETEASY_PATHS[neighborhood_name], self.stretch_rent),
                "count": 0,
                "results": [],
                "note": "hard_avoid_neighborhood",
            }

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
        neighborhoods = [hood for hood in self.load_neighborhoods() if not is_hard_avoid_neighborhood(hood)]
        neighborhoods = sorted(neighborhoods, key=self.neighborhood_priority_key)
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
    search.add_argument("--max-rent", type=int, default=TARGET_RENT)
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
        search_api = StreetEasyAPI(
            target_rent=min(TARGET_RENT, args.max_rent),
            stretch_rent=args.max_rent,
            output_count=args.count,
        )
        payload = search_api.search_neighborhood(args.neighborhood, count=args.count)
        if args.json:
            print(json.dumps(payload, ensure_ascii=False, separators=(",", ":")))
        else:
            print(json.dumps(payload, ensure_ascii=False, indent=2))
        return 0

    return 1


if __name__ == "__main__":
    raise SystemExit(main())
