#!/usr/bin/env python3
from __future__ import annotations

from streeteasy_api import StreetEasyAPI


def main() -> None:
    api = StreetEasyAPI()
    api.write_feed()


if __name__ == "__main__":
    main()
