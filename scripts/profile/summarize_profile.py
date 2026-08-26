#!/usr/bin/env python3
"""Summarize a filtered lean-bench-samply profile with symbolized Lean names."""

from __future__ import annotations

import argparse
import gzip
import json
from pathlib import Path

from factor_sampling_profile import Symbolicator, analyse


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", type=Path)
    parser.add_argument("--symbols", type=Path)
    parser.add_argument("--diagnostics", type=Path)
    parser.add_argument("--thread", required=True)
    parser.add_argument("--top", type=int, default=20)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    symbols = args.symbols or Path(str(args.profile).removesuffix(".json.gz") + ".json.syms.json")
    diagnostics = args.diagnostics or Path(str(args.profile) + ".diagnostics.json")
    with gzip.open(args.profile) as handle:
        profile = json.load(handle)
    summary = analyse(profile, Symbolicator(symbols), args.top, args.thread)
    document = {
        "profile": str(args.profile),
        "symbols": str(symbols),
        "diagnostics": json.loads(diagnostics.read_text()),
        **summary,
    }
    rendered = json.dumps(document, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
