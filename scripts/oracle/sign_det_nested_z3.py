#!/usr/bin/env python3
"""Check actual BKR tables at four infinitesimal depths against pinned Z3 RCF."""
from __future__ import annotations

import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.oracle.common import OracleMismatch, read_fixtures, write_failure
from scripts.oracle.sign_det_common import require, sign_vector
from scripts.oracle.sign_det_z3 import RCF, VERSION, check_version

DEFAULT_FIXTURE = ROOT / "conformance-fixtures/HexSignDet/nested-fields.jsonl"
LOCAL_FIXTURE = ROOT / "conformance-fixtures/HexSignDet/nested-fields-local.jsonl"
CASES = [f"nested-field/depth-{depth}" for depth in range(1, 5)]


def check_record(record):
    require(record.get("lib") == "HexSignDet" and record.get("op") == "table",
            "wrong nested-field operation")
    row = record["value"]
    depth = row["extensionDepth"]
    require(type(depth) is int and 1 <= depth <= 4 and
            record.get("case") == f"nested-field/depth-{depth}", "wrong field depth")
    require(row.get("family") == "nested-infinitesimal-coefficients", "wrong field family")
    require(row.get("zeroDomainRejected") is True, "depth-zero domain was accepted")
    context = row["coefficientContext"]
    require(len(context["levels"]) == depth, "coefficient depth differs")
    oracle = RCF(context, maximum_depth=4)
    result = row["result"]
    require(result.get("status") == "ok", "native construction failed")
    require(type(result.get("generatorSign")) is int and result["generatorSign"] == 1,
            "wrong nested generator sign")
    require(type(result.get("anchorDifferenceSign")) is int and result["anchorDifferenceSign"] == -1,
            "newest-level cancellation sign is wrong")
    require(result.get("foreignChildValid") is True, "foreign-head leaf is not valid on its own head")
    g = oracle.levels[0] - oracle.levels[0]*oracle.levels[0]
    anchor = oracle.levels[0]
    for epsilon in oracle.levels[1:]:
        anchor = g
        g = g - epsilon
    raw = result["input"]
    require(g > 0 and oracle.poly(raw["head"]) == [-g*g, oracle.zero, oracle.one] and
            [oracle.poly(q) for q in raw["queries"]] ==
            [[-g, oracle.one], [-anchor, oracle.one]], "wrong literal nested-field inputs")
    for name in ("reduced", "direct", "reference"):
        mode = result[name]
        require(mode.get("status") == "ok" and mode.get("replay") is True,
                "native table construction or replay failed")
        require(isinstance(mode["table"], list) and all(
            isinstance(pair, list) and len(pair) == 2 and sign_vector(pair[0], 2) and
            type(pair[1]) is int and pair[1] > 0 for pair in mode["table"]), "malformed sign table")
        if name != "reference":
            require(mode.get("graphReplay") is True and mode.get("leafLayout") is True,
                    "graph replay or leaf-layout check failed")
            require(all(mode.get(key) is False for key in
                        ("foreignContextReplay", "staleChildReplay", "copiedHeadReplay", "copiedMomentReplay", "missingSupportReplay")),
                    "stale or incomplete evidence was accepted")
    data = {"head": raw["head"], "queries": raw["queries"], "lower": "-inf", "upper": "+inf"}
    expected = oracle.table(data)
    require(expected is not None, "independent oracle rejected the root domain")
    expected = [[entry["signs"], entry["count"]] for entry in expected]
    for name in ("reduced", "direct", "reference"):
        require(result[name]["table"] == expected, "table differs from independent exact roots and signs")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?", type=Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--profile", choices=("ci", "local"), default="ci")
    parser.add_argument("--seed", type=int, default=10377)
    parser.add_argument("--failure-dir", type=Path, default=ROOT / "conformance-failures")
    args = parser.parse_args()
    try:
        check_version()
        seen = []
        failed = 0
        fixture = LOCAL_FIXTURE if args.profile == "local" else DEFAULT_FIXTURE
        cases = CASES if args.profile == "local" else CASES[:2]
        for record in read_fixtures(args.source or (fixture if args.check else None)):
            try:
                check_record(record)
                seen.append(record["case"])
            except (OracleMismatch, KeyError, TypeError, ValueError, ArithmeticError) as exc:
                failed += 1
                write_failure(args.failure_dir, library="HexSignDet", profile=args.profile,
                              seed=args.seed, case_id=record.get("case", "missing"), kind="nested-fields",
                              input_record=record, lean_output=record.get("value"), oracle_output=None,
                              oracle_name="Z3 RCF", oracle_version=VERSION, diff=str(exc))
                print(f"FAIL: {exc}", file=sys.stderr)
        require(seen == cases, "missing, duplicated or reordered nested-field cases")
        print(f"HexSignDet: {len(seen)} nested-field cases, {failed} failures ({VERSION})")
        return int(failed != 0)
    except (OracleMismatch, OSError, ImportError) as exc:
        print(f"FAIL: nested-field oracle: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
