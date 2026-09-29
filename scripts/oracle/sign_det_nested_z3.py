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
CASES = [f"nested-field/depth-{depth}" for depth in range(1, 5)]


def check_record(record):
    require(record.get("lib") == "HexSignDet" and record.get("op") == "table",
            "wrong nested-field operation")
    row = record["value"]
    depth = row["extensionDepth"]
    require(type(depth) is int and 1 <= depth <= 4 and
            record.get("case") == f"nested-field/depth-{depth}", "wrong field depth")
    for key, expected in (("headDegree", 2), ("queries", 2), ("realizedSupport", 2)):
        require(type(row.get(key)) is int and row[key] == expected, "wrong input dimensions")
    require(row.get("family") == "nested-infinitesimal-coefficients", "wrong field family")
    require(all(row.get(key) is True for key in
                ("reduced", "unreduced", "fullReference", "foreignContextRejected", "staleChildRejected")),
            "native conformance or stale-evidence rejection failed")
    raw = row["input"]
    require(len(raw["coefficientContext"]["levels"]) == depth, "coefficient depth differs")
    oracle = RCF(raw["coefficientContext"], maximum_depth=4)
    g = oracle.zero
    for epsilon in oracle.levels:
        g = g + epsilon
    require(g > 0 and oracle.poly(raw["head"]) == [-g*g, oracle.zero, oracle.one] and
            [oracle.poly(q) for q in raw["queries"]] ==
            [[oracle.zero, oracle.one], [-g, oracle.one]], "wrong literal nested-field inputs")
    require(isinstance(row["table"], list) and all(
        isinstance(pair, list) and len(pair) == 2 and sign_vector(pair[0], 2) and
        type(pair[1]) is int and pair[1] > 0 for pair in row["table"]), "malformed sign table")
    data = {"head": raw["head"], "queries": raw["queries"], "lower": "-inf", "upper": "+inf"}
    expected = oracle.table(data)
    require(expected is not None and row["table"] ==
            [[entry["signs"], entry["count"]] for entry in expected],
            "table differs from independent exact roots and signs")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?", type=Path, default=DEFAULT_FIXTURE)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--profile", choices=("ci", "local"), default="ci")
    parser.add_argument("--seed", type=int, default=10377)
    parser.add_argument("--failure-dir", type=Path, default=ROOT / "conformance-failures")
    args = parser.parse_args()
    try:
        check_version()
        seen = []
        failed = 0
        for record in read_fixtures(args.source):
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
        require(seen == CASES, "missing, duplicated or reordered nested-field cases")
        print(f"HexSignDet: {len(seen)} nested-field cases, {failed} failures ({VERSION})")
        return int(failed != 0)
    except (OracleMismatch, OSError, ImportError) as exc:
        print(f"FAIL: nested-field oracle: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
