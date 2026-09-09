#!/usr/bin/env python3
"""Check complete search traces against committed expected records.

Emit with ``lake exe hexgraphiso_emit_trace > /tmp/graphiso-trace.jsonl``.
Check with ``python3 scripts/oracle/graphiso_trace.py /tmp/graphiso-trace.jsonl``.
For an intentional traversal change, regenerate with ``--record --source SHA``
and review the changed records alongside the independent nauty oracle results.
"""
# Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Kim Morrison

from __future__ import annotations

import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
EXPECTED = ROOT / "conformance-fixtures/HexGraphIso/trace.jsonl.gz"
META = ROOT / "conformance-fixtures/HexGraphIso/trace.meta.json"
FIELDS = {"canonlab", "canong", "numnodes", "numorbits", "numgenerators",
          "numbadleaves", "maxlevel", "tctotal", "canupdates", "autos",
          "bestCodes", "orbits", "exit"}


def encode(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def load(path: Path) -> dict[tuple[str, str], dict]:
    records = {}
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt") as stream:
        for number, line in enumerate(stream, 1):
            row = json.loads(line)
            if (not isinstance(row, dict) or set(row) != {"corpus", "name", "input", "output"}
                    or not isinstance(row["corpus"], str) or not row["corpus"]
                    or not isinstance(row["name"], str) or not row["name"]
                    or not isinstance(row["input"], dict)
                    or set(row["input"]) != {"n", "k", "colors", "edges"}
                    or not isinstance(row["output"], dict) or set(row["output"]) != FIELDS):
                raise ValueError(f"{path}:{number}: invalid trace record")
            key = row["corpus"], row["name"]
            if key in records:
                raise ValueError(f"{path}:{number}: duplicate case {key}")
            records[key] = row
    if not records:
        raise ValueError(f"{path}: empty trace")
    return records


def metadata(records: dict, source: str) -> dict:
    corpus = hashlib.sha256()
    trace = hashlib.sha256()
    for key, row in sorted(records.items()):
        corpus.update(encode([*key, row["input"]]))
        trace.update(encode(row))
    return {"schema": 1, "source": source, "records": len(records),
            "corpora": dict(sorted(Counter(k[0] for k in records).items())),
            "corpus_sha256": corpus.hexdigest(), "trace_sha256": trace.hexdigest()}


def difference(expected: object, actual: object, field: str = "") -> str | None:
    if type(expected) is not type(actual):
        return field + " (type)"
    if isinstance(expected, dict):
        if expected.keys() != actual.keys():
            return field + " (fields)"
        for name in sorted(expected):
            if result := difference(expected[name], actual[name], f"{field}.{name}".lstrip(".")):
                return result
    elif isinstance(expected, list):
        if len(expected) != len(actual):
            return field + ".length"
        for i, (a, b) in enumerate(zip(expected, actual)):
            if result := difference(a, b, f"{field}[{i}]"):
                return result
    elif expected != actual:
        return field
    return None


def check(expected: dict, actual: dict) -> None:
    missing = expected.keys() - actual.keys()
    added = actual.keys() - expected.keys()
    if missing or added:
        raise ValueError(f"trace cases differ: missing={sorted(missing)[:3]}, added={sorted(added)[:3]}")
    for key in sorted(expected):
        if field := difference(expected[key], actual[key]):
            raise ValueError(f"trace mismatch {key[0]}/{key[1]}: {field}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("actual", type=Path)
    parser.add_argument("--expected", type=Path, default=EXPECTED)
    parser.add_argument("--metadata", type=Path, default=META)
    parser.add_argument("--record", action="store_true")
    parser.add_argument("--source", help="full source commit, required with --record")
    args = parser.parse_args()
    if args.record != bool(args.source):
        parser.error("--record and --source must be supplied together")
    if args.source and not re.fullmatch(r"[0-9a-f]{40}", args.source):
        parser.error("--source must be a full Git commit ID")
    try:
        actual = load(args.actual)
        if args.record:
            for key, row in actual.items():
                if row["output"]["exit"] != {"kind": "unwind", "level": 0, "short": False}:
                    raise ValueError(f"{key}: normal root did not terminate")
            data = b"".join(encode(row) for _, row in sorted(actual.items()))
            args.expected.write_bytes(gzip.compress(data, mtime=0))
            args.metadata.write_text(json.dumps(metadata(actual, args.source), indent=2) + "\n")
            print(f"recorded {len(actual)} search traces at {args.source}")
        else:
            expected = load(args.expected)
            recorded = json.loads(args.metadata.read_text())
            if recorded != metadata(expected, recorded["source"]):
                raise ValueError("trace metadata does not describe the committed records")
            check(expected, actual)
            print(f"search traces: {len(actual)} cases match committed records")
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"search trace check failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
