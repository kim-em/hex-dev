#!/usr/bin/env python3
"""Independent exact modular RREF and shared row-derivation oracle.

Uses Python integers and pow(a, -1, p), independently of the packed Lean
storage, Barrett arithmetic and forward sparse/dense elimination. Checks both
row-space containments by canonical RREF, not only rank. No CAS dependency.
"""
from __future__ import annotations

import argparse
import json
from math import isqrt
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.oracle.common import write_failure


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rref(rows, columns, p):
    a = [row[:] for row in rows]
    rank = 0
    for j in range(columns):
        pivot = next((i for i in range(rank, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inv = pow(a[rank][j], -1, p)
        a[rank] = [x * inv % p for x in a[rank]]
        for i in range(len(a)):
            if i != rank and a[i][j]:
                c = a[i][j]
                a[i] = [(x - c * y) % p for x, y in zip(a[i], a[rank])]
        rank += 1
    return a[:rank]


def check(value):
    p, n = value["p"], value["columns"]
    require(type(p) is int and 2 <= p < 2**31, "invalid prime range")
    require(all(p % d for d in range(2, isqrt(p) + 1)), "composite field")
    require(type(n) is int and n >= 0, "invalid dimension")
    reducers, targets, output = value["reducers"], value["targets"], value["rows"]
    inputs = reducers + targets
    for row in inputs + output:
        require(len(row) == n and all(type(x) is int and 0 <= x < p for x in row),
                "invalid matrix row")
    leading = [next((j for j, x in enumerate(row) if x), None) for row in output]
    require(all(j is not None for j in leading), "zero output row")
    require(leading == sorted(set(leading)), "not echelon in fixed columns")
    require(all(row[j] == 1 for row, j in zip(output, leading)), "nonmonic pivot")
    require(rref(inputs, n, p) == rref(output, n, p), "different row spaces")
    rank = len(rref(reducers, n, p))
    flags, refs = value["fromTarget"], value["refs"]
    require(len(flags) == len(output) == len(refs), "metadata length")
    require(all(type(flag) is bool for flag in flags), "invalid origin flag")
    require(value["reducerRank"] == rank == flags.count(False), "reducer rank")
    retained = [row for row, flag in zip(output, flags) if not flag]
    require(rref(retained, n, p) == rref(reducers, n, p), "lost reducer subspace")
    replay(inputs, output, value["trace"], refs, p)
    if "remainders" in value:
        output = value["remainders"]
        require(len(output) == len(targets), "lost zero or reordered target")
        for row in output:
            require(len(row) == n and all(type(x) is int and 0 <= x < p for x in row),
                    "invalid remainder row")
        pivots = rref(reducers, n, p)
        expected = []
        for target in targets:
            row = target[:]
            for pivot in pivots:
                j = next(j for j, c in enumerate(pivot) if c)
                c = row[j]
                row = [(x - c * y) % p for x, y in zip(row, pivot)]
            expected.append(row)
        require(output == expected, "independent target remainder or scalar mismatch")
        require(len(value["remainderRefs"]) == len(output), "remainder metadata length")
        replay(inputs, output, value["remainderTrace"], value["remainderRefs"], p)


def replay(inputs, output, trace, refs, p):
    nodes = []
    for node in trace:
        require(isinstance(node, list) and node, "invalid derivation node")
        tag = node[0]
        if tag == 0:
            require(len(node) == 2 and type(node[1]) is int and 0 <= node[1] < len(inputs),
                    "bad input reference")
            row = inputs[node[1]][:]
        else:
            require(tag in (1, 2) and len(node) == (4 if tag == 1 else 3), "bad operation")
            indices = node[1:-1]
            require(all(type(i) is int and 0 <= i < len(nodes) for i in indices),
                    "forward or invalid reference")
            c = node[-1]
            require(type(c) is int and 0 < c < p, "invalid operation coefficient")
            row = ([c * x % p for x in nodes[indices[0]]] if tag == 2 else
                   [(x + c * y) % p for x, y in zip(nodes[indices[0]], nodes[indices[1]])])
        nodes.append(row)
    for row, ref in zip(output, refs):
        require(type(ref) is int and 0 <= ref < len(nodes), "invalid output reference")
        require(nodes[ref] == row, "incorrect row derivation")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path, help="read a committed stream instead of stdin")
    parser.add_argument("--profile", default="core")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--failure-dir", type=Path, default=Path("conformance-failures"))
    args = parser.parse_args()
    count = 0
    seen = set()
    stream = args.check.read_text() if args.check else sys.stdin.read()
    for line in stream.splitlines():
        record = json.loads(line)
        try:
            require(record["lib"] == "HexGroebner" and record["op"] == "eliminate", "record kind")
            require(record["case"] not in seen, "duplicate case")
            seen.add(record["case"])
            require("remainders" in record["value"], "missing independent target profile")
            check(record["value"])
        except (ValueError, KeyError, TypeError, IndexError) as exc:
            path = write_failure(args.failure_dir, library="HexGroebner", profile=args.profile,
                seed=args.seed, case_id=record.get("case", "unknown"), kind="matrix",
                input_record=record, lean_output=record.get("value"), oracle_output=None,
                oracle_name="Python exact modular RREF and row derivation replay",
                oracle_version=sys.version.split()[0], diff=str(exc))
            raise SystemExit(f"{record.get('case')}: {exc}; replay: {path}") from exc
        count += 1
    require(count == 175, f"incomplete matrix corpus: {count}")
    print(f"OK: {count} prime-field matrices: echelon, row space, reducer space, independent target remainders, derivations")


if __name__ == "__main__":
    main()
