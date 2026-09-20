#!/usr/bin/env python3
"""Persistent exact-domain rank comparator for HexRank's LeanBench targets.

One JSON request and reply per line. ``prepare`` accepts a conformance-format
``record`` and replaces the sole cached matrix; ``rank`` computes its rank.
Input decoding is preparation. Every rank request recomputes the answer, with
no result cache. ``overhead`` returns zero; ``versions`` reports the engines.
The process lives for one LeanBench child's warmup and inner-repeat batch.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import sys

os.environ["SYMPY_GROUND_TYPES"] = "python"
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

import flint
import sympy
from scripts.oracle.rank_carriers import PolyCarrier, MvPolyCarrier


def decode(record):
    kind = record["kind"]
    if kind in {"matrix", "ratmatrix"}:
        rows = record["rows"]
        n = len(rows)
        m = len(rows[0]) if n else 0
        if any(len(row) != m for row in rows):
            raise ValueError("ragged matrix")
        if kind == "matrix":
            return flint.fmpz_mat(n, m, [int(x) for row in rows for x in row])
        return flint.fmpq_mat(n, m, [flint.fmpq(int(a), int(b)) for row in rows for a, b in row])
    if kind not in {"polymatrix", "mvpolymatrix"}:
        raise ValueError(f"unsupported carrier: {kind}")
    if kind == "polymatrix" and "p" in record["field"]:
        raise ValueError("rank benchmark supports QQ[x], not finite-field polynomial carriers")
    if kind == "mvpolymatrix" and int(record["arity"]) != 2:
        raise ValueError("rank benchmark supports exactly two polynomial variables")
    n, m = int(record["rows"]), int(record["cols"])
    if n < 0 or m < 0 or len(record["entries"]) != n or any(len(row) != m for row in record["entries"]):
        raise ValueError("polynomial matrix shape mismatch")
    for row in record["entries"]:
        for entry in row:
            if kind == "polymatrix":
                if len(entry["num"]) != len(entry["den"]):
                    raise ValueError("polynomial coefficient/denominator length mismatch")
                if any(int(den) == 0 for den in entry["den"]):
                    raise ValueError("zero polynomial coefficient denominator")
            else:
                for exponents, _ in entry:
                    if len(exponents) != 2 or any(int(e) < 0 for e in exponents):
                        raise ValueError("invalid polynomial exponents")
    return (PolyCarrier(record) if kind == "polymatrix" else MvPolyCarrier(record)).A


def main():
    matrix = None
    for line in sys.stdin:
        try:
            request = json.loads(line)
            op = request["op"]
            if op == "prepare":
                matrix = None
                matrix = decode(request["record"])
                result = True
            elif op == "rank":
                if matrix is None:
                    raise ValueError("rank requested before successful prepare")
                result = int(matrix.rank())
            elif op == "overhead":
                result = 0
            elif op == "versions":
                result = {"python": sys.version, "python_flint": flint.__version__, "sympy": sympy.__version__, "sympy_ground_types": os.environ["SYMPY_GROUND_TYPES"]}
            else:
                raise ValueError(f"unknown operation: {op}")
            reply = {"ok": True, "result": result}
        except Exception as exc:
            reply = {"ok": False, "error": f"{type(exc).__name__}: {exc}"}
        print(json.dumps(reply, separators=(",", ":")), flush=True)


if __name__ == "__main__":
    main()
