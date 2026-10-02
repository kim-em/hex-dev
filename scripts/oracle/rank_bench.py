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


def validate_entry(kind, entry):
    if kind == "polymatrix":
        if len(entry["num"]) != len(entry["den"]):
            raise ValueError("polynomial coefficient/denominator length mismatch")
        if any(int(den) == 0 for den in entry["den"]):
            raise ValueError("zero polynomial coefficient denominator")
    else:
        for exponents, _ in entry:
            if len(exponents) != 2 or any(int(e) < 0 for e in exponents):
                raise ValueError("invalid polynomial exponents")


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
            validate_entry(kind, entry)
    return (PolyCarrier(record) if kind == "polymatrix" else MvPolyCarrier(record)).A



def decode_certificate(record, certificate):
    """Prepare the exact ring identities, excluding all decoding from timing."""
    from sympy.polys.matrices import DomainMatrix
    kind = record["kind"]
    if kind not in {"polymatrix", "mvpolymatrix"}:
        raise ValueError("certificate comparisons use polynomial carriers")
    carrier = PolyCarrier(record) if kind == "polymatrix" else MvPolyCarrier(record)
    A = carrier.A
    n, m = A.shape
    r = int(certificate["rank"])
    rows, cols = certificate["rows"], certificate["cols"]
    adj = certificate["adj"]
    if (r < 0 or len(rows) != r or len(cols) != r or len(set(rows)) != r or len(set(cols)) != r
            or any(i < 0 or i >= n for i in rows) or any(j < 0 or j >= m for j in cols)
            or len(adj) != r or any(len(row) != r for row in adj)):
        raise ValueError("invalid certificate shape or pivot indices")
    for entry in [certificate["denom"], *(x for row in adj for x in row)]:
        validate_entry(kind, entry)
    D = DomainMatrix([[carrier.entry(x) for x in row] for row in adj], (r, r), A.domain)
    denom = carrier.entry(certificate["denom"])
    return (A, rows, cols, D, denom)


def second_rank(data):
    """Time the augmented elimination; rank r is not an independent B-validity test.

    Preparation separately verifies the original rank and certificate identities.
    """
    from sympy.polys.matrices import DomainMatrix
    A, rows, cols, _, _ = data
    B = A.extract(rows, cols)
    augmented = B.hstack(DomainMatrix.eye(B.shape, A.domain).to_dense())
    return int(augmented.rank())


def check_certificate(data):
    from sympy.polys.matrices import DomainMatrix
    A, rows, cols, adj, denom = data
    n, m = A.shape
    B = A.extract(rows, cols)
    C = A.extract(list(range(n)), cols)
    R = A.extract(rows, list(range(m)))
    identity = DomainMatrix.eye(B.shape, A.domain).to_dense()
    return bool(denom and B.matmul(adj) == identity.scalarmul(denom)
                and A.scalarmul(denom) == C.matmul(adj.matmul(R)))


def main():
    matrix = None
    certificate = None
    for line in sys.stdin:
        try:
            request = json.loads(line)
            op = request["op"]
            if op == "prepare":
                matrix = None
                certificate = None
                prepared = decode(request["record"])
                prepared_certificate = None
                if "certificate" in request:
                    prepared_certificate = decode_certificate(request["record"], request["certificate"])
                # Optional untimed fixture capture for coefficient-growth audits.
                if capture := os.environ.get("HEX_RANK_BENCH_CAPTURE"):
                    with open(capture, "a") as output:
                        output.write(json.dumps(request, separators=(",", ":")) + "\n")
                matrix = prepared
                certificate = prepared_certificate
                result = True
            elif op == "rank":
                if matrix is None:
                    raise ValueError("rank requested before successful prepare")
                result = int(matrix.rank())
            elif op == "second":
                if certificate is None:
                    raise ValueError("second pass requested before certificate preparation")
                result = second_rank(certificate)
            elif op == "check":
                if certificate is None:
                    raise ValueError("check requested before certificate preparation")
                result = check_certificate(certificate)
            elif op == "overhead":
                result = 0
            elif op == "versions":
                result = {"python": sys.version, "python_flint": flint.__version__, "flint": flint.__FLINT_VERSION__, "sympy": sympy.__version__, "sympy_ground_types": os.environ["SYMPY_GROUND_TYPES"]}
            else:
                raise ValueError(f"unknown operation: {op}")
            reply = {"ok": True, "result": result}
        except Exception as exc:
            reply = {"ok": False, "error": f"{type(exc).__name__}: {exc}"}
        print(json.dumps(reply, separators=(",", ":")), flush=True)


if __name__ == "__main__":
    main()
