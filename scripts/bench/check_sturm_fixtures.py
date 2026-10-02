#!/usr/bin/env python3
"""Independently check serialized shared polynomial/query benchmark fixtures.

Uses pinned python-flint through the existing exact qqbar oracle and FLINT's
nmod_poly arithmetic. This checks mathematical outputs and certificate
identities; it makes no timing or phase-completion claim.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.oracle.realroots_flint import (  # noqa: E402
    _check_tarski_certificate, _tarski_expected,
)


def check_query(row: dict) -> None:
    cert = row["certificate"]
    endpoints = [cert["lower"], cert["upper"]]
    expected = _tarski_expected(cert["head"], cert["query"], endpoints)
    if expected is None or cert["value"] != expected:
        raise ValueError("query differs from exact qqbar root sum")
    records = {}

    def put(suffix: str, kind: str, value: list) -> None:
        field = "coeffs" if kind == "poly" else "rows"
        records[("benchmark", "query" + suffix)] = {"kind": kind, field: value}

    for name in ("squarefree", "remainders"):
        chain = cert[name]
        prefix = "/" + name
        put(prefix + "/chain", "matrix", chain["chain"])
        put(prefix + "/degrees", "matrix", [chain["degrees"]])
        # Lean's triples are right-associated products in the JSON encoding.
        u, (q, v) = chain["initial"]
        put(prefix + "/initial/scales", "matrix", [[u, v]])
        put(prefix + "/initial/quotient", "poly", q)
        put(prefix + "/steps/scales", "matrix", [[u, v] for u, (q, v) in chain["steps"]])
        put(prefix + "/steps/quotients", "matrix", [q for u, (q, v) in chain["steps"]])
        terminal = chain["terminal"]
        put(prefix + "/terminal/scale", "matrix", [[terminal[0]]] if terminal else [])
        put(prefix + "/terminal/quotient", "poly", terminal[1] if terminal else [])
    put("/signs", "matrix", [cert["lowerSigns"], cert["upperSigns"]])
    put("/variations", "matrix", [[cert["lowerVariations"], cert["upperVariations"]]])
    _check_tarski_certificate(records, "benchmark", "query", cert["head"],
                             cert["query"], endpoints, cert["value"])


def check_poly(row: dict) -> None:
    from flint import nmod_poly

    if row["modulus"] != 7:
        raise ValueError("expected the fixed F7 fixture family")
    names = ("dividend", "divisor", "quotient", "remainder", "gcdLeft", "gcdRight", "gcd")
    if any(type(c) is not int or not 0 <= c < 7 for name in names for c in row[name]):
        raise ValueError("noncanonical F7 coefficient")
    p, q = nmod_poly(row["dividend"], 7), nmod_poly(row["divisor"], 7)
    u = row["multiplier"]
    if q.degree() < 0 or p.degree() < q.degree():
        raise ValueError("unexpected degree branch in the scientific fixture")
    if u != pow(int(q[q.degree()]), p.degree() - q.degree() + 1, 7):
        raise ValueError("incorrect fixed-exponent multiplier")
    quotient, remainder = divmod(p, q)
    if (nmod_poly(row["quotient"], 7) != u * quotient or
            nmod_poly(row["remainder"], 7) != u * remainder):
        raise ValueError("pseudo-division differs from scaled FLINT division")
    if (nmod_poly(row["gcdLeft"], 7).gcd(nmod_poly(row["gcdRight"], 7)) !=
            nmod_poly(row["gcd"], 7)):
        raise ValueError("Fibonacci pseudo-gcd differs from FLINT gcd")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fixtures", type=Path, nargs="+")
    args = parser.parse_args()
    for path in args.fixtures:
        count = 0
        for line in path.read_text().splitlines():
            if not line.strip():
                continue
            row = json.loads(line)
            (check_query if "certificate" in row else check_poly)(row)
            count += 1
        print(f"{path}: {count} exact fixtures passed")


if __name__ == "__main__":
    main()
