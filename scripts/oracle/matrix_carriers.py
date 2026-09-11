#!/usr/bin/env python3
"""Exact matrix oracle shared by symbolic carrier streams.

Each record kind has its own handler. The ``det`` arm calls DomainMatrix.det
(Bareiss in the pinned SymPy), independently of Hex's Leibniz enumeration.
All inputs and results are compared in their full canonical wire encoding.
"""

import json
import sys
from functools import lru_cache

from sympy import GF, QQ, ZZ, isprime
from sympy.polys.matrices import DomainMatrix


@lru_cache(None)
def context(carrier, base, arity, modulus):
    if base == "ZZ" and modulus == 0:
        ground = ZZ
    elif base == "QQ" and modulus == 0:
        ground = QQ
    elif base == "GF" and isprime(modulus) and modulus < 2**31:
        ground = GF(modulus, symmetric=False)
    else:
        raise ValueError(f"unsupported base domain: {base}/{modulus}")
    if carrier == "ratfn" and base == "QQ" and arity == 1:
        domain = ground.frac_field("x")
        ring = domain.field.ring
    elif carrier == "dense" and arity == 1:
        domain = ground.poly_ring("x")
        ring = domain.ring
    elif carrier == "mv" and arity in (2, 3) and base in ("ZZ", "QQ"):
        domain = ground.poly_ring(*(f"x{i}" for i in range(arity)))
        ring = domain.ring
    else:
        raise ValueError(f"unsupported carrier: {carrier}/{base}/{arity}")
    return ground, domain, ring


class Codec:
    def __init__(self, record):
        self.carrier = record["carrier"]
        self.base = record["base"]
        self.arity = record["arity"]
        self.modulus = record["modulus"]
        self.ground, self.domain, self.ring = context(
            self.carrier, self.base, self.arity, self.modulus)

    def scalar(self, value):
        if self.base == "QQ":
            if not isinstance(value, list) or len(value) != 2 or any(type(x) is not int for x in value):
                raise ValueError("rational coefficient must be an integer numerator/denominator pair")
            if value[1] <= 0:
                raise ValueError("rational denominator must be positive")
            result = self.ground(*value)
        else:
            if type(value) is not int:
                raise ValueError("coefficient must be an integer")
            result = self.ground(value)
        if self.encode_scalar(result) != value:
            raise ValueError("noncanonical scalar")
        return result

    def encode_scalar(self, value):
        if self.base == "QQ":
            return [int(value.numerator), int(value.denominator)]
        return int(value) % self.modulus if self.base == "GF" else int(value)

    def poly(self, values):
        if not isinstance(values, list):
            raise ValueError("polynomial must be an array")
        if self.carrier == "mv":
            terms = {}
            for exponents, coeff in values:
                if len(exponents) != self.arity or any(type(e) is not int or e < 0 for e in exponents):
                    raise ValueError("invalid exponent vector")
                if tuple(exponents) in terms:
                    raise ValueError("duplicate monomial")
                terms[tuple(exponents)] = self.scalar(coeff)
        else:
            terms = {(i,): self.scalar(c) for i, c in enumerate(values)}
        result = self.ring.from_dict(terms)
        if self.encode_poly(result) != values:
            raise ValueError("noncanonical polynomial (zero terms, trailing zeros, or term order)")
        return result

    def encode_poly(self, poly):
        if self.carrier == "mv":
            # Ascending grevlex: total degree, then reversed negative exponents.
            terms = sorted(poly.items(), key=lambda t: (sum(t[0]), tuple(-e for e in reversed(t[0]))))
            return [[list(m), self.encode_scalar(c)] for m, c in terms if c]
        return [self.encode_scalar(poly.get((i,), self.ground.zero))
                for i in range(int(poly.degree()) + 1)] if poly else []

    def decode(self, value):
        if self.carrier != "ratfn":
            return self.poly(value)
        if set(value) != {"num", "den"}:
            raise ValueError("fraction requires num and den")
        num, den = self.poly(value["num"]), self.poly(value["den"])
        if not den:
            raise ValueError("zero fraction denominator")
        result = self.domain.field.new(num, den)
        if self.encode(result) != value:
            raise ValueError("fraction is not reduced with monic denominator")
        return result

    def encode(self, value):
        if self.carrier != "ratfn":
            return self.encode_poly(value)
        leading = value.denom.LC
        return {"num": self.encode_poly(value.numer.quo_ground(leading)),
                "den": self.encode_poly(value.denom.quo_ground(leading))}


def prepare(record):
    codec = Codec(record)
    n, rows = record["n"], record["matrix"]
    if type(n) is not int or n < 0 or len(rows) != n or any(len(row) != n for row in rows):
        raise ValueError("matrix shape does not match dimension")
    matrix = DomainMatrix([[codec.decode(x) for x in row] for row in rows], (n, n), codec.domain)
    return codec, matrix


def determinant(record):
    codec, matrix = prepare(record)
    return codec.encode(matrix.det())


# Sibling carrier streams add disjoint kinds here; none depend on Bareiss fixtures.
HANDLERS = {"det": determinant}


def evaluate(record):
    kind = record["kind"]
    if kind not in HANDLERS:
        raise ValueError(f"unknown record kind: {kind}")
    return HANDLERS[kind](record)


def main():
    count = 0
    for line_number, line in enumerate(sys.stdin, 1):
        if not line.strip():
            continue
        try:
            record = json.loads(line)
            Codec(record).decode(record["determinant"])
            actual = evaluate(record)
            if actual != record["determinant"]:
                raise ValueError(f"determinant mismatch: expected {record['determinant']}, got {actual}")
        except Exception as error:
            print(f"FAIL matrix_carriers line {line_number}: {error}", file=sys.stderr)
            return 1
        count += 1
    if count == 0:
        print("FAIL matrix_carriers: empty fixture stream", file=sys.stderr)
        return 1
    print(f"OK matrix_carriers: {count} records", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
