#!/usr/bin/env python3
"""Independent canonical rational-function oracle using explicit SymPy domains.

Read schema-version-one JSONL records from stdin. Compare full canonical
coefficient arrays, partial results, polynomial parts, and certificate checks.
No expression simplifier or evaluation sampling decides fraction equality.
"""

import json
import sys
from functools import lru_cache

from sympy import GF, QQ, isprime
from sympy.polys.fields import field


@lru_cache(None)
def context(domain, characteristic):
    if domain == "QQ" and characteristic == 0:
        return field("x", QQ)
    if domain == "GF" and isprime(characteristic):
        return field("x", GF(characteristic))
    raise ValueError(f"unsupported coefficient field: {domain}/{characteristic}")


def evaluate(record):
    if record["schema_version"] != 1:
        raise ValueError("unknown fixture schema")
    ff, x = context(record["domain"], record["characteristic"])
    ring, domain = ff.ring, ff.domain
    rational = record["domain"] == "QQ"

    def scalar(value):
        return domain(*value) if rational else domain(value)

    def encode_scalar(value):
        if rational:
            return [int(value.numerator), int(value.denominator)]
        return int(value) % record["characteristic"]

    def poly(values):
        return ring.from_dict({(i,): scalar(c) for i, c in enumerate(values) if scalar(c)})

    def encode_poly(p):
        return [encode_scalar(p.get((i,), domain.zero)) for i in range(int(p.degree()) + 1)] if p else []

    def fraction(pair):
        p, q = poly(pair["num"]), poly(pair["den"])
        return ff.new(p, q) if q else None

    def encode(f):
        if f is None:
            return None
        c = f.denom.LC
        return {"num": encode_poly(f.numer.quo_ground(c)), "den": encode_poly(f.denom.quo_ground(c))}

    operands = record["operands"]
    op = record["operation"]
    if op == "normalize":
        return encode(fraction(operands[0]))
    if op == "check":
        raw, cert = operands[0], record["certificate"]
        p, q = poly(raw["num"]), poly(raw["den"])
        n, d, s, t = (poly(cert[k]) for k in ("num", "den", "s", "t"))
        return bool(q and d and d.LC == domain.one and n * q == p * d and s * n + t * d == ring.one)

    values = [fraction(pair) for pair in operands]
    if any(f is None for f in values):
        raise ValueError("arithmetic operand has a zero denominator")
    f = values[0]
    if op in ("add", "sub", "mul", "div", "div?", "equal"):
        g = values[1]
        if op == "equal":
            return f == g
        if op in ("div", "div?") and not g:
            return None if op == "div?" else encode(ff.zero)
        return encode({"add": lambda: f + g, "sub": lambda: f - g,
                       "mul": lambda: f * g, "div": lambda: f / g, "div?": lambda: f / g}[op]())
    if op == "neg":
        return encode(-f)
    if op in ("inv", "inv?"):
        return encode(1 / f) if f else (None if op == "inv?" else encode(ff.zero))
    if op == "pow":
        return encode(ff.one if record["exponent"] == 0 else f ** record["exponent"])
    if op == "derivative":
        return encode(f.diff(x))
    if op == "split":
        q, r = f.numer.div(f.denom)
        return {"polynomial": encode_poly(q), "proper": encode(ff.new(r, f.denom))}
    if op == "toPoly?":
        return encode_poly(f.numer.quo_ground(f.denom.LC)) if f.denom.degree() == 0 else None
    if op == "eval":
        a = scalar(record["point"])
        d = f.denom.evaluate(0, a)
        return encode_scalar(f.numer.evaluate(0, a) / d) if d else None
    raise ValueError(f"unknown operation: {op}")


def main():
    count = 0
    for line_number, line in enumerate(sys.stdin, 1):
        if not line.strip():
            continue
        record = json.loads(line)
        try:
            actual = evaluate(record)
            if actual != record["expected"]:
                raise AssertionError(f"expected {record['expected']!r}, oracle {actual!r}")
        except Exception as exc:
            print(f"FAIL HexRationalFn line {line_number}: {exc}\n{line.rstrip()}", file=sys.stderr)
            return 1
        count += 1
    if not count:
        print("FAIL HexRationalFn: no fixtures supplied", file=sys.stderr)
        return 1
    print(f"PASS HexRationalFn: {count} complete results agree with SymPy")
    return 0


if __name__ == "__main__":
    sys.exit(main())
