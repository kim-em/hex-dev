#!/usr/bin/env python3
"""Independent exact semantics for local real-closure section/sector samples.

Evaluate native contexts, selected roots, coefficient conversions and sample
values in pinned Z3 RCF. Check complete distinct boundaries, all cells, strict
membership and sign vectors, including non-Archimedean gaps. The Lean emitter
replays each context and value through the native reader; this oracle does not
independently replay polynomial certificate graphs or certify fraction syntax.
"""
from __future__ import annotations

import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.oracle.sign_det_z3 import RCF, check_version
from scripts.oracle.sign_det_common import require
from scripts.oracle.real_closure_isolation import multiply, parse_record, sign

CASES = ["irrational duplicate roots", "irreducible cubic roots", "mixed irrational roots",
         "root-free whole line", "infinitesimal gap", "selected parent infinitesimal gap"]


def polynomial_roots(rcf, p):
    """Deflate exact 0, ±1 factors before asking Z3 for the remaining roots.

    This avoids Z3 RCF comparing redundant extensions for a polynomial with
    both a rational root and an already selected non-Archimedean root.
    """
    p = p.copy()
    roots = []
    for root in (rcf.zero, rcf.one, -rcf.one):
        while len(p) > 1 and rcf.eval(p, root) == 0:
            quotient = [p[-1]]
            for coefficient in reversed(p[1:-1]):
                quotient.append(coefficient + root * quotient[-1])
            require(p[0] + root * quotient[-1] == 0, "sample deflation remainder")
            p = list(reversed(quotient))
            if all(root != previous for previous in roots):
                roots.append(root)
    if len(p) == 2:
        roots.append((-p[0]).__div__(p[1]))
    elif len(p) > 2:
        roots.extend(rcf.api.MkRoots(p, rcf.context))
    return roots


class Reader:
    def __init__(self, depth):
        self.depth = depth
        self.rcf = RCF({"id": 10377, "levels": [f"epsilon{i+1}" for i in range(max(1, depth))],
                        "order": "each-new-level-smaller-than-positive-base-elements"})

    def base(self, raw, depth):
        require(isinstance(raw, list), "malformed sample base value")
        if depth == 0:
            require(len(raw) == 3 and type(raw[0]) is int and raw[0] == 0 and
                    type(raw[1]) is int and type(raw[2]) is int and raw[2] > 0 and
                    math.gcd(raw[1], raw[2]) == 1, "noncanonical sample rational")
            return self.rcf.coeff(raw[1:], 0)
        require(len(raw) == 3 and type(raw[0]) is int and raw[0] == 1 and
                isinstance(raw[1], list) and isinstance(raw[2], list) and raw[2],
                "malformed sample infinitesimal fraction")
        p = [self.base(c, depth-1) for c in raw[1]]
        q = [self.base(c, depth-1) for c in raw[2]]
        require((not p or p[-1] != 0) and q[-1] != 0, "sample fraction trailing zero")
        epsilon = self.rcf.levels[depth-1]
        denominator = self.rcf.eval(q, epsilon)
        require(denominator != 0, "sample fraction zero denominator")
        return self.rcf.eval(p, epsilon).__div__(denominator)

    def value(self, raw, roots):
        require(isinstance(raw, list), "malformed sample native value")
        if not roots:
            return self.base(raw, self.depth)
        if raw == []:
            return self.rcf.zero
        require(len(raw) == 2 and isinstance(raw[0], list) and raw[0] and
                type(raw[1]) is int and raw[1] in (-1, 1), "malformed sample nonzero value")
        coefficients = [self.value(c, roots[:-1]) for c in raw[0]]
        require(coefficients[-1] != 0, "sample stored trailing zero")
        value = self.rcf.eval(coefficients, roots[-1])
        require(sign(value) == raw[1], "sample cached sign differs")
        return value

    def poly(self, raw, roots):
        require(isinstance(raw, list), "malformed sample polynomial")
        coefficients = [self.value(c, roots) for c in raw]
        require(not coefficients or coefficients[-1] != 0, "sample polynomial trailing zero")
        return coefficients

    def endpoint(self, raw, roots):
        require(isinstance(raw, list) and raw and type(raw[0]) is int,
                "malformed sample endpoint")
        if raw == [0]:
            return (-1, None)
        if raw == [2]:
            return (1, None)
        require(len(raw) == 2 and raw[0] == 1, "malformed finite sample endpoint")
        return (0, self.value(raw[1], roots))

    def context(self, raw):
        require(isinstance(raw, list) and len(raw) == 3 and raw[0] == [] and
                type(raw[1]) is int and raw[1] == self.depth and isinstance(raw[2], list),
                "wrong sample context stages")
        roots = []
        for frame in raw[2]:
            require(isinstance(frame, list) and len(frame) == 7 and frame[0] == [0] and
                    type(frame[0][0]) is int and isinstance(frame[6], list),
                    "malformed sample root frame")
            head = self.poly(frame[1], roots)
            require(len(head) > 1 and self.rcf.squarefree(head), "invalid sample head")
            lower, upper = self.endpoint(frame[2], roots), self.endpoint(frame[3], roots)
            slots, signs = frame[4], frame[5]
            require(isinstance(slots, list) and all(type(i) is int and 1 <= i < len(head) for i in slots)
                    and len(set(slots)) == len(slots) and isinstance(signs, list) and
                    len(signs) == len(slots) and all(type(s) is int and s in (-1, 0, 1) for s in signs),
                    "malformed sample Thom data")
            derivatives = self.rcf.derivatives(head)
            candidates = [root for root in polynomial_roots(self.rcf, head)
                          if (lower[0] == -1 or lower[0] == 0 and lower[1] < root) and
                          (upper[0] == 1 or upper[0] == 0 and root < upper[1]) and
                          [sign(self.rcf.eval(derivatives[i-1], root)) for i in slots] == signs]
            require(len(candidates) == 1, "sample context does not select one root")
            roots.append(candidates[0])
        return roots


def expected_polynomials(reader, case, roots):
    rcf = reader.rcf
    q = [-2 * rcf.one, rcf.zero, rcf.one]
    if case == CASES[0]:
        return [q, multiply(rcf, q, q)]
    if case == CASES[1]:
        return [[rcf.one, -3 * rcf.one, rcf.zero, rcf.one]]
    if case == CASES[2]:
        return [q, multiply(rcf, q, [-3 * rcf.one, rcf.zero, rcf.one])]
    if case == CASES[3]:
        return [[2 * rcf.one], []]
    if case == CASES[4]:
        epsilon = rcf.levels[0]
        return [[2 * epsilon * epsilon, -3 * epsilon, rcf.one]]
    require(len(roots) == 1 and rcf.one < roots[0] < 2 * rcf.one and
            roots[0] * roots[0] == rcf.one + rcf.levels[0], "wrong sample selected parent")
    return [[roots[0], -(rcf.one + roots[0]), rcf.one]]


def verify_sample(reader, parent_context, original, sample, expected_cell):
    require(isinstance(sample, dict) and
            set(sample) == {"context", "value", "cell", "polynomials", "signs", "member"},
            "malformed sample record")
    context = sample["context"]
    roots = reader.context(context)
    require(context[:2] == parent_context[:2] and
            context[2][:len(parent_context[2])] == parent_context[2] and
            len(context[2]) <= len(parent_context[2]) + 2, "sample context is not local to its boundaries")
    require(isinstance(sample["polynomials"], list), "malformed sample converted polynomials")
    converted = [reader.poly(p, roots) for p in sample["polynomials"]]
    require(converted == original, "sample coefficient conversion changed values")
    point = reader.value(sample["value"], roots)
    cell = sample["cell"]
    require(isinstance(cell, dict), "malformed sample cell")
    if expected_cell[0] == "section":
        require(set(cell) == {"kind", "root"} and cell["kind"] == "section",
                "sample cell kind differs")
        boundary = reader.value(cell["root"], roots)
        require(boundary == expected_cell[1], "sample section boundary differs")
        require(point == boundary, "sample section point differs")
    else:
        require(set(cell) == {"kind", "lower", "upper"} and cell["kind"] == "sector",
                "sample cell kind differs")
        lower, upper = reader.endpoint(cell["lower"], roots), reader.endpoint(cell["upper"], roots)
        require((lower, upper) == expected_cell[1:], "sample sector boundaries differ")
        require((lower[0] == -1 or lower[0] == 0 and lower[1] < point) and
                (upper[0] == 1 or upper[0] == 0 and point < upper[1]), "sample is outside sector")
    require(sample["member"] is True, "native sample membership rejected")
    require(isinstance(sample["signs"], list) and all(type(s) is int for s in sample["signs"]) and
            sample["signs"] == [sign(reader.rcf.eval(p, point)) for p in original],
            "sample computed signs differ")


def verify(rows):
    check_version()
    require([row.get("case") for row in rows] == CASES, "missing, duplicate or reordered sample cases")
    for case, row in zip(CASES, rows):
        require(set(row) == {"case", "context", "polynomials", "sections", "sectors"},
                "malformed sample family")
        reader = Reader(1 if case in CASES[4:] else 0)
        parent = reader.context(row["context"])
        require(len(parent) == (1 if case == CASES[5] else 0), "wrong sample predecessor depth")
        require(isinstance(row["polynomials"], list), "malformed sample input polynomials")
        polynomials = [reader.poly(p, parent) for p in row["polynomials"]]
        require(polynomials == expected_polynomials(reader, case, parent), "wrong sample family input")
        boundaries = []
        for p in polynomials:
            if len(p) > 1:
                for root in polynomial_roots(reader.rcf, p):
                    if all(root != previous for previous in boundaries):
                        boundaries.append(root)
        boundaries.sort()
        require(isinstance(row["sections"], list) and len(row["sections"]) == len(boundaries),
                "sample sections incomplete or duplicated")
        require(isinstance(row["sectors"], list) and len(row["sectors"]) == len(boundaries) + 1,
                "sample sectors incomplete or duplicated")
        for sample, root in zip(row["sections"], boundaries):
            verify_sample(reader, row["context"], polynomials, sample, ("section", root))
        endpoints = [(-1, None)] + [(0, root) for root in boundaries] + [(1, None)]
        for sample, lower, upper in zip(row["sectors"], endpoints, endpoints[1:]):
            verify_sample(reader, row["context"], polynomials, sample, ("sector", lower, upper))


def main():
    rows = [parse_record(line) for line in sys.stdin if line.strip()]
    verify(rows)
    print(f"verified {len(rows)} local sample families with exact Z3 RCF")


if __name__ == "__main__":
    main()
