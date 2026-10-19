#!/usr/bin/env python3
"""Exact real roots of X^n-2 and X^n-sqrt(2), including multiplicities.

The polynomial/sign/multiplicity fingerprint identifies every root on these
degree-one or even-degree Eisenstein fixtures. External roots are checked by exact
annihilation; the reported minimal polynomial follows from Eisenstein, rather
than being extracted from a backend's representation. Preparation is excluded;
root production, ordering, annihilation, JSON and temporary cleanup are timed.
No driver root cache is used. Backend contexts can retain internal caches.
"""
from __future__ import annotations

import argparse
import ctypes
from functools import cmp_to_key
from importlib.metadata import version
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))


def validate(degree, quadratic):
    if type(quadratic) is not bool:
        raise ValueError("quadratic must be a JSON Boolean")
    if type(degree) is not int or degree not in (1, 2, 4, 8, 16):
        raise ValueError("degree must be one of 1, 2, 4, 8, 16")


def fingerprint(degree, quadratic):
    validate(degree, quadratic)
    poly = [-2] + [0] * ((2 if quadratic else 1) * degree - 1) + [1]
    # Lean's nested Prod encoding: (polynomial, (sign, multiplicity)).
    return [[poly, [1, 1]]] if degree == 1 else [[poly, [-1, 1]], [poly, [1, 1]]]


class Flint:
    def __init__(self, degree, quadratic):
        from scripts.oracle.real_algebraic_qqbar import QQBar
        validate(degree, quadratic)
        self.degree, self.quadratic = degree, quadratic
        self.oracle = QQBar()
        o = self.oracle
        ctx = o.real if quadratic else o.integer
        self.zero = o.number(0)
        self.target = o.unary("sqrt", o.number(2)) if quadratic else o.number(2)
        constant = o.unary("neg", self.target) if quadratic else o.number(-2, ctx)
        self.coefficients = [constant] + [o.number(0, ctx)] * (degree - 1) + [o.number(1, ctx)]

    def roots(self):
        o = self.oracle
        checkpoint = len(o.owned)
        try:
            roots = sorted(o.roots(self.coefficients, integer=not self.quadratic),
                           key=cmp_to_key(lambda a, b: o.compare(a[0], b[0])))
            expected_signs = [1] if self.degree == 1 else [-1, 1]
            if len(roots) != len(expected_signs) or any(m != 1 for _, m in roots):
                raise ArithmeticError("unexpected real roots or multiplicities")
            signs = []
            for root, _ in roots:
                value = root
                for _ in range(self.degree.bit_length() - 1):
                    value = o.binary("mul", value, value)
                if o.compare(value, self.target) != 0:
                    raise ArithmeticError("root fails exact annihilation")
                signs.append(o.compare(root, self.zero))
            if signs != expected_signs:
                raise ArithmeticError("unexpected ordered root signs")
            return fingerprint(self.degree, self.quadratic)
        finally:
            for value, ctx in reversed(o.owned[checkpoint:]):
                o.lib.gr_heap_clear(value, ctypes.byref(ctx))
            del o.owned[checkpoint:]

    def close(self):
        self.oracle.close()


class Z3:
    def __init__(self, degree, quadratic):
        import z3
        from z3 import z3rcf
        validate(degree, quadratic)
        if version("z3-solver") != "4.15.4.0" or z3.get_version() != (4, 15, 4, 0):
            raise RuntimeError("requires z3-solver 4.15.4.0")
        self.degree, self.quadratic = degree, quadratic
        self.context, self.api = z3.Context(), z3rcf
        zero, one, two = [z3rcf.RCFNum(c, self.context) for c in (0, 1, 2)]
        if quadratic:
            candidates = sorted(z3rcf.MkRoots([-two, zero, one], self.context))
            if len(candidates) != 2 or not candidates[0] < 0 < candidates[1]:
                raise ArithmeticError("failed to prepare positive sqrt(2)")
            self.target = candidates[1]
        else:
            self.target = two
        self.coefficients = [-self.target] + [zero] * (degree - 1) + [one]

    def roots(self):
        roots = sorted(self.api.MkRoots(self.coefficients, self.context))
        signs = [1 if r > 0 else -1 if r < 0 else 0 for r in roots]
        if signs != ([1] if self.degree == 1 else [-1, 1]):
            raise ArithmeticError("unexpected ordered root signs")
        for root in roots:
            value = root
            for _ in range(self.degree.bit_length() - 1):
                value = value * value
            if value != self.target:
                raise ArithmeticError("root fails exact annihilation")
        # This nonzero-constant monomial has no repeated roots in characteristic 0.
        return fingerprint(self.degree, self.quadratic)

    def close(self):
        pass  # Context and RCFNum own their Z3 handles.


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tool", choices=("flint", "z3"), required=True)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        done = subprocess.run([sys.executable, "-m", "unittest",
            "scripts.oracle.test_real_algebraic_roots_bench"], cwd=ROOT,
            capture_output=True, text=True, check=False)
        output = done.stdout + done.stderr
        if done.returncode:
            print(json.dumps({"ok": False, "error":
                f"root endpoint self-test failed ({done.returncode}): {output[-8000:]}"}), flush=True)
            raise SystemExit(1)
        print(output[-1000:], file=sys.stderr, end="")
    endpoints = {}
    factory = Flint if args.tool == "flint" else Z3
    try:
        for line in sys.stdin:
            try:
                request = json.loads(line)
                degree, quadratic = request["degree"], request["quadratic"]
                validate(degree, quadratic)
                control = request.get("control", False)
                if type(control) is not bool:
                    raise ValueError("control must be a JSON Boolean")
                if control:
                    value = fingerprint(degree, quadratic)
                else:
                    key = degree, quadratic
                    if key not in endpoints:
                        endpoints[key] = factory(*key)
                    value = endpoints[key].roots()
                reply = {"ok": True, "result": value}
            except (KeyError, ValueError, ArithmeticError, TypeError) as error:
                reply = {"ok": False, "error": str(error)}
            print(json.dumps(reply), flush=True)
    finally:
        for endpoint in endpoints.values():
            endpoint.close()


if __name__ == "__main__":
    main()
