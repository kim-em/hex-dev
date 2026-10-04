#!/usr/bin/env python3
"""Persistent exact root-sum endpoints for the compiled Sturm benchmark.

Inputs and coefficient contexts are prepared once. Each non-control request
calls the root API, filters the open interval, evaluates the complete query
and sums its exact signs. No roots are cached by this driver; persistent
backend contexts may retain internal caches. JSON transport, root production and temporary
cleanup are timed. This is an informational end-to-end comparison, not literal
certificate replay or isolated root-production timing.
"""
from __future__ import annotations

import argparse
import ctypes
from importlib.metadata import version
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

HEAD = [1, 0, -32, 0, 160, 0, -256, 0, 128]  # T_8
QUERIES = {"count": [1], "mixed": [0, 1], "negative": [-1, 1], "common": HEAD}
EXPECTED = {"count": 8, "mixed": 0, "negative": -8, "common": 0}


class Flint:
    def __init__(self):
        from scripts.oracle.real_algebraic_qqbar import QQBar
        if version("python-flint") != "0.9.0":
            raise RuntimeError("requires python-flint 0.9.0 / FLINT 3.6.0")
        self.oracle = QQBar()
        o = self.oracle
        self.head = [o.number(c, o.integer) for c in HEAD]
        self.queries = {name: [o.number(c) for c in cs] for name, cs in QUERIES.items()}
        self.zero, self.lower, self.upper = [o.number(c) for c in [0, -2, 2]]

    def evaluate(self, coefficients, root):
        o = self.oracle
        value = self.zero
        for coefficient in reversed(coefficients):
            value = o.binary("add", o.binary("mul", value, root), coefficient)
        return value

    def query(self, name):
        o = self.oracle
        checkpoint = len(o.owned)
        try:
            roots = o.roots(self.head, integer=True)
            if len(roots) != 8 or any(m != 1 for _, m in roots):
                raise ArithmeticError("T_8 must have eight distinct real roots")
            return sum(o.compare(self.evaluate(self.queries[name], root), self.zero)
                       for root, _ in roots
                       if o.compare(self.lower, root) < 0 and o.compare(root, self.upper) < 0)
        finally:
            # These are the adapter's owned gr_heap values, not Python layouts.
            for value, context in reversed(o.owned[checkpoint:]):
                o.lib.gr_heap_clear(value, ctypes.byref(context))
            del o.owned[checkpoint:]

    def close(self):
        self.oracle.close()


class Z3:
    def __init__(self):
        import z3
        from z3 import z3rcf
        if version("z3-solver") != "4.15.4.0" or z3.get_version() != (4, 15, 4, 0):
            raise RuntimeError("requires z3-solver 4.15.4.0")
        self.context, self.api = z3.Context(), z3rcf
        self.head = [z3rcf.RCFNum(c, self.context) for c in HEAD]
        self.queries = {name: [z3rcf.RCFNum(c, self.context) for c in cs]
                        for name, cs in QUERIES.items()}
        self.zero = z3rcf.RCFNum(0, self.context)
        self.lower, self.upper = [z3rcf.RCFNum(c, self.context) for c in [-2, 2]]

    def evaluate(self, coefficients, root):
        value = self.zero
        for coefficient in reversed(coefficients):
            value = value * root + coefficient
        return value

    def query(self, name):
        roots = sorted(self.api.MkRoots(self.head, self.context))
        if len(roots) != 8 or not all(x < y for x, y in zip(roots, roots[1:])):
            raise ArithmeticError("T_8 must have eight distinct real roots")
        values = [self.evaluate(self.queries[name], root)
                  for root in roots if self.lower < root < self.upper]
        return sum(1 if value > 0 else -1 if value < 0 else 0 for value in values)

    def close(self):
        pass  # RCFNum and Context own and release their Z3 handles.


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tool", choices=["flint", "z3"], required=True)
    parser.add_argument("--self-test", action="store_true",
                        help="Run exact endpoint and protocol regressions before serving requests.")
    args = parser.parse_args()
    if args.self_test:
        import unittest
        suite = unittest.defaultTestLoader.loadTestsFromName("scripts.oracle.test_sturm_bench")
        result = unittest.TextTestRunner(stream=sys.stderr).run(suite)
        if not result.wasSuccessful():
            raise SystemExit(1)
    endpoint = Flint() if args.tool == "flint" else Z3()
    try:
        for line in sys.stdin:
            try:
                request = json.loads(line)
                name = request["case"]
                if name not in EXPECTED:
                    raise ValueError("unknown fixed query fixture")
                control = request.get("control", False)
                if type(control) is not bool:
                    raise TypeError("control must be a JSON Boolean")
                value = EXPECTED[name] if control else endpoint.query(name)
                reply = {"ok": True, "result": value}
            except (KeyError, ValueError, ArithmeticError, TypeError) as error:
                reply = {"ok": False, "error": str(error)}
            print(json.dumps(reply), flush=True)
    finally:
        endpoint.close()


if __name__ == "__main__":
    main()
