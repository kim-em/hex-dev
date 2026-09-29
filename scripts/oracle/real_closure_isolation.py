#!/usr/bin/env python3
"""Exact Z3 oracle for capped bisection followed by descriptor completion.

Checks the actual inputs, scalar-preserving deflation, retained cell counts,
selected roots, completeness and absence of duplicates. Proof graphs and
producer totality are not replayed by this oracle.
"""
from __future__ import annotations
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.oracle.sign_det_z3 import RCF, check_version
from scripts.oracle.sign_det_common import require

CASES = ["zero", "constant", "repeated", "nonmonic linear", "quadratic",
         "negative cubic with removed zero", "nonquadratic", "four roots",
         "whole-line inverse infinitesimal", "inseparable by rational bisection"]
RATIONAL_HEADS = [[], [5], [1, -2, 1], [-3, 2], [-2, 0, 1],
                  [0, 6, 0, -3], [-2, 0, 0, 1], [6, 0, -5, 0, 1]]


def sign(value):
    return 1 if value > 0 else -1 if value < 0 else 0


def multiply(rcf, p, q):
    if not p or not q:
        return []
    out = [rcf.zero for _ in range(len(p) + len(q) - 1)]
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i+j] = out[i+j] + a * b
    return rcf.trim(out)


def verify(rows):
    check_version()
    require([r.get("case") for r in rows] == CASES, "missing, repeated or reordered cases")
    for index, row in enumerate(rows):
        require(set(row) == {"case", "depth", "head", "output"}, "foreign fixture fields")
        depth = row["depth"]
        require(type(depth) is int and depth == (0 if index < 8 else 1), "wrong coefficient depth")
        rcf = RCF({"id": 10377, "levels": ["epsilon1"],
                   "order": "each-new-level-smaller-than-positive-base-elements"})
        def decode(raw):
            return rcf.coeff(raw, depth)
        def polynomial(raw):
            require(isinstance(raw, list), "malformed polynomial")
            p = [decode(c) for c in raw]
            require(not p or p[-1] != 0, "trailing zero coefficient")
            return p
        def endpoint(raw):
            require(isinstance(raw, list) and raw and type(raw[0]) is int, "malformed endpoint")
            if raw == [0]:
                return None, -1
            if raw == [2]:
                return None, 1
            require(len(raw) == 2 and raw[0] == 1, "malformed finite endpoint")
            return decode(raw[1]), 0
        def inside(root, lower, upper):
            lo, lt = endpoint(lower)
            hi, ht = endpoint(upper)
            return (lt == -1 or lt == 0 and lo < root) and (ht == 1 or ht == 0 and root < hi)
        def roots(p):
            return list(rcf.api.MkRoots(p, rcf.context)) if len(p) > 1 else []
        p = polynomial(row["head"])
        eps = rcf.levels[0]
        expected = RATIONAL_HEADS[index] if index < 8 else (
            [-rcf.one.__div__(eps), rcf.one] if index == 8 else [2 * eps * eps, -3 * eps, rcf.one])
        require(p == expected, "fixture does not contain the assigned input")
        output = row["output"]
        if not p or not rcf.squarefree(p):
            require(output is None, "invalid domain accepted")
            continue
        require(isinstance(output, dict) and set(output) == {"route", "points", "descriptors"},
                "producer failed or malformed completion")
        points = [decode(c) for c in output["points"]]
        route = output["route"]
        require(isinstance(route, dict), "malformed route")
        active = polynomial(route["head"])
        require(bool(active), "lost active polynomial")
        product = active
        for point in points:
            product = multiply(rcf, [-point, rcf.one], product)
        require(product == p, "deflation lost a factor or leading scalar")
        def absolute(value):
            return -value if value < 0 else value
        candidates = [2 ** i for i in range(1, 2 * len(p) + 1)]
        accepted_bounds = [b for b in candidates if all(absolute(a) < (b - 1) * absolute(p[-1]) for a in p[:-1])]
        if not accepted_bounds:
            require(set(route) == {"kind", "head"} and route["kind"] == "whole" and not points,
                    "wrong whole-line fallback")
        else:
            require(set(route) == {"kind", "head", "bound", "nodes", "cells"} and
                    route["kind"] == "bounded", "wrong bounded route")
            require(decode(route["bound"]) == accepted_bounds[0], "wrong finite bound policy")
            require(type(route["nodes"]) is int and 0 <= route["nodes"] <= 2 * len(p),
                    "bisection exceeded cap")
            cells = route["cells"]
            require(isinstance(cells, list), "malformed cells")
            intervals = []
            for cell in cells:
                require(set(cell) == {"lower", "upper", "count"}, "foreign cell fields")
                lo, hi = decode(cell["lower"]), decode(cell["upper"])
                require(lo < hi and rcf.eval(active, lo) != 0 and rcf.eval(active, hi) != 0,
                        "invalid retained cell")
                actual = [r for r in roots(active) if lo < r < hi]
                require(type(cell["count"]) is int and cell["count"] == len(actual), "false cell count")
                intervals.append((lo, hi))
            require(all(hi <= lo2 or hi2 <= lo for i, (lo, hi) in enumerate(intervals)
                        for lo2, hi2 in intervals[i+1:]), "overlapping retained cells")
            if index == 9:
                require(route["nodes"] == 2 * len(p) and any(c["count"] > 1 for c in cells),
                        "close-root fixture did not exercise capped BKR completion")
        selected = points.copy()
        require(isinstance(output["descriptors"], list), "malformed descriptor list")
        for d in output["descriptors"]:
            require(set(d) == {"context", "head", "lower", "upper", "indices", "signs"}, "foreign descriptor fields")
            require(type(d["context"]) is int and d["context"] == 10378, "foreign descriptor context")
            head = polynomial(d["head"])
            require(head == active, "descriptor retains a different head")
            derivatives = rcf.derivatives(head)
            if route["kind"] == "bounded":
                lo, lt = endpoint(d["lower"])
                hi, ht = endpoint(d["upper"])
                require(lt == 0 and ht == 0 and (lo, hi) in intervals,
                        "descriptor retains a stale cell")
                count = next(c["count"] for c in cells if decode(c["lower"]) == lo and decode(c["upper"]) == hi)
                require(count > 0, "descriptor emitted for empty cell")
                singleton = count == 1
            else:
                require(d["lower"] == [0] and d["upper"] == [2], "wrong whole-line endpoints")
                singleton = False
            expected_slots = [] if singleton else list(range(1, len(head)))
            require(d["indices"] == expected_slots and all(type(i) is int for i in d["indices"]),
                    "wrong derivative slots for actual cell count")
            queried = [] if singleton else derivatives
            require(isinstance(d["signs"], list) and len(d["signs"]) == len(queried) and
                    all(type(s) is int and s in (-1, 0, 1) for s in d["signs"]), "malformed derivative signs")
            actual = [r for r in roots(head) if inside(r, d["lower"], d["upper"]) and
                      [sign(rcf.eval(q, r)) for q in queried] == d["signs"]]
            require(len(actual) == 1, "descriptor does not select exactly one root")
            selected.append(actual[0])
        require(all(a != b for i, a in enumerate(selected) for b in selected[i+1:]),
                "root emitted twice")
        require(sorted(selected) == sorted(roots(p)), "completion lost or added a root")


def main():
    rows = [json.loads(line) for line in sys.stdin if line.strip()]
    verify(rows)
    print(f"verified {len(rows)} capped isolation fixtures with exact Z3 RCF")


if __name__ == "__main__":
    main()
