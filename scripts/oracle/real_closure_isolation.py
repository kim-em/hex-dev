#!/usr/bin/env python3
"""Exact Z3 oracle for capped bisection and root assembly over nested values.

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
         "whole-line inverse infinitesimal", "inseparable by rational bisection",
         "assembly zero", "assembly constant", "assembly pure power",
         "assembly repeated factors", "assembly root-free factor", "assembly simple zero",
         "nested algebraic coefficients", "nested algebraic multiplicities"]
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


def expected_assembly(rcf, index):
    x = [rcf.zero, rcf.one]
    if index == 10:
        return []
    if index == 11:
        return [5 * rcf.one]
    if index == 12:
        return [rcf.zero] * 6 + [-5 * rcf.one]
    if index == 13:
        factors = [[-3 * rcf.one], x, x] + [[-2 * rcf.one, rcf.zero, rcf.one]] * 3 + \
                  [[-3 * rcf.one, rcf.one]] * 5
    elif index == 14:
        factors = [[rcf.one, rcf.zero, rcf.one]] * 2 + [[-rcf.one, rcf.one]]
    else:
        factors = [x, [-rcf.one, rcf.one], [-rcf.one, rcf.one]]
    product = [rcf.one]
    for factor in factors:
        product = multiply(rcf, product, factor)
    return product


def verify_assembly(row, index):
    require(set(row) == {"case", "mode", "head", "output"} and row["mode"] == "assembly",
            "malformed assembly row")
    rcf = RCF({"id": 10377, "levels": ["epsilon1"],
               "order": "each-new-level-smaller-than-positive-base-elements"})
    def polynomial(raw):
        require(isinstance(raw, list), "malformed assembly polynomial")
        p = [rcf.coeff(c, 0) for c in raw]
        require(not p or p[-1] != 0, "trailing assembly zero coefficient")
        return p
    p = polynomial(row["head"])
    require(p == expected_assembly(rcf, index), "wrong assembly input")
    output = row["output"]
    require(isinstance(output, dict), "assembly producer failed")
    if not p:
        require(output == {"kind": "all"}, "zero polynomial lost all-roots result")
        return
    require(set(output) == {"kind", "entries"} and output["kind"] == "finite" and
            isinstance(output["entries"], list), "malformed finite assembly")
    roots = list(rcf.api.MkRoots(p, rcf.context)) if len(p) > 1 else []
    selected = []
    for entry in output["entries"]:
        require(set(entry) == {"root", "multiplicity"} and
                type(entry["multiplicity"]) is int and entry["multiplicity"] > 0,
                "malformed positive multiplicity")
        raw = entry["root"]
        require(isinstance(raw, dict), "malformed assembled root")
        if raw.get("kind") == "point":
            require(set(raw) == {"kind", "value"}, "malformed coefficient point")
            value = rcf.coeff(raw["value"], 0)
        else:
            require(set(raw) == {"kind", "context", "head", "lower", "upper",
                                 "indices", "signs"} and raw["kind"] == "selected" and
                    type(raw["context"]) is int and raw["context"] == 10378,
                    "malformed selected root")
            head = polynomial(raw["head"])
            require(bool(head), "zero selected head")
            lower, upper = raw["lower"], raw["upper"]
            def endpoint(endpoint):
                require(isinstance(endpoint, list) and endpoint and type(endpoint[0]) is int,
                        "malformed selected endpoint")
                if endpoint == [0]:
                    return None, -1
                if endpoint == [2]:
                    return None, 1
                require(len(endpoint) == 2 and endpoint[0] == 1,
                        "malformed finite selected endpoint")
                return rcf.coeff(endpoint[1], 0), 0
            lo, lt = endpoint(lower)
            hi, ht = endpoint(upper)
            derivatives = rcf.derivatives(head)
            indices = raw["indices"]
            require(isinstance(indices, list) and all(type(i) is int for i in indices) and
                    (indices == [] or indices == list(range(1, len(head)))),
                    "wrong assembled derivative slots")
            queried = [] if not indices else derivatives
            signs = raw["signs"]
            require(isinstance(signs, list) and len(signs) == len(queried) and
                    all(type(s) is int and s in (-1, 0, 1) for s in signs),
                    "malformed assembled signs")
            candidates = [root for root in rcf.api.MkRoots(head, rcf.context)
                          if (lt == -1 or lt == 0 and lo < root) and
                          (ht == 1 or ht == 0 and root < hi) and
                          [sign(rcf.eval(q, root)) for q in queried] == signs]
            require(len(candidates) == 1, "assembled descriptor does not select one root")
            value = candidates[0]
        require(rcf.eval(p, value) == 0, "assembled value is not an input root")
        derivatives = [p] + rcf.derivatives(p)
        actual = next((i for i, q in enumerate(derivatives) if rcf.eval(q, value) != 0), None)
        require(actual == entry["multiplicity"], "wrong assembled root multiplicity")
        selected.append(value)
    require(all(a != b for i, a in enumerate(selected) for b in selected[i+1:]),
            "assembled root duplicated")
    require(sorted(selected) == sorted(roots), "assembled root coverage differs from exact RCF")


def verify_nested(row, assembly_row):
    """Check roots and multiplicities over an earlier selected algebraic value."""
    require(set(row) == {"base", "case", "depth", "head", "output"} and
            type(row["depth"]) is int and row["depth"] == 1,
            "malformed nested algebraic row")
    rcf = RCF({"id": 10377, "levels": ["epsilon1"],
               "order": "each-new-level-smaller-than-positive-base-elements"})
    base_raw = row["base"]
    require(isinstance(base_raw, dict) and
            set(base_raw) == {"context", "head", "lower", "upper", "indices", "signs"} and
            type(base_raw["context"]) is int and base_raw["context"] == 10378 and
            base_raw["indices"] == [] and base_raw["signs"] == [],
            "malformed first-level descriptor")
    require(isinstance(base_raw["head"], list), "malformed first-level head")
    base = [rcf.coeff(q, 0) for q in base_raw["head"]]
    expected_base = multiply(rcf, [-2 * rcf.one, rcf.zero, rcf.one],
                             [-3 * rcf.one, rcf.one])
    require(base == expected_base, "wrong first-level definition")
    require(isinstance(base_raw["lower"], list) and len(base_raw["lower"]) == 2 and
            base_raw["lower"][0] == 1 and
            isinstance(base_raw["upper"], list) and len(base_raw["upper"]) == 2 and
            base_raw["upper"][0] == 1, "malformed first-level interval")
    base_lower = rcf.coeff(base_raw["lower"][1], 0)
    base_upper = rcf.coeff(base_raw["upper"][1], 0)
    require(base_lower == rcf.one and base_upper == 2 * rcf.one,
            "wrong first-level interval")
    base_roots = [root for root in rcf.api.MkRoots(base, rcf.context)
                  if base_lower < root < base_upper]
    require(len(base_roots) == 1, "base descriptor does not select one root")
    alpha = base_roots[0]

    def coefficient(raw):
        require(isinstance(raw, list), "malformed nested coefficient")
        poly = [rcf.coeff(q, 0) for q in raw]
        require(not poly or poly[-1] != 0, "trailing nested coefficient zero")
        value = rcf.eval(poly, alpha) if poly else rcf.zero
        require(value != 0 or not poly, "noncanonical nested zero")
        return value

    def polynomial(raw):
        require(isinstance(raw, list), "malformed nested polynomial")
        p = [coefficient(q) for q in raw]
        require(not p or p[-1] != 0, "trailing nested polynomial zero")
        return p

    def endpoint(raw):
        require(isinstance(raw, list) and raw and type(raw[0]) is int,
                "malformed nested endpoint")
        if raw == [0]:
            return None, -1
        if raw == [2]:
            return None, 1
        require(len(raw) == 2 and raw[0] == 1, "malformed finite nested endpoint")
        return coefficient(raw[1]), 0

    p = polynomial(row["head"])
    require(p == [-alpha, rcf.zero, rcf.one], "wrong nested algebraic input")
    roots = list(rcf.api.MkRoots(p, rcf.context))
    require(len(roots) == 2, "wrong independent nested root count")
    output = row["output"]
    require(isinstance(output, dict) and set(output) == {"route", "points", "descriptors"},
            "nested producer failed or malformed completion")
    require(output["points"] == [], "unexpected nested cut point")
    route = output["route"]
    def absolute(value):
        return -value if value < 0 else value
    bounds = [2 ** i for i in range(1, 2 * len(p) + 1)]
    accepted_bounds = [b for b in bounds if all(
        absolute(a) < (b - 1) * absolute(p[-1]) for a in p[:-1])]
    require(bool(accepted_bounds), "nested input lacks a finite bound")
    require(isinstance(route, dict) and
            set(route) == {"kind", "bound", "nodes", "head", "cells"} and
            route["kind"] == "bounded" and polynomial(route["head"]) == p and
            coefficient(route["bound"]) == accepted_bounds[0] and
            type(route["nodes"]) is int and 0 <= route["nodes"] <= 2 * len(p),
            "incorrect nested bounded route")
    cells = route["cells"]
    require(isinstance(cells, list), "malformed nested cells")
    intervals = []
    for cell in cells:
        require(isinstance(cell, dict) and set(cell) == {"lower", "upper", "count"},
                "malformed nested cell")
        lower, upper = coefficient(cell["lower"]), coefficient(cell["upper"])
        require(lower < upper and rcf.eval(p, lower) != 0 and rcf.eval(p, upper) != 0,
                "invalid nested cell")
        count = sum(lower < root < upper for root in roots)
        require(type(cell["count"]) is int and cell["count"] == count,
                "wrong nested cell count")
        intervals.append((lower, upper, count))
    require(all(hi <= lo2 or hi2 <= lo for i, (lo, hi, _) in enumerate(intervals)
                for lo2, hi2, _ in intervals[i+1:]), "overlapping nested cells")
    selected = []
    for descriptor in output["descriptors"]:
        require(isinstance(descriptor, dict) and
                set(descriptor) == {"context", "head", "lower", "upper", "indices", "signs"}
                and type(descriptor["context"]) is int and descriptor["context"] == 10379
                and polynomial(descriptor["head"]) == p,
                "stale nested descriptor")
        lower, lower_kind = endpoint(descriptor["lower"])
        upper, upper_kind = endpoint(descriptor["upper"])
        require(lower_kind == upper_kind == 0 and
                any(lower == lo and upper == hi and count == 1 for lo, hi, count in intervals)
                and descriptor["indices"] == [] and descriptor["signs"] == [],
                "incorrect singleton nested descriptor")
        candidates = [root for root in roots if lower < root < upper]
        require(len(candidates) == 1, "nested descriptor does not select one root")
        selected.append(candidates[0])
    require(len(selected) == 2 and selected[0] != selected[1] and
            sorted(selected) == sorted(roots), "nested roots missing or duplicated")

    require(set(assembly_row) == {"base", "case", "mode", "head", "output"} and
            assembly_row["mode"] == "assembly" and assembly_row["base"] == base_raw,
            "malformed nested assembly row")
    assembled = polynomial(assembly_row["head"])
    expected = multiply(rcf, multiply(rcf, p, p), [-rcf.one, rcf.one])
    require(assembled == expected, "wrong nested assembly input")
    result = assembly_row["output"]
    require(isinstance(result, dict) and set(result) == {"kind", "entries"} and
            result["kind"] == "finite" and isinstance(result["entries"], list),
            "nested assembly failed")
    expected_roots = list(rcf.api.MkRoots(assembled, rcf.context))
    emitted = []
    for entry in result["entries"]:
        require(isinstance(entry, dict) and set(entry) == {"root", "multiplicity"} and
                type(entry["multiplicity"]) is int and entry["multiplicity"] > 0,
                "malformed nested multiplicity")
        raw = entry["root"]
        require(isinstance(raw, dict), "malformed nested root")
        if raw.get("kind") == "point":
            require(set(raw) == {"kind", "value"}, "malformed nested point")
            value = coefficient(raw["value"])
        else:
            require(set(raw) == {"kind", "context", "head", "lower", "upper",
                                 "indices", "signs"} and raw["kind"] == "selected" and
                    type(raw["context"]) is int and raw["context"] == 10379,
                    "malformed nested selected root")
            factor = polynomial(raw["head"])
            require(bool(factor), "empty nested selected head")
            lower, lower_kind = endpoint(raw["lower"])
            upper, upper_kind = endpoint(raw["upper"])
            derivatives = rcf.derivatives(factor)
            slots = raw["indices"]
            require(isinstance(slots, list) and all(type(i) is int for i in slots) and
                    (slots == [] or slots == list(range(1, len(factor)))) and
                    isinstance(raw["signs"], list) and len(raw["signs"]) == len(slots) and
                    all(type(s) is int and s in (-1, 0, 1) for s in raw["signs"]),
                    "malformed nested selected signs")
            queried = [] if not slots else derivatives
            candidates = [root for root in rcf.api.MkRoots(factor, rcf.context)
                          if (lower_kind == -1 or lower_kind == 0 and lower < root) and
                          (upper_kind == 1 or upper_kind == 0 and root < upper) and
                          [sign(rcf.eval(q, root)) for q in queried] == raw["signs"]]
            require(len(candidates) == 1, "nested assembly descriptor is ambiguous")
            value = candidates[0]
        require(rcf.eval(assembled, value) == 0, "nested assembly emitted a foreign root")
        derivatives = [assembled] + rcf.derivatives(assembled)
        multiplicity = next((i for i, q in enumerate(derivatives)
                             if rcf.eval(q, value) != 0), None)
        require(multiplicity == entry["multiplicity"], "wrong nested root multiplicity")
        emitted.append(value)
    require(len(emitted) == 3 and all(a != b for i, a in enumerate(emitted)
                                      for b in emitted[i+1:]) and
            sorted(emitted) == sorted(expected_roots),
            "nested assembly roots missing or duplicated")


def verify(rows):
    check_version()
    require([r.get("case") for r in rows] == CASES, "missing, repeated or reordered cases")
    for index, row in enumerate(rows[:10]):
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
    for index, row in enumerate(rows[10:16], start=10):
        verify_assembly(row, index)
    verify_nested(rows[16], rows[17])


def main():
    rows = [json.loads(line) for line in sys.stdin if line.strip()]
    verify(rows)
    print(f"verified {len(rows)} capped isolation and root-assembly fixtures with exact Z3 RCF")


if __name__ == "__main__":
    main()
