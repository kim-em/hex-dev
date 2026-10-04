#!/usr/bin/env python3
"""Exact Z3 oracle for capped isolation, root assembly and native collection.

Checks the actual inputs, scalar-preserving deflation, retained cell counts,
selected roots, completeness and absence of duplicates. Proof graphs and
producer totality are not replayed by this oracle.
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

CASES = ["zero", "constant", "repeated", "nonmonic linear", "quadratic",
         "negative cubic with removed zero", "nonquadratic", "four roots",
         "whole-line inverse infinitesimal", "inseparable by rational bisection",
         "assembly zero", "assembly constant", "assembly pure power",
         "assembly repeated factors", "assembly root-free factor", "assembly simple zero",
         "nested algebraic coefficients", "nested algebraic multiplicities",
         "assembly nonzero cut point", "native common root contexts",
         "nested infinitesimal algebraic replay"]
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
    elif index == 18:
        factors = [[3 * rcf.one, -5 * rcf.one, 2 * rcf.one]] * 2
    else:
        factors = [x, [-rcf.one, rcf.one], [-rcf.one, rcf.one]]
    product = [rcf.one]
    for factor in factors:
        product = multiply(rcf, product, factor)
    return product


def verify_assembly(row, index, *, depth=0, expected=None, require_cut_point=True):
    require(set(row) == {"case", "mode", "head", "output"} and row["mode"] == "assembly",
            "malformed assembly row")
    rcf = RCF({"id": 10377, "levels": ["epsilon1"],
               "order": "each-new-level-smaller-than-positive-base-elements"})
    def polynomial(raw):
        require(isinstance(raw, list), "malformed assembly polynomial")
        p = [rcf.coeff(c, depth) for c in raw]
        require(not p or p[-1] != 0, "trailing assembly zero coefficient")
        return p
    p = polynomial(row["head"])
    require(p == (expected_assembly(rcf, index) if expected is None else expected(rcf)),
            "wrong assembly input")
    output = row["output"]
    require(isinstance(output, dict), "assembly producer failed")
    if not p:
        require(output == {"kind": "all"}, "zero polynomial lost all-roots result")
        return
    require(set(output) == {"kind", "entries"} and output["kind"] == "finite" and
            isinstance(output["entries"], list), "malformed finite assembly")
    roots = list(rcf.api.MkRoots(p, rcf.context)) if len(p) > 1 else []
    selected = []
    points = []
    for entry in output["entries"]:
        require(set(entry) == {"root", "multiplicity"} and
                type(entry["multiplicity"]) is int and entry["multiplicity"] > 0,
                "malformed positive multiplicity")
        raw = entry["root"]
        require(isinstance(raw, dict), "malformed assembled root")
        if raw.get("kind") == "point":
            require(set(raw) == {"kind", "value"}, "malformed coefficient point")
            value = rcf.coeff(raw["value"], depth)
            points.append((value, entry["multiplicity"]))
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
                return rcf.coeff(endpoint[1], depth), 0
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
    require(all(a < b for a, b in zip(selected, selected[1:])),
            "assembled roots are not strictly increasing")
    if index == 18 and require_cut_point:
        require((rcf.one, 2) in points,
                "nonzero cut-point fixture did not exercise a bisection point")


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
    require(all(a < b for a, b in zip(emitted, emitted[1:])),
            "nested assembled roots are not strictly increasing")


def native_value(rcf, raw, roots, depth=0):
    require(isinstance(raw, list), "malformed native stored value")
    if not roots and depth:
        require(len(raw) == 3 and raw[0] == 1 and type(raw[0]) is int and
                isinstance(raw[1], list) and isinstance(raw[2], list) and raw[2],
                "malformed native fraction level")
        numerator = [native_value(rcf, c, [], depth - 1) for c in raw[1]]
        denominator = [native_value(rcf, c, [], depth - 1) for c in raw[2]]
        require((not numerator or numerator[-1] != 0) and denominator[-1] != 0,
                "native fraction trailing zero")
        point = rcf.levels[depth - 1]
        den = rcf.eval(denominator, point)
        require(den != 0, "native fraction zero denominator")
        return rcf.eval(numerator, point).__div__(den)
    if not roots:
        require(len(raw) == 3 and raw[0] == 0 and type(raw[0]) is int and
                type(raw[1]) is int and type(raw[2]) is int and raw[2] > 0 and
                math.gcd(raw[1], raw[2]) == 1, "noncanonical native rational")
        return rcf.coeff(raw[1:], 0)
    if raw == []:
        return rcf.zero
    require(len(raw) == 2 and isinstance(raw[0], list) and raw[0] and
            type(raw[1]) is int and raw[1] in (-1, 1), "malformed native nonzero")
    coefficients = [native_value(rcf, c, roots[:-1], depth) for c in raw[0]]
    require(coefficients[-1] != 0, "native stored trailing zero")
    interpreted = rcf.eval(coefficients, roots[-1])
    require(sign(interpreted) == raw[1], "native cached sign differs")
    return interpreted


def verify_collection(row):
    """Interpret native stored coefficients, roots and cached signs in Z3.

    This checks selected-root and arithmetic semantics independently. The
    embedded Lean replay graphs are retained data, not replayed by this oracle.
    """
    require(set(row) == {"case", "mode", "context", "inputs", "sum", "inverse",
                         "zero", "two", "three"} and row["mode"] == "collection",
            "malformed native collection row")
    rcf = RCF({"id": 10377, "levels": ["epsilon1"],
               "order": "each-new-level-smaller-than-positive-base-elements"})

    def value(raw, roots):
        return native_value(rcf, raw, roots)

    def context(raw, expected_heads):
        require(isinstance(raw, list) and len(raw) == 3 and raw[0] == [] and
                type(raw[1]) is int and raw[1] == 0 and isinstance(raw[2], list) and
                len(raw[2]) == len(expected_heads), "wrong native context stages")
        roots = []
        for frame, expected in zip(raw[2], expected_heads):
            require(isinstance(frame, list) and len(frame) == 7 and frame[0] == [0] and
                    type(frame[0][0]) is int and
                    isinstance(frame[1], list) and isinstance(frame[6], list),
                    "malformed native root frame")
            head = [value(c, roots) for c in frame[1]]
            require(head == [n * rcf.one for n in expected], "wrong native root equation")
            require(isinstance(frame[2], list) and len(frame[2]) == 2 and
                    type(frame[2][0]) is int and frame[2][0] == 1 and
                    isinstance(frame[3], list) and len(frame[3]) == 2 and
                    type(frame[3][0]) is int and frame[3][0] == 1,
                    "wrong native root interval")
            lower, upper = value(frame[2][1], roots), value(frame[3][1], roots)
            require(lower == rcf.one and upper == 2 * rcf.one, "native root interval changed")
            slots, signs = frame[4], frame[5]
            require(isinstance(slots, list) and all(type(i) is int for i in slots) and
                    slots in ([], list(range(1, len(head)))) and isinstance(signs, list) and
                    len(signs) == len(slots) and
                    all(type(s) is int and s in (-1, 0, 1) for s in signs),
                    "malformed native root signs")
            derivatives = [] if not slots else rcf.derivatives(head)
            candidates = [root for root in rcf.api.MkRoots(head, rcf.context)
                          if lower < root < upper and
                          [sign(rcf.eval(q, root)) for q in derivatives] == signs]
            require(len(candidates) == 1, "native frame does not select one root")
            roots.append(candidates[0])
        return roots

    heads = [[-2, 0, 1], [-9, 0, 3]]
    shared = context(row["context"], heads)
    require(isinstance(row["inputs"], list) and len(row["inputs"]) == 3,
            "native collection lost a source")
    mapped = []
    for entry, expected_heads, expected in zip(row["inputs"],
                                              [heads[:1], [], heads[1:]],
                                              [shared[0], rcf.zero, shared[1]]):
        require(set(entry) == {"context", "value", "mapped", "oldInverse", "mappedInverse"},
                "malformed native root inclusion")
        original = context(entry["context"], expected_heads)
        before, after = value(entry["value"], original), value(entry["mapped"], shared)
        require(before == after == expected, "native inclusion changed selected root")
        old_inverse = value(entry["oldInverse"], original)
        mapped_inverse = value(entry["mappedInverse"], shared)
        require(old_inverse == mapped_inverse and mapped_inverse * (after - rcf.one) == rcf.one,
                "native whole-context inverse changed")
        mapped.append(after)
    total, inverse = value(row["sum"], shared), value(row["inverse"], shared)
    require(total == mapped[0] + mapped[2] and total * inverse == rcf.one,
            "native mixed-context arithmetic differs")
    require(total**4 - 10 * total**2 + 1 == 0, "native sum equation differs")
    require(value(row["zero"], shared) == 0 and value(row["two"], shared) == 2 * rcf.one and
            value(row["three"], shared) == 3 * rcf.one, "native coefficients changed")


def verify_nested_replay(row):
    """Check the actual native tower, per-query signs and stored inverses.

    Lean independently replays serialized descriptor and selected-sign graphs.
    This oracle evaluates their mathematical domains and consumer queries in
    an independent exact real closed field; it does not replay matrix proofs.
    """
    require(set(row) == {"case", "mode", "context", "selected", "values", "signs"}
            and row["mode"] == "nested-replay", "malformed nested replay row")
    rcf = RCF({"id": 10377, "levels": ["epsilon1", "epsilon2"],
               "order": "each-new-level-smaller-than-positive-base-elements"})
    context = row["context"]
    require(isinstance(context, list) and len(context) == 3 and context[0] == []
            and type(context[1]) is int and context[1] == 2 and
            isinstance(context[2], list) and len(context[2]) == 2,
            "wrong nested replay stages")
    epsilon, delta = rcf.levels
    roots = []
    frames = context[2]
    for index, frame in enumerate(frames):
        require(isinstance(frame, list) and len(frame) == 7 and frame[0] == [0]
                and type(frame[0][0]) is int, "malformed nested replay frame")
        head = [native_value(rcf, c, roots, 2) for c in frame[1]]
        expected = [-(2 * rcf.one + epsilon if index == 0 else roots[0] + delta),
                    rcf.zero, rcf.one]
        require(head == expected, "wrong nested replay equation")
        require(isinstance(frame[2], list) and len(frame[2]) == 2 and
                frame[2][0] == 1 and type(frame[2][0]) is int and
                isinstance(frame[3], list) and len(frame[3]) == 2 and
                frame[3][0] == 1 and type(frame[3][0]) is int and
                native_value(rcf, frame[2][1], roots, 2) == rcf.one and
                native_value(rcf, frame[3][1], roots, 2) == 2 * rcf.one,
                "wrong nested replay interval")
        require(frame[4] == [] and frame[5] == [],
                "wrong nested replay Thom data")
        candidates = [r for r in rcf.api.MkRoots(head, rcf.context)
                      if rcf.one < r < 2 * rcf.one and sign(r) == 1]
        require(len(candidates) == 1, "nested replay did not select a unique root")
        roots.append(candidates[0])
    alpha, beta = roots
    require(isinstance(row["selected"], list) and len(row["selected"]) == 2,
            "nested replay missing a selected-sign family")
    first_queries = [[-rcf.one, rcf.one]]
    second_queries = [[-rcf.one, rcf.one], [-2 * rcf.one, rcf.one]]
    for index, (entry, expected_queries, point) in enumerate(zip(
            row["selected"], [first_queries, second_queries], roots)):
        require(isinstance(entry, dict) and set(entry) == {"queries", "values", "certificates"},
                "malformed nested selected signs")
        queries = [[native_value(rcf, c, roots[:index], 2) for c in q]
                   for q in entry["queries"]]
        require(queries == expected_queries, "wrong nested consumer queries")
        expected_signs = [sign(rcf.eval(q, point)) for q in queries]
        require(entry["values"] == expected_signs and
                all(type(s) is int for s in entry["values"]), "nested selected signs differ")
        require(isinstance(entry["certificates"], list) and
                len(entry["certificates"]) == len(queries), "nested certificates missing")
        for certificate, query, expected_sign in zip(entry["certificates"], queries, expected_signs):
            require(isinstance(certificate, dict) and
                    set(certificate) == {"queries", "values", "graph"},
                    "malformed nested certificate")
            certificate_queries = [[native_value(rcf, c, roots[:index], 2) for c in q]
                                   for q in certificate["queries"]]
            require(certificate_queries == [query], "nested certificate query differs")
            require(certificate["values"] == [expected_sign] and
                    all(type(s) is int for s in certificate["values"]),
                    "nested certificate signs differ")
            graph = certificate["graph"]
            require(isinstance(graph, list) and len(graph) == 3 and
                    type(graph[0]) is int and graph[0] == 1 and
                    type(graph[1]) is int and isinstance(graph[2], list) and
                    0 <= graph[1] < len(graph[2]), "malformed nested graph")
            for position, encoded in enumerate(graph[2]):
                require(isinstance(encoded, list) and len(encoded) == 2 and
                        isinstance(encoded[0], list) and len(encoded[0]) == 11,
                        "malformed nested graph node")
                children = encoded[1]
                require(children == [] or (isinstance(children, list) and len(children) == 1 and
                        isinstance(children[0], list) and len(children[0]) == 2 and
                        all(type(i) is int and 0 <= i < position for i in children[0])),
                        "nested graph references are not child-before-parent")
                node = encoded[0]
                require(node[:4] == frames[index][:4], "nested graph domain differs")
                node_queries = [[native_value(rcf, c, roots[:index], 2) for c in q]
                                for q in node[4]]
                word = [sign(rcf.eval(q, point)) for q in node_queries]
                system = node[6]
                require(isinstance(system, list) and len(system) == 6 and
                        type(node[5]) is int and node[5] > 0,
                        "malformed nested integer system")
                size = node[5]
                exponents, columns, counts, moments, inverse, denominator = system
                require(all(isinstance(v, list) and len(v) == size for v in system[:5]) and
                        type(denominator) is int and denominator != 0 and
                        all(type(n) is int and n >= 0 for n in counts),
                        "malformed nested integer dimensions")
                require(all(isinstance(w, list) and len(w) == len(word) and
                            all(type(a) is int and a in (-1, 0, 1) for a in w) for w in columns)
                        and len({tuple(w) for w in columns}) == size,
                        "malformed nested sign support")
                require([(w, n) for w, n in zip(columns, counts) if n] == [(word, 1)],
                        "nested graph table differs from exact roots")
                matrix = []
                for powers, moment in zip(exponents, moments):
                    require(isinstance(powers, list) and len(powers) == len(word) and
                            all(type(a) is int and a in (0, 1, 2) for a in powers) and
                            type(moment) is int, "malformed nested moment row")
                    power = lambda w: math.prod(a ** e for a, e in zip(w, powers))
                    require(moment == power(word), "nested graph moment differs")
                    matrix.append([power(w) for w in columns])
                require(all(isinstance(v, list) and len(v) == size and
                            all(type(a) is int for a in v) for v in inverse),
                        "malformed nested inverse matrix")
                require(all(sum(matrix[i][k] * inverse[k][j] for k in range(size)) ==
                            (denominator if i == j else 0)
                            for i in range(size) for j in range(size)),
                        "nested inverse matrix identity failed")
            root_queries = [[native_value(rcf, c, roots[:index], 2) for c in q]
                            for q in graph[2][graph[1]][0][4]]
            require(root_queries == [query],
                    "nested graph query binding differs")
    require(isinstance(row["values"], list) and len(row["values"]) == 8,
            "nested replay lost a stored value")
    values = [native_value(rcf, raw, roots, 2) for raw in row["values"]]
    require(values[:4] == [beta, alpha, epsilon, delta], "nested stored values changed")
    require(values[4] * (beta - rcf.one) == rcf.one and
            values[5] * (alpha - rcf.one) == rcf.one and values[6] == 0 and
            values[7] == beta - (6 * rcf.one).__div__(5 * rcf.one) and sign(values[7]) == -1,
            "nested guard inversion or defining equation changed")
    require(row["signs"] == [sign(value) for value in values] and
            all(type(s) is int for s in row["signs"]), "nested stored signs changed")


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
    verify_assembly(rows[18], 18)
    verify_collection(rows[19])
    verify_nested_replay(rows[20])


def parse_record(text):
    def fields(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, "duplicate JSON field: " + key)
            result[key] = value
        return result
    return json.loads(text, object_pairs_hook=fields)


def main():
    rows = [parse_record(line) for line in sys.stdin if line.strip()]
    verify(rows)
    print(f"verified {len(rows)} isolation, assembly and native-collection fixtures with exact Z3 RCF")


if __name__ == "__main__":
    main()
