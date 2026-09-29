#!/usr/bin/env python3
"""Independent exact FLINT oracle for BKR over actual common number fields.

Reconstruct the selected generator and original coefficients from their integer
polynomials and rational intervals. Evaluate emitted QAdjoin coordinates at that
embedding, then use general qqbar polynomial roots and exact evaluation. No Lean
Tarski moments, matrix solutions, candidate supports or Thom rule are reused.
"""
from __future__ import annotations

import argparse
from collections import Counter
from functools import cmp_to_key
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.oracle.common import OracleMismatch, read_fixtures, write_failure
from scripts.oracle.real_algebraic_qqbar import QQBar, Unavailable, VERSION
from scripts.oracle.sign_det_common import require, check_table, sign_vector
from scripts.oracle.sign_det_flint import rational

DEFAULT_FIXTURE = ROOT / "conformance-fixtures/HexSignDet/common-fields.jsonl"
CASES = {
    "common/independent-quadratics": ([[-2, 0, 1], [-3, 0, 1]], 4),
    "common/independent-cubics": ([[-2, 0, 0, 1], [-4, 0, 0, 1]], 3),
}


def check_record(record):
    from flint import fmpz_poly

    require(record.get("kind") == "result" and record.get("lib") == "HexSignDet"
            and record.get("op") == "common-field" and record.get("case") in CASES,
            "unexpected common-field fixture")
    data = record["value"]
    require(type(data.get("schema")) is int and data["schema"] == 1, "unsupported schema")
    expected_inputs, degree = CASES[record["case"]]
    require(isinstance(data.get("inputs"), list) and len(data["inputs"]) == 2,
            "missing independent inputs")
    require([a.get("polynomial") for a in data["inputs"]] == expected_inputs,
            "wrong independent defining polynomials")

    with QQBar() as q:
        zero, one = q.number(0), q.number(1)

        def compare(a, b):
            return q.compare(a, b)

        def sign(a):
            order = compare(a, zero)
            return (order > 0) - (order < 0)

        def evaluate(coefficients, x):
            out = zero
            for coefficient in reversed(coefficients):
                out = q.binary("add", q.binary("mul", out, x), coefficient)
            return out

        def selected(raw):
            p = raw["polynomial"]
            require(isinstance(p, list) and len(p) >= 2 and
                    all(type(c) is int for c in p) and p[-1] != 0,
                    "malformed generator polynomial")
            factors = fmpz_poly(p).factor()[1]
            require(len(factors) == 1 and factors[0][1] == 1 and
                    factors[0][0].degree() == len(p) - 1, "reducible generator polynomial")
            lower, upper = q.number(rational(raw["lower"])), q.number(rational(raw["upper"]))
            require(compare(lower, upper) < 0, "invalid selected interval")
            roots = q.roots([q.number(c, q.integer) for c in p], integer=True)
            hits = [r for r, multiplicity in roots if multiplicity == 1 and
                    compare(lower, r) < 0 and compare(r, upper) < 0]
            require(len(hits) == 1, "interval does not select one root")
            return hits[0]

        generator = selected(data["generator"])
        require(len(data["generator"]["polynomial"]) - 1 == degree,
                "wrong common-field degree")
        original = [selected(raw) for raw in data["inputs"]]
        require(all(compare(a, zero) > 0 for a in original), "wrong original embeddings")

        def coordinate(raw):
            require(isinstance(raw, list), "coordinate must be a coefficient list")
            return evaluate([q.number(rational(c)) for c in raw], generator)

        require(isinstance(data.get("coordinates"), list) and len(data["coordinates"]) == 2,
                "missing common-field coordinates")
        a, b = [coordinate(c) for c in data["coordinates"]]
        require(all(compare(x, y) == 0 for x, y in zip((a, b), original)),
                "common-field coordinates change selected values")
        require(compare(a, b) < 0, "selected input order changed")

        def polynomial(raw):
            require(isinstance(raw, list), "polynomial must be a coordinate list")
            return [coordinate(c) for c in raw]

        def equal_poly(left, right):
            size = max(len(left), len(right))
            return all(compare(left[i] if i < len(left) else zero,
                               right[i] if i < len(right) else zero) == 0 for i in range(size))

        qa, qb = [q.unary("neg", a), one], [q.unary("neg", b), one]
        head = polynomial(data["head"])
        expected_head = [q.binary("mul", a, b),
                         q.unary("neg", q.binary("add", a, b)), one]
        require(equal_poly(head, expected_head), "wrong common-field head")
        require(isinstance(data.get("queries"), list) and len(data["queries"]) == 3,
                "wrong query list")
        queries = [polynomial(raw) for raw in data["queries"]]
        require(all(equal_poly(x, y) for x, y in zip(queries,
                (qa, qb, [q.binary("sub", a, b)]))), "wrong ordered queries")
        roots = q.roots(head)
        require(all(m == 1 for _, m in roots), "non-squarefree root domain")
        roots.sort(key=cmp_to_key(lambda x, y: compare(x[0], y[0])))
        roots = [r for r, _ in roots]
        require(len(roots) == 2 and compare(roots[0], a) == 0 and compare(roots[1], b) == 0,
                "wrong independent root set")
        words = [[sign(evaluate(query, r)) for query in queries] for r in roots]
        expected_table = [{"signs": list(word), "count": count}
                          for word, count in sorted(Counter(map(tuple, words)).items())]
        out = data["result"]
        require(out.get("status") == "ok", "producer did not succeed")
        check_table(out.get("table"), expected_table, 3)
        require(type(out.get("absentCount")) is int and out["absentCount"] == 0,
                "incorrect omitted count")
        derivatives = []
        current = head
        while len(current) > 1:
            current = [q.binary("mul", q.number(i), current[i])
                       for i in range(1, len(current))]
            derivatives.append(current)
        actual_roots = out.get("roots")
        require(isinstance(actual_roots, list) and len(actual_roots) == len(roots),
                "missing or duplicated roots")
        for actual, root, word in zip(actual_roots, roots, words):
            indices = actual.get("indices")
            require(isinstance(indices, list) and all(type(i) is int for i in indices) and
                    indices == list(range(1, len(derivatives) + 1)), "malformed full slots")
            signs = [sign(evaluate(d, root)) for d in derivatives]
            require(sign_vector(actual.get("signs"), len(signs)) and actual["signs"] == signs,
                    "wrong derivative word or root order")
            require(sign_vector(actual.get("selected"), len(word)) and actual["selected"] == word,
                    "wrong selected-root signs")
            require(actual.get("replay") is True, "unchecked root")
        expected_order = "lt" if compare(a, b) < 0 else "gt" if compare(a, b) > 0 else "eq"
        reverse = {"lt": "gt", "gt": "lt", "eq": "eq"}[expected_order]
        require(out.get("order") == expected_order and out.get("totalOrder") == expected_order and
                out.get("reverseOrder") == reverse, "wrong common-field comparison")
        common_roots = q.roots(polynomial(out["commonHead"]))
        common_roots.sort(key=cmp_to_key(lambda x, y: compare(x[0], y[0])))
        require(len(common_roots) == len(roots) and all(m == 1 and compare(r, s) == 0
                for (r, m), s in zip(common_roots, roots)), "wrong common root union")
        require(sign_vector(out.get("reencodedSigns"), 1) and out["reencodedSigns"] == [1] and
                sign_vector(out.get("reencodedSelected"), 3) and
                out["reencodedSelected"] == words[0] and out.get("equalOrder") == "eq",
                "reencoding changes selected root")
        for field in ("commonReplay", "leftReplay", "rightReplay", "reencodingReplay"):
            require(out.get(field) is True, f"unchecked {field}")
        for field in ("copiedReplay", "staleReplay", "repeatedAccepted"):
            require(out.get(field) is False, f"invalid evidence accepted: {field}")


def check(source, failure_dir, profile, seed):
    seen, failures = set(), 0
    for record in read_fixtures(source):
        case = record.get("case", "?")
        try:
            require(case not in seen, "duplicate fixture case")
            seen.add(case)
            check_record(record)
        except (OracleMismatch, ArithmeticError, KeyError, TypeError, ValueError) as exc:
            failures += 1
            write_failure(failure_dir, library="HexSignDet", profile=profile, seed=seed,
                          case_id=case, kind="common-field", input_record=record,
                          lean_output=record.get("value"), oracle_output=None,
                          oracle_name="FLINT qqbar", oracle_version=VERSION, diff=str(exc))
            print(f"FAIL {case}: {exc}", file=sys.stderr)
    require(set(CASES) <= seen, f"missing common-field cases: {sorted(set(CASES) - seen)}")
    print(f"HexSignDet: {len(seen)} exact common-field cases, {failures} failures ({VERSION})")
    return int(failures != 0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--profile", default="ci", choices=("ci", "local"))
    parser.add_argument("--seed", type=int, default=10377)
    parser.add_argument("--failure-dir", type=Path, default=ROOT / "conformance-failures")
    args = parser.parse_args()
    try:
        with QQBar():
            pass
        return check(args.source or (DEFAULT_FIXTURE if args.check else None),
                     args.failure_dir, args.profile, args.seed)
    except (OracleMismatch, Unavailable, OSError, ImportError) as exc:
        print(f"FAIL HexSignDet common-field oracle: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
