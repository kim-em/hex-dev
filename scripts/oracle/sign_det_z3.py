#!/usr/bin/env python3
"""Exact Z3 RCF oracle for sign determination over nested infinitesimals.

Pin: z3-solver 4.15.4.0 and numeric runtime version (4, 15, 4, 0).
Each record gets a fresh RCF context;
each successive infinitesimal is smaller than positive base-field elements.
Roots, signs and comparisons use exact RCF operations, never decimal output.
"""
from __future__ import annotations

import argparse
from collections import Counter
from importlib.metadata import version
from pathlib import Path
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.oracle.common import OracleMismatch, read_fixtures, write_failure
from scripts.oracle.sign_det_common import require, check_encoding, check_output, sign_vector

VERSION = "z3-solver 4.15.4.0"
DEFAULT_FIXTURE = ROOT / "conformance-fixtures/HexSignDet/infinitesimal.jsonl"
REQUIRED_CASES = {"infinitesimal/" + name for name in (
    "passmore/whole", "passmore/positive", "passmore/empty", "descriptor/passmore/cubic",
    "descriptor/passmore/square", "descriptor/passmore/ambiguous", "compare/passmore/order",
    "reencode/passmore/reencode", "square/zero-repeat", "square/negative-scale",
    "square/repeated", "square/root-endpoint", "square/cancelled", "nested/whole",
    "nested/singleton", "descriptor/nested/singleton", "descriptor/nested/stale-context",
    "reencode/nested/reencode", "descriptor/square/negative-head", "compare/square/scaled-equal",
    "compare/passmore/shared-cubic", "square/zero-root", "square/constant", "square/root-free",
    "nested/reversed", "nested/root-endpoint", "descriptor/passmore/absent",
    "descriptor/passmore/malformed", "descriptor/nested/reversed",
)}


def check_version() -> None:
    import z3
    require(version("z3-solver") == "4.15.4.0" and z3.get_version()[:4] == (4, 15, 4, 0),
            "the exact pinned z3-solver 4.15.4.0 is required")


class RCF:
    """An independent exact root oracle for one serialized coefficient context."""

    def __init__(self, context: Any):
        import z3
        from z3 import z3rcf
        require(isinstance(context, dict) and set(context) == {"id", "levels", "order"},
                "malformed coefficient context")
        levels = context["levels"]
        require(type(context["id"]) is int and context["id"] == 10377 and
                isinstance(levels, list) and 1 <= len(levels) <= 2 and
                levels == [f"epsilon{i + 1}" for i in range(len(levels))] and
                context["order"] == "each-new-level-smaller-than-positive-base-elements",
                "foreign, reordered or incomplete coefficient context")
        self.context = z3.Context()
        self.api = z3rcf
        self.levels = [z3rcf.MkInfinitesimal(name, self.context) for name in levels]
        self.zero = z3rcf.RCFNum(0, self.context)
        self.one = z3rcf.RCFNum(1, self.context)

    def coeff(self, value: Any, depth: int | None = None):
        if depth is None:
            depth = len(self.levels)
        if depth == 0:
            require(isinstance(value, list) and len(value) == 2 and
                    all(type(v) is int for v in value) and value[1] > 0,
                    "malformed exact rational coefficient")
            return self.api.RCFNum(f"{value[0]}/{value[1]}", self.context)
        require(isinstance(value, dict) and set(value) == {"num", "den"} and
                isinstance(value["num"], list) and isinstance(value["den"], list),
                "malformed rational-function coefficient")
        point = self.levels[depth - 1]
        num = self.eval([self.coeff(c, depth - 1) for c in value["num"]], point)
        den = self.eval([self.coeff(c, depth - 1) for c in value["den"]], point)
        require(den != 0, "zero coefficient denominator")
        # This pinned Python API exposes __div__, not Python 3 __truediv__.
        return num.__div__(den)

    def poly(self, value: Any):
        require(isinstance(value, list), "polynomial coefficients must be a list")
        return self.trim([self.coeff(c) for c in value])

    @staticmethod
    def trim(p):
        while p and p[-1] == 0:
            p.pop()
        return p

    def eval(self, p, x):
        result = self.zero
        for c in reversed(p):
            result = result * x + c
        return result

    def derivative(self, p):
        return self.trim([c * i for i, c in enumerate(p)][1:])

    def derivatives(self, p):
        result = []
        for _ in range(len(p) - 1):
            p = self.derivative(p)
            result.append(p)
        return result

    def remainder(self, p, q):
        require(bool(q), "polynomial division by zero")
        p = p.copy()
        while len(p) >= len(q):
            offset = len(p) - len(q)
            scale = p[-1].__div__(q[-1])
            for i, c in enumerate(q):
                p[offset + i] = p[offset + i] - scale * c
            self.trim(p)
        return p

    def squarefree(self, p):
        if not p:
            return False
        q = self.derivative(p)
        while q:
            p, q = q, self.remainder(p, q)
        return len(p) == 1

    def endpoint(self, value):
        if value == "-inf":
            return (0, self.zero)
        if value == "+inf":
            return (2, self.zero)
        return (1, self.coeff(value))

    def domain(self, raw):
        p = self.poly(raw["head"])
        a, b = self.endpoint(raw["lower"]), self.endpoint(raw["upper"])
        if not self.squarefree(p) or not a < b:
            return p, None
        if any(tag == 1 and self.eval(p, x) == 0 for tag, x in (a, b)):
            return p, None
        roots = sorted(self.api.MkRoots(p, self.context)) if len(p) > 1 else []
        require(all(x < y for x, y in zip(roots, roots[1:])), "oracle returned duplicate roots")
        return p, [x for x in roots if (a[0] == 0 or a[1] < x) and (b[0] == 2 or x < b[1])]

    def signs(self, queries, root):
        return [1 if (v := self.eval(q, root)) > 0 else -1 if v < 0 else 0 for q in queries]

    def table(self, data):
        _, roots = self.domain(data)
        queries = [self.poly(q) for q in data["queries"]]
        if roots is None:
            return None
        counts = Counter(tuple(self.signs(queries, root)) for root in roots)
        return [{"signs": list(signs), "count": count} for signs, count in sorted(counts.items())]

    def selection(self, raw, p, roots):
        indices, signs = raw["indices"], raw["signs"]
        require(type(raw["context"]) is int and raw["context"] >= 0 and
                isinstance(indices, list) and isinstance(signs, list), "malformed descriptor input")
        if raw["context"] != 10377:
            return "context", []
        if roots is None:
            return "domain", []
        n = len(p) - 1
        if (n <= 0 or any(type(i) is not int or not 1 <= i <= n for i in indices) or
                len(indices) != len(set(indices)) or not sign_vector(signs, len(indices))):
            return "malformed", []
        derivatives = self.derivatives(p)
        selected = [r for r in roots if self.signs([derivatives[i - 1] for i in indices], r) == signs]
        return (None if len(selected) == 1 else "absent" if not selected else "ambiguous"), selected

    def descriptor(self, data):
        p, roots = self.domain(data)
        derivatives = self.derivatives(p)
        n = len(derivatives)
        actual_roots = data["roots"]
        if roots is None:
            require(actual_roots == {"status": "invalid-domain"}, "invalid root-list domain accepted")
        else:
            require(isinstance(actual_roots, dict) and isinstance(actual_roots.get("roots"), list),
                    "missing root list")
            for encoding in actual_roots["roots"]:
                check_encoding(encoding, n)
            expected = [{"indices": list(range(1, n + 1)), "signs": self.signs(derivatives, r),
                         "replay": True} for r in roots]
            require(actual_roots == {"status": "ok", "roots": expected},
                    "full encodings differ from exact increasing Z3 roots")
        reason, selected = self.selection(data, p, roots)
        actual = data["validation"]
        if reason is not None:
            require(actual == {"status": "invalid-descriptor", "reason": reason},
                    f"invalid descriptor reason differs: {reason}")
            return
        require(actual.get("status") == "ok" and actual.get("replay") is True,
                "valid descriptor construction/replay failed")
        require(actual.get("staleContextReplay") is False and
                actual.get("changedHeadReplay") is False, "stale descriptor evidence accepted")
        check_encoding(actual.get("completion"), n)
        require(isinstance(actual.get("selected"), dict) and
                sign_vector(actual["selected"].get("signs"), len(data["queries"])),
                "malformed selected query signs")
        expected = {"status": "ok", "indices": list(range(1, n + 1)),
                    "signs": self.signs(derivatives, selected[0]), "replay": True, "bindings": True,
                    "copiedQueriesReplay": False}
        require(actual["completion"] == expected, "completion changes selected root")
        require(actual.get("selected") == {"status": "ok", "replay": True,
                "signs": self.signs([self.poly(q) for q in data["queries"]], selected[0])},
                "selected query signs differ from exact Z3 evaluation")

    def selected(self, raw):
        p, roots = self.domain(raw)
        reason, selected = self.selection(raw, p, roots)
        require(reason is None, f"invalid comparison/re-encoding source: {reason}")
        return p, selected[0]

    def comparison(self, data):
        left, a = self.selected(data["left"])
        right, b = self.selected(data["right"])
        out = data["result"]
        require(out.get("status") == "ok" and all(out.get(flag) is True for flag in
                ("commonReplay", "leftReplay", "rightReplay")), "unchecked comparison")
        head = self.poly(out["commonHead"])
        product = [self.zero] * (len(left) + len(right) - 1)
        for i, x in enumerate(left):
            for j, y in enumerate(right):
                product[i + j] = product[i + j] + x * y
        require(self.squarefree(head) and not self.remainder(product, head) and
                not self.remainder(head, left) and not self.remainder(head, right),
                "common head is not a squarefree root union")
        require(out.get("order") == ("lt" if a < b else "gt" if a > b else "eq"),
                "comparison differs from exact Z3 root order")
        derivatives = self.derivatives(head)
        require(sign_vector(out.get("leftSigns"), len(derivatives)) and
                sign_vector(out.get("rightSigns"), len(derivatives)), "malformed common-root encodings")
        require(out.get("leftSigns") == self.signs(derivatives, a) and
                out.get("rightSigns") == self.signs(derivatives, b), "wrong common-root encodings")

    def reencoding(self, data):
        _, root = self.selected(data["source"])
        p, roots = self.domain(data)
        out = data["result"]
        if roots is None or not any(root == r for r in roots):
            require(out == {"status": "none"}, "re-encoding accepted an absent root")
            return
        derivatives = self.derivatives(p)
        check_encoding(out, len(derivatives))
        require(out == {"status": "ok", "indices": list(range(1, len(derivatives) + 1)),
                "signs": self.signs(derivatives, root), "replay": True}, "re-encoding changes root")


def check_record(record):
    require(record.get("kind") == "result" and record.get("lib") == "HexSignDet" and
            record.get("op") in ("table", "descriptor", "compare", "reencode"),
            "unexpected infinitesimal fixture record")
    payload = record["value"]
    context = payload["coefficientContext"]
    oracle = RCF(context)
    parts = record["case"].split("/")
    require(len(oracle.levels) == (2 if "nested" in parts else 1),
            "case has the wrong coefficient depth")
    data = payload["data"]
    require(isinstance(data, dict) and type(data.get("schema")) is int and data["schema"] == 1,
            "unsupported infinitesimal fixture schema")
    operation = record["op"]
    if "passmore" in parts:
        raw = data["source"] if operation == "reencode" else data["left"] if operation == "compare" else data
        epsilon = oracle.levels[0]
        require(oracle.poly(raw["head"]) ==
                [oracle.one, oracle.zero, -epsilon, -epsilon, oracle.zero, epsilon * epsilon],
                "case does not contain the required Passmore polynomial")
    if operation == "table":
        expected = oracle.table(data)
        for mode in ("reduced", "direct"):
            check_output(data[mode], expected, len(data["queries"]))
            if expected is not None:
                require(data[mode].get("staleChildReplay") is False, "stale child evidence accepted")
                if len(data["queries"]) > 1:
                    require(data[mode].get("missingSupportReplay") is False,
                            "multi-query table accepted as a leaf")
                else:
                    require(data[mode].get("missingSupportReplay", "missing") is None,
                            "unexpected missing-support test for a leaf")
        if len(data["queries"]) <= 4:
            require("reference" in data, "small fixture lacks full-ternary reference")
        if "reference" in data:
            check_output(data["reference"], expected, len(data["queries"]))
    else:
        getattr(oracle, {"compare": "comparison", "reencode": "reencoding"}.get(operation, operation))(data)


def check(source, failure_dir, profile, seed):
    seen = set()
    failures = 0
    for record in read_fixtures(source):
        case = record["case"]
        try:
            require(case not in seen, "duplicate case")
            seen.add(case)
            check_record(record)
        except (OracleMismatch, KeyError, TypeError, ValueError, ArithmeticError) as exc:
            failures += 1
            write_failure(failure_dir, library="HexSignDet", profile=profile, seed=seed,
                          case_id=case, kind="infinitesimal", input_record=record,
                          lean_output=record.get("value"), oracle_output=None,
                          oracle_name="Z3 RCF", oracle_version=VERSION, diff=str(exc))
            print(f"FAIL {case}: {exc}", file=sys.stderr)
    require(REQUIRED_CASES <= seen, f"missing infinitesimal cases: {sorted(REQUIRED_CASES - seen)}")
    print(f"HexSignDet: {len(seen)} exact infinitesimal cases, {failures} failures ({VERSION})")
    return int(failures != 0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--profile", choices=("ci", "local"), default="ci")
    parser.add_argument("--seed", type=int, default=10377)
    parser.add_argument("--failure-dir", type=Path, default=ROOT / "conformance-failures")
    args = parser.parse_args()
    try:
        check_version()
        return check(args.source or (DEFAULT_FIXTURE if args.check else None),
                     args.failure_dir, args.profile, args.seed)
    except (OracleMismatch, OSError, ImportError) as exc:
        print(f"FAIL HexSignDet Z3 oracle: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
