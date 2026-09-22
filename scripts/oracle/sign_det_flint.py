#!/usr/bin/env python3
"""Exact independent root/sign-table oracle for rational BKR fixtures.

FLINT checks the root domain over Q, enumerates its real qqbar roots and
evaluates every query at those roots. It neither solves moment systems nor
calls the Lean Tarski producer. Complete sparse table equality detects missing
conditions even when forged counts have the correct total. The shared qqbar
adapter enforces the pinned python-flint/FLINT versions.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from functools import cmp_to_key
from math import lcm
from pathlib import Path
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.oracle.common import OracleMismatch, read_fixtures, write_failure
from scripts.oracle.real_algebraic_qqbar import QQBar, Unavailable, VERSION

DEFAULT_FIXTURE = ROOT / "conformance-fixtures/HexSignDet/sign_det.jsonl"
REQUIRED_CASES = {
    "two-roots", "negative-head", "empty-queries", "zero-root",
    "duplicate-zero-constant", "irrational-common-factor", "cubic-derivatives",
    "negative-cubic-derivatives", "high-degree-queries", "rational-scaling",
    "finite-interval", "left-half-line", "right-half-line", "many-queries",
    *(f"{name}/{suffix}" for name in ("constant", "negative-constant", "root-free",
                                    "zero-head", "repeated-head", "cancelled-head")
      for suffix in ("empty", "queries")),
    *(f"invalid-interval/{i}" for i in range(9)),
    *(f"seed-10377/{i}" for i in range(24)),
    *(f"descriptor/{name}" for name in (
        "negative-root", "positive-root", "empty-queries", "permuted-slots", "singleton-empty",
        "negative-head", "irrational", "cubic-left", "cubic-center", "cubic-right", "negative-cubic",
        "absent", "ambiguous", "empty-ambiguous", "unrealized-full", "duplicate-slot", "zero-slot",
        "large-slot", "short-signs", "bad-sign", "stale-context", "constant", "root-free",
        "zero-head", "repeated-head", "root-endpoint", "reversed-interval")),
    *(f"compare/{name}" for name in ("equal-linear-vectors", "reverse-linear", "permuted-slots",
        "shared-irrational", "distinct-irrational", "negative-head", "scaled-head",
        "foreign-endpoint", "disjoint-intervals", "overlapping-equal")),
    *(f"reencode/{name}" for name in ("shared-irrational", "outside-target", "missing-root",
        "invalid-target", "foreign-endpoints")),
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise OracleMismatch(message)


def rational(value: Any) -> Fraction:
    require(isinstance(value, list) and len(value) == 2 and
            all(type(x) is int for x in value) and value[1] > 0,
            f"invalid exact rational: {value!r}")
    return Fraction(*value)


def polynomial(value: Any) -> list[Fraction]:
    require(isinstance(value, list), "polynomial coefficients must be a list")
    return [rational(c) for c in value]


def endpoint(value: Any) -> tuple[int, Fraction]:
    if value == "-inf":
        return (0, Fraction(0))
    if value == "+inf":
        return (2, Fraction(0))
    return (1, rational(value))


def root_words(data: dict[str, Any]) -> list[list[int]] | None:
    """Exact sign vectors in numerical root order, or domain failure."""
    from flint import fmpq, fmpq_poly

    p = polynomial(data["head"])
    require(isinstance(data["queries"], list), "queries must be an ordered list")
    queries = [polynomial(q) for q in data["queries"]]
    lower, upper = endpoint(data["lower"]), endpoint(data["upper"])
    poly = fmpq_poly([fmpq(c.numerator, c.denominator) for c in p])
    if poly.is_zero() or poly.gcd(poly.derivative()).degree() > 0 or not lower < upper:
        return None
    for tag, value in (lower, upper):
        if tag == 1 and poly(fmpq(value.numerator, value.denominator)) == 0:
            return None
    if poly.degree() == 0:
        return []

    denominator = lcm(*(c.denominator for c in p))
    integers = [int(c * denominator) for c in p]
    words: list[list[int]] = []
    with QQBar() as q:
        roots = q.roots([q.number(c, q.integer) for c in integers], integer=True)
        zero = q.number(0)
        lo = q.number(lower[1]) if lower[0] == 1 else None
        hi = q.number(upper[1]) if upper[0] == 1 else None
        operands = [[q.number(c) for c in reversed(query)] for query in queries]
        roots.sort(key=cmp_to_key(lambda a, b: q.compare(a[0], b[0])))
        for root, multiplicity in roots:
            require(multiplicity == 1, "squarefree root has nonunit multiplicity")
            if lo is not None and q.compare(lo, root) >= 0:
                continue
            if hi is not None and q.compare(root, hi) >= 0:
                continue
            signs = []
            for coefficients in operands:
                value = zero
                for coefficient in coefficients:
                    value = q.binary("add", q.binary("mul", value, root), coefficient)
                sign = q.compare(value, zero)
                signs.append((sign > 0) - (sign < 0))
            words.append(signs)
    return words


def expected_table(data: dict[str, Any]) -> list[dict[str, Any]] | None:
    """Return exact sorted positive counts, or mathematical domain failure."""
    words = root_words(data)
    if words is None:
        return None
    counts = Counter(tuple(word) for word in words)
    return [{"signs": list(signs), "count": count} for signs, count in sorted(counts.items())]


def check_output(output: Any, expected: list[dict[str, Any]] | None, arity: int) -> None:
    require(isinstance(output, dict), "missing constructor result")
    if expected is None:
        require(output == {"status": "invalid-domain"}, "invalid domain was accepted")
        return
    require(output.get("status") == "ok", f"valid-domain construction failed: {output!r}")
    require(output.get("replay") is True, "produced replay did not pass its checker")
    check_table(output.get("table"), expected, arity)


def check_table(table: Any, expected: list[dict[str, Any]], arity: int) -> None:
    require(isinstance(table, list), "missing sparse sign table")
    seen = set()
    for row in table:
        require(isinstance(row, dict) and set(row) == {"signs", "count"}, "malformed table row")
        signs, count = row["signs"], row["count"]
        require(isinstance(signs, list) and len(signs) == arity and
                all(type(s) is int and s in (-1, 0, 1) for s in signs), "malformed sign condition")
        require(type(count) is int and count > 0, "sparse counts must be positive integers")
        key = tuple(signs)
        require(key not in seen, "duplicate sign condition")
        seen.add(key)
    require(table == sorted(table, key=lambda row: row["signs"]),
            "produced table rows are not in the serialization order")
    require(table == expected, f"complete sign table differs: Lean={table!r}, FLINT={expected!r}")


def derivative_queries(head: Any) -> list[list[list[int]]]:
    coefficients = polynomial(head)
    while coefficients and coefficients[-1] == 0:
        coefficients.pop()
    derivatives = []
    for _ in range(max(0, len(coefficients) - 1)):
        coefficients = [i * c for i, c in enumerate(coefficients)][1:]
        derivatives.append([[c.numerator, c.denominator] for c in coefficients])
    return derivatives


def sign_vector(value: Any, size: int) -> bool:
    return (isinstance(value, list) and len(value) == size and
            all(type(v) is int and v in (-1, 0, 1) for v in value))


def check_encoding(value: Any, degree: int) -> None:
    require(isinstance(value, dict) and isinstance(value.get("indices"), list) and
            all(type(i) is int for i in value["indices"]) and
            value["indices"] == list(range(1, degree + 1)) and
            sign_vector(value.get("signs"), degree) and value.get("replay") is True,
            "malformed or unchecked full root encoding")


def check_descriptor(data: dict[str, Any]) -> None:
    require(type(data["context"]) is int and data["context"] >= 0, "malformed descriptor context")
    derivatives = derivative_queries(data["head"])
    n = len(derivatives)
    words = root_words({**data, "queries": derivatives + data["queries"]})
    roots = data["roots"]
    if words is None:
        require(roots == {"status": "invalid-domain"}, "invalid root-list domain was accepted")
    else:
        require(roots.get("status") == "ok", "root-list construction failed")
        require(isinstance(roots.get("roots"), list), "missing full descriptor list")
        for encoding in roots["roots"]:
            check_encoding(encoding, n)
        expected_roots = [{"indices": list(range(1, n + 1)), "signs": word[:n], "replay": True}
                          for word in words]
        require(roots.get("roots") == expected_roots,
                "full descriptor list differs from exact increasing FLINT roots")
    indices, signs = data["indices"], data["signs"]
    require(isinstance(indices, list) and isinstance(signs, list), "malformed descriptor input")
    reason = None
    selected = []
    if data["context"] != 10377:
        reason = "context"
    elif (n == 0 or len(indices) != len(signs) or
          any(type(i) is not int or not 1 <= i <= n for i in indices) or
          len(set(indices)) != len(indices) or
          any(type(v) is not int or v not in (-1, 0, 1) for v in signs)):
        reason = "malformed"
    elif words is None:
        reason = "domain"
    else:
        selected = [word for word in words if [word[i - 1] for i in indices] == signs]
        if not selected:
            reason = "absent"
        elif len(selected) != 1:
            reason = "ambiguous"
    actual = data["validation"]
    if reason is not None:
        require(actual == {"status": "invalid-descriptor", "reason": reason},
                f"descriptor validity/reason differs: expected {reason}, got {actual!r}")
        return
    require(actual.get("status") == "ok" and actual.get("replay") is True,
            "valid descriptor construction/replay failed")
    word = selected[0]
    check_encoding(actual.get("completion"), n)
    require(actual["completion"].get("bindings") is True, "unbound completion")
    require(isinstance(actual.get("selected"), dict) and
            sign_vector(actual["selected"].get("signs"), len(data["queries"])) and
            actual["selected"].get("replay") is True, "malformed or unchecked selected signs")
    require(actual.get("completion") == {
        "status": "ok", "indices": list(range(1, n + 1)), "signs": word[:n],
        "replay": True, "bindings": True}, "completion changes the root or full derivative signs")
    require(actual.get("selected") == {"status": "ok", "signs": word[n:], "replay": True},
            "selected-root query signs differ from exact evaluation")


def selection_constraints(raw: dict[str, Any]) -> tuple[list[Any], list[int]]:
    derivatives = derivative_queries(raw["head"])
    indices, signs = raw["indices"], raw["signs"]
    require(type(raw["context"]) is int and raw["context"] == 10377 and derivatives and
            isinstance(indices, list) and all(type(i) is int and 1 <= i <= len(derivatives) for i in indices)
            and len(set(indices)) == len(indices) and sign_vector(signs, len(indices)),
            "malformed source descriptor")
    queries = [derivatives[i - 1] for i in indices]
    words = root_words({**raw, "queries": queries})
    require(words is not None and words.count(signs) == 1, "source descriptor is not uniquely realized")
    queries = [raw["head"]] + queries
    required = [0] + signs
    for boundary, sign in ((raw["lower"], 1), (raw["upper"], -1)):
        tag, value = endpoint(boundary)
        if tag == 1:
            queries.append([[(-value).numerator, value.denominator], [1, 1]])
            required.append(sign)
    return queries, required


def check_comparison(data: dict[str, Any]) -> None:
    from flint import fmpq, fmpq_poly

    lq, ls = selection_constraints(data["left"])
    rq, rs = selection_constraints(data["right"])
    actual = data["result"]
    require(actual.get("status") == "ok", "comparison construction failed")
    for flag in ("commonReplay", "leftReplay", "rightReplay"):
        require(actual.get(flag) is True, f"comparison lacks {flag}")
    def flint_poly(coefficients):
        return fmpq_poly([fmpq(c.numerator, c.denominator) for c in polynomial(coefficients)])
    left, right, head = (flint_poly(coefficients) for coefficients in
                         (data["left"]["head"], data["right"]["head"], actual["commonHead"]))
    require(not head.is_zero() and head.gcd(head.derivative()).degree() == 0 and
            (left * right) % head == 0 and head % left == 0 and head % right == 0,
            "common head is not a squarefree root union")
    derivatives = derivative_queries(actual["commonHead"])
    n = len(derivatives)
    words = root_words({"head": actual["commonHead"], "lower": "-inf", "upper": "+inf",
                        "queries": derivatives + lq + rq})
    require(words is not None, "invalid common root domain")
    li = [i for i, word in enumerate(words) if word[n:n + len(ls)] == ls]
    ri = [i for i, word in enumerate(words) if word[n + len(ls):] == rs]
    require(len(li) == len(ri) == 1, "common head loses a selected root")
    expected_order = "lt" if li[0] < ri[0] else "gt" if li[0] > ri[0] else "eq"
    require(actual.get("order") == expected_order, "comparison differs from exact numerical root order")
    for field, index in (("leftSigns", li[0]), ("rightSigns", ri[0])):
        require(sign_vector(actual.get(field), n) and actual[field] == words[index][:n],
                f"{field} encodes a different common-head root")


def check_reencoding(data: dict[str, Any]) -> None:
    queries, signs = selection_constraints(data["source"])
    derivatives = derivative_queries(data["head"])
    n = len(derivatives)
    words = root_words({**data, "queries": derivatives + queries})
    selected = [] if words is None else [word for word in words if word[n:] == signs]
    require(len(selected) <= 1, "multiple roots satisfy a validated source descriptor")
    actual = data["result"]
    if not selected:
        require(actual == {"status": "none"}, "re-encoding accepted an invalid or absent target root")
    else:
        check_encoding(actual, n)
        require(actual.get("status") == "ok" and actual["signs"] == selected[0][:n],
                "re-encoding changes the selected root")


def check_record(record: dict[str, Any]) -> None:
    require(record.get("kind") == "result" and record.get("lib") == "HexSignDet" and
            record.get("op") in ("table", "descriptor", "compare", "reencode"), "unexpected sign-determination fixture record")
    data = record["value"]
    require(isinstance(data, dict) and type(data.get("schema")) is int and data["schema"] == 1,
            "unsupported sign-table schema")
    if record["op"] == "compare":
        check_comparison(data)
        return
    if record["op"] == "reencode":
        check_reencoding(data)
        return
    if record["op"] == "descriptor":
        check_descriptor(data)
        return
    expected = expected_table(data)
    if expected is None:
        require(data.get("algebraic", "missing") is None, "invalid domain has algebraic root table")
    else:
        check_table(data.get("algebraic"), expected, len(data["queries"]))
    for mode in ("reduced", "direct"):
        check_output(data[mode], expected, len(data["queries"]))
    if len(data["queries"]) <= 4:
        require("reference" in data, "small fixture is missing full-ternary reference")
    if "reference" in data:
        check_output(data["reference"], expected, len(data["queries"]))


def check(source: str | Path | None, failure_dir: Path, profile: str, seed: int) -> int:
    seen: set[str] = set()
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
                          case_id=case, kind="sign-table", input_record=record,
                          lean_output=record.get("value"), oracle_output=None,
                          oracle_name="FLINT qqbar", oracle_version=VERSION, diff=str(exc))
            print(f"FAIL {case}: {exc}", file=sys.stderr)
    require(REQUIRED_CASES <= seen,
            f"incomplete sign-table fixture stream: missing {sorted(REQUIRED_CASES - seen)}")
    print(f"HexSignDet: {len(seen)} exact root/sign cases, {failures} failures ({VERSION})")
    return int(failures != 0)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--profile", choices=("ci", "local"), default="ci")
    parser.add_argument("--seed", type=int, default=10377)
    parser.add_argument("--failure-dir", type=Path, default=ROOT / "conformance-failures")
    args = parser.parse_args()
    try:
        with QQBar():
            pass
        return check(args.source or (DEFAULT_FIXTURE if args.check else None),
                     args.failure_dir, args.profile, args.seed)
    except (Unavailable, OracleMismatch, OSError, ImportError) as exc:
        print(f"FAIL HexSignDet oracle: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
