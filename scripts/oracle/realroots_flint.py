#!/usr/bin/env python3
"""python-flint oracle driver for ``hex-real-roots``.

Reads a JSONL stream produced by ``lake exe hexrealroots_emit_fixtures``
(or the committed sample at
``conformance-fixtures/HexRealRoots/realroots.jsonl``) and re-derives
the real roots of each integer polynomial *independently* through
python-flint's ``fmpz_poly``.  It never calls the Lean isolator: the
expected values come from FLINT/Arb, not from re-running the operation
under test.

Two tiers, all endpoint arithmetic in exact ``fractions.Fraction``:

* **exact tier** — ``fmpz_poly.factor()`` yields the rational roots
  (the linear factors).  Every rational root must lie in exactly one
  Lean interval ``(a, b]`` (``a < r <= b`` in ``Fraction`` arithmetic),
  and every Lean interval that contains a rational root is matched.

* **ball tier** — ``fmpz_poly.complex_roots()`` gives certified
  isolating balls; FLINT sets the imaginary part to exact zero for the
  real roots, so ``imag.is_zero()`` counts the real roots and
  ``imag.contains(0)`` guards the (never-observed, for square-free
  input) ambiguous case.  The working precision is escalated until every
  real root's real-part enclosure ``[lo, hi]`` is narrow enough to sit
  strictly inside exactly one Lean interval, giving the interval ↔ real
  root bijection.

Checks, per square-free fixture:

  (i)   ``root_count`` == ``len(isolations)`` == number of real roots;
  (ii)  bijection: each Lean interval holds exactly one real root and
        each real root lands in exactly one Lean interval;
  (iii) ``lower < upper`` for each interval and ``upper_i <= lower_{i+1}``
        for consecutive intervals, in exact ``Fraction`` arithmetic;
  (iv)  rejection (``isolate_none``): the input is genuinely rejectable
        — the zero polynomial, or non-square-free
        (``deg gcd(p, p') > 0`` in FLINT) — and Lean returned ``none``.

On mismatch it writes a JSON failure record under
``conformance-failures/`` and exits non-zero so CI fails the job.
Missing python-flint prints ``SKIP`` and exits 0.

Usage::

    lake exe hexrealroots_emit_fixtures | python3 scripts/oracle/realroots_flint.py
    python3 scripts/oracle/realroots_flint.py --check
    python3 scripts/oracle/realroots_flint.py path/to/file.jsonl
"""
from __future__ import annotations

import argparse
import os
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexRealRoots" / "realroots.jsonl"
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402  (after sys.path insert)
    OracleMismatch,
    read_fixtures,
    split_fixtures_results,
    write_failure,
)

# Working precisions (bits) the ball tier escalates through.  Degree-15
# fixtures with small coefficients resolve at the first entry; the
# larger caps are a safety margin so the loop always terminates on a
# certified enclosure for square-free input.
PREC_LADDER = (64, 128, 256, 512, 1024, 2048, 4096)


def _flint_version() -> str:
    try:
        import flint  # type: ignore[import-not-found]
        return getattr(flint, "__version__", "unknown")
    except Exception:
        return "unknown"


def _fmpq_to_fraction(q: Any) -> Fraction:
    """Exact ``fractions.Fraction`` from a python-flint ``fmpq``."""
    return Fraction(int(q.numer()), int(q.denom()))


def _dyadic_value(pair: list[int]) -> Fraction:
    """Decode a ``[num, exp]`` dyadic endpoint: value ``num * 2^(-exp)``."""
    num, exp = pair
    return Fraction(num) * (Fraction(2) ** (-exp))


def _intervals(isolations: Any) -> list[tuple[Fraction, Fraction]]:
    """Decode the ``isolations`` result value (rows
    ``[lo_num, lo_exp, hi_num, hi_exp]``) into ``(lower, upper)`` pairs."""
    if not isinstance(isolations, list):
        raise OracleMismatch(f"isolations value must be a list, got {isolations!r}")
    out: list[tuple[Fraction, Fraction]] = []
    for row in isolations:
        if not isinstance(row, list) or len(row) != 4:
            raise OracleMismatch(
                f"each isolation row must be [lo_num, lo_exp, hi_num, hi_exp], got {row!r}"
            )
        lo = _dyadic_value(row[0:2])
        hi = _dyadic_value(row[2:4])
        out.append((lo, hi))
    return out


def _rational_roots(coeffs: list[int]) -> list[Fraction]:
    """The exact rational roots of ``coeffs`` via ``fmpz_poly.factor()``.

    A linear factor ``a*x + b`` (coefficient list ``[b, a]``) contributes
    the root ``-b/a``.  Square-free input means every factor has
    multiplicity one, so each rational root appears once."""
    from flint import fmpz_poly  # type: ignore[import-not-found]
    _content, factors = fmpz_poly(coeffs).factor()
    roots: list[Fraction] = []
    for factor, _mult in factors:
        fc = [int(c) for c in factor.coeffs()]
        if len(fc) == 2:  # linear: fc = [b, a]
            b, a = fc[0], fc[1]
            roots.append(Fraction(-b, a))
    return roots


def _real_root_enclosures(
    coeffs: list[int], min_gap: Fraction
) -> list[tuple[Fraction, Fraction]]:
    """Rational ``[lo, hi]`` enclosures of the real roots of ``coeffs``.

    Uses ``fmpz_poly.complex_roots()`` at escalating precision.  A root
    is real iff its imaginary part is exact zero; the loop keeps raising
    precision until every real root's real-part enclosure is narrower
    than ``min_gap`` (so it cannot straddle two Lean endpoints) and no
    ambiguous imaginary part remains.  The precision ladder is finite, so
    an adversarial root cluster can exhaust it; that surfaces as an
    explicit "precision ladder exhausted" mismatch (a false failure to
    investigate, never an unsound pass).  For square-free input it
    terminates well within the ladder,
    whose roots are simple and separated."""
    from flint import ctx, fmpz_poly  # type: ignore[import-not-found]
    poly = fmpz_poly(coeffs)
    saved = ctx.prec
    try:
        for prec in PREC_LADDER:
            ctx.prec = prec
            enclosures: list[tuple[Fraction, Fraction]] = []
            ambiguous = False
            for root, _mult in poly.complex_roots():
                if root.imag.is_zero():
                    re = root.real
                    lo = _fmpq_to_fraction(re.lower().fmpq())
                    hi = _fmpq_to_fraction(re.upper().fmpq())
                    enclosures.append((lo, hi))
                elif root.imag.contains(0):
                    # Imaginary part not certified away from the real
                    # axis: sharpen and retry.
                    ambiguous = True
                    break
                # else: certified non-real, ignore.
            if ambiguous:
                continue
            if all(hi - lo < min_gap for lo, hi in enclosures):
                return enclosures
        raise OracleMismatch(
            "ball tier failed to certify real roots within the precision ladder"
        )
    finally:
        ctx.prec = saved


def _endpoint_min_gap(
    intervals: list[tuple[Fraction, Fraction]]
) -> Fraction:
    """Smallest positive distance between distinct Lean endpoint values.

    A ball-tier enclosure narrower than this cannot span two endpoints,
    which is what makes the interval match unique.  Defaults to ``1``
    when there are fewer than two distinct endpoints."""
    endpoints = sorted({e for lo, hi in intervals for e in (lo, hi)})
    gaps = [b - a for a, b in zip(endpoints, endpoints[1:]) if b > a]
    return min(gaps) if gaps else Fraction(1)


def _is_zero_poly(coeffs: list[int]) -> bool:
    return all(c == 0 for c in coeffs)


def _nonsquarefree(coeffs: list[int]) -> bool:
    """``deg gcd(p, p') > 0``: the FLINT non-square-free test."""
    from flint import fmpz_poly  # type: ignore[import-not-found]
    p = fmpz_poly(coeffs)
    return p.gcd(p.derivative()).degree() > 0


def _match_intervals(
    intervals: list[tuple[Fraction, Fraction]],
    rational_roots: list[Fraction],
    enclosures: list[tuple[Fraction, Fraction]],
) -> None:
    """Assert the interval ↔ real root bijection.

    Each real root — a rational root ``r`` (matched by ``a < r <= b``) or
    an irrational enclosure ``[lo, hi]`` (matched by ``a < lo`` and
    ``hi <= b``) — lands in exactly one interval, and each interval
    receives exactly one root."""
    hits = [0] * len(intervals)

    def assign(is_in) -> None:
        matched = [k for k, iv in enumerate(intervals) if is_in(iv)]
        if len(matched) != 1:
            raise OracleMismatch(
                f"root matched {len(matched)} intervals (expected 1): "
                f"intervals={intervals}"
            )
        hits[matched[0]] += 1

    # Rational roots are exact; irrational enclosures are those balls not
    # containing any rational root.
    for r in rational_roots:
        assign(lambda iv, r=r: iv[0] < r <= iv[1])
    for lo, hi in enclosures:
        if any(lo <= r <= hi for r in rational_roots):
            continue  # this ball encloses a rational root already counted
        assign(lambda iv, lo=lo, hi=hi: iv[0] < lo and hi <= iv[1])

    for k, h in enumerate(hits):
        if h != 1:
            raise OracleMismatch(
                f"interval {intervals[k]} received {h} roots (expected 1)"
            )


def check(
    source: str | Path | None,
    *,
    failure_dir: Path,
    profile: str,
    seed: int,
) -> int:
    cases, results = split_fixtures_results(read_fixtures(source))
    oracle_version = _flint_version()
    failures = 0
    checked = {"exact": 0, "ball": 0, "reject": 0}

    # Group results by case so we see root_count, isolations, and
    # isolate_none together.
    by_case: dict[tuple[str, str], dict[str, Any]] = {}
    for result in results:
        by_case.setdefault((result["lib"], result["case"]), {})[result["op"]] = result[
            "value"
        ]

    for (lib, case_id), ops in by_case.items():
        record = cases.get((lib, case_id))
        if record is None or record["kind"] != "poly":
            print(f"FAIL {lib}/{case_id}: missing poly fixture", file=sys.stderr)
            failures += 1
            continue
        coeffs = list(record["coeffs"])
        try:
            if "isolate_none" in ops:
                # (iv) rejection: genuinely rejectable and Lean said none.
                if ops["isolate_none"] is not True:
                    raise OracleMismatch(
                        f"isolate_none value must be true, got {ops['isolate_none']!r}"
                    )
                if not (_is_zero_poly(coeffs) or _nonsquarefree(coeffs)):
                    raise OracleMismatch(
                        "isolate_none on an input that is neither zero nor "
                        "non-square-free (FLINT gcd(p, p') has degree 0)"
                    )
                checked["reject"] += 1
                continue

            if "root_count" not in ops or "isolations" not in ops:
                raise OracleMismatch(
                    f"square-free case missing root_count/isolations "
                    f"(ops present: {sorted(ops)})"
                )
            # Independence: never trust the emitter's classification. A
            # result-bearing case must genuinely be a nonzero square-free
            # input by FLINT's own test.
            if _is_zero_poly(coeffs) or _nonsquarefree(coeffs):
                raise OracleMismatch(
                    "isolation result emitted for a zero or non-square-free "
                    "input (FLINT gcd(p, p') has positive degree)"
                )
            root_count = ops["root_count"]
            intervals = _intervals(ops["isolations"])

            # (iii) lower < upper and ordering.
            for lo, hi in intervals:
                if not lo < hi:
                    raise OracleMismatch(f"interval lower >= upper: {(lo, hi)}")
            for (lo1, hi1), (lo2, hi2) in zip(intervals, intervals[1:]):
                if not hi1 <= lo2:
                    raise OracleMismatch(
                        f"intervals out of order / overlapping: "
                        f"{(lo1, hi1)} then {(lo2, hi2)}"
                    )

            min_gap = _endpoint_min_gap(intervals)
            enclosures = _real_root_enclosures(coeffs, min_gap)
            n_real = len(enclosures)

            # (i) counts agree.
            if not (root_count == n_real == len(intervals)):
                raise OracleMismatch(
                    f"count mismatch: root_count={root_count}, "
                    f"len(isolations)={len(intervals)}, FLINT real roots={n_real}"
                )

            # (ii) + exact tier bijection.
            rational_roots = _rational_roots(coeffs)
            _match_intervals(intervals, rational_roots, enclosures)

            checked["ball"] += 1
            checked["exact"] += 1 if rational_roots else 0
        except OracleMismatch as exc:
            failures += 1
            diff = str(exc)
            path = write_failure(
                failure_dir,
                library=lib,
                profile=profile,
                seed=seed,
                case_id=case_id,
                kind="real_roots",
                input_record=record,
                lean_output=ops,
                oracle_output="see diff",
                oracle_name="python-flint",
                oracle_version=oracle_version,
                diff=diff,
            )
            print(f"FAIL {lib}/{case_id}: {exc}\n  failure record: {path}", file=sys.stderr)

    print(
        f"realroots_flint.py: checked {checked['ball']} isolation case(s) "
        f"({checked['exact']} with rational roots), {checked['reject']} rejection "
        f"case(s), {failures} failure(s)",
        file=sys.stderr,
    )
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    src = parser.add_mutually_exclusive_group()
    src.add_argument("input", nargs="?", help="JSONL fixture path (default: stdin)")
    src.add_argument(
        "--check",
        action="store_true",
        help=f"read the committed sample at {DEFAULT_FIXTURE.relative_to(REPO_ROOT)}",
    )
    parser.add_argument(
        "--failure-dir",
        default=os.environ.get("HEX_FAILURE_DIR", str(DEFAULT_FAILURE_DIR)),
        help="directory for JSON failure records",
    )
    parser.add_argument("--profile", default="ci")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args(argv)

    source: str | None = str(DEFAULT_FIXTURE) if args.check else args.input

    try:
        import flint  # noqa: F401  (presence check)
    except ImportError:
        print("SKIP: python-flint not installed", file=sys.stderr)
        return 0

    return check(
        source,
        failure_dir=Path(args.failure_dir),
        profile=args.profile,
        seed=args.seed,
    )


if __name__ == "__main__":
    raise SystemExit(main())
