#!/usr/bin/env python3
"""fpylll oracle driver for `hex-lll`.

Reads a JSONL stream produced by `lake exe hexlll_emit_fixtures` (or
the committed sample at `conformance-fixtures/HexLLL/lll.jsonl`) and
re-runs each `lll` reduction through `fpylll.LLL.reduction`.

LLL output is not unique in general, so this oracle compares the two
reduced bases via lattice-equality and δ-reducedness rather than
literal basis equality:

1. **Lattice equality.** The Lean basis and the fpylll basis must
   span the same `Z`-lattice. Verified by computing the row-style
   Hermite Normal Form (HNF) of both bases via `fpylll.IntegerMatrix`
   and asserting equality. HNF is canonical for a `Z`-lattice given a
   row order, so HNF agreement is the right structural check.
2. **δ-reducedness of Lean's basis.** `fpylll.LLL.is_reduced` is run
   on Lean's basis directly (with the same `δ = 3/4` Lean uses).
3. **Shortest-vector norm parity.** Lean's `b[0]` and fpylll's `b[0]`
   are the shortest vectors in their respective reduced bases; they
   must satisfy `||lean[0]||² ≤ α^{n-1} · ||fpylll[0]||²` and vice
   versa with `α = 1/(δ - 1/4) = 2` for `δ = 3/4`. This is the LLL
   gap factor — any pair of `δ`-reduced bases of the same lattice
   satisfy this inequality, so a violation indicates either non-
   `δ`-reducedness on Lean's side or a span mismatch.

Usage::

    # CI: pipe Lean's emission directly into the oracle.
    lake exe hexlll_emit_fixtures | python3 scripts/oracle/lll_fpylll.py

    # Local: replay against the committed sample.
    python3 scripts/oracle/lll_fpylll.py --check
"""
from __future__ import annotations

import argparse
import os
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexLLL" / "lll.jsonl"
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402  (after sys.path insert)
    OracleMismatch,
    read_fixtures,
    split_fixtures_results,
    write_failure,
)


# `δ = 3/4` matches `HexLLL.EmitFixtures.emitCase`.
LLL_DELTA = 0.75
ALPHA_SQUARED_PER_GAP = 2.0  # 1 / (δ - 1/4) for δ = 3/4.


def _basis_rows(record: dict[str, Any]) -> list[list[int]]:
    if record["kind"] != "lattice":
        raise ValueError(f"expected lattice record, got {record['kind']}")
    return [list(row) for row in record["basis"]]


def _result_basis(record: dict[str, Any]) -> list[list[int]]:
    if record["kind"] != "result" or record["op"] != "lll":
        raise ValueError(f"expected lll result, got {record}")
    value = record["value"]
    if not isinstance(value, list):
        raise ValueError(f"lll result value must be List[List[int]]: {record}")
    return [[int(c) for c in row] for row in value]


def _norm_sq(row: list[int]) -> int:
    return sum(c * c for c in row)


def _hnf_rows(rows: list[list[int]]) -> list[list[int]]:
    """Row-style Hermite Normal Form of an integer matrix.

    Uses `flint.fmpz_mat.hnf()` if python-flint is installed (preferred —
    matches the other oracle drivers in this repo); falls back to
    `fpylll.IntegerMatrix` HNF otherwise.

    The convention here is rows-as-generators: HNF is computed on the
    matrix whose rows are the basis vectors. Two row-bases generate the
    same `Z`-lattice iff they have equal row HNF (under the same row
    convention).
    """
    try:
        from flint import fmpz_mat  # type: ignore[import-not-found]
        m = fmpz_mat([[int(c) for c in r] for r in rows])
        h = m.hnf()
        out: list[list[int]] = []
        for i in range(h.nrows()):
            out.append([int(h[i, j]) for j in range(h.ncols())])
        return out
    except ImportError:
        pass
    raise RuntimeError("python-flint is not installed and fpylll exposes no HNF API")


def _drop_zero_rows(rows: list[list[int]]) -> list[list[int]]:
    return [r for r in rows if any(c != 0 for c in r)]


def _normalised_hnf(rows: list[list[int]]) -> list[list[int]]:
    """HNF with zero rows dropped — two bases generate the same lattice
    iff their normalised HNFs match. Dropping zero rows handles the
    redundant-row case (rectangular full-rank lattices represented by
    n × m bases with `n ≤ m`)."""
    return _drop_zero_rows(_hnf_rows(rows))


def _rank(matrix: list[list[Fraction]]) -> int:
    """Exact rank over Q for small oracle matrices."""
    rows = [row[:] for row in matrix if any(value != 0 for value in row)]
    if not rows:
        return 0
    row_count = len(rows)
    col_count = len(rows[0])
    rank = 0
    for col in range(col_count):
        pivot = next((i for i in range(rank, row_count) if rows[i][col] != 0), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        pivot_value = rows[rank][col]
        rows[rank] = [value / pivot_value for value in rows[rank]]
        for i in range(row_count):
            if i == rank or rows[i][col] == 0:
                continue
            factor = rows[i][col]
            rows[i] = [
                value - factor * pivot_entry
                for value, pivot_entry in zip(rows[i], rows[rank], strict=True)
            ]
        rank += 1
        if rank == row_count:
            break
    return rank


def _independent_columns(rows: list[list[int]]) -> list[int]:
    """Choose columns whose row-restricted square submatrix has full rank."""
    if not rows:
        return []
    row_count = len(rows)
    col_count = len(rows[0])
    selected: list[int] = []
    for col in range(col_count):
        trial = selected + [col]
        matrix = [
            [Fraction(rows[i][j]) for j in trial]
            for i in range(row_count)
        ]
        if _rank(matrix) > len(selected):
            selected = trial
            if len(selected) == row_count:
                return selected
    raise ValueError("basis rows are not linearly independent over Q")


def _inverse(matrix: list[list[Fraction]]) -> list[list[Fraction]]:
    n = len(matrix)
    aug = [
        row[:] + [Fraction(1 if i == j else 0) for j in range(n)]
        for i, row in enumerate(matrix)
    ]
    for col in range(n):
        pivot = next((i for i in range(col, n) if aug[i][col] != 0), None)
        if pivot is None:
            raise ValueError("singular matrix")
        aug[col], aug[pivot] = aug[pivot], aug[col]
        pivot_value = aug[col][col]
        aug[col] = [value / pivot_value for value in aug[col]]
        for i in range(n):
            if i == col or aug[i][col] == 0:
                continue
            factor = aug[i][col]
            aug[i] = [
                value - factor * pivot_entry
                for value, pivot_entry in zip(aug[i], aug[col], strict=True)
            ]
    return [row[n:] for row in aug]


def _row_lattice_contains(basis: list[list[int]], row: list[int]) -> bool:
    """Check whether `row` is an integer combination of full-row-rank basis rows.

    This is the fpylll-only fallback for environments without python-flint.
    It avoids relying on fpylll's removed/optional HNF API by solving over an
    independent column minor and then checking that the resulting coefficients
    are integral and reconstruct the full row.
    """
    if not basis:
        return not any(row)
    pivots = _independent_columns(basis)
    minor = [
        [Fraction(basis[i][j]) for j in pivots]
        for i in range(len(basis))
    ]
    inv = _inverse(minor)
    restricted = [Fraction(row[j]) for j in pivots]
    coeffs = [
        sum(restricted[k] * inv[k][j] for k in range(len(inv)))
        for j in range(len(inv))
    ]
    if any(coeff.denominator != 1 for coeff in coeffs):
        return False
    reconstructed = [
        sum(coeffs[i] * basis[i][j] for i in range(len(basis)))
        for j in range(len(basis[0]))
    ]
    return reconstructed == [Fraction(value) for value in row]


def _same_row_lattice(left: list[list[int]], right: list[list[int]]) -> bool:
    try:
        return _normalised_hnf(left) == _normalised_hnf(right)
    except RuntimeError:
        pass
    left_nonzero = _drop_zero_rows(left)
    right_nonzero = _drop_zero_rows(right)
    if len(left_nonzero) != len(right_nonzero):
        return False
    return all(_row_lattice_contains(left_nonzero, row) for row in right_nonzero) and all(
        _row_lattice_contains(right_nonzero, row) for row in left_nonzero
    )


def _fpylll_reduce(rows: list[list[int]]) -> list[list[int]]:
    from fpylll import LLL, IntegerMatrix  # type: ignore[import-not-found]
    M = IntegerMatrix.from_matrix(rows)
    LLL.reduction(M, delta=LLL_DELTA)
    return [[int(M[i, j]) for j in range(M.ncols)] for i in range(M.nrows)]


def _is_lll_reduced(rows: list[list[int]]) -> bool:
    """Run `fpylll.LLL.is_reduced` on a basis at the configured δ."""
    from fpylll import LLL, IntegerMatrix  # type: ignore[import-not-found]
    M = IntegerMatrix.from_matrix(rows)
    return bool(LLL.is_reduced(M, delta=LLL_DELTA))


def _gap_bound(n: int) -> float:
    """Squared LLL gap factor `α^{n-1}` for `α = 1/(δ - 1/4)`."""
    if n <= 1:
        return 1.0
    return ALPHA_SQUARED_PER_GAP ** (n - 1)


def _fpylll_version() -> str:
    try:
        import fpylll  # type: ignore[import-not-found]
        return getattr(fpylll, "__version__", "unknown")
    except Exception:
        return "unknown"


def _first_row_checksum(row: list[int]) -> int:
    acc = 0
    for value in row:
        acc = acc * 65537 + int(value)
    return acc


def bench_checksum(source: str | Path | None) -> int:
    """Read one whitespace matrix, reduce it with fpylll, print b[0]'s checksum.

    Input format is deliberately small and bench-oriented:

        rows cols
        a_00 a_01 ... a_(rows-1,cols-1)

    The checksum matches `Hex.LLLBench.intVectorChecksum`, so lean-bench can
    use `compare` between the Lean fixed target and the process-call target.
    """
    if source is None:
        text = sys.stdin.read()
    else:
        text = Path(source).read_text(encoding="utf-8")
    words = text.split()
    if len(words) < 2:
        raise ValueError("bench input must start with rows and cols")
    rows = int(words[0])
    cols = int(words[1])
    entries = [int(w) for w in words[2:]]
    expected = rows * cols
    if len(entries) != expected:
        raise ValueError(f"expected {expected} matrix entries, got {len(entries)}")
    matrix = [entries[i * cols : (i + 1) * cols] for i in range(rows)]
    reduced = _fpylll_reduce(matrix)
    if not reduced:
        print(0)
    else:
        print(_first_row_checksum(reduced[0]))
    return 0


def _check_case(
    *,
    case_id: str,
    input_basis: list[list[int]],
    lean_basis: list[list[int]],
    failure_dir: Path,
    profile: str,
    seed: int,
    oracle_version: str,
) -> bool:
    """Run all checks for one `(input, lean_output)` pair. Returns True
    on pass, False on fail (after writing a failure record)."""
    fpylll_basis = _fpylll_reduce(input_basis)

    failures: list[str] = []

    # 1. Lattice equality (Lean output spans the same Z-lattice as input).
    try:
        if not _same_row_lattice(input_basis, lean_basis):
            failures.append("lattice-equality: lean basis spans a different Z-lattice")
    except Exception as exc:
        failures.append(f"lattice-equality: HNF computation failed ({exc})")

    # 2. δ-reducedness of Lean's basis.
    try:
        if not _is_lll_reduced(lean_basis):
            failures.append(
                f"reducedness: lean basis is NOT δ={LLL_DELTA}-LLL-reduced"
            )
    except Exception as exc:
        failures.append(f"reducedness: fpylll.LLL.is_reduced failed ({exc})")

    # 3. Shortest-vector norm parity (within the LLL gap factor).
    try:
        n = len(lean_basis)
        if n > 0 and len(fpylll_basis) > 0:
            lean_norm = _norm_sq(lean_basis[0])
            ref_norm = _norm_sq(fpylll_basis[0])
            bound = _gap_bound(n)
            # Both bases are δ-reduced over the same lattice, so the
            # LLL bound applies symmetrically.
            if lean_norm > bound * max(1, ref_norm):
                failures.append(
                    "shortest-vector: lean ||b[0]||²="
                    f"{lean_norm} exceeds {bound:.1f}·||fpylll[0]||²={ref_norm}"
                )
            if ref_norm > bound * max(1, lean_norm):
                failures.append(
                    "shortest-vector: fpylll ||b[0]||²="
                    f"{ref_norm} exceeds {bound:.1f}·||lean[0]||²={lean_norm}"
                )
    except Exception as exc:
        failures.append(f"shortest-vector: norm comparison failed ({exc})")

    if not failures:
        return True

    diff = "; ".join(failures)
    path = write_failure(
        failure_dir,
        library="HexLLL",
        profile=profile,
        seed=seed,
        case_id=case_id,
        kind="lll",
        input_record={"basis": input_basis},
        lean_output=lean_basis,
        oracle_output=fpylll_basis,
        oracle_name="fpylll",
        oracle_version=oracle_version,
        diff=diff,
    )
    print(
        f"FAIL HexLLL/{case_id}: {diff}\n  failure record: {path}",
        file=sys.stderr,
    )
    return False


def check(
    source: str | Path | None,
    *,
    failure_dir: Path,
    profile: str,
    seed: int,
) -> int:
    cases, results = split_fixtures_results(read_fixtures(source))
    oracle_version = _fpylll_version()
    failures = 0
    checked = 0
    for result in results:
        case_id = result["case"]
        if result["op"] != "lll":
            raise OracleMismatch(
                f"HexLLL/{case_id}: unsupported op {result['op']!r}; "
                f"extend lll_fpylll.py."
            )
        case = cases.get(("HexLLL", case_id))
        if case is None:
            raise OracleMismatch(
                f"HexLLL/{case_id}: result has no matching lattice fixture."
            )
        passed = _check_case(
            case_id=case_id,
            input_basis=_basis_rows(case),
            lean_basis=_result_basis(result),
            failure_dir=failure_dir,
            profile=profile,
            seed=seed,
            oracle_version=oracle_version,
        )
        checked += 1
        if not passed:
            failures += 1
    print(
        f"lll_fpylll.py: checked {checked} case(s), {failures} failure(s)",
        file=sys.stderr,
    )
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    src = parser.add_mutually_exclusive_group()
    src.add_argument(
        "input",
        nargs="?",
        help="JSONL fixture path (default: stdin)",
    )
    src.add_argument(
        "--check",
        action="store_true",
        help=f"read the committed sample at {DEFAULT_FIXTURE.relative_to(REPO_ROOT)}",
    )
    src.add_argument(
        "--bench-checksum",
        action="store_true",
        help=(
            "read one whitespace matrix and print fpylll's first-row checksum "
            "for HexLLL/Bench.lean process-call comparator registrations"
        ),
    )
    parser.add_argument(
        "--failure-dir",
        default=os.environ.get("HEX_FAILURE_DIR", str(DEFAULT_FAILURE_DIR)),
        help="directory for JSON failure records",
    )
    parser.add_argument("--profile", default="ci")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args(argv)

    if args.check:
        source: str | None = str(DEFAULT_FIXTURE)
    else:
        source = args.input  # may be None → stdin

    try:
        import fpylll  # noqa: F401  (presence check)
    except ImportError:
        # Mirror SPEC's `if_available` mode: a missing oracle is a skip,
        # not a failure. CI installs fpylll before invoking the oracle,
        # so an ImportError here in CI means the install failed.
        if args.bench_checksum:
            print("ERROR: fpylll not installed", file=sys.stderr)
            return 1
        print("SKIP: fpylll not installed", file=sys.stderr)
        return 0

    if args.bench_checksum:
        return bench_checksum(source)

    return check(
        source,
        failure_dir=Path(args.failure_dir),
        profile=args.profile,
        seed=args.seed,
    )


if __name__ == "__main__":
    raise SystemExit(main())
