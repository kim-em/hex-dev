#!/usr/bin/env python3
"""python-flint oracle driver for `hex-matrix`.

Reads a JSONL stream produced by `lake exe hexmatrix_emit_fixtures`
(or the committed sample at
`conformance-fixtures/HexMatrix/matrix.jsonl`) and re-runs each
operation through python-flint's `fmpz_mat` / `fmpq_mat`.  On
mismatch, writes a JSON failure record under `conformance-failures/`
and exits non-zero so CI fails the job.

Operations cross-checked
------------------------

* `det`       — Lean `Matrix.det` (combinatorial sum over `n!`
  permutations).  python-flint computes the integer determinant via
  `fmpz_mat.det()`.
* `bareiss`   — Lean `Matrix.bareiss` (fraction-free Bareiss).  The
  oracle expectation is identical to `det`: any disagreement here means
  Lean's two determinant implementations have drifted.
* `rank`      — Lean `Matrix.rref_rank` over `Q`.  python-flint's
  `fmpz_mat.rank()` agrees with the rational rank of the integer matrix.
* `rref`      — Lean's rational reduced row echelon form together with
  pivot columns and rank.  RREF is unique over `Q`, so the oracle can
  compare entrywise after building both sides as `fmpq_mat`.
* `nullspace` — Lean's rational basis of the right kernel.  Bases are
  not unique, so the oracle verifies basis-independent invariants:
  (a) the number of basis vectors equals `m - rank`,
  (b) each Lean basis vector is annihilated by `M` over `Q`,
  (c) the Lean basis vectors are linearly independent
      (rank of the basis matrix equals the nullity).

Usage::

    # CI: pipe Lean's emission directly into the oracle.
    lake exe hexmatrix_emit_fixtures | \\
        python3 scripts/oracle/matrix_flint.py

    # Local: replay against the committed sample.
    python3 scripts/oracle/matrix_flint.py --check

    # Read from an explicit JSONL path.
    python3 scripts/oracle/matrix_flint.py path/to/file.jsonl

`--check` is exactly equivalent to passing
``conformance-fixtures/HexMatrix/matrix.jsonl``.
"""
from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexMatrix" / "matrix.jsonl"
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402  (after sys.path insert)
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _flint_version() -> str:
    try:
        import flint  # type: ignore[import-not-found]
        return getattr(flint, "__version__", "unknown")
    except Exception:
        return "unknown"


def _rows(record: dict[str, Any]) -> list[list[int]]:
    if record["kind"] != "matrix":
        raise ValueError(f"expected matrix record, got {record['kind']}")
    return [list(row) for row in record["rows"]]


def _fmpz_mat(rows: list[list[int]]):
    from flint import fmpz_mat  # type: ignore[import-not-found]
    if not rows:
        return fmpz_mat(0, 0)
    return fmpz_mat([list(row) for row in rows])


def _fmpq_mat_from_int(rows: list[list[int]]):
    from flint import fmpq_mat  # type: ignore[import-not-found]
    return fmpq_mat(_fmpz_mat(rows))


def _fmpq_mat_from_pairs(rows: list[list[list[int]]]):
    """Build a `fmpq_mat` from rows of `[num, den]` pairs."""
    from flint import fmpq, fmpq_mat  # type: ignore[import-not-found]
    n = len(rows)
    m = len(rows[0]) if n else 0
    out = fmpq_mat(n, m)
    for i, row in enumerate(rows):
        for j, entry in enumerate(row):
            num, den = entry
            out[i, j] = fmpq(int(num), int(den))
    return out


def _check_det(
    *,
    case_id: str,
    lib: str,
    matrix_record: dict[str, Any],
    lean_value: int,
    failure_dir: Path,
    profile: str,
    seed: int,
    oracle_version: str,
) -> None:
    rows = _rows(matrix_record)
    if len(rows) != len(rows[0]):
        raise OracleMismatch(
            f"{lib}/{case_id}: det requires a square matrix, "
            f"got {len(rows)}x{len(rows[0])}"
        )
    oracle_value = int(_fmpz_mat(rows).det())
    assert_equal(
        lean_value,
        oracle_value,
        library=lib,
        case_id=f"{case_id}:det",
        kind="det",
        input_record=matrix_record,
        oracle_name="python-flint",
        oracle_version=oracle_version,
        failure_dir=failure_dir,
        profile=profile,
        seed=seed,
    )


def _check_bareiss(
    *,
    case_id: str,
    lib: str,
    matrix_record: dict[str, Any],
    lean_value: int,
    failure_dir: Path,
    profile: str,
    seed: int,
    oracle_version: str,
) -> None:
    # Bareiss must agree with the determinant.  Any divergence between
    # Lean's two implementations is an internal Lean bug; the oracle
    # treats them as the same expectation.
    _check_det(
        case_id=case_id,
        lib=lib,
        matrix_record=matrix_record,
        lean_value=lean_value,
        failure_dir=failure_dir,
        profile=profile,
        seed=seed,
        oracle_version=oracle_version,
    )


def _check_rank(
    *,
    case_id: str,
    lib: str,
    matrix_record: dict[str, Any],
    lean_value: int,
    failure_dir: Path,
    profile: str,
    seed: int,
    oracle_version: str,
) -> None:
    rows = _rows(matrix_record)
    oracle_value = int(_fmpz_mat(rows).rank())
    assert_equal(
        lean_value,
        oracle_value,
        library=lib,
        case_id=f"{case_id}:rank",
        kind="rank",
        input_record=matrix_record,
        oracle_name="python-flint",
        oracle_version=oracle_version,
        failure_dir=failure_dir,
        profile=profile,
        seed=seed,
    )


def _check_rref(
    *,
    case_id: str,
    lib: str,
    matrix_record: dict[str, Any],
    lean_value: dict[str, Any],
    failure_dir: Path,
    profile: str,
    seed: int,
    oracle_version: str,
) -> None:
    rows = _rows(matrix_record)
    oracle_q = _fmpq_mat_from_int(rows)
    oracle_rref, oracle_rank = oracle_q.rref()

    lean_rank = int(lean_value["rank"])
    lean_pivots = [int(c) for c in lean_value["pivotCols"]]
    lean_echelon = lean_value["echelon"]

    assert_equal(
        lean_rank,
        int(oracle_rank),
        library=lib,
        case_id=f"{case_id}:rref-rank",
        kind="rref-rank",
        input_record=matrix_record,
        oracle_name="python-flint",
        oracle_version=oracle_version,
        failure_dir=failure_dir,
        profile=profile,
        seed=seed,
    )

    # Pivot columns of the canonical RREF: read them off the echelon
    # form (first nonzero entry in each pivot row).
    oracle_pivots: list[int] = []
    n_rows = oracle_rref.nrows()
    n_cols = oracle_rref.ncols()
    for i in range(int(oracle_rank)):
        for j in range(n_cols):
            if oracle_rref[i, j] != 0:
                oracle_pivots.append(j)
                break
    assert_equal(
        lean_pivots,
        oracle_pivots,
        library=lib,
        case_id=f"{case_id}:rref-pivots",
        kind="rref-pivots",
        input_record=matrix_record,
        oracle_name="python-flint",
        oracle_version=oracle_version,
        failure_dir=failure_dir,
        profile=profile,
        seed=seed,
    )

    # Entrywise comparison after building both as fmpq_mat.
    lean_q = _fmpq_mat_from_pairs(lean_echelon)
    if lean_q != oracle_rref:
        # Surface a readable diff.
        from flint import fmpq  # type: ignore[import-not-found]
        lean_repr = [
            [(int(lean_q[i, j].p), int(lean_q[i, j].q))
             for j in range(n_cols)]
            for i in range(n_rows)
        ]
        oracle_repr = [
            [(int(oracle_rref[i, j].p), int(oracle_rref[i, j].q))
             for j in range(n_cols)]
            for i in range(n_rows)
        ]
        assert_equal(
            lean_repr,
            oracle_repr,
            library=lib,
            case_id=f"{case_id}:rref-echelon",
            kind="rref-echelon",
            input_record=matrix_record,
            oracle_name="python-flint",
            oracle_version=oracle_version,
            failure_dir=failure_dir,
            profile=profile,
            seed=seed,
        )


def _check_nullspace(
    *,
    case_id: str,
    lib: str,
    matrix_record: dict[str, Any],
    lean_value: list[list[list[int]]],
    failure_dir: Path,
    profile: str,
    seed: int,
    oracle_version: str,
) -> None:
    rows = _rows(matrix_record)
    n = len(rows)
    m = len(rows[0]) if n else 0
    oracle_z = _fmpz_mat(rows)
    oracle_rank = int(oracle_z.rank())
    expected_nullity = m - oracle_rank

    # (a) Basis cardinality matches m - rank.
    assert_equal(
        len(lean_value),
        expected_nullity,
        library=lib,
        case_id=f"{case_id}:nullspace-dim",
        kind="nullspace-dim",
        input_record=matrix_record,
        oracle_name="python-flint",
        oracle_version=oracle_version,
        failure_dir=failure_dir,
        profile=profile,
        seed=seed,
    )

    if expected_nullity == 0:
        return

    from flint import fmpq, fmpq_mat  # type: ignore[import-not-found]

    M_q = _fmpq_mat_from_int(rows)

    # (b) Each Lean basis vector is annihilated by M over Q.
    for k, vec in enumerate(lean_value):
        if len(vec) != m:
            raise OracleMismatch(
                f"{lib}/{case_id}: nullspace basis vector {k} has "
                f"length {len(vec)}, expected {m}"
            )
        v = fmpq_mat(m, 1)
        for j, (num, den) in enumerate(vec):
            v[j, 0] = fmpq(int(num), int(den))
        Mv = M_q * v
        zero_check = all(Mv[i, 0] == 0 for i in range(n))
        if not zero_check:
            assert_equal(
                [(int(Mv[i, 0].p), int(Mv[i, 0].q)) for i in range(n)],
                [(0, 1)] * n,
                library=lib,
                case_id=f"{case_id}:nullspace-annihilation/{k}",
                kind="nullspace-annihilation",
                input_record=matrix_record,
                oracle_name="python-flint",
                oracle_version=oracle_version,
                failure_dir=failure_dir,
                profile=profile,
                seed=seed,
            )

    # (c) The Lean basis is linearly independent (rank = nullity).
    # Stack the basis vectors as rows of an `expected_nullity × m`
    # matrix and check its rank.
    basis_q = fmpq_mat(expected_nullity, m)
    for i, vec in enumerate(lean_value):
        for j, (num, den) in enumerate(vec):
            basis_q[i, j] = fmpq(int(num), int(den))
    basis_z, _denom = basis_q.numer_denom()
    basis_rank = int(basis_z.rank())
    assert_equal(
        basis_rank,
        expected_nullity,
        library=lib,
        case_id=f"{case_id}:nullspace-independence",
        kind="nullspace-independence",
        input_record=matrix_record,
        oracle_name="python-flint",
        oracle_version=oracle_version,
        failure_dir=failure_dir,
        profile=profile,
        seed=seed,
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
    checked = 0
    handlers = {
        "det":       _check_det,
        "bareiss":   _check_bareiss,
        "rank":      _check_rank,
        "rref":      _check_rref,
        "nullspace": _check_nullspace,
    }
    for result in results:
        lib = result["lib"]
        case_id = result["case"]
        op = result["op"]
        lean_value = result["value"]
        matrix_record = cases.get((lib, case_id))
        if matrix_record is None:
            print(
                f"FAIL {lib}/{case_id} ({op}): missing matrix fixture",
                file=sys.stderr,
            )
            failures += 1
            continue
        handler = handlers.get(op)
        if handler is None:
            raise OracleMismatch(
                f"{lib}/{case_id}: unsupported op {op!r} "
                f"in matrix_flint.py; extend the driver."
            )
        try:
            handler(
                case_id=case_id, lib=lib, matrix_record=matrix_record,
                lean_value=lean_value,
                failure_dir=failure_dir, profile=profile, seed=seed,
                oracle_version=oracle_version,
            )
            checked += 1
        except OracleMismatch as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({op}): {exc}", file=sys.stderr)
    print(
        f"matrix_flint.py: checked {checked} case(s), {failures} failure(s)",
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
        import flint  # noqa: F401  (presence check)
    except ImportError:
        # Mirror SPEC's `if_available` mode: a missing oracle is a
        # skip, not a failure.  CI installs python-flint before this
        # script runs.
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
