#!/usr/bin/env python3
"""python-flint oracle driver for `hex-gram-schmidt`.

Reads a JSONL stream produced by `lake exe hexgramschmidt_emit_fixtures`
(or the committed sample at
`conformance-fixtures/HexGramSchmidt/gram_schmidt.jsonl`) and re-runs
each integer Gram-Schmidt computation through python-flint's
`fmpq_mat`.  On mismatch, writes a JSON failure record under
`conformance-failures/` and exits non-zero so CI fails the job.

Operations cross-checked
------------------------

* `gram_det_vec` — the `n+1` leading principal Gram determinants
  ``d_0=1, d_1, ..., d_n`` where ``d_k = det(B[:k] · B[:k]^T)``.  The
  oracle computes each `d_k` as the exact integer determinant of the
  leading `k × k` Gram matrix via `fmpq_mat.det()`.
* `scaled_coeffs` — the integer matrix `S` whose lower-triangular
  entry `S[i][j]` for `j < i` equals ``d_{j+1} * mu[i][j]`` (where
  ``mu`` are the rational Gram-Schmidt coefficients of `B`), whose
  diagonal entry `S[i][i]` equals `d_{i+1}`, and whose above-diagonal
  entries are zero.  Equivalently, `S[i][j]` for `j < i` is the
  determinant of the `(j+1) x (j+1)` matrix obtained from the leading
  `(j+1) x (j+1)` Gram matrix by replacing its last column with the
  inner products `[B[0]*B[i], B[1]*B[i], ..., B[j]*B[i]]^T` — this is
  the closed form Lean's ``scaledCoeffMatrix`` evaluates.  The oracle
  builds exactly that matrix and asks `fmpq_mat.det()` for the
  answer.

Both checks assume the input basis is row-independent (every leading
prefix of `B` has full row rank).  The committed fixture set obeys
this; if a future case is singular, ``Hex.GramSchmidt.Int.scaledCoeffs``
zero-fills past the first singular pivot and the determinant formula
no longer matches — in that case the oracle will report a mismatch
and the case should either be made nonsingular or cross-checked with
a different convention.

Usage::

    # CI: pipe Lean's emission directly into the oracle.
    lake exe hexgramschmidt_emit_fixtures | \\
        python3 scripts/oracle/gs_flint.py

    # Local: replay against the committed sample.
    python3 scripts/oracle/gs_flint.py --check

    # Read from an explicit JSONL path.
    python3 scripts/oracle/gs_flint.py path/to/file.jsonl

`--check` is exactly equivalent to passing
``conformance-fixtures/HexGramSchmidt/gram_schmidt.jsonl``.
"""
from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = (
    REPO_ROOT / "conformance-fixtures" / "HexGramSchmidt" / "gram_schmidt.jsonl"
)
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402  (after sys.path insert)
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _basis(record: dict[str, Any]) -> list[list[int]]:
    if record["kind"] != "lattice":
        raise ValueError(f"expected lattice record, got {record['kind']}")
    return [list(row) for row in record["basis"]]


def _flint_version() -> str:
    try:
        import flint  # type: ignore[import-not-found]
        return getattr(flint, "__version__", "unknown")
    except Exception:
        return "unknown"


def _gram_matrix(basis: list[list[int]]):
    """Build the integer Gram matrix ``B B^T`` as an `fmpq_mat`."""
    from flint import fmpq_mat  # type: ignore[import-not-found]
    n = len(basis)
    m = len(basis[0]) if n else 0
    entries: list[list[int]] = [
        [sum(basis[i][k] * basis[j][k] for k in range(m)) for j in range(n)]
        for i in range(n)
    ]
    return fmpq_mat(entries) if n else fmpq_mat(0, 0)


def _det_int(mat) -> int:
    """Take the determinant of an `fmpq_mat`, assert it is an integer,
    and return the native Python `int`."""
    from flint import fmpq  # type: ignore[import-not-found]
    d: fmpq = mat.det()
    if d.q != 1:
        raise OracleMismatch(
            f"oracle bug: Gram-derived determinant {d} is not an integer"
        )
    return int(d.p)


def _leading_submatrix(mat, k: int):
    """Return the leading `k x k` submatrix of an `fmpq_mat`."""
    from flint import fmpq_mat  # type: ignore[import-not-found]
    if k == 0:
        return fmpq_mat(0, 0)
    return fmpq_mat([[mat[i, j] for j in range(k)] for i in range(k)])


def _gram_det_vec(gram, n: int) -> list[int]:
    """Leading principal Gram determinants `[d_0, d_1, ..., d_n]`."""
    out: list[int] = [1]
    for k in range(1, n + 1):
        out.append(_det_int(_leading_submatrix(gram, k)))
    return out


def _scaled_coeff(gram, i: int, j: int) -> int:
    """Determinant of the `(j+1) x (j+1)` matrix obtained from the
    leading `(j+1) x (j+1)` Gram by replacing its last column with the
    inner products `[gram[0,i], gram[1,i], ..., gram[j,i]]^T`."""
    from flint import fmpq_mat  # type: ignore[import-not-found]
    size = j + 1
    rows: list[list] = []
    for p in range(size):
        row = []
        for q in range(size):
            if q == j:
                row.append(gram[p, i])
            else:
                row.append(gram[p, q])
        rows.append(row)
    return _det_int(fmpq_mat(rows))


def _scaled_coeffs(gram, n: int) -> list[list[int]]:
    """Build the `n x n` integer scaled-coefficient matrix that mirrors
    ``Hex.GramSchmidt.Int.scaledCoeffs`` on a row-independent basis."""
    out: list[list[int]] = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1):
            out[i][j] = _scaled_coeff(gram, i, j)
    return out


def _check_gram_det_vec(
    *,
    case_id: str,
    lib: str,
    lattice_record: dict[str, Any],
    lean_value: list[int],
    failure_dir: Path,
    profile: str,
    seed: int,
    oracle_version: str,
) -> None:
    basis = _basis(lattice_record)
    n = len(basis)
    gram = _gram_matrix(basis)
    oracle_value = _gram_det_vec(gram, n)
    assert_equal(
        [int(v) for v in lean_value],
        oracle_value,
        library=lib,
        case_id=f"{case_id}:gram_det_vec",
        kind="gram_det_vec",
        input_record=lattice_record,
        oracle_name="python-flint",
        oracle_version=oracle_version,
        failure_dir=failure_dir,
        profile=profile,
        seed=seed,
    )


def _check_scaled_coeffs(
    *,
    case_id: str,
    lib: str,
    lattice_record: dict[str, Any],
    lean_value: list[list[int]],
    failure_dir: Path,
    profile: str,
    seed: int,
    oracle_version: str,
) -> None:
    basis = _basis(lattice_record)
    n = len(basis)
    gram = _gram_matrix(basis)
    oracle_value = _scaled_coeffs(gram, n)
    assert_equal(
        [[int(x) for x in row] for row in lean_value],
        oracle_value,
        library=lib,
        case_id=f"{case_id}:scaled_coeffs",
        kind="scaled_coeffs",
        input_record=lattice_record,
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
    for result in results:
        lib = result["lib"]
        case_id = result["case"]
        op = result["op"]
        lean_value = result["value"]
        lattice_record = cases.get((lib, case_id))
        if lattice_record is None:
            print(
                f"FAIL {lib}/{case_id} ({op}): missing lattice fixture",
                file=sys.stderr,
            )
            failures += 1
            continue
        try:
            if op == "gram_det_vec":
                _check_gram_det_vec(
                    case_id=case_id, lib=lib, lattice_record=lattice_record,
                    lean_value=lean_value,
                    failure_dir=failure_dir, profile=profile, seed=seed,
                    oracle_version=oracle_version,
                )
            elif op == "scaled_coeffs":
                _check_scaled_coeffs(
                    case_id=case_id, lib=lib, lattice_record=lattice_record,
                    lean_value=lean_value,
                    failure_dir=failure_dir, profile=profile, seed=seed,
                    oracle_version=oracle_version,
                )
            else:
                raise OracleMismatch(
                    f"{lib}/{case_id}: unsupported op {op!r} "
                    f"in gs_flint.py; extend the driver."
                )
            checked += 1
        except OracleMismatch as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({op}): {exc}", file=sys.stderr)
    print(
        f"gs_flint.py: checked {checked} case(s), {failures} failure(s)",
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
