#!/usr/bin/env python3
"""Rank oracle driver for ``HexRank`` across its coefficient carriers.

Reads the JSONL stream produced by ``lake exe hexrank_emit_fixtures`` (or the
committed sample at ``conformance-fixtures/HexRank/rank.jsonl``) and
recomputes every operation with an independent implementation:

* ``Int``, ``Rat`` and ``ZMod64 p`` fixtures (``matrix``, ``ratmatrix``,
  ``modmatrix`` records) through python-flint's ``fmpz_mat``, ``fmpq_mat``
  and ``nmod_mat``;
* ``DensePoly`` fixtures (``polymatrix`` records over ``QQ[x]`` and
  ``GF(p)[x]``) and ``MvPoly`` fixtures (``mvpolymatrix`` records over
  ``ZZ[x0, ...]``) through SymPy's ``DomainMatrix`` over the exact polynomial
  domain, converted with ``to_field()`` where a rank or reduced form is
  wanted. The ordinary ``sympy.Matrix.rank()`` is never used: it takes no
  coefficient domain, so residues would be added in characteristic zero.

Operations cross-checked
------------------------

* ``rank``       — compared as integers.
* ``colProfile`` — the pivot columns of the oracle's own reduced row echelon
  form over the fraction field, compared as lists.
* ``rowProfile`` — the rows ``i`` with ``rank(A[0..i]) = rank(A[0..i-1]) + 1``,
  recomputed with the oracle's rank on row prefixes, compared as sorted lists.
* ``denom``      — the determinant of the oracle's submatrix at the
  Lean-reported ``rows × cols`` (this reuses Lean's index selection, which is
  permitted canonicalisation: the value compared is the oracle's
  determinant).
* ``cert``       — the oracle re-verifies the three certificate identities
  ``denom ≠ 0``, ``B * adj = denom • 1`` and
  ``denom • A = A[·, cols] * (adj * A[rows, ·])`` with its own arithmetic and
  re-checks the certified rank against its own rank. A certificate that
  passes Lean's ``checkRank`` but fails here is a checker bug.

Usage::

    lake exe hexrank_emit_fixtures | python3 scripts/oracle/rank_carriers.py
    python3 scripts/oracle/rank_carriers.py --check
    python3 scripts/oracle/rank_carriers.py path/to/file.jsonl
"""
from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Any


# SymPy's flint-backed ground types cannot yet convert `GF(p)` residues into
# the fraction field `GF(p)(x)` that `DomainMatrix.to_field` builds, so the
# polynomial carriers pin SymPy to its pure-Python ground types. python-flint
# itself is still used directly for the scalar carriers.
os.environ.setdefault("SYMPY_GROUND_TYPES", "python")

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexRank" / "rank.jsonl"
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _oracle_version() -> str:
    parts = []
    try:
        import flint

        parts.append(f"python-flint {flint.__version__}")
    except ImportError:  # pragma: no cover - reported by preflight
        pass
    try:
        import sympy

        parts.append(f"sympy {sympy.__version__}")
    except ImportError:  # pragma: no cover
        pass
    return "; ".join(parts)


# ---------------------------------------------------------------------------
# Carrier abstraction.
#
# Every carrier exposes the same small interface over a SymPy
# ``DomainMatrix``: build the matrix from the fixture record, decode an
# emitted entry, and compare. python-flint is used as the primary rank /
# determinant engine where it applies (``Int``, ``Rat``, ``ZMod64 p``) so the
# two libraries cross-check each other on those carriers.
# ---------------------------------------------------------------------------


class Carrier:
    """A coefficient domain with fixture decoding and rank primitives."""

    def __init__(self, record: dict[str, Any]) -> None:
        from sympy.polys.matrices import DomainMatrix

        self.record = record
        self.domain, entries, self.rows, self.cols = self._decode(record)
        if self.rows == 0 or self.cols == 0:
            self.A = DomainMatrix.zeros((self.rows, self.cols), self.domain)
        else:
            self.A = DomainMatrix(entries, (self.rows, self.cols), self.domain)

    # -- decoding ----------------------------------------------------------

    def _decode(self, record: dict[str, Any]):  # type: ignore[no-untyped-def]
        raise NotImplementedError

    def entry(self, value: Any) -> Any:
        """Decode one emitted result entry into a domain element."""
        raise NotImplementedError

    # -- primitives --------------------------------------------------------

    def _pivots(self, M) -> list[int]:  # type: ignore[no-untyped-def]
        """Pivot columns of the reduced row echelon form over the fraction
        field, computed by SymPy's fraction-free `rref_den` over the ring
        itself (the pivot structure is the same, and no conversion into the
        fraction field is needed)."""
        if M.shape[0] == 0 or M.shape[1] == 0:
            return []
        _rref, _den, pivots = M.rref_den()
        return [int(p) for p in pivots]

    def rank(self, M=None) -> int:  # type: ignore[no-untyped-def]
        M = self.A if M is None else M
        return len(self._pivots(M))

    def det(self, M) -> Any:  # type: ignore[no-untyped-def]
        if M.shape[0] == 0:
            return self.domain.one
        return M.det()

    def pivot_columns(self) -> list[int]:
        return self._pivots(self.A)

    def row_profile(self) -> list[int]:
        out = []
        previous = 0
        for i in range(self.rows):
            prefix = self.A.extract(list(range(i + 1)), list(range(self.cols)))
            r = self.rank(prefix)
            if r == previous + 1:
                out.append(i)
            previous = r
        return out

    def submatrix(self, rows: list[int], cols: list[int]):  # type: ignore[no-untyped-def]
        from sympy.polys.matrices import DomainMatrix

        if len(rows) == 0:
            return DomainMatrix.zeros((0, 0), self.domain)
        return self.A.extract(rows, cols)

    def matrix_of(self, entries: list[list[Any]], shape: tuple[int, int]):  # type: ignore[no-untyped-def]
        from sympy.polys.matrices import DomainMatrix

        if shape[0] == 0 or shape[1] == 0:
            return DomainMatrix.zeros(shape, self.domain)
        decoded = [[self.entry(v) for v in row] for row in entries]
        return DomainMatrix(decoded, shape, self.domain)


class IntCarrier(Carrier):
    def _decode(self, record):  # type: ignore[no-untyped-def]
        from sympy import ZZ

        rows = [[ZZ(int(v)) for v in row] for row in record["rows"]]
        n = len(rows)
        m = len(rows[0]) if n else 0
        return ZZ, rows, n, m

    def entry(self, value):  # type: ignore[no-untyped-def]
        from sympy import ZZ

        return ZZ(int(value))

    def rank(self, M=None) -> int:  # type: ignore[no-untyped-def]
        from flint import fmpz_mat

        M = self.A if M is None else M
        if M.shape[0] == 0 or M.shape[1] == 0:
            return 0
        flint_rank = int(fmpz_mat([[int(x) for x in row] for row in M.to_list()]).rank())
        sympy_rank = super().rank(M)
        if flint_rank != sympy_rank:  # pragma: no cover - oracle self-check
            raise AssertionError(f"flint rank {flint_rank} != sympy rank {sympy_rank}")
        return flint_rank

    def det(self, M):  # type: ignore[no-untyped-def]
        from flint import fmpz_mat
        from sympy import ZZ

        if M.shape[0] == 0:
            return ZZ.one
        return ZZ(int(fmpz_mat([[int(x) for x in row] for row in M.to_list()]).det()))


class RatCarrier(Carrier):
    """``Rat`` matrices: ``ratmatrix`` records, rows of ``[num, den]`` pairs."""

    def _decode(self, record):  # type: ignore[no-untyped-def]
        from sympy import QQ

        rows = [[QQ(int(num), int(den)) for num, den in row] for row in record["rows"]]
        n = len(rows)
        m = len(rows[0]) if n else 0
        return QQ, rows, n, m

    def entry(self, value):  # type: ignore[no-untyped-def]
        from sympy import QQ

        return QQ(int(value["num"]), int(value["den"]))

    def rank(self, M=None) -> int:  # type: ignore[no-untyped-def]
        from flint import fmpq, fmpq_mat

        M = self.A if M is None else M
        if M.shape[0] == 0 or M.shape[1] == 0:
            return 0
        rows = [[fmpq(int(x.numerator), int(x.denominator)) for x in row] for row in M.to_list()]
        flint_rank = int(fmpq_mat(rows).rank())
        sympy_rank = super().rank(M)
        if flint_rank != sympy_rank:  # pragma: no cover
            raise AssertionError(f"flint rank {flint_rank} != sympy rank {sympy_rank}")
        return flint_rank


class ZModCarrier(Carrier):
    """``ZMod64 p`` matrices: ``modmatrix`` records with their modulus."""

    def _decode(self, record):  # type: ignore[no-untyped-def]
        from sympy import GF

        p = int(record["modulus"])
        K = GF(p)
        rows = [[K(int(v)) for v in row] for row in record["rows"]]
        n = len(rows)
        m = len(rows[0]) if n else 0
        self.p = p
        return K, rows, n, m

    def entry(self, value):  # type: ignore[no-untyped-def]
        return self.domain(int(value))

    def rank(self, M=None) -> int:  # type: ignore[no-untyped-def]
        from flint import nmod_mat

        M = self.A if M is None else M
        if M.shape[0] == 0 or M.shape[1] == 0:
            return 0
        rows = [[int(x) % self.p for x in row] for row in M.to_list()]
        flint_rank = int(nmod_mat(rows, self.p).rank())
        sympy_rank = super().rank(M)
        if flint_rank != sympy_rank:  # pragma: no cover
            raise AssertionError(f"flint rank {flint_rank} != sympy rank {sympy_rank}")
        return flint_rank


class PolyCarrier(Carrier):
    """``DensePoly`` over ``QQ`` or ``GF(p)``: ``polymatrix`` records."""

    def _decode(self, record):  # type: ignore[no-untyped-def]
        import sympy as sp
        from sympy import GF, QQ

        x = sp.Symbol("x")
        field = record["field"]
        if "p" in field:
            self.p = int(field["p"])
            R = GF(self.p)[x]
        else:
            self.p = None
            R = QQ[x]
        self.x = x
        self.R = R
        n, m = int(record["rows"]), int(record["cols"])
        rows = [[self._poly(v) for v in row] for row in record["entries"]] if n and m else []
        return R, rows, n, m

    def _poly(self, coeffs: Any):  # type: ignore[no-untyped-def]
        import sympy as sp

        x = self.x
        if self.p is not None:
            expr = sum((sp.Integer(int(c)) * x**i for i, c in enumerate(coeffs)), sp.Integer(0))
        else:
            expr = sum(
                (sp.Rational(int(num), int(den)) * x**i
                 for i, (num, den) in enumerate(zip(coeffs["num"], coeffs["den"]))),
                sp.Integer(0),
            )
        return self.R.from_sympy(sp.expand(expr))

    def entry(self, value):  # type: ignore[no-untyped-def]
        return self._poly(value)


class MvPolyCarrier(Carrier):
    """``MvPoly k Int`` : ``mvpolymatrix`` records over ``ZZ[x0, ..., x_{k-1}]``."""

    def _decode(self, record):  # type: ignore[no-untyped-def]
        import sympy as sp
        from sympy import ZZ

        k = int(record["arity"])
        self.xs = sp.symbols(f"x0:{k}") if k else ()
        R = ZZ[self.xs] if k else ZZ
        self.R = R
        n, m = int(record["rows"]), int(record["cols"])
        rows = [[self._poly(v) for v in row] for row in record["entries"]] if n and m else []
        return R, rows, n, m

    def _poly(self, terms: Any):  # type: ignore[no-untyped-def]
        import sympy as sp

        expr = sp.Integer(0)
        for exponents, coeff in terms:
            mono = sp.Integer(int(coeff))
            for x, e in zip(self.xs, exponents):
                mono *= x ** int(e)
            expr += mono
        return self.R.from_sympy(sp.expand(expr))

    def entry(self, value):  # type: ignore[no-untyped-def]
        return self._poly(value)


CARRIERS = {
    "matrix": IntCarrier,
    "ratmatrix": RatCarrier,
    "modmatrix": ZModCarrier,
    "polymatrix": PolyCarrier,
    "mvpolymatrix": MvPolyCarrier,
}


# ---------------------------------------------------------------------------
# Per-op checks.
# ---------------------------------------------------------------------------


def _check(lean: Any, oracle: Any, *, case_id: str, lib: str, op: str, record: dict[str, Any],
           failure_dir: Path, profile: str, seed: int) -> None:
    assert_equal(
        lean,
        oracle,
        library=lib,
        case_id=f"{case_id}:{op}",
        kind=op,
        input_record=record,
        oracle_name="rank-carriers",
        oracle_version=_oracle_version(),
        failure_dir=failure_dir,
        profile=profile,
        seed=seed,
    )


def _check_rank(carrier: Carrier, lean: Any, **ctx: Any) -> None:
    _check(int(lean), carrier.rank(), op="rank", **ctx)


def _check_col_profile(carrier: Carrier, lean: Any, **ctx: Any) -> None:
    _check([int(v) for v in lean], carrier.pivot_columns(), op="colProfile", **ctx)


def _check_row_profile(carrier: Carrier, lean: Any, **ctx: Any) -> None:
    _check(sorted(int(v) for v in lean), carrier.row_profile(), op="rowProfile", **ctx)


def _check_denom(carrier: Carrier, lean: Any, **ctx: Any) -> None:
    rows = [int(v) for v in lean["rows"]]
    cols = [int(v) for v in lean["cols"]]
    oracle = carrier.det(carrier.submatrix(rows, cols))
    _check(str(carrier.entry(lean["denom"])), str(oracle), op="denom", **ctx)


def _check_cert(carrier: Carrier, lean: Any, **ctx: Any) -> None:
    from sympy.polys.matrices import DomainMatrix

    r = int(lean["rank"])
    rows = [int(v) for v in lean["rows"]]
    cols = [int(v) for v in lean["cols"]]
    d = carrier.entry(lean["denom"])
    adj = carrier.matrix_of(lean["adj"], (r, r))
    dom = carrier.domain
    verdict: dict[str, Any] = {"rank": r}
    verdict["denom_nonzero"] = bool(d != dom.zero)
    B = carrier.submatrix(rows, cols)
    if r == 0:
        verdict["block_identity"] = True
    else:
        eye = DomainMatrix.eye(r, dom)
        verdict["block_identity"] = bool((B * adj).to_dense() == (eye * d).to_dense())
    if carrier.rows == 0 or carrier.cols == 0:
        verdict["column_identity"] = True
    else:
        C = carrier.A.extract(list(range(carrier.rows)), cols) if r else \
            DomainMatrix.zeros((carrier.rows, 0), dom)
        P = carrier.A.extract(rows, list(range(carrier.cols))) if r else \
            DomainMatrix.zeros((0, carrier.cols), dom)
        lhs = (carrier.A * d).to_dense()
        rhs = (C * (adj * P)).to_dense()
        verdict["column_identity"] = bool(lhs == rhs)
    verdict["rank_agrees"] = carrier.rank() == r
    expected = {"rank": r, "denom_nonzero": True, "block_identity": True,
                "column_identity": True, "rank_agrees": True}
    _check(verdict, expected, op="cert", **ctx)


HANDLERS = {
    "rank": _check_rank,
    "colProfile": _check_col_profile,
    "rowProfile": _check_row_profile,
    "denom": _check_denom,
    "cert": _check_cert,
}


def check(source: str | Path | None, failure_dir: Path, profile: str, seed: int) -> int:
    try:
        import flint  # noqa: F401
        import sympy  # noqa: F401
    except ImportError as exc:
        print(f"SKIP: {exc.name} not installed", file=sys.stderr)
        return 0
    cases, results = split_fixtures_results(read_fixtures(source))
    failures = 0
    if not cases:
        print("FAIL HexRank: empty fixture stream", file=sys.stderr)
        return 1
    seen: dict[tuple[str, str], list[str]] = {key: [] for key in cases}
    carriers: dict[tuple[str, str], Carrier] = {}
    for result in results:
        key = (result["lib"], result["case"])
        record = cases[key]
        if key not in carriers:
            carriers[key] = CARRIERS[record["kind"]](record)
        carrier = carriers[key]
        seen[key].append(result["op"])
        handler = HANDLERS.get(result["op"])
        if handler is None:
            print(f"FAIL {key[0]}/{key[1]}: unknown op {result['op']}", file=sys.stderr)
            failures += 1
            continue
        try:
            handler(carrier, result["value"], case_id=key[1], lib=key[0], record=record,
                    failure_dir=failure_dir, profile=profile, seed=seed)
        except OracleMismatch as exc:
            print(f"FAIL {key[0]}/{key[1]} ({result['op']}): {exc}", file=sys.stderr)
            failures += 1
    # every case carries each operation exactly once, so a missing result
    # record (an emitter regression) fails rather than silently passing
    for key, ops in seen.items():
        if sorted(ops) != sorted(HANDLERS):
            print(f"FAIL {key[0]}/{key[1]}: expected the ops {sorted(HANDLERS)} once each, "
                  f"got {sorted(ops)}", file=sys.stderr)
            failures += 1
    return 1 if failures else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("input", nargs="?", help="JSONL path (default: stdin)")
    parser.add_argument("--check", action="store_true",
                        help=f"replay the committed sample {DEFAULT_FIXTURE}")
    parser.add_argument("--failure-dir", default=str(DEFAULT_FAILURE_DIR))
    parser.add_argument("--profile", default=os.environ.get("HEX_ORACLE_PROFILE", "ci"))
    parser.add_argument("--seed", type=int, default=int(os.environ.get("HEX_ORACLE_SEED", "0")))
    args = parser.parse_args()
    source: str | Path | None
    if args.check:
        source = DEFAULT_FIXTURE
    else:
        source = args.input
    return check(source, Path(args.failure_dir), args.profile, args.seed)


if __name__ == "__main__":
    sys.exit(main())
