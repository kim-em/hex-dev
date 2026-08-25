#!/usr/bin/env python3
"""Persistent PARI/SymPy benchmark service for Hex.

The line protocol matches ``flint_bench_driver.py``.  Version one exposes the
same-algorithm comparator required by hex-char-poly:

``fmpz_mat/charpoly_berkowitz``
    Accept square integer ``rows`` and return PARI ``charpoly(..., flag=3)``
    as a complete ascending coefficient list.

``fmpz_mat/minpoly``
    Accept square integer ``rows`` and return PARI's matrix minimal
    polynomial as an ascending coefficient list.

``fmpz_mat/hnf``
    Accept rectangular integer row generators and return the canonical row
    HNF. PARI's column convention is converted with ``J_m A^T`` and
    ``J_r H'^T J_m``, padding the missing zero rows.

``fmpz_mat/overhead``
    Return ``0`` without constructing a matrix, calibrating protocol cost.

``fmpz_mat/snf``
    Accept square integer ``rows`` and return PARI ``matsnf`` in ascending
    divisibility order with nonnegative representatives.

``polymatrix/pari_snf``
    Accept a square matrix over ``QQ[x]`` in the Hex polynomial-matrix fixture
    schema and return the monic invariant factors from PARI ``matsnf``.

``polymatrix/sympy_snf``
    Accept a rectangular matrix over ``QQ[x]`` in the same schema and return
    SymPy ``smith_normal_form`` invariant factors.

``polymatrix/overhead``
    Return zero without constructing a matrix; this calibrates the persistent
    JSON framing shared by the two polynomial-matrix comparators.
"""
from __future__ import annotations

import json
import sys
import traceback
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(REPO_ROOT))

try:
    import cypari2  # type: ignore[import-not-found]

    _pari = cypari2.Pari()
    _import_error: str | None = None
except Exception as exc:  # pragma: no cover - dependency/runtime guard
    _pari = None
    _import_error = f"cypari2/PARI not available: {exc!r}"


def _require_pari():
    if _pari is None:
        raise RuntimeError(_import_error or "cypari2/PARI unavailable")
    return _pari


def _charpoly_berkowitz(request: dict[str, Any]) -> list[int]:
    pari = _require_pari()
    rows = [[int(value) for value in row] for row in request["rows"]]
    n = len(rows)
    if any(len(row) != n for row in rows):
        raise ValueError("charpoly requires a square matrix")
    matrix = pari.matrix(n, n, [value for row in rows for value in row])
    polynomial = matrix.charpoly("x", 3)
    coefficients = [int(value) for value in polynomial.list()]
    if len(coefficients) != n + 1:
        raise RuntimeError(
            f"PARI charpoly returned {len(coefficients)} coefficients for n={n}"
        )
    return coefficients


def _minpoly(request: dict[str, Any]) -> list[int]:
    pari = _require_pari()
    rows = [[int(value) for value in row] for row in request["rows"]]
    n = len(rows)
    if any(len(row) != n for row in rows):
        raise ValueError("minpoly requires a square matrix")
    matrix = pari.matrix(n, n, [value for row in rows for value in row])
    return [int(value) for value in matrix.minpoly("x").list()]


def _hnf(request: dict[str, Any]) -> list[list[int]]:
    pari = _require_pari()
    rows = [[int(value) for value in row] for row in request["rows"]]
    n = len(rows)
    m = len(rows[0]) if n else 0
    if any(len(row) != m for row in rows):
        raise ValueError("hnf requires rectangular rows")
    if n == 0 or m == 0:
        return [[0] * m for _ in range(n)]

    # PARI computes a column HNF. Reverse the ambient coordinates before the
    # transpose, then undo both reversals after its compact rank-r output.
    column_input = [
        [rows[j][i] for j in range(n)]
        for i in reversed(range(m))
    ]
    matrix = pari.matrix(
        m, n, [value for row in column_input for value in row]
    )
    compact = pari.mathnf(matrix)
    rank = int(compact.ncols())
    compact_rows = [
        [int(compact[i, j]) for j in range(rank)]
        for i in range(m)
    ]
    form = [
        [compact_rows[m - 1 - j][rank - 1 - i] for j in range(m)]
        for i in range(rank)
    ]
    return form + [[0] * m for _ in range(n - rank)]


def _snf(request: dict[str, Any]) -> list[int]:
    pari = _require_pari()
    rows = [[int(value) for value in row] for row in request["rows"]]
    n = len(rows)
    if any(len(row) != n for row in rows):
        raise ValueError("snf benchmark requires a square matrix")
    matrix = pari.matrix(n, n, [value for row in rows for value in row])
    # PARI orders its elementary divisors in the reverse convention:
    # d_n | ... | d_1. Hex exposes d_1 | ... | d_n.
    return [abs(int(value)) for value in reversed(matrix.matsnf().list())]


def _rat_coefficients(entry: dict[str, list[int]]) -> list[tuple[int, int]]:
    numbers = [int(value) for value in entry["num"]]
    denominators = [int(value) for value in entry["den"]]
    if len(numbers) != len(denominators):
        raise ValueError("rational polynomial numerator/denominator length mismatch")
    if any(value == 0 for value in denominators):
        raise ValueError("rational polynomial coefficient has zero denominator")
    return list(zip(numbers, denominators, strict=True))


def _pari_polynomial(entry: Any, field: dict[str, Any]):
    pari = _require_pari()
    if "p" in field:
        modulus = int(field["p"])
        coefficients = [pari.Mod(int(value), modulus) for value in entry]
    else:
        coefficients = [
            pari(number) / denominator
            for number, denominator in _rat_coefficients(entry)
        ]
    return pari.Polrev(coefficients)


def _rat_value(number: Any) -> tuple[int, int]:
    pari = _require_pari()
    return int(pari.numerator(number)), int(pari.denominator(number))


def _pari_poly_value(polynomial: Any, field: dict[str, Any]) -> Any:
    pari = _require_pari()
    if polynomial == 0:
        return [] if "p" in field else {"num": [], "den": []}
    leading = pari.pollead(polynomial)
    monic = polynomial / leading
    coefficients = list(pari.Vecrev(monic))
    if "p" in field:
        modulus = int(field["p"])
        return [int(pari.lift(value)) % modulus for value in coefficients]
    values = [_rat_value(value) for value in coefficients]
    while values and values[-1][0] == 0:
        values.pop()
    return {
        "num": [number for number, _ in values],
        "den": [denominator for _, denominator in values],
    }


def _pari_snf(request: dict[str, Any]) -> list[dict[str, list[int]]]:
    pari = _require_pari()
    record = request["matrix"]
    rows, cols = int(record["rows"]), int(record["cols"])
    if rows != cols:
        raise ValueError("PARI polynomial matsnf comparator requires a square matrix")
    entries = record["entries"]
    field = record["field"]
    if len(entries) != rows or any(len(row) != cols for row in entries):
        raise ValueError("polynomial matrix dimensions do not match its entries")
    matrix = pari.matrix(
        rows,
        cols,
        [_pari_polynomial(entry, field) for row in entries for entry in row],
    )
    # PARI orders the diagonal from largest to smallest divisibility. Hex and
    # SymPy use the opposite order, so reverse it after dropping the zero tail.
    diagonal = [value for value in list(matrix.matsnf()) if value != 0]
    return [_pari_poly_value(value, field) for value in reversed(diagonal)]


def _sympy_snf(request: dict[str, Any]) -> list[dict[str, list[int]]]:
    # Reuse the conformance oracle's independently implemented canonicalization
    # so benchmark and oracle paths cannot drift in their wire convention.
    from scripts.oracle.polymatrix import _smith

    return _smith(request["matrix"])


def _dispatch(request: dict[str, Any]) -> Any:
    family = request.get("family")
    operation = request.get("op")
    if family == "fmpz_mat" and operation == "charpoly_berkowitz":
        return _charpoly_berkowitz(request)
    if family == "fmpz_mat" and operation == "minpoly":
        return _minpoly(request)
    if family == "fmpz_mat" and operation == "hnf":
        return _hnf(request)
    if family == "fmpz_mat" and operation == "overhead":
        return 0
    if family == "fmpz_mat" and operation == "snf":
        return _snf(request)
    if family == "polymatrix" and operation == "pari_snf":
        return _pari_snf(request)
    if family == "polymatrix" and operation == "sympy_snf":
        return _sympy_snf(request)
    if family == "polymatrix" and operation == "overhead":
        return 0
    raise ValueError(f"unknown PARI benchmark operation {family!r}/{operation!r}")


def main() -> int:
    for line in sys.stdin:
        try:
            request = json.loads(line)
            result = _dispatch(request)
            reply = {"ok": True, "result": result}
        except Exception as exc:  # keep the persistent service alive
            reply = {
                "ok": False,
                "error": f"{type(exc).__name__}: {exc}",
                "traceback": traceback.format_exc(limit=3),
            }
        print(json.dumps(reply, separators=(",", ":")), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
