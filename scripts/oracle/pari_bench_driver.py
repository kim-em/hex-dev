#!/usr/bin/env python3
"""Persistent cypari2/PARI benchmark service for Hex.

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
"""
from __future__ import annotations

import json
import sys
import traceback
from typing import Any

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
