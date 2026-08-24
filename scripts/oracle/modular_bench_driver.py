#!/usr/bin/env python3
"""Persistent gmpy2/python-flint comparator service for HexModular.

The protocol is one JSON object per input line and one JSON object per output
line. Successful replies are ``{"ok": true, "result": ...}``; failures carry
``{"ok": false, "error": ...}`` and do not terminate the service.

Operations:

* ``overhead`` returns zero without arithmetic and measures steady-state JSON
  framing and dispatch.
* ``gmpy2_gcdext`` accepts positive integers ``m`` and ``a`` and returns
  ``[g, t]`` from ``g, s, t = gmpy2.gcdext(m, a)``.
* ``flint_crt`` accepts scalar ``entries = [[residue, modulus], ...]`` and
  returns ``[product, symmetric_value]``. Each Garner step uses
  ``flint.fmpz_mod_ctx`` inversion and `fmpz` arithmetic.
* ``flint_crt_vec`` accepts ``entries = [[[residue, ...], modulus], ...]`` and
  returns ``[product, [symmetric_value, ...]]``. The context and inverse are
  shared across coordinates, matching `CrtVec.push`'s architecture.

The process imports both optional packages before reading requests. Their
absence is reported only when the corresponding operation is selected, so the
driver itself remains diagnosable on minimal installations.
"""

from __future__ import annotations

import json
import sys
import traceback
from typing import Any

# Scientific ladders deliberately cross Python 3.11's decimal conversion
# safety threshold (100000-bit Fibonacci inputs have about 30000 digits).
# These integers come from the trusted local benchmark fixture, not a network
# service, so retaining their exact JSON representation is intentional.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

try:
    import gmpy2  # type: ignore[import-not-found]

    _gmpy2_error: str | None = None
except Exception as exc:  # pragma: no cover - environment-dependent
    gmpy2 = None  # type: ignore[assignment]
    _gmpy2_error = f"gmpy2 unavailable: {exc!r}"

try:
    import flint  # type: ignore[import-not-found]

    _flint_error: str | None = None
except Exception as exc:  # pragma: no cover - environment-dependent
    flint = None  # type: ignore[assignment]
    _flint_error = f"python-flint unavailable: {exc!r}"


def _require_gmpy2() -> None:
    if gmpy2 is None:
        raise RuntimeError(_gmpy2_error or "gmpy2 unavailable")


def _require_flint() -> None:
    if flint is None:
        raise RuntimeError(_flint_error or "python-flint unavailable")


def _sym(value: Any, modulus: Any) -> Any:
    return value - modulus if 2 * value > modulus else value


def _gmpy2_gcdext(request: dict[str, Any]) -> list[int]:
    _require_gmpy2()
    gcd, _s, t = gmpy2.gcdext(int(request["m"]), int(request["a"]))
    return [int(gcd), int(t)]


def _flint_crt(request: dict[str, Any]) -> list[int]:
    _require_flint()
    value = flint.fmpz(0)
    modulus = flint.fmpz(1)
    for raw_residue, raw_modulus in request["entries"]:
        next_modulus = int(raw_modulus)
        context = flint.fmpz_mod_ctx(next_modulus)
        inverse = context(modulus).inverse()
        delta = context(int(raw_residue) - value) * inverse
        value = value + modulus * int(delta)
        modulus = modulus * next_modulus
        value = _sym(value, modulus)
    return [int(modulus), int(value)]


def _flint_crt_vec(request: dict[str, Any]) -> list[Any]:
    _require_flint()
    entries = request["entries"]
    width = len(entries[0][0]) if entries else 0
    values = [flint.fmpz(0) for _ in range(width)]
    modulus = flint.fmpz(1)
    for raw_residues, raw_modulus in entries:
        next_modulus = int(raw_modulus)
        context = flint.fmpz_mod_ctx(next_modulus)
        inverse = context(modulus).inverse()
        product = modulus * next_modulus
        for index, raw_residue in enumerate(raw_residues):
            delta = context(int(raw_residue) - values[index]) * inverse
            values[index] = _sym(values[index] + modulus * int(delta), product)
        modulus = product
    return [int(modulus), [int(value) for value in values]]


def _dispatch(request: dict[str, Any]) -> Any:
    operation = request.get("op")
    if operation == "overhead":
        return 0
    if operation == "gmpy2_gcdext":
        return _gmpy2_gcdext(request)
    if operation == "flint_crt":
        return _flint_crt(request)
    if operation == "flint_crt_vec":
        return _flint_crt_vec(request)
    raise ValueError(f"unknown operation: {operation!r}")


def main() -> int:
    for line in sys.stdin:
        try:
            request = json.loads(line)
            if not isinstance(request, dict):
                raise TypeError("request must be a JSON object")
            reply = {"ok": True, "result": _dispatch(request)}
        except Exception as exc:  # pragma: no cover - defensive protocol path
            reply = {
                "ok": False,
                "error": f"{type(exc).__name__}: {exc}",
                "traceback": traceback.format_exc(limit=4),
            }
        print(json.dumps(reply, separators=(",", ":")), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
