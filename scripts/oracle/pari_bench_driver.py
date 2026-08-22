#!/usr/bin/env python3
"""Shared cypari2/PARI persistent-subprocess bench driver for Hex.

Loops on stdin, one JSON request per line; emits one JSON reply per
request on stdout. Instantiates one ``cypari2.Pari`` interpreter at
startup and reuses it for every subsequent call, so the only per-call
cost is JSON encode/decode and the PARI operation itself.

Per ``SPEC/benchmarking.md`` §"External comparators" §"Process call":
this driver is the persistent-subprocess shape required when per-call
overhead is non-negligible. A fixed benchmark starts a fresh Lean child
for each outer warmup or repeat. Within one child, ``warmupFirstIter``
starts this driver before timing, stores its stdin / stdout handles in
an ``IO.Ref`` (see ``Hex/BenchOracle/Pari.lean``), and the auto-tuned
inner-repeat batch reuses those handles. Thus one driver startup is
amortised across the measured calls in that child; it is not shared
across outer repeats.

## Framing

Identical to ``scripts/oracle/flint_bench_driver.py``: one request per
line on stdin, one JSON reply per line on stdout, flushed after every
reply. EOF on stdin terminates the driver. A malformed request is
*never* fatal — the driver writes an error frame and continues.

Request shape::

    {"family": "<family>", "op": "<op>", ...family-specific fields}

Reply shape on success::

    {"ok": true, "result": <family-specific value>}

Reply shape on failure::

    {"ok": false, "error": "<message>"}

## Rational encoding

Rational numbers cross the protocol as two-element integer arrays
``[num, den]`` with ``den > 0`` and ``gcd(num, den) = 1`` (both sides
send normalised values; PARI's ``numerator``/``denominator`` and Lean's
``Rat`` both maintain that normal form). Polynomials are coefficient
lists ascending in degree, trimmed of trailing zeros — the same
convention ``Hex.DensePoly`` uses.

## Comparator families and operations

### ``polmod`` (arithmetic in Q[x]/(m))

Request fields: ``modulus`` (integer coefficient list of the defining
polynomial, ascending), ``a``, ``b`` (rational coefficient lists as
``[num, den]`` pairs, reduced representatives of degree < deg m).

* ``mul`` — returns ``lift(Mod(a, m) * Mod(b, m))`` as a rational
  coefficient list. This is PARI's t_POLMOD multiplication, the unit
  surface paired with ``Hex.QAdjoin`` multiplication.
* ``inv`` — returns ``lift(Mod(a, m)^(-1))`` as a rational coefficient
  list (PARI's t_POLMOD extended-gcd inversion, paired with
  ``Hex.QAdjoin`` inversion). Fails with an error frame when ``a`` is
  not invertible modulo ``m``.
* ``overhead`` — returns ``0`` without touching PARI; the steady-state
  JSON framing / dispatch calibration used by headline reports.

### ``nf`` (number-field polynomial factorization)

Request fields: ``field`` (integer coefficient list of the defining
polynomial of the number field, ascending, variable ``y``), ``poly``
(rational coefficient list, ``[num, den]`` pairs, ascending, variable
``x``).

* ``factor_degrees`` — runs ``nffactor(nfinit(field), poly)`` and
  returns the factor degree/multiplicity multiset as a sorted list
  ``[[degree, multiplicity], ...]``. The degree multiset is the stable
  cross-implementation observable joined on by ``compare``: PARI's
  factor coefficients live in its own nf presentation, so raw
  coefficients are not comparable, but the degree/multiplicity
  multiset of a complete factorization is representation-free.

## Per-call overhead

The driver constructs the ``Pari`` interpreter once at startup;
per-call cost in the steady state is JSON decode + dispatch + PARI call
+ JSON encode. Measured per-call overhead (the ``polmod``/``overhead``
op) is recorded in each consuming library's headline report.

## Stdlib only, plus cypari2

Like the other ``scripts/oracle/*.py`` drivers, this script depends
only on the python stdlib and ``cypari2`` (the same binding the
HexNumberField / HexNumberFieldTower conformance oracles use). The
``cypari2`` import is local-to-startup so the first request does not
pay it.
"""
from __future__ import annotations

import json
import sys
import traceback
from typing import Any, Callable

try:
    import cypari2  # type: ignore[import-not-found]

    _pari = cypari2.Pari()
    # Headroom for nfinit/nffactor at the registered bench rungs.
    _pari.allocatemem(64 * 1024 * 1024, silent=True)
    _pari_import_error: str | None = None
except Exception as exc:  # pragma: no cover - defensive
    _pari = None  # type: ignore[assignment]
    _pari_import_error = f"cypari2 not available: {exc!r}"


def _require_pari():
    if _pari is None:
        raise RuntimeError(_pari_import_error or "cypari2 unavailable")
    return _pari


def _rat(pair: Any):
    """Build a PARI rational from a ``[num, den]`` pair."""
    if not isinstance(pair, list) or len(pair) != 2:
        raise ValueError(f"rational must be a [num, den] pair, got {pair!r}")
    pari = _require_pari()
    return pari(int(pair[0])) / pari(int(pair[1]))


def _int_poly(coeffs: list[int], variable: str):
    pari = _require_pari()
    return pari.Polrev([int(c) for c in coeffs], variable)


def _rat_poly(pairs: list[Any], variable: str):
    pari = _require_pari()
    return pari.Polrev([_rat(pair) for pair in pairs], variable)


def _rat_coeffs(poly) -> list[list[int]]:
    """Ascending ``[num, den]`` coefficient pairs of a PARI polynomial
    (or scalar), trimmed of trailing zeros by PARI's normal form."""
    pari = _require_pari()
    return [
        [int(pari.numerator(c)), int(pari.denominator(c))]
        for c in pari.Vecrev(poly)
    ]


# ---------------------------------------------------------------------
# `polmod` (arithmetic in Q[x]/(m))
# ---------------------------------------------------------------------


def _polmod_mul(req: dict[str, Any]) -> list[list[int]]:
    pari = _require_pari()
    modulus = _int_poly(req["modulus"], "x")
    a = pari.Mod(_rat_poly(req["a"], "x"), modulus)
    b = pari.Mod(_rat_poly(req["b"], "x"), modulus)
    return _rat_coeffs(pari.lift(a * b))


def _polmod_inv(req: dict[str, Any]) -> list[list[int]]:
    pari = _require_pari()
    modulus = _int_poly(req["modulus"], "x")
    a = pari.Mod(_rat_poly(req["a"], "x"), modulus)
    return _rat_coeffs(pari.lift(a ** (-1)))


def _polmod_overhead(_req: dict[str, Any]) -> int:
    return 0


_POLMOD_OPS: dict[str, Callable[[dict[str, Any]], Any]] = {
    "mul": _polmod_mul,
    "inv": _polmod_inv,
    "overhead": _polmod_overhead,
}


# ---------------------------------------------------------------------
# `nf` (number-field polynomial factorization)
# ---------------------------------------------------------------------


def _nf_factor_degrees(req: dict[str, Any]) -> list[list[int]]:
    pari = _require_pari()
    field = _int_poly(req["field"], "y")
    poly = _rat_poly(req["poly"], "x")
    factorization = pari.nffactor(pari.nfinit(field), poly)
    rows = int(pari.matsize(factorization)[0])
    pairs = sorted(
        (int(pari.poldegree(factorization[i, 0])), int(factorization[i, 1]))
        for i in range(rows)
    )
    return [[degree, multiplicity] for degree, multiplicity in pairs]


_NF_OPS: dict[str, Callable[[dict[str, Any]], Any]] = {
    "factor_degrees": _nf_factor_degrees,
}


# ---------------------------------------------------------------------
# Dispatch
# ---------------------------------------------------------------------


_FAMILIES: dict[str, dict[str, Callable[[dict[str, Any]], Any]]] = {
    "polmod": _POLMOD_OPS,
    "nf": _NF_OPS,
}


def _dispatch(req: dict[str, Any]) -> Any:
    family = req.get("family")
    op = req.get("op")
    if not isinstance(family, str):
        raise ValueError("request missing string 'family' field")
    if not isinstance(op, str):
        raise ValueError("request missing string 'op' field")
    ops = _FAMILIES.get(family)
    if ops is None:
        raise ValueError(f"unknown family {family!r}; known: {sorted(_FAMILIES)}")
    handler = ops.get(op)
    if handler is None:
        raise ValueError(
            f"unknown op {op!r} for family {family!r}; known: {sorted(ops)}"
        )
    return handler(req)


def _serve(stdin, stdout) -> None:
    for raw in stdin:
        line = raw.rstrip("\n")
        if not line:
            continue
        try:
            req = json.loads(line)
            if not isinstance(req, dict):
                raise ValueError(
                    f"top-level JSON must be an object, got {type(req).__name__}"
                )
            result = _dispatch(req)
            reply: dict[str, Any] = {"ok": True, "result": result}
        except Exception as exc:
            reply = {"ok": False, "error": f"{type(exc).__name__}: {exc}"}
        try:
            stdout.write(json.dumps(reply, separators=(",", ":")) + "\n")
            stdout.flush()
        except BrokenPipeError:  # pragma: no cover - consumer hung up
            return


# Smoke-test invocation::
#
#   printf '%s\n' \
#       '{"family":"polmod","op":"mul","modulus":[-2,0,0,0,1],"a":[[1,2],[0,1],[0,1],[1,1]],"b":[[0,1],[1,1]]}' \
#       '{"family":"polmod","op":"inv","modulus":[-2,0,1],"a":[[0,1],[1,1]]}' \
#       '{"family":"nf","op":"factor_degrees","field":[-2,0,1],"poly":[[-2,1],[0,1],[1,1]]}' \
#       '{"family":"polmod","op":"overhead"}' \
#       | python3 scripts/oracle/pari_bench_driver.py
#
# Expected replies (one per request, in order)::
#
#   {"ok":true,"result":[[2,1],[1,2]]}
#   {"ok":true,"result":[[0,1],[1,2]]}
#   {"ok":true,"result":[[1,1],[1,1]]}
#   {"ok":true,"result":0}


def main() -> int:
    _serve(sys.stdin, sys.stdout)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:  # pragma: no cover
        sys.exit(130)
    except BrokenPipeError:  # pragma: no cover
        sys.exit(0)
    except Exception:  # pragma: no cover - defensive
        traceback.print_exc()
        sys.exit(1)
