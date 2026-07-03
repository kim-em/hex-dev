#!/usr/bin/env python3
"""Shared warm-service loop for the cross-system factorization benchmark suite.

Every measured system runs as a persistent process speaking the suite line
protocol (identical to the verified Isabelle comparator
``scripts/oracle/bz-isabelle/Main.hs`` and the hex ``hexbz_factor_service``):

* request (one line): ``{"coeffs":[c0,c1,...]}`` -- integer coefficients,
  **ascending** degree order.
* reply (one line): ``{"ok":true,"result":{"scalar":s,"factors":[{"coeffs":[...],
  "multiplicity":m},...]}}`` on success, ``{"ok":true,"result":null}`` when the
  system declines, or ``{"ok":false,"error":"..."}`` on a malformed request or
  an internal failure.

A driver supplies ``factor_fn(coeffs: list[int])`` returning either
``(scalar: int, factors: list[tuple[list[int], int]])`` (each factor as an
ascending coefficient list paired with its positive multiplicity), or ``None``
to decline. ``serve`` handles line framing, JSON, error capture and flushing.
"""

from __future__ import annotations

import json
import sys
from typing import Callable, Optional, Sequence, Tuple

FactorResult = Optional[Tuple[int, Sequence[Tuple[Sequence[int], int]]]]
FactorFn = Callable[[list], FactorResult]


def _reply(result: FactorResult) -> str:
    if result is None:
        payload = {"ok": True, "result": None}
    else:
        scalar, factors = result
        payload = {
            "ok": True,
            "result": {
                "scalar": int(scalar),
                "factors": [
                    {"coeffs": [int(c) for c in coeffs], "multiplicity": int(mult)}
                    for coeffs, mult in factors
                ],
            },
        }
    return json.dumps(payload, separators=(",", ":"))


def _error(message: str) -> str:
    return json.dumps({"ok": False, "error": message}, separators=(",", ":"))


def serve(factor_fn: FactorFn) -> None:
    out = sys.stdout
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        try:
            request = json.loads(line)
            coeffs = request["coeffs"]
            if not isinstance(coeffs, list):
                raise ValueError("coeffs must be an array")
            # Require JSON integers, matching the Lean service; reject bools,
            # floats and numeric strings so all systems accept the same inputs.
            if not all(type(c) is int for c in coeffs):
                raise ValueError("coeffs must all be integers")
        except Exception as exc:  # noqa: BLE001 -- report any malformed request
            out.write(_error(f"expected JSON object with integer array field coeffs: {exc}") + "\n")
            out.flush()
            continue
        try:
            result = factor_fn(coeffs)
        except Exception as exc:  # noqa: BLE001 -- report any internal failure
            out.write(_error(f"{type(exc).__name__}: {exc}") + "\n")
            out.flush()
            continue
        out.write(_reply(result) + "\n")
        out.flush()
