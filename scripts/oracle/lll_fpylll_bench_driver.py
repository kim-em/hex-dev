#!/usr/bin/env python3
"""Persistent-subprocess fpylll bench driver for `hex-lll`.

Loops on stdin, one matrix per line; emits one integer per line on
stdout. Imports `fpylll` once at startup and reuses the loaded
module for every subsequent request, so the only per-call cost is
parse + `fpylll.LLL.reduction` + emit.

Per `SPEC/benchmarking.md` (post-#3657) §"External comparators"
§"Process call": this driver is the persistent-subprocess shape
required when per-call overhead is non-negligible. The HexLLL bench
harness spawns the driver once per `lake exe hexlll_bench run`
invocation, holds its stdin / stdout handles in
`Hex.LLLBench.fpylllChildRef`, and reuses the file descriptors
across every measured call in that bench process. One process
startup and one `import fpylll` is amortised across all comparator
calls in the run.

## Framing

The request framing matches the Isabelle persistent driver wired
in HO-16 so the same `HexLLL/Bench.lean` helper
(`matrixHaskell`) feeds both comparators. Each request is one line
containing the input matrix in Haskell's `[[Integer]]` read syntax
(e.g. `[[1,2],[3,4]]`), terminated by `\n`. Each reply is one line
containing a single integer — the bench scalar `fpylll.LLL.reduction`
produces for that matrix — terminated by `\n`.

The scalar emitted is the first-row checksum of fpylll's reduced
basis, matching `Hex.LLLBench.intVectorChecksum`. This pairs with
`runFpylllFirstShortVector*Checksum` registrations in
`HexLLL/Bench.lean`. Use the existing per-call `lll_fpylll.py
--bench-checksum` path if you need the same scalar without the
persistent shape.

EOF on stdin terminates the driver.

A malformed request is *never* fatal — the driver writes an error
line and continues the loop. The error line is the literal string
`ERROR: <message>`; the bench-side parser treats any non-integer
reply as a driver fault and retries once.

## Per-call overhead

The driver imports `fpylll` once at startup; per-call cost in the
steady state is `ast.literal_eval` + `fpylll.LLL.reduction` + the
checksum fold. Measured per-call overhead is recorded in
`reports/hex-lll-performance.md` once HO-18 regenerates the headline
report.

## Stdlib only, plus fpylll

Like the other `scripts/oracle/*.py` drivers, this script depends
only on the python stdlib and `fpylll`. The `fpylll` import is
local-to-startup (not lazy) so the first request does not pay an
import cost.
"""
from __future__ import annotations

import ast
import sys
import traceback
from typing import Iterable

try:
    from fpylll import IntegerMatrix, LLL  # type: ignore[import-not-found]
    _fpylll_import_error: str | None = None
except Exception as exc:  # pragma: no cover - defensive
    IntegerMatrix = None  # type: ignore[assignment]
    LLL = None  # type: ignore[assignment]
    _fpylll_import_error = f"fpylll not available: {exc!r}"


# `δ = 0.75` matches `HexLLL.EmitFixtures.emitCase` and the Lean
# bench wiring at `δ = 3/4`.
LLL_DELTA = 0.75


def _parse_matrix(line: str) -> list[list[int]]:
    """Parse a Haskell-style `[[Integer]]` matrix line into a Python
    list of lists of `int`. Uses `ast.literal_eval`, which accepts
    Python's superset of the Haskell `[[Integer]]` read syntax that
    Lean's `matrixHaskell` emits.
    """
    value = ast.literal_eval(line)
    if not isinstance(value, list):
        raise ValueError(f"top-level expression must be a list, got {type(value).__name__}")
    rows: list[list[int]] = []
    for row in value:
        if not isinstance(row, list):
            raise ValueError(f"row must be a list, got {type(row).__name__}")
        rows.append([int(c) for c in row])
    if rows:
        width = len(rows[0])
        for r in rows:
            if len(r) != width:
                raise ValueError("matrix rows have inconsistent width")
    return rows


def _first_row_checksum(row: Iterable[int]) -> int:
    """Mirror `Hex.LLLBench.intVectorChecksum`."""
    acc = 0
    for value in row:
        acc = acc * 65537 + int(value)
    return acc


def _reduce_and_checksum(rows: list[list[int]]) -> int:
    if IntegerMatrix is None or LLL is None:
        raise RuntimeError(_fpylll_import_error or "fpylll unavailable")
    if not rows:
        return 0
    M = IntegerMatrix.from_matrix(rows)
    LLL.reduction(M, delta=LLL_DELTA)
    if M.nrows == 0:
        return 0
    first_row = [int(M[0, j]) for j in range(M.ncols)]
    return _first_row_checksum(first_row)


def _serve(stdin, stdout) -> None:
    for raw in stdin:
        line = raw.rstrip("\n")
        if not line:
            # Blank-line sentinel: silently skip, the consumer is
            # not expecting a reply.
            continue
        try:
            matrix = _parse_matrix(line)
            checksum = _reduce_and_checksum(matrix)
            stdout.write(f"{checksum}\n")
        except Exception as exc:
            stdout.write(f"ERROR: {type(exc).__name__}: {exc}\n")
        try:
            stdout.flush()
        except BrokenPipeError:  # pragma: no cover - consumer hung up
            return


# Smoke-test invocation::
#
#   printf '%s\n' \\
#       '[[1,0],[0,1]]' \\
#       '[[2,0],[0,2]]' \\
#       | python3 scripts/oracle/lll_fpylll_bench_driver.py
#
# Expected replies (one per request, in order)::
#
#   65537
#   131074
#
# Malformed lines are echoed back as `ERROR: <type>: <message>` and
# never terminate the driver.


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
