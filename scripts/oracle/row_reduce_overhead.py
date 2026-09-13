#!/usr/bin/env python3
"""Field comparator overhead with the identical request and complete response.

Select using HEX_FLINT_BENCH_DRIVER. Only the native matrix operation is
cached after warmup; request parsing, input-cache lookup, rational extraction,
response serialization, transport, and Lean-side decoding remain measured.
This is a protocol calibration driver, not an algorithm comparator.
"""
from __future__ import annotations

import flint_bench_driver as driver


def main() -> int:
    driver._FMPQ_MAT_OPS["field_inverse"] = lambda req: driver._fmpq_field(
        req, inverse=True, cached_result=True)
    driver._FMPQ_MAT_OPS["field_solve"] = lambda req: driver._fmpq_field(
        req, inverse=False, cached_result=True)
    return driver.main()


if __name__ == "__main__":
    raise SystemExit(main())
