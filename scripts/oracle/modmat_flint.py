#!/usr/bin/env python3
"""Check modular-matrix fixtures using the shared FLINT matrix oracle."""
import matrix_flint

matrix_flint.DEFAULT_FIXTURE = (
    matrix_flint.REPO_ROOT / "conformance-fixtures/HexModularMatrix/modmat.jsonl"
)

if __name__ == "__main__":
    raise SystemExit(matrix_flint.main())
