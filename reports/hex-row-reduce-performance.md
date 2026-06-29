# HexRowReduce Performance Report

`HexRowReduce` was split out of `HexMatrix` (the row-echelon transform and
the executable RREF stack with its pivot/free-column partition and
span/nullspace APIs). Its code is unchanged by the split.

The Phase-4 benchmarking and conformance for this surface are currently
administered through `HexMatrix`: the RREF / rank / nullspace fixtures are
emitted by `hexmatrix_emit_fixtures` and verified against
`scripts/oracle/matrix_flint.py` (`rank`, `rref`, `nullspace` operations).
See `reports/hex-matrix-performance.md` for the consolidated measurement.

Partitioning the bench and conformance drivers into a dedicated
`bench/HexRowReduce` / `conformance/HexRowReduce` with their own oracle
stream is tracked as the follow-up to the library split.
