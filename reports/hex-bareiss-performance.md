# HexBareiss Performance Report

`HexBareiss` was split out of `HexMatrix` (the executable fraction-free
Bareiss determinant algorithm over `Int` and its bordered-minor support).
Its code is unchanged by the split.

The Phase-4 benchmarking and conformance for the Bareiss surface are
currently administered through `HexMatrix`: the `runBareissDet` bench target
(input family `structured-bareiss-determinant`) and the paired Hex/FLINT
`fmpz_mat.det` informational comparator rungs exercise this path, and the
`bareiss` conformance operation cross-checks it against the generic
determinant. See `reports/hex-matrix-performance.md` for the consolidated
measurement, including the FLINT comparator ratios and the standing Concern
about the structural gap versus multimodular CRT.

Partitioning the bench and conformance drivers into a dedicated
`bench/HexBareiss` / `conformance/HexBareiss` with their own oracle stream
is tracked as the follow-up to the library split.
