# HexDeterminant Performance Report

`HexDeterminant` was split out of `HexMatrix` (the generic Leibniz-formula
determinant, the determinant behaviour of elementary row/column operations,
cofactor/adjugate theory, Cauchy-Binet expansion, and the Plücker /
Desnanot-Jacobi identities). Its code is unchanged by the split.

The Phase-4 benchmarking and conformance for the determinant surface are
currently administered through `HexMatrix`: the generic Leibniz determinant
is exercised by the `runLeibnizDet` bench target (input family
`leibniz-small-determinant`) and cross-checked against the row-pivoted
Bareiss determinant and FLINT's `fmpz_mat.det`. See
`reports/hex-matrix-performance.md` for the consolidated measurement.

Partitioning the bench and conformance drivers into a dedicated
`bench/HexDeterminant` / `conformance/HexDeterminant` with their own oracle
stream is tracked as the follow-up to the library split.
