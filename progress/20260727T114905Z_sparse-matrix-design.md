# Sparse matrix representation design

**Accomplished**

- Confirmed Hex currently has only the flat row-major dense `Matrix` type and
  no existing CSR, CSC, or other sparse-matrix representation.
- Evaluated the proposed duplicated row/column association-list layout against
  the sparse matrix multiplication access pattern.
- Identified CSR-style row storage for both operands plus a Gustavson row
  accumulator as the appropriate initial computational design.

**Current frontier**

- Sparse multiplication can traverse `A` row-wise and, for each `A[i,k]`,
  traverse row `k` of `B`; it does not require a column index for `B`.
- A production representation should use contiguous CSR arrays with sorted,
  unique, in-bounds column indices and no stored zeros, rather than pointer-heavy
  association lists.
- Output fill-in is central: for independent 5%-dense supports at `n = 1024`,
  a structural product entry is present with probability about 92%, ignoring
  coefficient cancellation, so sparse inputs may warrant a dense output.

**Next step**

- If implemented, specify a separate sparse type, its canonical invariants,
  CSR multiplication and accumulator strategy, dense/sparse conversion and
  correspondence theorem, and a fill-in-aware benchmark grid.

**Blockers**

- None.
