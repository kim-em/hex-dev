# Matrix additive structure and `sub_identity_mulVec` cleanup (rebased on opaque Matrix)

## Accomplished

- Rebased onto main after #8442 made `Hex.Matrix` an opaque one-field
  structure. With `Matrix` no longer a transparent abbrev for nested
  `Vector`, entrywise arithmetic instances no longer leak into `grind`'s
  linarith on downstream `det` proofs, so the full set is safe.
- Added entrywise `Add`/`Neg`/`Sub` instances on `Matrix R n m` in
  `HexMatrix/Basic.lean`, with `@[grind =]` entry lemmas
  `getElem_add`/`getElem_neg`/`getElem_sub`. The defs use the executable
  pair accessor `A[(i, j)]` (the nested `A[i][j]` form is noncomputable
  post-#8442).
- Added `sub_mulVec : (A - B) * v = A * v - B * v` in
  `HexMatrix/MatrixAlgebra.lean` and collapsed `sub_identity_mulVec` to
  `(Q - Matrix.identity n) * v = Q * v - v`, proved by
  `rw [sub_mulVec, identity_mulVec]`. The old thirty-line entrywise
  `ofFn fun i j => Q[i][j] - if i = j then 1 else 0` statement is gone.
- Restated `fixedSpaceMatrix` as
  `berlekampMatrix f hmonic - Matrix.identity (basisSize f)` and updated
  the one call site with a `show ... * ...` bridge from the `.mulVec`
  spelling to `*`.

## Current frontier

- `HexMatrix`, `HexBerlekamp`, and the full linear-algebra conformance set
  (`HexMatrix`/`HexRowReduce`/`HexDeterminant`/`HexBareiss`/`HexGramSchmidt`/
  `HexLLL`/`HexBerlekamp` Conformance) all build green: 280 jobs.
  `HexDeterminant.Conformance` (which the pre-opaque version broke) is green.

## Next step

- CI on the PR exercises the full graph and the `*Mathlib` bridge layers.

## Blockers

- None.
