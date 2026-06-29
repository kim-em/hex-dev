# Mathlib algebra instances + equiv upgrades for HexMatrixMathlib

## Accomplished

Built out `HexMatrixMathlib`, which previously held only `matrixEquiv` and the
three row-operation lemmas:

- **`HexMatrixMathlib/Vector.lean`** (new): relocated `vectorEquiv`,
  `vectorEquiv_apply/_symm_apply`, `matrixEquiv_row`, and the
  `foldl_finRange_eq_sum` fold-to-`Finset.sum` bridge down from
  `HexRowReduceMathlib/RankSpanNullspace.lean` (they lived in the
  `HexMatrixMathlib` namespace there, a latent name clash). Added `dotProduct_eq`,
  `matrixEquiv_col`, and a generalized public `vectorEquiv_mulVec`.
- **`HexMatrix/Basic.lean`**: added the homogeneous `Mul (Matrix R n n)` instance
  (defeq to `Hex.Matrix.mul`), required by Mathlib's `Semiring`/`Ring`.
- **`HexMatrixMathlib/Algebra.lean`** (new): the Mathlib algebraic tower on
  `Hex.Matrix`, transported along `matrixEquiv` via `Function.Injective.*`
  (`AddCommMonoid`, `AddCommGroup`, `Module`, `Semiring`, `Ring`, `Algebra`),
  with per-operation `@[simp, grind =]` transport lemmas and the four bundled
  equivalences `matrixAddEquiv` (`≃+`), `matrixLinearEquiv` (`≃ₗ`),
  `matrixRingEquiv` (`≃+*`), `matrixAlgEquiv` (`≃ₐ`). Includes regression-guard
  `example`s pinning the canonical zero/one to the executable `ofFn` versions.
- **`HexMatrixMathlib/Lemmas.lean`** (new): `matrixEquiv_transpose/_setRow/_setCol`.
- **`HexMatrixMathlib/Gram.lean`** (new): `matrixEquiv_gramMatrix = M * Mᵀ`.
- **`HexMatrixMathlib/Submatrix.lean`** (new): `principalSubmatrix`/`takeRows`
  correspond to `Matrix.submatrix` reindexed by `Fin.castLE`.
- Refactored `RankSpanNullspace.lean` to drop the relocated declarations and
  import `HexMatrixMathlib.Vector`; updated the umbrella and SPEC.

Whole-monorepo `lake build` is green; no `sorry`/`axiom`. Codex second opinion
found no soundness/correctness issues (validated the injective transport and the
`Zero`-diamond resolution); its suggestions (regression guards, documenting the
proof-facing cast/pow plumbing) are applied.

## Notes / context

- `Hex.Matrix R n m = Vector (Vector R m) n` carries TWO non-defeq `Zero`
  instances under Mathlib `[Semiring R]` (core `Vector.replicate` zero vs Hex's
  `ofFn` `Matrix.zero`). Resolution deterministically selects Hex's `ofFn` zero;
  the whole tower and `matrixEquiv_zero` share it. Guard `example`s lock this in.
- `HexMatrix/MatrixAlgebra.lean:~422` has a **flaky `grind`** (fails then passes
  on retry) independent of this work — worth a separate hardening pass.
- This work overlaps live fleet branches (`refactor/vector-namespace`,
  `refactor/dotproduct-smul-consolidate`, executable `Matrix.add/neg/sub`); built
  off `main`, so expect to reconcile when those land.

## Next step

Land the PR; reconcile with the fleet's executable-algebra branches if they merge
first.

## Blockers

None.
