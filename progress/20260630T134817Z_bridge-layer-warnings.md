# Clear bridge-layer warnings newly exposed by default *Mathlib targets

## Accomplished

#8475 made the `*Mathlib` bridge libraries default build targets, so a plain
`lake build` now surfaces a batch of pre-existing linter warnings in those
layers. Cleared every such warning in the sorry-free bridge files; full
`lake build` (4081 jobs, incl. the merge-gating `HexBerlekampZassenhausMathlib`)
is green.

- Deprecations: `Polynomial.degree_derivative_eq` → `degree_derivative` (the
  new lemma takes `p` implicitly and `p.natDegree ≠ 0`, so `hnatpos.ne'`) in
  `HexPolyZMathlib/RobinsonForm.lean`; `Polynomial.finset_sum_coeff` →
  `finsetSum_coeff` in `HexBerlekampMathlib/Basic.lean`.
- Unused simp arguments: `Fin.castLT` (`HexMatrixMathlib/Submatrix.lean`),
  the sole `smul_mul_assoc`/`mul_smul_comm` (`HexMatrixMathlib/Algebra.lean`,
  now bare `simp`), `real_inner_eq_re_inner`
  (`HexGramSchmidtMathlib/Basic.lean`), `Fin.getElem_fin`
  (`HexBareissMathlib/Bareiss.lean`), and three in
  `HexGramSchmidtMathlib/Int/RowAdd.lean`.
- Removed a no-op `change Hex.Matrix.det logicalSource = 1` in
  `HexBareissMathlib/Bareiss.lean`.
- `linter.overlappingInstances`: dropped the redundant `[IsCancelMulZero α]`
  from four `normalizedFactors_*` theorems in
  `HexBerlekampZassenhausMathlib/UFDPartition.lean` (synthesized from
  `[UniqueFactorizationMonoid α]`).

## Current frontier

All sorry-free bridge-layer warnings cleared. Deliberately untouched: the two
sorry-bearing files (`HexBerlekampZassenhausMathlib/{Basic,FactorSoundness}.lean`,
18 warnings) and the `@[expose]` module-system warning in
`HexBerlekampZassenhaus/CrossCheck.lean`.

## Next step

The remaining build warnings are all module-system (`privateInPublic`, the
`@[expose]` and `primeModulusOfPrime defProp` cases) or live in sorry-bearing
files.

## Blockers

None.
