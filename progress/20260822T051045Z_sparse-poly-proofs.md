# hex-sparse-poly: Phase 5 proof completion

## Accomplished

- The selected `ExtTreeMap`-accumulation multiplication twin is in the
  library: `mulTree`/`mulImpl` in `Arith.lean` with the proved
  `@[csimp] mul_eq_impl` value equality (via `getD_mulTree` and
  `coeffList_mulImpl`), so compiled `*` now runs the Phase-4 winner
  while the kernel-facing sort-and-combine specification is unchanged.
- The compose agreement pack in `Eval.lean` is closed:
  `compose_toDense`, `substPow_toDense`, `substPow_eq_compose`,
  `eval_compose`, `eval_substPow`, and `coeff_substScale`, built on a
  dense power-sum ladder (`psf_eq_terms_sum`,
  `termsOfCoeffsList_toDense`, `toDense_composePower`) plus supporting
  `Dense.lean` lemmas (`toDense_scale`, `toDense_C`,
  `monomial_mul_monomial`, `pow_succ`).
- The two `divExactMonic?` iff lemmas in `Euclid.lean` are proved:
  `divExactMonic?_isSome` via the dense `mod_eq_zero_of_dvd` transport,
  and `divExactMonic?_eq_some` via a new private dense monic
  cancellation (`leadingCoeff_mul` on the difference, trivial-ring case
  split off).
- `grep sorry` over the library is empty; no `axiom`, no
  `native_decide`. `lake build HexSparsePoly HexConformance
  HexSparsePolyTests hexsparsepoly_bench` green; `check_dag.py` and
  `libgraph.py` pass. `done_through: 5`.

## Current frontier

Phase 5 complete. `scripts/status.py` now shows HexSparsePoly at
Phase 6 (polish) and HexSparsePolyMathlib unblocked.

## Next step

Milestone 6: activate HexSparsePolyMathlib (`Equiv.lean` with
`denseEquiv`, `equiv`, `coeff_equiv`, and the `equiv_support`
headline), then Phase 6 polish for both libraries (there is a known
backlog of unusedSimpArgs / unusedSectionVars linter warnings).

## Blockers

None.
