# ChainCorrespond: executable/abstract Sturm correspondence

## Accomplished
- New `HexRealRootsMathlib/ChainCorrespond.lean`, wired into the umbrella.
- `squareFreeRat_iff (f) (hf : f ≠ 0) : SquareFreeRat f ↔ Squarefree (toPolyℚ f)`.
  Reuses `HexPolyMathlib.toPolynomial_gcd_associated` (field-generic raw-gcd
  correspondence) + `separable_def` / `PerfectField.separable_iff_squarefree` /
  `EuclideanDomain.gcd_isUnit_iff` / `isUnit_iff_degree_eq_zero`. The `f = 0`
  corner is genuinely excluded (SquareFreeRat 0 holds, Squarefree 0 false), so
  the theorem carries an `f ≠ 0` hypothesis (diverges from the SPEC's
  unconditional statement — the SPEC statement is unsound at 0).
- `sturmVarAt_eq (chain) (x) : Hex.sturmVarAt chain x = Sturm.sturmVar
  (chain.toList.map toPolyℝ) (Dyadic.toReal x)`. Supported by:
  - `toReal_evalDyadic`: exact dyadic Horner eval, cast to ℝ, = Mathlib eval of
    the real cast (Horner-polynomial bridge + `Dyadic.toRat` ring-hom lemmas).
  - `sign_dyadicSign`: `dyadicSign` as a real has the same `SignType.sign` as
    the dyadic's real value.
  - `signVar_eq`: executable integer `signVar` = abstract `signVariations` of
    the ℝ-casts.
- All sorry-free; only standard axioms (propext/Classical.choice/Quot.sound).
  `lake build HexRealRootsMathlib` green; `check_dag.py` exit 0.

## Current frontier
Remaining SPEC targets NOT yet done: `sturmChain_isSturmChain` (all
`IsSturmChain` fields — root_flank is the hard one), `sturmCount_eq_card_roots`,
`rootCount_eq_card_roots`, plus the primitivePart root-set transfer.

## Next step
Build `spem` correspondence (positive-rational-multiple-of-remainder) by
induction on `spemAux` fuel, then assemble the `IsSturmChain` fields at
`toPolyℝ (primitivePart p)`.

## Blockers
- Module-system gotcha: `where`-auxiliaries (e.g. `Hex.signVar.go`) are
  non-public and cannot be named cross-module; work through the public wrapper.
- `l.map (fun i => (i:ℝ))` mis-elaborates to a `flatMap`; use
  `(Int.cast : ℤ → ℝ)` so Mathlib `List.map` lemmas fire.
