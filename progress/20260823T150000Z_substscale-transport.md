# substScale transport across the dense conversion and into the companion (#9482)

## Accomplished

- `HexSparsePoly/Eval.lean`: `substScale_eq_compose` (argument scaling
  is composition with the degree-one monomial `a · x`) and
  `substScale_toDense`, completing the `*_toDense` transport list.
- `HexSparsePolyMathlib/Equiv.lean`: `equiv_substScale`, closing the
  last gap in the one-lemma-per-public-operation correspondence
  surface.
- Generalised two existing lemmas rather than adding near-duplicates:
  `monomial_one_pow` → `monomial_pow` (arbitrary coefficient), and
  `C_mul_monomial` to an arbitrary monomial coefficient; the private
  `coeff_monomial_foldl` now takes the exponent and coefficient maps as
  parameters so both substitution proofs share it.
- Companion conformance target gained the `substScale` clause; SPECs,
  READMEs, and the manual chapter updated.

## Decisions

- The dense-side normal form is `DensePoly.monomial 1 a`, not
  `DensePoly.C a * DensePoly.X` as the issue suggested: `Hex.DensePoly`
  has no `X`. This matches `substPow_toDense`, which lands on
  `DensePoly.monomial k 1`. The companion still states the Mathlib-side
  shape the issue asked for (`Polynomial.C a * Polynomial.X`), bridged
  by `Polynomial.C_mul_X_eq_monomial`.

## Verification

`lake build HexSparsePoly HexSparsePolyMathlib
HexSparsePolyMathlib.Conformance HexSparsePoly.Conformance
HexSparsePolyTests` and `lake build HexManual` green; the repo lint
scripts (copyright, line counts, DAG, phase 4/7, conformance targets,
release manifest, manual split) pass. No new `sorry`, no `axiom`.
