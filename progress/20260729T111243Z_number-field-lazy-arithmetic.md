# Number-field lazy arithmetic semantics

## Accomplished

- Began the next cohesive NumberField milestone locally while PR #9091 remained
  in CI; no additional PR was opened.
- Proved `AlgebraicRoot.neg_toComplex` from polynomial reflection and certified
  root isolation.
- Exposed the existing domain-level common-root resultant criterion under the
  shorter name `DensePoly.resultant_eq_zero_of_common_eval`.
- Added the executable coefficient contract `ZPoly.coeff_liftOuter` beside
  `liftOuter`, avoiding reliance on opaque `Array.map` reduction downstream.
- Proved the coefficient-specialized bivariate resultant vanishes at a common
  root, and used it to prove that `ZPoly.addEliminant a.p b.p` vanishes at
  `a.toComplex + b.toComplex`.
- Proved `HexPolyZMathlib.isRoot_squareFreeCore`: every complex root of a
  nonzero integer polynomial remains a root of its executable square-free
  core. The proof uses the signed primitive decomposition, the repeated-part
  derivative divisor, and Mathlib's characteristic-zero root-transfer lemma.
- Verified `lake build HexNumberField.Lazy`,
  `lake build HexResultantMathlib.Specialize`, and
  `lake build HexNumberFieldMathlib.Lazy`.

## Current frontier

The raw addition eliminant now has the required semantic root, and that root
survives `ZPoly.squareFreeCore`. Checked-addition soundness now reduces to
showing the refined operand balls contain their selected roots and the output
filter selected the unique matching isolation.

## Next step

Factor the successful `AlgebraicRoot.ofEliminant?` branch into a reusable
soundness lemma for addition, multiplication, and inversion, reusing the
existing root-selection geometry from exactification and the operation-ball
membership/radius bounds from `HexNumberFieldMathlib.Approx`.

## Blockers

None. PR #9091 passed its full CI suite and merged as `09668c54` while this
local stage was in progress.
