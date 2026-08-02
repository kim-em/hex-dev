# Number-field lazy addition totality

## Accomplished

- Confirmed PR #9091 completed its full CI suite and merged before continuing
  this stage; no new PR was opened.
- Proved that the addition eliminant is nonzero and has
  `a.toComplex + b.toComplex` as a root, using specialization of the bivariate
  resultant and a coprimality witness away from the finite set of root sums.
- Added the square-free-core primitivity and positive-leading-coefficient
  contracts needed by the generic eliminant pipeline.
- Factored the successful eliminant path into reusable soundness and totality
  lemmas. The totality proof connects isolation completeness, refined-root
  separation, and sufficiently small operation balls.
- Proved checked addition soundness and totality. Consequently the total
  addition and the checked and total subtraction semantic theorems are now
  complete without new `sorry`s.
- Verified `lake build HexNumberFieldMathlib.Lazy`.

## Current frontier

Lazy negation, addition, and subtraction now have complete Mathlib semantics.
The remaining arithmetic obligations are multiplication and inversion; division
then follows by composition.

## Next step

Prove the multiplication eliminant's nonzeroness and common-root statement,
show that removing its `X` factor preserves the selected nonzero product root,
and reuse the generic eliminant lemmas with the multiplication-ball guard bound.

## Blockers

None.
