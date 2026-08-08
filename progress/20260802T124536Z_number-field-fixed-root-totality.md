# Number-field fixed-root totality

## Accomplished

- Proved the coefficient-height and ball-radius bounds used by bounded root
  disambiguation, including totality and soundness of the fixed-field evaluator.
- Proved common-denominator clearing and conjugate-specialization identities for
  the bivariate norm construction.
- Proved that the norm eliminant of a nonzero fixed-field polynomial is nonzero
  by avoiding the finitely many roots across all conjugate embeddings and using
  the executable/Mathlib resultant correspondence.
- Proved positive-degree component normalization, component-driver totality,
  Yun output positivity, merge totality, and totality of `QAdjoin.roots?`.
- Proved that `QAdjoin.roots` is exactly the successful checked output and that
  it returns `.all` exactly for the zero semantic polynomial.
- Verified `lake build` and `lake build HexConformance`.

## Current frontier

The fixed-field driver has no remaining operational failure path. The remaining
fixed-field root theorems concern semantic membership, multiplicity transfer,
duplicate elimination, ordering, and total multiplicity.

## Next step

Develop the Yun semantic invariant and component candidate completeness, then
lift those results through merge and sorting to close the remaining fixed-field
root contracts before reusing them for `AlgebraicPoly`.

## Blockers

None.
