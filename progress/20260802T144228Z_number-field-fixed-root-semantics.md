# Number-field fixed-root semantics

## Accomplished

- Proved soundness and completeness of the executable fixed-field Yun
  decomposition, including exact transfer of Mathlib root multiplicities.
- Proved soundness and completeness of component candidate isolation and the
  selected-embedding filter.
- Refactored semantic root merging to a structural list recursion, made
  duplicate normalization idempotent on certified multiplicities, and proved
  membership, multiplicity, and duplicate-freedom invariants through both
  nested folds.
- Replaced the final quicksort with stable merge sort, proved the executable
  root comparator total and transitive, and closed all fixed-field membership,
  multiplicity, positivity, duplicate-freedom, ordering, and degree-sum
  contracts.
- Verified `lake build HexNumberFieldMathlib.ComponentRoots`, the full
  `lake build`, and `lake build HexConformance`.

## Current frontier

The fixed-field root driver is total and semantically complete. The seven
remaining root API placeholders are confined to the downstream
`AlgebraicPoly` driver, whose lift requires totality and semantic correctness
of `Common.presentation?`.

## Next step

Land the fixed-field semantics PR as one cohesive change, then prove
`Common.presentation?` total and coefficient-preserving before reusing the
fixed-field contracts to close the `AlgebraicPoly` root API.

## Blockers

None for the fixed-field stage. The algebraic lift requires a substantive new
presentation layer rather than a direct wrapper proof.
