# HexNumberField minimal-polynomial review fixes

## Accomplished

- Strengthened conversion regressions to distinguish the positive and negative
  conjugates, rather than checking only their shared polynomial.
- Added a degree-one early Krylov exit for a rational fixed-field element and
  converted `1 + sqrt 2` through a minimal polynomial unrelated to the defining
  polynomial.
- Exercised the primary total conversion wrapper directly.
- Documented the separation-margin argument and why checked refinement cannot
  be replaced by the fallback-bearing approximation wrapper.
- Materialized multiplication columns once before filling the matrix and made
  impossible Krylov indexing failures loud instead of silently inserting zero
  vectors.
- Added the explicit meta import for the row-reduction dependency and rebuilt
  `HexNumberField.Convert` and `HexNumberField`.

## Current frontier

The independent review found no incorrect public data or valid-input fallback.
Its correctness and regression findings are addressed. Incremental row
reduction and reusing an already computed isolation array remain optional
performance improvements, not correctness blockers.

## Next step

Push the review fix and rebase/push the lazy-arithmetic and disambiguation PRs
so the entire active stack contains it.

## Blockers

None.
