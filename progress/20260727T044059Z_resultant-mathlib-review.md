# HexResultantMathlib scaffold review repair

## Accomplished

- Corrected the bivariate common-root theorem and its SPEC contract to require
  positive outer degree for at least one input, excluding the false `(0, 0)`
  formal-resultant case.
- Added `HexResultantMathlib` to the existing single-job CI library target set
  after checking the repository CI doctrine.
- Repaired the moved source-local SPEC link in the library index.
- Rebuilt `HexResultantMathlib` and reran DAG, copyright, line-count, and
  whitespace checks successfully.

## Current frontier

The scaffold's theorem statements are mathematically consistent with the
project's formal-degree conventions, and the activated library is now exercised
by merge-gating CI.

## Next step

Update PR #8886, then repair the reviewed HexNumberField core invariants and CI
coverage while approximation and QAdjoin reviews remain active.

## Blockers

None.
