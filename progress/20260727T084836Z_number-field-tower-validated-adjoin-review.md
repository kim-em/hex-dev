# Number-field tower validated-adjoin review

## Accomplished

- Consolidated certified and raw fixed-embedding evaluation by making the
  public tower wrappers delegate to `RawEvaluation`.
- Restricted raw relative extension construction to `Internal.extend?` and
  required every admitted relative level to have degree greater than one.
- Proved `Level.structural_of_check`, removing the proof placeholder at the
  raw-to-certified structural boundary.
- Restored the zero-polynomial Yun regression.
- Added a compiled nonlinear conjugate-selection regression: over the fixed
  positive `Q(sqrt(2))` embedding, the positive fourth root of two selects
  `X^2 - sqrt(2)` rather than `X^2 + sqrt(2)`.
- Verified `lake build HexNumberFieldTower.Split` and the full `lake build`.

## Current frontier

The validated adjoining API now has one evaluation implementation and a
degree-aware internal construction boundary. The remaining proof placeholders
in `Basic.lean` are Phase 1 algebra laws, not data or validation witnesses.

## Next step

Rebase the splitting-field milestone onto these review fixes, publish its draft
PR, and begin tower flattening while independent reviews run asynchronously.

## Blockers

None.
