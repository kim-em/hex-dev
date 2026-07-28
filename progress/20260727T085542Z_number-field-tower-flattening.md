# Number-field tower flattening

## Accomplished

- Added `HexNumberFieldTower.Flatten` and exported it from the library umbrella.
- Implemented the finite signed-shift primitive-element search with the exact
  `choose(D, 2) + 1` bound and a full-degree acceptance check.
- Exactified fixed tower generators from oldest to newest while retaining their
  canonical mixed-radix coordinates.
- Recovered every old generator in the primitive power basis using the existing
  exact trace-pairing row-reduction driver.
- Constructed both coordinate maps and required round trips on the complete
  tower basis and primitive power basis before returning `Flattening`.
- Added compiled regressions for the rational tower, `Q(sqrt(2))`, and
  `Q(sqrt(2), sqrt(3))`; the two-level case selects `sqrt(2) + sqrt(3)` and
  checks both recovered generator coordinates.
- Verified `lake build HexNumberFieldTower.Flatten` and the full `lake build`.

## Current frontier

The computational API described by `hex-number-field-tower.md` is now present
through primitive-element flattening. The draft stack still needs independent
review results folded in, followed by conformance fixtures and companion proofs.

## Next step

Publish the flattening milestone as a stacked draft PR, start its asynchronous
review, and move directly into core conformance coverage while the review
monitors continue.

## Blockers

None.
