# Pseudo-division reconstruction

## Accomplished

- Proved the high-coefficient quotient convolution identity by reflecting the
  bounded index range, discarding terms beyond the divisor support, splitting
  off the current active coefficient, and factoring the common
  leading-coefficient power.
- Used the low-coefficient remainder formula and the high-coefficient active
  recurrence to prove `pseudoDivMod_reconstruct_core` without `sorry`.
- Incorporated the completed bounded-convolution review. It correctly found
  that most of the first proof duplicated the existing Mathlib-free layer in
  `HexPoly.Euclid.MulRing`; the duplicate definitions and proofs are removed,
  the private proof layer is imported with `import all`, and only the new
  minimum-bound bridge remains locally.
- The reconstruction theorem now directly connects all proof-only builders
  to the public executable `pseudoDivMod`, resolving the earlier review's
  concern that those builders could drift independently.
- Independently cross-checked the high-index arithmetic in a read-only Sol
  audit.
- Built `HexResultant`, `HexConformance`, and `HexManual`; verified all four
  Resultant benchmarks; and passed Phase 4, DAG, copyright, line-count,
  proof-hygiene, and diff checks.

## Current frontier

- `HexResultant/Basic.lean` now contains no `sorry`; pseudo-division
  reconstruction and its structural quotient/remainder bounds are complete.
- The bounded-convolution review's blocker is fixed in the final tree, but the
  stacked milestone branches still need reconciliation so the fix appears at
  the earliest affected PR rather than only in this descendant.
- Other Resultant SPEC obligations remain in `Subresultant.lean` and the
  Mathlib bridge modules.

## Next step

- Publish the reconstruction milestone and start its independent review in
  the background.
- Reconcile the convolution/active stack so the deduplication fix is present
  in the reviewed base PR.
- Continue with the remaining Resultant and NumberField SPEC theorem gaps.

## Blockers

- No proof blocker for pseudo-division reconstruction.
