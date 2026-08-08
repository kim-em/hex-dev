# HexMvPoly v4 kernel evidence

## Accomplished

- Captured the v4 kernel proof-probe sweep from clean commit `77b76dd3` on
  `chungus2`, pinned to logical CPU 22 with six rotated paired samples.
- Obtained a release-quality artifact with no validity exceptions, preflight
  failures, rejected pair attempts, or exhausted pairs. Three busy preflight
  windows were rejected before measurement.
- Applied round-matched construction subtraction to addition, cancellation,
  and SOS and classified the 2× threshold with conservative noise bounds.
- Found no passing family: addition is noise-limited; cancellation has
  interval [1.447×, 2.402×]; SOS has interval [1.987×, 3.857×];
  multiplication's interval is wholly below 2×; structural is unresolved.
- Replaced the superseded v3 artifact and updated both performance reports,
  the threshold rule in the library SPEC, and the future-work representation
  decision. `ExtTreeMap` remains the single production representation.
- Clarified that the reusable optimization frontier is a direct tree-cursor
  version of the existing `Std.ExtTreeMap.foldl₂` plus a linear ordered-tree
  builder, with coefficient combination and zero deletion remaining
  `HexMvPoly` policy.
- Re-ran Phase-4, DAG, release-manifest, Mathlib-free bench/probe, 63 harness
  tests, and the complete manual build successfully.

## Current frontier

The final implementation, consumer acceptance, reusable map API, and
release-quality measurement evidence are complete. One follow-up independent
review is required before opening the completion PR.

## Next step

Commit the v4 artifact and report decision, obtain a fresh Claude second
opinion on the final diff and evidence interpretation, address any findings,
then open the completion PR and monitor CI to merge.

## Blockers

None.
