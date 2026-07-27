# RCF strict separation and endpoint classification

## Accomplished

- Added raw strict-gap checking with adjacent/all-pairs and real-root ordering
  soundness theorems.
- Added replay-based midpoint refinement, structurally fuel-bounded pair
  separation, a left-to-right scan, and a final checker-filtered builder.
- Added exact root-versus-dyadic endpoint classification, proved every
  successful result against the unique isolated root, and proved valid replay
  isolations always classify.
- Exported a lightweight exact endpoint-evaluation lemma and reused it in the
  existing two-circle development.
- Added kernel and compiled regressions for midpoint ownership, close roots,
  overlaps, malformed counts, repeated middle-interval refinement, shared
  endpoint roots, all comparison outcomes, and defensive branches.
- Updated the RCF and real-root companion SPECs and verified the full
  9465-target `lake build`.
- Addressed both blockers from an independent Claude review: production-path
  coverage and stale `refine1With` wording in the SPEC.

## Current frontier

Strictly separated generalized isolations and exact bounded-endpoint
comparisons are available for cell construction.

## Next step

Build the semantic/executable cell decomposition, prove the partition and
cell-membership facts, then connect atom signs across open and root cells.

## Blockers

None.
