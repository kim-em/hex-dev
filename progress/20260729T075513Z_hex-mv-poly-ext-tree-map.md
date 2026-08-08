# Hex multivariate polynomial reusable tree-map API

## Accomplished

- Added `HexBasic.ExtTreeMap` as the designated home for reusable,
  upstream-shaped `Std.ExtTreeMap` operations.
- Implemented a joint ordered traversal of two maps and a deletion-capable,
  size-biased merge that preserves callback argument order.
- Added executable empty-map laws for both APIs.
- Repointed the monomial layer at the reusable module and removed
  `HexMvPoly.Basic`'s direct Batteries dependency in favor of
  `HexBasic.ListShim`.

## Current frontier

- The reusable module and `HexMvPoly.Basic` build cleanly.
- The initial core API PR is still running its final CI stages with auto-merge
  enabled.
- The merge API has its boundary laws; a general per-key lookup theorem remains
  useful before `MvPoly.add` can consume it without weakening the canonical
  nonzero invariant or its size-biased complexity.

## Next step

- Prove the lookup semantics of the generic deletion-capable merge, then
  refactor polynomial addition onto it.
- Continue discharging the remaining coefficient and recursive laws after the
  core PR merges.

## Blockers

- None.
