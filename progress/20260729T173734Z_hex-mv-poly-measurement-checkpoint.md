# HexMvPoly measurement checkpoint

## Accomplished

- Removed equality-instance coherence from the executable constructor and
  arithmetic layer by taking lawful boolean equality directly, while keeping
  the ordered-list polynomial equality path explicit.
- Switched addition to the reusable deletion-capable
  `Std.ExtTreeMap.mergeWith?` API and negation to one-pass tree filtering;
  documented `HexBasic/ExtTreeMap.lean` as the upstream-only home for generic
  map algorithms.
- Added direct `eval₂Hom`/`aeval` correspondence, randomized Mathlib
  conformance, broader matched kernel probes, and comparator/corpus fixes.
- Made the pinned SOS and CompPoly consumer setup preserve SOS's original
  verifier helpers, disclose the one CompPoly toolchain proof rewrite, and
  build every acceptance target from pristine clones.
- Changed the kernel sweep decision to use round-matched import-subtracted
  workloads, robust import-baseline and same-module null envelopes, explicit
  comparison axes, and invalidation for excessive null spread.
- Passed the full 9,649-job monorepo build, all registered conformance and
  proof-probe targets, all 11 native benchmark verifications, exact fixture
  regeneration, and 59 independent SymPy oracle cases.

## Current frontier

The source and measurement harness are ready for a clean commit. Existing
kernel/native/comparator artifacts and their report tables predate the changed
corpora and baseline subtraction, so they are not valid evidence for this
source state.

## Next step

Commit this source checkpoint, run the release-quality kernel sweep from the
clean commit, regenerate the native and comparator exports, and replace the
performance reports and figures from those new artifacts.

## Blockers

None.
