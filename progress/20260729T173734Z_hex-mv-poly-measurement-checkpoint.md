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
- Ran the six-sample designated-host kernel sweep from clean commit
  `7acdff89`; its artifact is release-quality with no validity exceptions.
  Sparse addition (4.697×) and sum-of-squares (2.411×) meet the predeclared
  two-family gate for a future kernel-specialized sorted representation.
- Regenerated all eleven native ladders from clean commit `163e100c` with
  three outer trials per rung; every target remains consistent with its
  declared complexity and no ladder was budget-truncated.
- Regenerated the five-family CompPoly and sorted-proxy exports from a pristine
  pinned CompPoly checkout against clean Hex commit `a7430482`, again with
  three outer trials, and rebuilt all five comparator figures.
- Passed the full 9,649-job monorepo build, all registered conformance and
  proof-probe targets, all 11 native benchmark verifications, exact fixture
  regeneration, and 59 independent SymPy oracle cases.

## Current frontier

The corrected kernel, native, and external comparator artifacts are recorded.
The performance report and source-profile account still need to be aligned
with the new artifacts.

## Next step

Commit the comparator exports and figures, refresh the five source profiles
from the resulting clean commit, and replace the performance report tables
and profile account.

## Blockers

None.
