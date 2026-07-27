# Mathlib-free RCF Sturm replay checks

## Accomplished

- Added `HexRCF.SturmCheck`, containing the generalized replay data,
  executable validation, literal root counts, pure degree/nonzero consequences,
  and the accepted-head nonzero theorem.
- Reduced `HexRCF.SturmReplay` to the Mathlib-facing replay, Sturm-chain,
  squarefreeness, and root-count correspondence layer while preserving every
  existing qualified declaration name through a public import.
- Made the compiled `SturmBuilder` consume `SturmCheck` directly. Its semantic
  tests now import `SturmReplay` explicitly instead of relying on the old
  transitive dependency.
- Updated the HexRCF umbrella and SPEC file map.
- Verified full HexRCF builds and mechanically checked that the repository-local
  closures of `HexRCF.SturmCheck` and `HexRCF.SturmBuilder` contain neither
  `Mathlib.*` nor `HexRealRootsMathlib.*`. DAG, Phase-4, release-manifest,
  trust-surface, copyright, diff, and banned-token checks pass. An independent
  Sol review returned GO.

## Current frontier

Issue #8987 is implemented on a branch stacked above the syntax-seam PR #8983.
The extraction exposes the first nontrivial executable RCF certificate builder
with a genuinely Mathlib-free import closure.

## Next step

Publish the stacked PR, then split the carrier certificate data and Boolean
checker from its real-root semantic proofs so compiled carrier construction can
depend on the pure syntax and replay-check modules.

## Blockers

None for this extraction. The parent syntax PR is still completing CI, so this
PR should remain stacked until #8983 merges and can then be rebased onto main.
