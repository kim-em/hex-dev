# Mathlib-free compiled RCF decision

## Accomplished

- Added `HexRCF.DecisionCheck`, containing compiled real-root isolation,
  strict separation, endpoint classification, sign-matrix and certificate
  assembly, retained build results, replay validation, and `decide`.
- Reduced `HexRCF.Decision` to `decide_sound`, the sole theorem interpreting
  an accepted verdict in real-valued sentence semantics, while preserving the
  existing public declaration surface through imports.
- Rewired `Reify` and `DecisionTests` to request the pure decision module's
  bodies explicitly for compiled/meta execution, and switched the shared
  conformance fixture emitter to the pure decision import.
- Updated the HexRCF umbrella and SPEC file map.
- Verified focused decision, test, reification, and tactic targets and the full
  HexRCF build. Mechanically checked the 47-module `DecisionCheck` closure
  contains neither `Mathlib.*` nor `HexRealRootsMathlib.*`; the Certificate and
  Builder closures remain pure. DAG, Phase-4, release-manifest, trust-surface,
  copyright, diff, and banned-token checks pass. The standalone
  `hexrcf_emit_fixtures` executable also builds through the pure closure. An
  independent Sol review returned GO after auditing declarations, imports,
  API preservation, and consumers.

## Current frontier

Issue #9006 is implemented on a branch stacked above the sign-matrix-check PR
#9005. The complete compiled decision track required by directive #8973 now
has a mechanically verified Mathlib-free import closure.

## Next step

Publish the stacked PR, then define controlled one-parameter LeanBench
families over `DecisionCheck` separately from the fresh-module tactic probes,
and reconcile the Phase-4 evidence contract around those two tracks.

## Blockers

None for this extraction. The branch remains stacked until its parent chain
merges; it can then be rebased and retargeted to main.
