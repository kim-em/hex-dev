# Interval runtime retained-contract hardening

## Accomplished

- Restacked the approved typed-runtime edge onto `fc60c4bfb74062a9742eca73d3477bdec16eab90`, preserving the incoming sparse-polynomial Lake registrations and reconciling the exact factor-sweep exemption.
- Re-capped every retained action generation through `Result.Limits.state.maxGeneration`, covering transition, typed-event, equality-origin, and split actions.
- Added a restarted-child retained-tree generation one-over canary.
- Corrected the retained quote-count and whole-tree runtime-validation complexity contracts, including authenticated root-branch cost.

## Current frontier

The typed runtime edge has the final requested contract hardenings and is ready for focused and static validation before its lease-protected PR update.

## Next step

Run the affected conformance builds and repository static gates, amend the single feature commit, and force-push PR #9377 if the remote base and lease remain exact.

## Blockers

None.
