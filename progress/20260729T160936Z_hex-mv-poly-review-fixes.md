# HexMvPoly review fixes

## Accomplished

- Fixed Mathlib/Grind instance coherence for transported `MvPoly` arithmetic
  and added `Int`/`Rat` regression checks.
- Added direct Mathlib correspondence for Horner evaluation, homogeneous
  components, and partial evaluation, while documenting the boundary around
  explicit-order and representation-filter APIs.
- Generalized the sorted proof-probe comparator and added matched kernel
  probes for separated/interleaved/scattered addition, low- and
  high-collision multiplication, grevlex, arity eight, `Int`, and `Rat`.
- Added a reproducible pinned consumer setup. Fresh SOS and CompPoly clones
  built all acceptance targets; SOS no longer needs consumer-local Grind
  instances.
- Recorded independent Phase 2 review issues #9101 and #9102 and added their
  machine-checkable review tokens.
- Corrected the native benchmark source path and updated the consumer
  acceptance account.

## Current frontier

The implementation and review-fix sources build. The expanded kernel sweep
and the sorted native proxy need fresh release-quality artifacts from a clean
commit, followed by regenerated report tables, plots, and null-control
analysis.

## Next step

Commit the source-side review fixes, rerun both affected scientific exports on
the pinned host, update the two performance reports, then request a fresh
Claude review before opening the implementation PR.

## Blockers

None.
