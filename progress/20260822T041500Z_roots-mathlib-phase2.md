# HexRootsMathlib Phase-2 review and bump to 2

## Accomplished

- Performed the Phase-2 scaffolding review of HexRootsMathlib against
  its SPEC via a non-author reviewer agent: zero banned markers across
  41 modules, all 38 SPEC-declared modules present, every SPEC-named
  theorem present with matching statement, completeness constants
  reproduced exactly, regression surface CI-reachable four ways.
- Committed the substantive attestation
  status/hex-roots-mathlib.scaffolding-reviewed.
- Fixed the one-directional SPEC drift with the review: declared the
  isolate! total consumption surface (IsolateTotal.lean) and
  Examples.lean, added Completeness/RefinementCompleteness.lean to the
  file table, moved the witness-implies-Pellet attribution from
  Geometry.lean to Pellet.lean, repaired a dangling sentence.
- Filed #9384 for the code-level hygiene items (triplicated private
  helpers, the vacuously-hypothesised same-file alias with its
  HexNumberFieldMathlib call site, ArgumentTopology pruning), scoped to
  the wave's HexRootsMathlib Phase-6 pass.
- Bumped done_through 0 -> 2 (Phase 1 was long since complete: full
  scaffold, umbrella, local SPEC, deps HexRoots and HexPolyZMathlib
  both >= 1; the counter had simply never been advanced).

## Current frontier

- Next rung per the wave bump queue
  (progress/20260822T034500Z_wave-dag-and-headline-audit.md):
  HexRootsMathlib 2 -> 4 via the Phase-3 exemption record and the
  Phase-4 mathlib-bridge declaration.

## Next step

- Land the 2 -> 4 PR, then HexResultantMathlib 3 -> 5.

## Blockers

- None.
