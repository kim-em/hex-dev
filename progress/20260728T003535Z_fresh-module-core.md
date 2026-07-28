# Neutral fresh-module sweep core

## Accomplished

- Added a library-neutral declarative runner for externally timed
  reference/candidate proof-probe pairs.
- Preserved exact measured-module invalidation, Lake-only rebuilding, raw wall
  samples, peak RSS, artefact sizes, source and checkout provenance,
  timeout/process-group cleanup, and dirty/busy-host refusal.
- Added an untimed `+<module>:deps` preflight so both orientations begin with
  the complete shared import closure warm.
- Added rotated pair order, alternating orientation, stable signed
  candidate-minus-reference deltas, and per-module axiom policies.
- Rejected pair-name ambiguity and any transitive local import path between
  measured modules.
- Added fifteen self-contained tests using the existing HexIntervalMathlib
  probe surface and wired them into the existing single CI lint step.
- Validated both pair orientations with diagnostic fresh builds; the dirty,
  busy-host output remains outside the repository and is not release evidence.

## Current frontier

- The neutral core is ready to publish independently of the unfinished
  HexRealRootsMathlib artifact and HexRCF implementation branches.

## Next step

- Rebase #8980 onto this shared infrastructure and keep only its thin
  `isolate_roots` adapter there.
- Stack the HexRCF proof-probe adapter and module matrix on the same core.

## Blockers

- None for the shared core.
