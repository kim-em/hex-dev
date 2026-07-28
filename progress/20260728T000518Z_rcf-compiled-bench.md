# HexRCF compiled Phase-4 benchmarks

## Accomplished

- Added the Mathlib-free `hexrcf_bench` executable with ten registered targets
  covering decision carrier degree, repeated/distinct deduplication, three
  common-root cases, separation depth, and cells/sign/formula replay.
- Kept fixture construction outside the timed regions, including accepted
  `.cells` certificate construction and checking for replay targets.
- Added structural hashes for the reflected inputs and certificate evidence so
  LeanBench's mandatory in-timer result hash measures real outputs.
- Guarded every verify input and every exact scientific schedule rung against
  failed deterministic preparation.
- Installed the executable in the existing single CI job and documented the
  concrete registration names and wall-cost models in the HexRCF SPEC.
- Validated the target build, list, verify, verify budget, Mathlib-free closure,
  27 lint unit tests, full HexRCF build, DAG, Phase-4 contract, release manifest,
  trust surface, copyright, file sizes, conformance target matrix, and diff.
- Confirmed on the dirty development host that all ten chosen schedules are
  consistent with their declared models; this is schedule diagnostics, not a
  release timing artifact or Phase-4 completion claim.
- Received an independent GO review of fixture validity, timed boundaries,
  structural-hash costs, schedules, models, and CI wiring.

## Current frontier

- The compiled benchmark implementation for directive #9011 is complete and
  stacked on the Phase-4 evidence-contract branch from #9010.
- The reusable clean-host harness and committed scientific timing artifact are
  intentionally outside this change.

## Next step

- Publish the stacked draft PR for #9011, then continue with the fresh-module
  proof-probe targets once their reusable harness dependency is available.
- Advance the extraction PR stack as each parent finishes CI and squash-merges.

## Blockers

- None for the compiled benchmark change.
- Release-quality timing evidence still depends on the dedicated-host harness
  tracked separately; no timing artifact or `done_through` update belongs here.
