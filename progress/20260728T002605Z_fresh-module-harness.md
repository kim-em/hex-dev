# Reusable fresh-module proof harness

## Accomplished

- Extracted the HexRealRootsMathlib sweep mechanics into a reusable,
  declarative fresh-module harness.
- Recast measurements as named reference/candidate pairs so later tactic
  suites can measure phase deltas such as `Search - Input` and
  `Replay - Literal` without duplicating the runner.
- Added pair-order rotation and alternating reference/candidate orientation
  while retaining signed candidate-minus-reference deltas.
- Made theorem-axiom expectations a per-module policy and rejected measured
  modules whose transitive import closure reaches another measured module.
- Kept the HexRealRootsMathlib suite as a thin six-pair declaration over its
  existing import-only baseline.
- Expanded regression coverage from seven to fifteen tests, including exact
  target-artifact removal, pair orientation, duplicate-name rejection,
  transitive measured-module import rejection, and per-module axiom checks.
- Added the shared harness tests to the existing single CI lint step.
- Ran the complete six-pair suite once and a two-round focused pair
  diagnostically; all builds and axiom checks passed, both orientations were
  recorded, and external output paths worked. These dirty/busy-host runs are
  not release evidence and no timing artifact was committed.
- Revalidated the proof-probe/Mathlib-free lint, DAG, file-size, Python
  compilation, and diff checks.

## Current frontier

- PR #8980 now has a reusable runner shape suitable for HexRCF in addition to
  its original `isolate_roots` suite.
- Its scientific artifact, performance report, premise audit, and Phase-4
  marker remain intentionally pending.

## Next step

- Publish the harness refactor, then declare the HexRCF five-pair-per-case
  probe suite and premise-check generation of the degree-50 literal
  certificate.
- Correct the stacked Phase-4 contract wording to describe exact measured
  module invalidation over a warm dependency cache rather than whole-build
  directory isolation.

## Blockers

- No structural harness blocker.
- Release-quality measurements still require a clean, quiescent named host.
