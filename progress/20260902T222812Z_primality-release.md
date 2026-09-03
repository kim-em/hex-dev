# hex-primality: Phase 5–7 and split publication

## Accomplished

- Audited the core and Mathlib bridge API, proofs, names, documentation, and
  trust surface; removed target-local deprecation warnings, documented the
  remaining public structure fields and theorem, and made the bridge a proper
  public module-system umbrella.
- Corrected the manual's table, trial-division, and certificate-reach claims;
  added the Mathlib correspondence and cross-references; and added standalone
  READMEs with build-checked examples for both released repositories.
- Advanced both library counters to Phase 7, added the pair and aggregate pins
  to the release graph, supplied their single-job CI workflows, and made the
  aggregate import both public umbrellas.
- Bootstrapped the two empty repositories with unmanaged Lake/toolchain
  skeletons. Live-baseline sync dry-runs validate their managed paths and
  existing cross-repository pin locations.
- Locally passed the core/bridge builds and conformance modules, all 17
  benchmark verification cases, 63 PARI/python-flint oracle cases, the
  deterministic table check, Phase-4/7 checks, the trust scan, DAG checks, and
  release-manifest/manual-split checks.
- Passed Mathlib's full `runLinter` suite on every core and bridge module. A
  fresh 17-target compiled benchmark run reproduced the committed core
  scaling verdicts and fixed-case timings, while the bridge's six-sample
  rotated fresh-module regression kept every candidate below its 10-second
  release gate (maximum 3.57 seconds).

## Current frontier

The monorepo changes passed independent Opus review with no blocking soundness
finding. Managed source has not yet been published to either mirror;
publication remains gated on a clean workflow dry-run and green PR state.

## Next step

Publish the core and bridge through the release workflow and record their
resulting `main` SHAs before merging. Updating the released aggregate's
unmanaged Lake file and umbrella is deliberately excluded by issue #9891's
no-hand-edit scope.

## Blockers

None.
