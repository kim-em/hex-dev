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
  skeletons. Live-baseline sync dry-runs validate every managed path and pin.
- Locally passed the core/bridge builds and conformance modules, all 17
  benchmark verification cases, 63 PARI/python-flint oracle cases, the
  deterministic table check, Phase-4/7 checks, the trust scan, DAG checks, and
  release-manifest/manual-split checks.

## Current frontier

The monorepo changes are ready for full CI and independent review. Managed
source has not yet been published to either mirror; publication remains gated
on a clean workflow dry-run and green PR state.

## Next step

Open the PR, run the independent Opus review while CI executes, address any
findings, then publish the core, bridge, and aggregate pins through the release
workflow and record the resulting `main` SHAs before merging.

## Blockers

None.
