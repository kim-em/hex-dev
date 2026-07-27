# RCF two-track Phase-4 contract

## Accomplished

- Defined separate Phase-4 evidence tracks for Mathlib-free compiled
  computation and Mathlib-facing elaboration, tactics, proof emission, and
  kernel replay. The compiled track retains all LeanBench, scientific verdict,
  comparator, and profiling requirements; the proof track uses externally
  timed fresh-module builds with explicit replacement evidence.
- Specified controlled HexRCF compiled ladders for carrier degree,
  deduplication, common-root batches, separation depth, and three independent
  prebuilt-certificate replay dimensions, with adjacent cost derivations.
- Added explicit manifest-owned `proof_probes` roots and HexRCF Phase-4
  comparator/input-family metadata while retaining `done_through: 3`.
- Hardened the bench lint so the proof exception is exact and component-aware,
  rejects malformed or overlapping roots and symlink escapes, scans forbidden
  behavior through each probe's repository-local import closure, and rejects
  missing or empty reservations once a library claims Phase 4.
- Added adversarial regression coverage. All 27 lint tests, the real bench
  lint, `lake build HexRCF`, DAG, Phase-4, release-manifest, trust-surface,
  copyright, source-line-count, conformance-matrix, Python compilation, and
  diff checks pass. An independent Sol architecture audit returned GO.

## Current frontier

Issue #9008 is implemented on a branch stacked above the Mathlib-free
DecisionCheck extraction. This change establishes the structural contract and
controlled families only; it deliberately records no scientific measurements
and makes no Phase-4 completion claim.

## Next step

Publish the stacked contract PR, then implement `bench/HexRCF/Bench.lean` and
the fresh-module `bench/HexRCF/ProofProbe/` variants against this contract.
Rebase and promote the extraction PR chain one parent at a time as each parent
lands.

## Blockers

Scientific proof/tactic timing remains gated on the HexRealRootsMathlib
Phase-4 prerequisite and a clean, quiescent dedicated host. The structural
contract itself has no blocker; its PR remains stacked until the extraction
chain merges.
