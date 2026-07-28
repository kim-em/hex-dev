# Polynomial factorization comparator refresh

## Accomplished

- Provisioned transient Nix environments for PARI/GP 2.17.3 with cypari2
  2.2.4, NTL 11.6.0, Isabelle2025-2, AFP 2026-05-29, and GHC 9.10.3.
- Recorded exhaustive, CPU-0-pinned, 10-second-cutoff sweeps over all 392
  committed factorization cases for the previously stale external systems:
  PARI/GP 391/392, NTL 391/392, verified Isabelle BZ 371/392, and verified
  Isabelle LLL 314/392.
- Kept the already-current Hex and FLINT sweeps intact, merged all six current
  artifacts for reporting, and regenerated the 25 factor-sweep figures.
- Updated the consolidated factorization report, the BZ headline report, the
  cross-system sweep report, and the Isabelle investigation with current
  provenance, frontiers, ratios, and timeout-selection caveats.
- Audited the six sweep artifacts for one corpus hash, 392 rows per system,
  exhaustive cutoff configuration, clean cross-checks, and documented file
  hashes.
- Re-ran `lake build`, `scripts/check_phase4.py`, `scripts/check_dag.py`, and
  `git diff --check`; all passed.

## Current frontier

The complete refresh is ready to commit and publish. Measurements remain
commit-pinned to `5c371a5abb85ca6ef6510ec60888f3048db71719`; subsequent `main`
changes include factorization naming/documentation work and a bounded
primality-check optimization but do not alter the measured factorization
dispatcher or corpus protocol.

## Next step

Commit the evidence package, rebase its source-level benchmark repair over
current `main`, open the PR, run the requested independent second-opinion
review, address verified findings, and merge after precise CI inspection.

## Blockers

None.
