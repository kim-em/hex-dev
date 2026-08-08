# Recombination cache benchmark and publication

## Accomplished

- Recorded a clean, CPU-pinned 392-row public/classical factorization sweep at
  `b0150d2b`; every returned factor-degree multiset passed the corpus oracle.
- Confirmed a 0.988× eligible-row median versus the preceding Hex sweep, with
  `sd5` improving from 89.008 ms to 39.730 ms and its shifted variants improving
  by 2.6×–2.7×.
- Updated the cross-system reports: public Hex now has a 0.866× eligible-row
  median versus verified Isabelle BZ, with 136 Hex wins and 99 Isabelle wins.
- Regenerated all 25 factorization figures from the new Hex rows and the
  unchanged current lattice, FLINT, PARI/GP, NTL, and Isabelle exports.
- Re-ran repository metadata, trust-surface, DAG, line-count, copyright, JSON
  cross-check, and whitespace validation successfully.

## Current frontier

The implementation and durable performance evidence are ready for publication.
The optimization is neutral on the broad corpus and concentrated on expensive
classical subset recombination; it leaves the 392-row solve frontier unchanged.

## Next step

Publish the branch, run the merge-gating CI, address any review findings, and
merge the pull request.

## Blockers

None.
