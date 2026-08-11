# Issue #9155: current factorization performance prose

## Accomplished

- An independent review identified that the formerly selected `d27e0bf2` Hex
  record had a 43.976 us protocol-overhead outlier and a 1.6x to 1.8x inflated
  cyclotomic band. Retook only the Hex arm from clean `58c873ca` on
  verified-idle CPU 1; its overhead is 23.575 us and its SHA-256 is
  `3c96905dae847e634de7e20934a9074e582ce7d545294471adebf945b6c1efe9`.
- Reconciled the two public factorization reports with that Hex record and the
  unchanged external record at `aa68c920`: 383/392 Hex rows solve, the nine
  timeout names are exact, and current summary, paired, family, and
  combined-cactus numbers agree with the selected artifacts.
- Corrected CPU-affinity, early-termination, repetition, percentile, historical
  comparison, Wilkinson, hard-row, and former-crossover wording. Regeneration
  now distinguishes the early-terminated Hex arm from the full external arm and
  selects a verified-idle core.
- Added `scripts/bench/factor_sweep_table.py`, sharing the cactus reader and
  newest-per-system rule, to reproduce the summary, comparator, and Isabelle
  family tables deterministically. It refuses non-answer statuses other than
  timeouts and fails if a corpus family lacks a display name.
- Refreshed `polynomial-factorization-performance.md`, the third report that
  declares itself current, after final review found it still described the
  pre-certificate state.
- Regenerated all 25 cactus/runtime figures from the fresh Hex arm and unchanged
  external arm. Verified factor-sweep freshness, the exact combined-cactus rank
  window, default versus explicit record selection, generated-table agreement,
  Python compilation, and whitespace.
- Obtained independent numerical and prose reviews, fixed their stale current-
  tense passages, contaminated-record finding, complete-report coverage, and
  reproducibility concerns.

## Current frontier

- After #9155, the open BZ performance issues are #9151, #9152, #9153, and
  #9177. #9151 remains a plausible general inner-loop simplification; #9152 is
  a smaller but clean lifetime correction and depends on it.
- A representative counterfactual found no selected support rejected by
  #9153's retained-prime degree intersection, so production proof work is not
  justified without contrary full-corpus evidence.
- #9177 can close a narrowly defined measurement question, but even the
  favorable observed arithmetic effect projects to about 0.04% end-to-end on
  the measured `cyclo_phi385` row.

## Next step

Run #9151's current-entry measurement gate, emphasizing reducible products such
as `sd5_x_phi11` rather than certificate-short-circuited plain Swinnerton-Dyer
rows. If it clears the gate, settle the integer-modulus boundary before #9152
hoists lift-support and target-image data across subset levels.

## Blockers

None.
