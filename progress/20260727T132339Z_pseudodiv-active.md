# Pseudo-division active recurrence

## Accomplished

- Proved that the completed pseudo-division active array has exactly the
  requested length and that every entry satisfies its creation-time
  cancellation recurrence after later entries have been appended.
- Incorporated the completed independent review of the index-kernel PR. The
  review found no merge blocker; its concrete API feedback led to generic
  quotient/remainder size bounds, weaker assumptions on the remainder
  coefficient lemma, non-shadowing builder names, and a less brittle power
  table base case.
- Removed hypotheses that were irrelevant to the structural quotient bound
  and removed lightweight-ring assumptions from both structural output-size
  theorems.
- Built `HexResultant`, `HexConformance`, and `HexManual`; verified all four
  Resultant benchmarks; and passed Phase 4, DAG, copyright, line-count,
  forbidden-token, and diff checks.

## Current frontier

- The low-coefficient reconstruction case is supported by the bounded
  convolution theorem and the remainder coefficient formula.
- The active recurrence is now available for the high-coefficient case. The
  remaining hard lemma reverses the quotient convolution index and factors
  the leading-coefficient power so it matches that recurrence.
- The independent review of the bounded-convolution PR is still running in
  the background and has not delayed this milestone.

## Next step

- Publish this active-recurrence milestone as a stacked draft PR.
- Prove the high-coefficient convolution reindexing/factorization, then use
  the low and high coefficient cases to close
  `pseudoDivMod_reconstruct_core`.

## Blockers

- No known implementation blocker; the remaining proof is a substantial
  finite-sum reindexing argument.
