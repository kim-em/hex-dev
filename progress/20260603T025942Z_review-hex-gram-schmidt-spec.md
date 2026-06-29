# 20260603T025942Z SPEC review

## Accomplished

- Reviewed the proposed `SPEC/Libraries/hex-gram-schmidt.md` clause change for
  `scaledCoeffs`.
- Checked the local Isabelle Haskell extraction around `sigma_array` /
  `dmu_array_row`.
- Checked existing SPEC and bench references for old Bareiss-shaped wording
  that may need follow-up if the clause lands.

## Current frontier

The review is advisory only; no SPEC or Lean implementation files were changed.

## Next step

If the clause is accepted, tighten the recurrence wording with the concrete
`sigma` formula and update stale Bareiss references in the Gram-Schmidt and LLL
benchmark/spec text.

## Blockers

- None for the review.
