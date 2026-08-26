# Polynomial factorization performance review follow-up

## Accomplished

- Addressed both independent Claude Opus review passes on PR #9047.
- Recovered and committed the already-recorded Berlekamp/profile and
  classical/lattice spike stdout without rerunning measurements; verified the
  profile stdout line-for-line against the original session capture and pinned
  both artifacts by SHA-256.
- Corrected cross-system ratio reporting to exclude rows below a ten-times
  protocol-overhead signal floor, documented the `SD_5`/`SD_6` dispatcher seam,
  restored chart links, and made dirty-worktree provenance explicit throughout
  the refreshed reports.
- Fixed the cactus plotter's default record selection to use only the current
  corpus hash and made future factor-sweep exports retain factor-degree
  multisets for post-hoc differential checks.
- Added expected hashes for all eight repaired fixed BZ benchmarks and added
  the four report-driving diagnostic executables to the existing single CI job.
- Preserved the unrelated Strassen base-kernel measurement note after the
  second reviewer identified its removal as out of scope.
- Verified `lake build` (9553 jobs), all 16 BZ smoke benchmarks, the four
  diagnostic executable targets, plot regeneration (25 figures),
  `check_benches_mathlib_free.py`, `check_phase4.py`, `check_dag.py`, Python
  syntax, factor-degree serialization, and `git diff --check`.

## Current frontier

The performance evidence is internally consistent and traceable. Current
PARI/GP, NTL, verified Isabelle BZ, and verified Isabelle LLL records cover the
same 392-row corpus as the refreshed Hex and FLINT records. PR #9047 needs its
review-fix commit rebased over the latest `origin/main`, pushed, and allowed to
clear merge-gating CI.

## Next step

Commit this review follow-up, rebase on the current main tip, rerun integration
checks, push PR #9047, inspect the underlying Actions job state/logs, and merge
with squash once green.

## Blockers

None.
