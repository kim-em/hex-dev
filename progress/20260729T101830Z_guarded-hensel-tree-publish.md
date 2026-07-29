# Guarded multifactor Hensel tree publication

## Accomplished

- Regenerated all cross-system BZ figures from the clean three-service Hex
  sweep at `53bb12e2`, while retaining the already-current FLINT, PARI/GP, NTL,
  and Isabelle exports unchanged.
- Updated the factor-sweep, aggregate polynomial-factorization, BZ performance,
  and Isabelle investigation reports to the final guarded-tree measurements.
- Confirmed the current artifact checksum and clean-worktree metadata; all three
  Hex services agree on every common result.
- Completed the final full `lake build` (9,629 jobs), Hensel benchmark verify
  (69 registrations), BZ benchmark verify (16 registrations), published trust
  audit (369 files), DAG check, Mathlib-free bench lint (25 executables and 33
  proof probes), SVG parse check, and diff hygiene check.

## Current frontier

Public Hex solves 373/392 rows with a 420.153 microsecond median and 5.302 ms
p90. Against verified Isabelle BZ, 238 overhead-eligible pairs have a 0.909x
Hex/Isabelle median; Hex wins 127 rows and Isabelle 111. The lead survives both
the preceding lower Hex floor (0.892x) and the common larger floor (0.916x), but
Chebyshev and Legendre still favour Isabelle at 2.05x and 1.85x family medians.
No-decline classical retains a small 0.9% paired-median advantage on ordinary
rows, while public has selected hard-row wins and the additional `sd6` solve.

## Next step

Commit and publish the refreshed reports and figures, merge after CI, then
continue profiling the remaining Chebyshev, Legendre, and Swinnerton-Dyer gaps.

## Blockers

None.
