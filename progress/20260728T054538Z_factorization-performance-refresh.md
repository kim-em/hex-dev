# Polynomial factorization performance refresh

## Accomplished

- Audited the factorization performance reports, exports, plots, corpus hash,
  benchmark registrations, and available external comparator dependencies.
- Repaired eight BZ canonical-fixture registrations: replaced scientifically
  invalid one-point parametric ladders with fixed opaque-IO benchmarks so the
  compiler cannot fold them to nanosecond constants.
- Rebuilt and verified the HexBerlekamp, HexPolyFp, HexHensel, and
  HexBerlekampZassenhaus benchmark suites.
- Recorded current parametric and fixed artifacts at revision
  `5c371a5abb85ca6ef6510ec60888f3048db71719` on `chungus2`, including
  python-flint 0.9.0 comparator ladders.
- Ran the complete 392-row native and FLINT factorization sweeps with a
  10-second cutoff and no early termination. All answering systems agreed.
- Ran the four-case kernel/tactic/Rabin diagnostic and refreshed its plot.
- Reran the classical-product, lattice-seam, and Berlekamp phase/witness
  compiled diagnostics.
- Replaced the factorization headline and diagnostic reports with current
  results, added `reports/polynomial-factorization-performance.md`, regenerated
  every BZ corpus SVG, and removed obsolete unversioned profile CSVs.
- Removed stale timing ratios from source comments and retired the invalid
  Isabelle timing claims.
- Validation passed: all 140 relevant registered benchmarks verified,
  `scripts/check_phase4.py`, `scripts/check_dag.py`, `git diff --check`, and
  the full 9509-job `lake build`.

## Current frontier

- Current corpus frontier at 10 seconds: public 371/392, lattice 365/392,
  classical-no-decline 371/392, FLINT 391/392.
- Rabin and DDF remain substantially behind FLINT at the largest shared rungs.
- Twenty-one public/classical rows and twenty-seven lattice rows still time
  out.
- The current BZ scaling registrations complete, but their classical BHKS
  upper-bound models are too loose for the small fixtures, so the scientific
  verdicts remain inconclusive.
- Witness splitting and GCD work dominate the optimized fully split Berlekamp
  path; nullspace construction is a small share there.

## Next step

- Review and land the refreshed reports, artifacts, figures, and benchmark
  registration fix together.
- On a host with PARI/GP, NTL, Isabelle, and GHC installed, rerun those four
  external systems against the same corpus hash and merge them into the plots.
- Use the exact timeout rows in the current sweep JSON to choose the next
  public/lattice optimization targets.

## Blockers

- PARI/GP is unavailable because `gp` is not installed.
- NTL is unavailable because its headers and library are not installed.
- Isabelle comparators are unavailable because Isabelle and GHC are not
  installed.
