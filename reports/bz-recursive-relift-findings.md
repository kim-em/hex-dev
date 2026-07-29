# Recursive Relift Findings

The prior prototype timings in this report were retired during the
2026-07-29 refresh because they described older code paths. The current
production performance evidence is:

- public factorization at split-family rung 24: 2.261 ms;
- fallback probe at rung 24: 1.950 ms;
- fast-path `(degree,height,precision,local factors)=(8,32,128,8)`:
  1.669 ms;
- fixed `SD_3` lattice factorization: 1.613 ms;
- fixed `SD_4` lattice factorization: 29.580 ms.

All values are at revision `a1fdbd81ef038faa41765fb39a79cd083109c8ed`,
measured on `chungus2` with CPU 0 pinned.
The exports identify the full measured implementation revision above.

The raw data is in:

- `reports/bench-results/hex-berlekamp-zassenhaus-parametric-a1fdbd81-chungus2.json`;
- `reports/bench-results/hex-berlekamp-zassenhaus-fixed-a1fdbd81-chungus2.json`.

The active dispatcher and lattice seam are summarized in
`bz-classical-spike-findings.md`. Historical recursive-relift prototype
results remain available through git history, not as current report claims.
