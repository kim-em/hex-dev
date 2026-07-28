# Recursive Relift Findings

The prior prototype timings in this report were retired during the
2026-07-28 refresh because they described older code paths. The current
production performance evidence is:

- public factorization at split-family rung 24: 2.254 ms;
- fallback probe at rung 24: 3.042 ms;
- fast-path `(degree,height,precision,local factors)=(8,32,128,8)`:
  3.284 ms;
- fixed `SD_3` lattice factorization: 2.596 ms;
- fixed `SD_4` lattice factorization: 34.266 ms.

All values are at revision `5c371a5abb85ca6ef6510ec60888f3048db71719`,
measured on `chungus2` with CPU 0 pinned. The raw data is in:

- `reports/bench-results/hex-berlekamp-zassenhaus-parametric-5c371a5a-chungus2.json`;
- `reports/bench-results/hex-berlekamp-zassenhaus-fixed-5c371a5a-chungus2.json`.

The active dispatcher and lattice seam are summarized in
`bz-classical-spike-findings.md`. Historical recursive-relift prototype
results remain available through git history, not as current report claims.
