# Recursive Relift Findings

The prior prototype timings in this report were retired during the
2026-07-29 refresh because they described older code paths. The current
production performance evidence is:

- public factorization at split-family rung 24: 1.817 ms;
- fallback probe at rung 24: 1.556 ms;
- fast-path `(degree,height,precision,local factors)=(8,32,128,8)`:
  1.554 ms;
- fixed `SD_3` lattice factorization: 1.624 ms;
- fixed `SD_4` lattice factorization: 29.573 ms.

All values cover the exact-exponent/factor-only implementation over base
revision `b4b3675472f58958c9c2f9b2ab2f7aae16c3dc62`, measured on `chungus2`
with CPU 0 pinned. The dirty-worktree marker records that the runtime patch
and reports were pending over that base.

The raw data is under `reports/bench-results/`:

- `hex-berlekamp-zassenhaus-parametric-b4b36754-exact-factor-only-overlay-chungus2.json`;
- `hex-berlekamp-zassenhaus-fixed-b4b36754-exact-factor-only-overlay-chungus2.json`.

The active dispatcher and lattice seam are summarized in
`bz-classical-spike-findings.md`. Historical recursive-relift prototype
results remain available through git history, not as current report claims.
