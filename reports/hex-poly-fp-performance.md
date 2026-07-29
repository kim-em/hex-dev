# HexPolyFp Performance Report

Current at revision `a1fdbd81ef038faa41765fb39a79cd083109c8ed`,
measured 2026-07-29 on `chungus2` (AMD EPYC 9455, Linux x86-64), pinned to
CPU 0.

The export records a dirty worktree because the ownership fix, fresh artifacts,
and reports were pending together. A preceding anomalous run was discarded
after an A/B/A control against `origin/main` showed matching fixed/main/fixed
upper rungs; this table is the replacement three-trial record.

## Verdicts

| Target | Model | Largest rung | Median | Verdict |
|---|---|---:|---:|---|
| Frobenius `X` mod | `n³` | 80 | 297.714 ms | inconclusive |
| GCD | `n²` | 256 | 45.104 µs | inconclusive; observed faster |
| Weighted product | `n²` | 4096 | 659.711 ms | consistent |
| Square-free decomposition | `n²` | 768 | 6.569 ms | consistent |
| Frobenius power mod | `n³` | 64 | 339.451 ms | consistent |
| Power mod monic | `n² log n` | 512 | 148.786 ms | consistent |
| Division mod | `n²` | 256 | 960.070 µs | consistent |
| Modular composition | `n³` | 192 | 372.371 ms | consistent |

Raw export:
`reports/bench-results/hex-poly-fp-a1fdbd81-chungus2.json` (SHA-256
`6a6c16c7074b13d6301a4e48ba49274745ea0b3c4f5a80f3a28451461131c4b5`).
`list` and `verify` passed.

The replacement medians are close to the preceding record and show no
systematic regression from the factorization changes. Isolated trials still
show host interference at a few rungs, which is why the report uses the median
of three outer trials.

## Comparator and Profile

No external comparator is declared for this headline suite. FLINT comparisons
for factorization layers are documented in the HexBerlekamp, HexHensel, and
cross-system sweep reports. The timing ladders directly cover the input
families `quotient-powers`, `modular-composition`, and `product-squarefree`;
no sampling trace was collected.

## Concerns

- The GCD declaration remains deliberately conservative; observed scaling is
  faster than `n²`.
- Frobenius `X` remains inconclusive; division and modular composition are
  consistent in the replacement run.
- Modular composition and Frobenius powering remain the largest substrate
  costs in these representative upper rungs.
