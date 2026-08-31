# HexPolyFp Performance Report

Current at revision `f1ab9696cee5fac0cb8ea17bfdfd19caf63bd7c3`,
measured 2026-07-29 on `chungus2` (AMD EPYC 9455, Linux x86-64), pinned to
CPU 0.

The export records a clean worktree. It includes the exact inverse-cached
finite-field remainder/GCD worker used by Berlekamp splitting and BZ prime
selection; all eight ladders were refreshed rather than mixing revisions.

## Verdicts

| Target | Model | Largest rung | Median | Verdict |
|---|---|---:|---:|---|
| Frobenius `X` mod | `n³` | 80 | 297.287 ms | inconclusive |
| GCD | `n²` | 256 | 43.570 µs | inconclusive; observed faster |
| Weighted product | `n²` | 4096 | 668.277 ms | consistent |
| Square-free decomposition | `n²` | 768 | 6.492 ms | consistent |
| Frobenius power mod | `n³` | 64 | 337.743 ms | consistent |
| Power mod monic | `n² log n` | 512 | 147.076 ms | consistent |
| Division mod | `n²` | 256 | 998.410 µs | consistent |
| Modular composition | `n³` | 192 | 376.752 ms | consistent |

Raw export:
`reports/bench-results/hex-poly-fp-f1ab9696-gcd-hensel-chungus2.json`
(SHA-256
`fcb72f342a3edb09cce09214101182765b9037e4ba12f46ea14e32360e8265c3`).
`list` and `verify` passed.

The current medians remain close to the preceding record. GCD improves by 3.4%
at the degree-256 rung; unrelated rows move by at most 4.0%, consistent with
same-host measurement variation rather than a broad substrate regression.

## Comparator and Profile

No external comparator is declared for this headline suite. FLINT comparisons
for factorization layers are documented in the HexBerlekamp, HexHensel, and
cross-system sweep reports. The timing ladders directly cover the input
families `quotient-powers`, `modular-composition`, and `product-squarefree`;
no sampling trace was collected.

## Concerns

- [#9809](https://github.com/kim-em/hex-dev/issues/9809) tracks the two
  inconclusive registrations and missing profile evidence.
- The GCD declaration remains deliberately conservative; observed scaling is
  faster than `n²`.
- Frobenius `X` remains inconclusive; division and modular composition are
  consistent in the replacement run.
- Modular composition and Frobenius powering remain the largest substrate
  costs in these representative upper rungs.
