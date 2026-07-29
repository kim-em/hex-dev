# HexBZ Kernel and Tactic Factorization Diagnostic

Current at revision `a1fdbd81ef038faa41765fb39a79cd083109c8ed`,
measured 2026-07-29 on `chungus2` (AMD EPYC 9455, Linux x86-64), pinned to
CPU 0.

Each case builds a fresh Lake module for direct kernel evaluation of
`Hex.ZPoly.factorize`, `factor_poly`, applicable `irreducibility` calls, and
linear/incremental replay of identical literal Rabin certificates. These are
end-to-end fresh-module wall times, including import, elaboration, search, and
kernel checking—not kernel-only times.

Median import baselines were 877.587 ms for factorization entry points and
6.243 s for the certificate umbrella.

## Validation Sample

| Case | Degree | Direct kernel | `factor_poly` | `irreducibility` | Witness class |
|---|---:|---:|---:|---:|---|
| `quartic_a4` | 4 | 1.316 s | 6.652 s | 6.695 s | multi-prime |
| `cyclo_phi5` | 4 | 1.058 s | 6.273 s | 6.294 s | free mod `p` |
| `xpow6_minus1` | 6 | 1.614 s | 6.270 s | not applicable | mixed free |
| `sd2` | 4 | 1.195 s | provider decline | provider decline | provider decline |

All expected successes completed inside the 30-second module cutoff and the
artifact reports zero unexpected errors. The `sd2` declines are explicit
provider-boundary results, not timeouts.

The preceding record had 1.212 s and 4.624 s import baselines. The direct
Mathlib-free path therefore improves substantially, while the certificate
umbrella and tactic totals regress by roughly 35%. This refresh does not hide
that regression: the runtime factorizer optimization and the tactic import
cone move in opposite directions and need separate interpretation.

## Linear Versus Incremental Rabin Replay

| Prime | Degree | Linear | Incremental |
|---:|---:|---:|---:|
| 17 | 2 | 7.234 s | 6.302 s |
| 17 | 2 | 7.260 s | 6.332 s |
| 5 | 1 | 6.254 s | 6.263 s |
| 5 | 3 | 6.737 s | 6.314 s |

The incremental checker is faster in three of four medians. The degree-one
difference is below the noise implied by the large import baseline. Signed
baseline deltas and all samples are in the raw artifact.

## Artifact

`reports/bench-results/hexbz-kernel-factor-a1fdbd81-chungus2.json`
(SHA-256
`3da0b31b102609fbb2ed6a16deb9bdb0ecb17da2ab73c4cc9fb1b8a4d5b5acc3`).

The export records a dirty worktree because the borrowed-argument ownership
fix and refreshed evidence were pending commit. Its full hash identifies the
implementation base; direct execution includes that ownership fix.

## Reproducing

```sh
taskset -c 0 python3 scripts/bench/kernel_factor_sweep.py \
  --name cyclo_phi5 --name xpow6_minus1 \
  --name quartic_a4 --name sd2 \
  --timeout 30 --rabin-repeats 3 \
  --output reports/bench-results/hexbz-kernel-factor-a1fdbd81-chungus2.json
```
