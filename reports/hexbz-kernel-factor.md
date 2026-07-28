# HexBZ Kernel and Tactic Factorization Diagnostic

Current at revision `5c371a5abb85ca6ef6510ec60888f3048db71719`,
measured 2026-07-28 on `chungus2` (AMD EPYC 9455, Linux x86-64),
pinned to CPU 0.

## Method and Timing Labels

Each case builds a fresh Lake module for:

- direct kernel evaluation of `Hex.ZPoly.factorize` against the compiled
  factorization;
- `factor_poly` on the full integer polynomial;
- `irreducibility` for cases marked irreducible;
- identical literal Rabin certificates replayed through the linear and
  incremental checkers when multi-prime witness data exists.

Times are end-to-end fresh-module wall times, not kernel-only times. They
include imports, elaboration, certificate search where applicable, and kernel
checking. The median import baselines were:

- factorization entry points: 1.212 s;
- certificate umbrella: 4.624 s.

## Validation Sample

| Case | Degree | Direct kernel | `factor_poly` | `irreducibility` | Witness class |
|---|---:|---:|---:|---:|---|
| `quartic_a4` | 4 | 2.347 s | 4.912 s | 4.513 s | multi-prime |
| `cyclo_phi5` | 4 | 1.422 s | 3.712 s | 3.690 s | free mod `p` |
| `xpow6_minus1` | 6 | 2.342 s | 3.654 s | not applicable | mixed free |
| `sd2` | 4 | 1.929 s | provider decline | provider decline | provider decline |

All expected successes completed inside the 30-second module cutoff.
`factor_poly` and `irreducibility` declining `sd2` is a provider-boundary
result, not a timeout or unexpected error.

## Linear Versus Incremental Rabin Replay

`quartic_a4` produced four literal certificate cases. Median fresh-module
times:

| Prime | Degree | Linear | Incremental |
|---:|---:|---:|---:|
| 17 | 2 | 4.861 s | 3.572 s |
| 17 | 2 | 5.033 s | 3.760 s |
| 5 | 1 | 3.608 s | 3.659 s |
| 5 | 3 | 4.465 s | 3.942 s |

The signed import-baseline deltas and all three samples per checker are in the
raw artifact. Negative deltas are valid measurement noise around the large
certificate-import baseline.

## Artifact

`reports/bench-results/hexbz-kernel-factor-5c371a5a-chungus2.json`
(SHA-256
`57f86afaaafefbff1e74b131375cd3784f5d31f3bef6db87084947eab038d04d`).
The artifact reports zero unexpected errors.

## Reproducing

```sh
taskset -c 0 python3 scripts/bench/kernel_factor_sweep.py \
  --name cyclo_phi5 --name xpow6_minus1 \
  --name quartic_a4 --name sd2 \
  --timeout 30 --rabin-repeats 3 \
  --output reports/bench-results/hexbz-kernel-factor-5c371a5a-chungus2.json
```
