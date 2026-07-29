# HexBZ Kernel and Tactic Factorization Diagnostic

Current at revision `8c4acebc5fc04bd52b7ec2f6fa15c4f2eb4c6ece`,
measured 2026-07-29 on `chungus2` (AMD EPYC 9455, Linux x86-64), pinned to
CPU 0.

Each case builds a fresh Lake module for direct kernel evaluation of
`Hex.ZPoly.factorize`, `factor_poly`, applicable `irreducibility` calls, and
linear/incremental replay of identical literal Rabin certificates. These are
end-to-end fresh-module wall times, including import, elaboration, search, and
kernel checking—not kernel-only times.

Median import baselines were 897.900 ms for factorization entry points and
6.407 s for the certificate umbrella.

## Validation Sample

| Case | Degree | Direct kernel | `factor_poly` | `irreducibility` | Witness class |
|---|---:|---:|---:|---:|---|
| `quartic_a4` | 4 | 1.343 s | 6.916 s | 6.892 s | multi-prime |
| `cyclo_phi5` | 4 | 1.078 s | 6.571 s | 6.596 s | free mod `p` |
| `xpow6_minus1` | 6 | 1.694 s | 6.487 s | not applicable | mixed free |
| `sd2` | 4 | 1.246 s | provider decline | provider decline | provider decline |

All expected successes completed inside the 30-second module cutoff and the
artifact reports zero unexpected errors. The `sd2` declines are explicit
provider-boundary results, not timeouts.

Against the immediately preceding export, the two import baselines rise by
2.3% and 2.6%, and the successful end-to-end cases drift upward by 2–5%. These
fresh-module one-shot differences are small enough that the new selector guard
shows no visible kernel-level discontinuity.

## Linear Versus Incremental Rabin Replay

| Prime | Degree | Linear | Incremental |
|---:|---:|---:|---:|
| 17 | 2 | 8.756 s | 6.560 s |
| 17 | 2 | 10.193 s | 7.844 s |
| 5 | 1 | 6.917 s | 6.755 s |
| 5 | 3 | 7.016 s | 6.580 s |

The incremental checker is faster in all four medians. Signed baseline deltas
and all samples are in the raw artifact.

## Artifact

`reports/bench-results/hexbz-kernel-factor-8c4acebc-chungus2.json`
(SHA-256
`0b2105264881c692ac5c91a8febf6d9f5d9a5a23170b01e525af6eadc27ebb97`).

The export records a clean worktree.

## Reproducing

```sh
taskset -c 0 python3 scripts/bench/kernel_factor_sweep.py \
  --name cyclo_phi5 --name xpow6_minus1 \
  --name quartic_a4 --name sd2 \
  --timeout 30 --rabin-repeats 3 \
  --output reports/bench-results/hexbz-kernel-factor-8c4acebc-chungus2.json
```
