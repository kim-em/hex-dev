# Symbolic determinant certificate experiment

This experiment measures the certificate-only implementation at commit
`7b04a0450d5643381f3651b645d1ea5a22c39f32` before the small closed-form route
and the relocation to HexPolyDetMathlib. Its result does not describe the
shipping implementation. The full raw record is
[hex-symbolic-det-before-migration.json.gz](bench-results/hex-symbolic-det-before-migration.json.gz).

The fixed schedule completed all 732 arm samples (61 cases, six samples per
arm) and ten attribution profiles. Sources were unchanged and the initial
repository and dependency checkouts were clean. The manifest, source hashes,
CPU lease/topology, host observations, compiler output and failed samples
are retained in the record. There were 49 Mathlib and 53 Hex candidate
timeouts. No completed run was removed and no replacement run was taken.

The strict shipping bar was not met. Among cases with six completed samples
in both arms, Hex was faster only on N8K4D1S1. The closed-algebraic zero
target is a scope probe: both tactics fail to use the relation α² = 2
between independent atoms; the successful probe theorem verifies that failure.

The separate [pilot](bench-results/hex-symbolic-det-pilot.json.gz) is a
diagnostic subset with dirty provenance and is excluded from this experiment.
These datasets and the revised implementation sweep are separate experiments;
they are not an adjacent paired before/after comparison.

## Method and medians

Each fresh proof module is paired with its own import-only baseline, using
the unmodified pinned Mathlib `norm_det` plus residual `ring` against `det`.
Six trial-major rounds rotate the cases and alternate arm and baseline order.
The per-build ceiling is 45 seconds. A median is reported only with all six
successful samples. Values are median proof-minus-baseline wall times in ms;
negative baseline-subtracted observations, if any, remain in the raw data.
Host: chungus2, AMD EPYC 9455, Lean 4.34.0-rc2, automatically leased CPU 82.

| Case | Mathlib ms | Hex ms | Mathlib / Hex | Completed M/H |
|---|---:|---:|---:|---:|
| N2K1D1S1 | 41.14 | 148.83 | 0.276 | 6/6 |
| N2K1D2S1 | 85.09 | 132.98 | 0.640 | 6/6 |
| N2K1D4S1 | 15.58 | 164.44 | 0.095 | 6/6 |
| N2K1D4S4 | 151.48 | 398.22 | 0.380 | 6/6 |
| N2K2D1S1 | 6.57 | 143.06 | 0.046 | 6/6 |
| N2K2D2S1 | 48.08 | 184.23 | 0.261 | 6/6 |
| N2K2D2S4 | 102.98 | 383.91 | 0.268 | 6/6 |
| N2K2D4S1 | 85.84 | 173.26 | 0.495 | 6/6 |
| N2K2D4S4 | 199.98 | 476.30 | 0.420 | 6/6 |
| N2K4D1S1 | 2.75 | 140.75 | 0.020 | 6/6 |
| N2K4D1S4 | 99.01 | 369.45 | 0.268 | 6/6 |
| N2K4D2S1 | 46.19 | 184.05 | 0.251 | 6/6 |
| N2K4D2S4 | 138.71 | 407.34 | 0.341 | 6/6 |
| N2K4D4S1 | 50.22 | 134.26 | 0.374 | 6/6 |
| N2K4D4S4 | 182.12 | 395.08 | 0.461 | 6/6 |
| N2K4D4S16 | 2852.86 | 4682.87 | 0.609 | 6/6 |
| N4K1D1S1 | 97.24 | 295.12 | 0.329 | 6/6 |
| N4K1D2S1 | 283.16 | 501.14 | 0.565 | 6/6 |
| N4K1D4S1 | 196.33 | 495.97 | 0.396 | 6/6 |
| N4K1D4S4 | 1192.45 | 2200.02 | 0.542 | 6/6 |
| N4K2D1S1 | 149.62 | 293.60 | 0.510 | 6/6 |
| N4K2D2S1 | 289.81 | 490.73 | 0.591 | 6/6 |
| N4K2D2S4 | 1099.10 | 2527.85 | 0.435 | 6/6 |
| N4K2D4S1 | 286.17 | 485.89 | 0.589 | 6/6 |
| N4K2D4S4 | 2051.53 | 4300.53 | 0.477 | 6/6 |
| N4K4D1S1 | 146.60 | 319.11 | 0.459 | 6/6 |
| N4K4D1S4 | 692.66 | 2085.62 | 0.332 | 6/6 |
| N4K4D2S1 | 289.15 | 486.75 | 0.594 | 6/6 |
| N4K4D2S4 | 2158.41 | 5048.89 | 0.428 | 6/6 |
| N4K4D4S1 | 248.53 | 481.37 | 0.516 | 6/6 |
| N4K4D4S4 | 2245.49 | 5148.88 | 0.436 | 6/6 |
| N4K4D4S16 | timeout | timeout | — | 0/0 |
| N8K1D1S1 | 665.80 | 1417.25 | 0.470 | 6/6 |
| N8K1D2S1 | 2694.78 | 3489.95 | 0.772 | 6/6 |
| N8K1D4S1 | 2685.87 | 3502.21 | 0.767 | 6/6 |
| N8K1D4S4 | timeout | timeout | — | 5/1 |
| N8K2D1S1 | 1061.05 | 1477.73 | 0.718 | 6/6 |
| N8K2D2S1 | 3046.26 | 3551.58 | 0.858 | 6/6 |
| N8K2D2S4 | timeout | timeout | — | 0/0 |
| N8K2D4S1 | 3040.51 | 3540.58 | 0.859 | 6/6 |
| N8K2D4S4 | timeout | timeout | — | 0/0 |
| N8K4D1S1 | 2097.23 | 1581.64 | 1.326 | 6/6 |
| N8K4D1S4 | timeout | timeout | — | 0/0 |
| N8K4D2S1 | 4147.20 | 4310.27 | 0.962 | 6/6 |
| N8K4D2S4 | timeout | timeout | — | 0/0 |
| N8K4D4S1 | 4091.61 | 4191.50 | 0.976 | 6/6 |
| N8K4D4S4 | timeout | timeout | — | 0/0 |
| N8K4D4S16 | timeout | timeout | — | 0/0 |
| Rational2 | 101.84 | 408.32 | 0.249 | 6/6 |
| Singular2 | 85.24 | 98.51 | 0.865 | 6/6 |
| Algebraic2 | 1.77 | 194.41 | 0.009 | 6/6 |
| Rational4 | 2198.07 | 2680.76 | 0.820 | 6/6 |
| Singular4 | 93.69 | 286.54 | 0.327 | 6/6 |
| Algebraic4 | 104.65 | 282.88 | 0.370 | 6/6 |
| Rational8 | timeout | timeout | — | 0/0 |
| Singular8 | 914.17 | 1377.34 | 0.664 | 6/6 |
| Algebraic8 | 216.96 | 954.86 | 0.227 | 6/6 |
| Swaps | 7.05 | 184.98 | 0.038 | 6/6 |
| Tridiagonal | 86.46 | 204.71 | 0.422 | 6/6 |
| AlgebraicScope | 24.73 | 175.88 | 0.141 | 6/6 |
| Valuation | 48.55 | 122.57 | 0.396 | 6/6 |

The raw profiles retain reification, producer, list conversion, compiled
self-check, entry identification, synchronous auxiliary kernel check and total
elaboration separately, together with certificate size, minor support/degree,
coefficient bits and proof-node traces. They also retain the full kernel
type-checking profile; the auxiliary check alone is not the entire proof cost.
Expanded minor support causes the dense high-degree cases to exceed the
ceiling in both arms; these observations remain in the comparison.
