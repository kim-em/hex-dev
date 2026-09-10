# Characteristic-polynomial carrier performance

## Comparator ratios

The six symbolic carrier families compare Hex's instrumented Berkowitz
recurrence with SymPy 1.14.0 `DomainMatrix.det()` (Bareiss) on the identical
`tI − A`. These ratios are informational. The existing integer FLINT/PARI
registrations are outside this carrier measurement.

Measurements used Lean 4.34.0-rc2, lean-bench, Python 3.14.6 and SymPy’s
FLINT ground backend (python-flint 0.9.0) on an AMD EPYC 9455 shared
host, pinned to automatically selected logical CPU 32. Initial load averages
were 32.12, 12.59, and 5.67; other work, including a full repository build,
continued during the measurements. Every completed sample is retained.

Each point is a separate `setup_fixed_benchmark`, with five measured repeats,
a discarded warmup, and `warmupFirstIter := true`. The harness auto-tunes inner
repeats to its 1 ms fixed-benchmark floor. Hex/SymPy argument order alternates
across consecutive points. The external Python process persists within each
child batch; import and startup happen before measurement.

The trivial persistent request (`carrierNoop`, returning `[]`) took a median
**6.013 µs**. Raw ratios are SymPy/Hex; adjusted ratios are
`(SymPy − 6.013 µs) / Hex`. This subtraction removes the measured
fixed request overhead, not input-dependent JSON encoding, decoding or domain
construction. Both arms construct the same deterministic input during their
calls. Hex timings include observing structural growth in every Toeplitz column
and intermediate coefficient vector, and serializing the full polynomial.
SymPy timings include request serialization, canonical-input checks, exact-domain
construction, the determinant, and response serialization. These are integration
latencies, not isolated arithmetic-kernel timings.

All 30 pairs agree on hashes of the entire canonical coefficient array. The
separate growth run also compares each instrumented recurrence with public
`Matrix.charPoly`, without charging that duplicate computation to the timing.

The parameter is entry degree for DenseInt/DenseRat/DenseMod/RatFn and entry
term count for MvInt/MvRat. Multivariate entries have arity three and fixed
total degree five. Peak is maximum dense array length, multivariate term count,
or sum of reduced numerator and monic denominator array lengths, respectively.

| Carrier | n | Parameter | Peak | Hex µs | SymPy µs | Raw ratio | Adjusted ratio |
|---|---:|---:|---:|---:|---:|---:|---:|
| DenseInt | 2 | 1 | 3 | 2.71 | 175.44 | 64.62 | 62.41 |
| DenseInt | 3 | 1 | 4 | 6.57 | 612.90 | 93.34 | 92.43 |
| DenseInt | 3 | 2 | 7 | 9.43 | 731.78 | 77.59 | 76.96 |
| DenseInt | 3 | 3 | 10 | 11.56 | 881.33 | 76.27 | 75.75 |
| DenseInt | 4 | 1 | 5 | 15.63 | 1837.83 | 117.61 | 117.22 |
| DenseMod | 2 | 1 | 3 | 6.24 | 191.22 | 30.63 | 29.67 |
| DenseMod | 3 | 1 | 4 | 8.89 | 649.74 | 73.07 | 72.39 |
| DenseMod | 3 | 2 | 7 | 12.06 | 784.88 | 65.08 | 64.58 |
| DenseMod | 3 | 3 | 10 | 16.40 | 1012.12 | 61.72 | 61.35 |
| DenseMod | 4 | 1 | 5 | 20.41 | 1827.46 | 89.52 | 89.22 |
| DenseRat | 2 | 1 | 3 | 11.51 | 215.39 | 18.71 | 18.19 |
| DenseRat | 3 | 1 | 4 | 40.27 | 777.81 | 19.31 | 19.16 |
| DenseRat | 3 | 2 | 7 | 124.30 | 1575.88 | 12.68 | 12.63 |
| DenseRat | 3 | 3 | 10 | 192.43 | 1931.12 | 10.04 | 10.00 |
| DenseRat | 4 | 1 | 5 | 186.60 | 3223.01 | 17.27 | 17.24 |
| MvInt | 2 | 2 | 3 | 11.59 | 348.91 | 30.10 | 29.59 |
| MvInt | 3 | 2 | 4 | 68.11 | 812.91 | 11.94 | 11.85 |
| MvInt | 3 | 4 | 10 | 313.37 | 1170.97 | 3.74 | 3.72 |
| MvInt | 3 | 6 | 28 | 557.64 | 1814.40 | 3.25 | 3.24 |
| MvInt | 4 | 2 | 5 | 133.22 | 2165.14 | 16.25 | 16.21 |
| MvRat | 2 | 2 | 3 | 19.14 | 251.70 | 13.15 | 12.84 |
| MvRat | 3 | 2 | 4 | 70.71 | 814.66 | 11.52 | 11.44 |
| MvRat | 3 | 4 | 10 | 309.70 | 1384.69 | 4.47 | 4.45 |
| MvRat | 3 | 6 | 28 | 852.26 | 2733.16 | 3.21 | 3.20 |
| MvRat | 4 | 2 | 5 | 243.46 | 2333.79 | 9.59 | 9.56 |
| RatFn | 2 | 1 | 10 | 433.56 | 2369.38 | 5.46 | 5.45 |
| RatFn | 3 | 1 | 20 | 2292.83 | 15975.15 | 6.97 | 6.96 |
| RatFn | 3 | 2 | 38 | 10211.32 | 17001.13 | 1.66 | 1.66 |
| RatFn | 3 | 3 | 56 | 38075.87 | 20702.25 | 0.54 | 0.54 |
| RatFn | 4 | 1 | 34 | 63863.24 | 54625.18 | 0.86 | 0.86 |

The variation between repeats is shared-host context; no sample was discarded
and no point was rerun. These measurements do not establish a fitted complexity
bound or a Phase-4 gate.

## Reproduction and artifacts

Build with `lake build hexcharpoly_bench`. With SymPy installed, run each pair,
for example:

```sh
HEX_CARRIER_BENCH_PYTHON=python3 .lake/build/bin/hexcharpoly_bench compare \
  Hex.CharPolyBench.DenseInt.n3k2 Hex.CharPolyBench.SympyDenseInt.n3k2 \
  --export-file dense-int-n3k2.json
HEX_CARRIER_BENCH_PYTHON=python3 .lake/build/bin/hexcharpoly_bench run \
  Hex.CharPolyBench.carrierNoop --export-file overhead.json
.lake/build/bin/hexcharpoly_bench carrier-growth
```

Use the shared `scripts/bench/idle_core.py` CPU selection helper and pin the
parent process; children inherit its affinity. Dimension sweeps are 2/3/4 at
degree 1 (two terms for multivariate); degree sweeps are 1/2/3 at dimension 3;
term-count sweeps are 2/4/6 at dimension 3. The degree/term-count one-dimensional
sweeps share their intersection rung. The `hex` tag selects all 30 Hex carrier
registrations; `carrier` also includes the external comparisons and overhead.
`verify-ci` excludes the scheduled-only registrations, and is selected by the
existing CI bench script.

Raw five-repeat timings, result hashes, configurations and environment metadata
are preserved in [measurements.json](hex-char-poly-carriers/measurements.json).
The [overhead samples](hex-char-poly-carriers/noop.json),
[growth observations](hex-char-poly-carriers/growth.jsonl), and
[host/source context](hex-char-poly-carriers/context.json) accompany them.
The context records the benchmark source SHA-256; the run exports identify the
base commit and dirty worktree containing this implementation.
