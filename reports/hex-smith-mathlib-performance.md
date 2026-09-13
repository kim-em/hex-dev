# hex-smith-mathlib: tactic proof performance

All 300 candidate samples passed the preregistered 60-second absolute ceiling. The largest observed fresh-module time was 8.262 seconds. Comparator status is **no-comparable-surface-in-named-comparator**; no ratio or speedup is claimed.

Source commit: `652e9d9b706e5852f48ef32588a79452fe7ca3d8`. Host: `chungus2`. Each process used CPU 6 with `LEAN_NUM_THREADS=1`. The three companion sweeps ran concurrently on separately leased CPUs. Host activity and SMT sibling usage are retained as context; every completed sample counts.

The seeded generator uses seed 10238 and includes every SPEC family, dimension, height and goal component, plus empty shapes. Each candidate has six adjacent import-baseline/candidate pairs, with rotating case order and alternating arm order. Fresh-module times include literal recognition, the compiled producer and recheck, proof assembly, kernel checking, certificate statistics and profiler output. Kernel times are the cumulative `type checking` profile.

| Family | Goal component | Cases | Largest median (s) | Largest sample (s) | Largest kernel median (s) |
|---|---|---:|---:|---:|---:|
| `chain-conjugate` | quotient | 8 | 4.041 | 4.117 | 1.290 |
| `empty-columns` | quotient | 1 | 2.647 | 2.680 | 0.004 |
| `empty-rows` | quotient | 1 | 2.641 | 2.725 | 0.004 |
| `large-coefficients` | quotient | 16 | 4.089 | 4.141 | 1.325 |
| `rank-deficient` | quotient | 8 | 3.833 | 4.024 | 1.025 |
| `rectangular-presentation` | quotient | 16 | 8.136 | 8.262 | 5.210 |

[All case medians and baseline deltas](bench-results/hex-smith-mathlib-tactic-probes-652e9d9b706e-chungus2.md), [complete raw evidence](bench-results/hex-smith-mathlib-tactic-probes-652e9d9b706e-chungus2.json), and [certificate and artifact measurements](bench-results/hex-smith-mathlib-tactic-probes-652e9d9b706e-chungus2-certificates.json) include all six samples, actual input and certificate bit heights, entry counts, serialized data sizes, emitted artifact sizes, axiom sets and source/toolchain/host provenance. Certificate byte counts measure the UTF-8 `reprStr` serialization of the literal data; emitted Lean artifact sizes are recorded separately.

The [diagnostic archive](bench-results/hex-structural-tactics-diagnostics.json.gz) retains 2209 completed arms from prior sources, their source provenance and interruption reasons, and the initial profiled builds. The archive is marked `release_quality: false`; it includes completed reports for their superseded source commits. The complete evidence linked above is marked `release_quality: true`.

Reproduce from a clean checkout of the measured source commit with a new external output directory:

```bash
lake build
python3 scripts/bench/structural_tactic_sweep.py --owner HexSmithMathlib --directory /tmp/hex-smith-mathlib-proof-evidence
```

Compiled algorithm performance belongs to `HexSmith`. These are build-only proof probes, with no Mathlib-importing benchmark executable. The 60-second gate is an operational bound on this host, not an asymptotic or portable timing claim.
