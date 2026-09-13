# hex-hermite-mathlib: tactic proof performance

All 660 candidate samples passed the preregistered 60-second absolute ceiling. The largest observed fresh-module time was 9.758 seconds. Comparator status is **no-comparable-surface-in-named-comparator**; no ratio or speedup is claimed.

Source commit: `652e9d9b706e5852f48ef32588a79452fe7ca3d8`. Host: `chungus2`. Each process used CPU 5 with `LEAN_NUM_THREADS=1`. The three companion sweeps ran concurrently on separately leased CPUs. Host activity and SMT sibling usage are retained as context; every completed sample counts.

The seeded generator uses seed 10238 and includes every SPEC family, dimension, height and goal component, plus empty shapes. Each candidate has six adjacent import-baseline/candidate pairs, with rotating case order and alternating arm order. Fresh-module times include literal recognition, the compiled producer and recheck, proof assembly, kernel checking, certificate statistics and profiler output. Kernel times are the cumulative `type checking` profile.

| Family | Goal component | Cases | Largest median (s) | Largest sample (s) | Largest kernel median (s) |
|---|---|---:|---:|---:|---:|
| `empty-columns` | basis | 1 | 2.582 | 2.618 | 0.005 |
| `empty-rows` | basis | 1 | 2.540 | 2.611 | 0.002 |
| `membership-residual` | basis | 12 | 3.318 | 3.328 | 0.578 |
| `membership-residual` | member | 12 | 4.176 | 4.227 | 0.597 |
| `membership-residual` | nonmember | 12 | 4.117 | 4.152 | 0.587 |
| `rank-deficient-hermite` | basis | 12 | 3.217 | 3.245 | 0.518 |
| `rank-deficient-hermite` | member | 12 | 4.321 | 4.476 | 0.546 |
| `tall-hermite` | basis | 12 | 6.183 | 6.505 | 3.355 |
| `tall-hermite` | member | 12 | 9.647 | 9.758 | 3.355 |
| `unimodular-conjugate` | basis | 12 | 3.821 | 3.909 | 1.100 |
| `unimodular-conjugate` | member | 12 | 4.773 | 4.890 | 1.180 |

[All case medians and baseline deltas](bench-results/hex-hermite-mathlib-tactic-probes-652e9d9b706e-chungus2.md), [complete raw evidence](bench-results/hex-hermite-mathlib-tactic-probes-652e9d9b706e-chungus2.json), and [certificate and artifact measurements](bench-results/hex-hermite-mathlib-tactic-probes-652e9d9b706e-chungus2-certificates.json) include all six samples, actual input and certificate bit heights, entry counts, serialized data sizes, emitted artifact sizes, axiom sets and source/toolchain/host provenance. Certificate byte counts measure the UTF-8 `reprStr` serialization of the literal data; emitted Lean artifact sizes are recorded separately.

The [diagnostic archive](bench-results/hex-structural-tactics-diagnostics.json.gz) retains 2209 completed arms from prior sources, their source provenance and interruption reasons, and the initial profiled builds. The archive is marked `release_quality: false`; it includes completed reports for their superseded source commits. The complete evidence linked above is marked `release_quality: true`.

Reproduce from a clean checkout of the measured source commit with a new external output directory:

```bash
lake build
python3 scripts/bench/structural_tactic_sweep.py --owner HexHermiteMathlib --directory /tmp/hex-hermite-mathlib-proof-evidence
```

Compiled algorithm performance belongs to `HexHermite`. These are build-only proof probes, with no Mathlib-importing benchmark executable. The 60-second gate is an operational bound on this host, not an asymptotic or portable timing claim.
