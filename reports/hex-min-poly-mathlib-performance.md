# hex-min-poly-mathlib: tactic proof performance

All 204 candidate samples passed the preregistered 60-second absolute ceiling. The largest observed fresh-module time was 31.026 seconds. Comparator status is **no-comparable-surface-in-named-comparator**; no ratio or speedup is claimed.

Source commit: `1442335fdc528569abce32b9923b5ce364a0b2c4`. Host: `chungus2`. Each process used CPU 39 with `LEAN_NUM_THREADS=1`. The three companion sweeps ran concurrently on separately leased CPUs. Host activity and SMT sibling usage are retained as context; every completed sample counts.

The seeded generator uses seed 10238 and includes every SPEC family, dimension, height and goal component, plus empty shapes and one 16×16 entrywise literal case per owner. Each candidate has six adjacent import-baseline/candidate pairs, with rotating case order and alternating arm order. Fresh-module times include literal recognition, the compiled producer and recheck, proof assembly, kernel checking, certificate statistics and profiler output. Kernel times are the cumulative `type checking` profile.

| Family | Goal component | Cases | Largest median (s) | Largest sample (s) | Largest kernel median (s) |
|---|---|---:|---:|---:|---:|
| `cyclic` | equality | 8 | 18.492 | 18.561 | 14.650 |
| `empty` | equality | 1 | 2.623 | 2.638 | 0.003 |
| `entrywise-literal` | equality | 1 | 18.425 | 18.470 | 2.690 |
| `nilpotent` | equality | 8 | 7.879 | 8.074 | 5.005 |
| `rational-dense` | equality | 8 | 30.748 | 31.026 | 19.200 |
| `repeated-block` | equality | 8 | 7.816 | 7.845 | 4.680 |

[All case medians and baseline deltas](bench-results/hex-min-poly-mathlib-tactic-probes-1442335fdc52-chungus2.md), [complete raw evidence](bench-results/hex-min-poly-mathlib-tactic-probes-1442335fdc52-chungus2.json.gz), and [certificate and artifact measurements](bench-results/hex-min-poly-mathlib-tactic-probes-1442335fdc52-chungus2-certificates.json) include all six samples, actual input and certificate bit heights, entry counts, serialized data sizes, emitted artifact sizes, axiom sets and source/toolchain/host provenance. Certificate byte counts measure the UTF-8 `reprStr` serialization of the literal data; emitted Lean artifact sizes are recorded separately.

The [diagnostic archive](bench-results/hex-structural-tactics-diagnostics.json.gz) retains 4525 completed arms from prior sources, their source provenance and interruption reasons, and the initial profiled builds. The archive is marked `release_quality: false`; it includes completed reports for their superseded source commits. The complete evidence linked above is marked `release_quality: true`.

Reproduce from a clean checkout of the measured source commit with a new external output directory:

```bash
lake build
python3 scripts/bench/structural_tactic_sweep.py --owner HexMinPolyMathlib --directory /tmp/hex-min-poly-mathlib-proof-evidence
```

Compiled algorithm performance belongs to `HexMinPoly`. These are build-only proof probes, with no Mathlib-importing benchmark executable. CI builds all generated probes to detect source and elaboration regressions. The 60-second gate is an operational bound on this host, not an asymptotic or portable timing claim.
