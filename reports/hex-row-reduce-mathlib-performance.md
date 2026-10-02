# hex-row-reduce-mathlib: inverse and solve proof performance

All 1,200 candidate samples passed the preregistered 60-second absolute ceiling. The largest observed fresh-module time was 22.123 seconds. Comparator status is **no-comparable-surface-in-named-comparator**; no ratio or speedup is claimed.

Source commit: `9468e7785f9de5eede06440d2baccc75e55bc552`. Host: `chungus2`. The primary sweep used CPU 80, and the separate informational normalization sweep used CPU 89, both automatically leased with `LEAN_NUM_THREADS=1`. The sweeps began while the full monorepo build was finishing. Host activity, frequency and SMT sibling usage are recorded as context; every completed sample counts.

The generator uses seed 10239 and covers every required family, dimension, height and goal component: 80 inverse probes and 120 solve probes. Inconsistent systems use exactly the deficient-affine matrices with a changed right-hand side. Each candidate has six adjacent import-baseline/candidate pairs, rotating case order and alternating arm order. The 60-second cap was fixed in the committed manifest before measurement. Fresh-module times include literal recognition, compiled production and rechecking, proof assembly, kernel checking, certificate statistics and profiler output. Kernel times are the cumulative `type checking` profile. At dimension 2 the two singular rank schedules coincide (`n − 1 = n / 2 = 1`), so each bit-height has two separately measured copies of the same input. The counts describe scheduled probes, not distinct matrices.

| Family | Goal component | Cases | Largest median (s) | Largest sample (s) | Largest kernel median (s) |
|---|---|---:|---:|---:|---:|
| `deficient-affine` | complete | 12 | 3.718 | 4.591 | 0.698 |
| `deficient-affine` | residual | 12 | 3.179 | 3.900 | 0.100 |
| `dense-invertible` | inverse | 8 | 17.724 | 18.812 | 0.910 |
| `dense-invertible` | product | 8 | 17.878 | 19.205 | 0.909 |
| `inconsistent-separator` | complete | 12 | 3.119 | 3.220 | 0.120 |
| `inconsistent-separator` | negative | 12 | 3.207 | 3.300 | 0.111 |
| `pivot-swaps` | inverse | 8 | 3.323 | 4.185 | 0.383 |
| `pivot-swaps` | product | 8 | 3.336 | 4.105 | 0.380 |
| `rational-height` | inverse | 16 | 19.728 | 21.581 | 0.964 |
| `rational-height` | product | 16 | 19.874 | 22.123 | 0.966 |
| `singular-kernel` | singular | 16 | 2.827 | 3.498 | 0.045 |
| `square-unique` | complete | 12 | 3.620 | 4.513 | 0.610 |
| `square-unique` | residual | 12 | 3.181 | 3.812 | 0.100 |
| `tall-consistent` | complete | 12 | 7.070 | 8.133 | 3.670 |
| `tall-consistent` | residual | 12 | 3.819 | 4.505 | 0.260 |
| `wide-affine` | complete | 12 | 5.522 | 7.003 | 2.215 |
| `wide-affine` | residual | 12 | 3.621 | 4.405 | 0.236 |

The following columns give the largest per-probe median cumulative profiler time in each family, in seconds. Categories are profiler labels and are not additive; maxima in different columns may come from different probes. An absent category contributes zero.

| Family | Elaboration | Simp | Typeclass inference | Type checking |
|---|---:|---:|---:|---:|
| `deficient-affine` | 0.309 | 0.000 | 0.144 | 0.698 |
| `dense-invertible` | 2.185 | 0.000 | 12.900 | 0.910 |
| `inconsistent-separator` | 0.316 | 0.000 | 0.137 | 0.120 |
| `pivot-swaps` | 0.499 | 0.000 | 0.137 | 0.383 |
| `rational-height` | 2.680 | 0.000 | 14.400 | 0.966 |
| `singular-kernel` | 0.127 | 0.000 | 0.020 | 0.045 |
| `square-unique` | 0.312 | 0.000 | 0.141 | 0.610 |
| `tall-consistent` | 0.667 | 0.000 | 0.383 | 3.670 |
| `wide-affine` | 0.623 | 0.000 | 0.221 | 2.215 |

Typeclass inference dominates the largest dense and rational-height inverse probes. These cumulative profiles do not identify a particular source call as the cause; no entry-parser bottleneck or parser speedup is inferred. The 32-per-axis acceptance limit is a capability bound, while performance coverage is the committed ladder.

[All case medians and baseline deltas](bench-results/hex-row-reduce-mathlib-tactic-probes-9468e7785f9d-chungus2.md), [complete raw evidence](bench-results/hex-row-reduce-mathlib-tactic-probes-9468e7785f9d-chungus2.json.gz), and [certificate and artifact measurements](bench-results/hex-row-reduce-mathlib-tactic-probes-9468e7785f9d-chungus2-certificates.json) retain all six samples, actual input and certificate bit heights, scaled integer entry counts, denominator counts, serialized sizes, emitted artifact sizes, axiom sets and source/toolchain/host provenance. Certificate byte counts measure the UTF-8 `reprStr` serialization of the input and witness; emitted Lean artifact sizes are recorded separately. Every accepted probe depends only on `propext`, `Classical.choice` and `Quot.sound`.

The informational entrywise proofs close all 14 selected small product/residual rungs, with all 84 samples passing. They prove the identical propositions using `fin_cases` and `norm_num`, without computing an inverse or complete solution space. [Their complete raw evidence](bench-results/hex-row-reduce-mathlib-tactic-probes-9468e7785f9d-chungus2-normalization.json.gz) uses its own matched import-only baseline and the same six-round protocol.

| Family | Dimension | Component | Tactic median (s) | Normalization median (s) | Normalization max (s) | Closes |
|---|---:|---|---:|---:|---:|---|
| `dense-invertible` | 2×2 | product | 2.719 | 2.809 | 3.381 | yes |
| `dense-invertible` | 4×4 | product | 2.815 | 3.477 | 4.135 | yes |
| `pivot-swaps` | 2×2 | product | 2.715 | 2.804 | 3.381 | yes |
| `pivot-swaps` | 4×4 | product | 2.717 | 3.207 | 3.700 | yes |
| `rational-height` | 2×2 | product | 2.718 | 2.819 | 3.027 | yes |
| `rational-height` | 4×4 | product | 2.814 | 3.799 | 4.013 | yes |
| `deficient-affine` | 2×2 | residual | 2.715 | 2.794 | 2.800 | yes |
| `deficient-affine` | 4×4 | residual | 2.719 | 2.898 | 2.911 | yes |
| `square-unique` | 2×2 | residual | 2.715 | 2.800 | 2.807 | yes |
| `square-unique` | 4×4 | residual | 2.718 | 2.929 | 3.025 | yes |
| `tall-consistent` | 4×2 | residual | 2.719 | 2.800 | 3.003 | yes |
| `tall-consistent` | 8×4 | residual | 2.739 | 3.265 | 3.324 | yes |
| `wide-affine` | 2×4 | residual | 2.719 | 2.799 | 3.001 | yes |
| `wide-affine` | 4×8 | residual | 2.721 | 3.104 | 3.193 | yes |

The [development build archive](bench-results/hex-row-reduce-tactic-diagnostics.json.gz) preserves unpaired compilation and diagnostic logs, including the concurrent development builds that took 78–86 seconds for the largest-height inverses. Those builds lack the prescribed measurement protocol. The archive also retains the first source’s interrupted primary sweep and completed normalization sweep. The primary sweep was stopped to fix unresolved-metavariable dispatch, with its current arm explicitly terminated and all completed arms preserved. The archive is marked `release_quality: false` for the current implementation; nested complete reports retain their original source attribution. The complete paired evidence above is marked `release_quality: true`.

Reproduce from a clean checkout of the measured source commit, using new external output directories:

```bash
lake build
python3 scripts/bench/row_reduce_tactic_sweep.py --directory /tmp/hex-row-reduce-proof-evidence
python3 scripts/bench/row_reduce_tactic_sweep.py --normalization --directory /tmp/hex-row-reduce-normalization-evidence
```

[Earlier complete paired measurements](bench-results/hex-row-reduce-mathlib-tactic-probes-2782ec3aeb30-chungus2.json.gz) and their [normalization measurements](bench-results/hex-row-reduce-mathlib-tactic-probes-2782ec3aeb30-chungus2-normalization.json.gz) remain available with their original source attribution. They are not pooled with the current-source samples.

Compiled algorithm performance belongs to `HexRowReduce`. These are build-only proof probes, with no Mathlib-importing benchmark executable. CI builds every generated module through the existing `HexStructuralTacticProofProbe` target. The ceiling is an operational bound on this host, not an asymptotic or portable timing claim.
