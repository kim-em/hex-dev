# hex-row-reduce-mathlib: inverse and solve proof performance

All 1,200 candidate samples passed the preregistered 60-second absolute ceiling. The largest observed fresh-module time was 21.219 seconds. Comparator status is **no-comparable-surface-in-named-comparator**; no ratio or speedup is claimed.

Source commit: `2782ec3aeb303043104d7959c4faf3f98d061164`. Host: `chungus2`. The primary sweep used CPU 15, and the separate informational normalization sweep used CPU 13, both automatically leased with `LEAN_NUM_THREADS=1`. The sweeps began while the full monorepo build was finishing. Host activity, frequency and SMT sibling usage are recorded as context; every completed sample counts.

The generator uses seed 10239 and covers every required family, dimension, height and goal component: 80 inverse probes and 120 solve probes. Inconsistent systems use exactly the deficient-affine matrices with a changed right-hand side. Each candidate has six adjacent import-baseline/candidate pairs, rotating case order and alternating arm order. The 60-second cap was fixed in the committed manifest before measurement. Fresh-module times include literal recognition, compiled production and rechecking, proof assembly, kernel checking, certificate statistics and profiler output. Kernel times are the cumulative `type checking` profile.

| Family | Goal component | Cases | Largest median (s) | Largest sample (s) | Largest kernel median (s) |
|---|---|---:|---:|---:|---:|
| `deficient-affine` | complete | 12 | 3.757 | 4.407 | 0.777 |
| `deficient-affine` | residual | 12 | 3.120 | 3.609 | 0.104 |
| `dense-invertible` | inverse | 8 | 17.915 | 18.720 | 1.002 |
| `dense-invertible` | product | 8 | 18.116 | 18.731 | 1.105 |
| `inconsistent-separator` | complete | 12 | 3.018 | 5.115 | 0.121 |
| `inconsistent-separator` | negative | 12 | 3.120 | 5.547 | 0.114 |
| `pivot-swaps` | inverse | 8 | 3.326 | 3.931 | 0.401 |
| `pivot-swaps` | product | 8 | 3.380 | 3.447 | 0.407 |
| `rational-height` | inverse | 16 | 20.138 | 21.219 | 1.260 |
| `rational-height` | product | 16 | 20.034 | 20.325 | 1.175 |
| `singular-kernel` | singular | 16 | 2.863 | 3.309 | 0.046 |
| `square-unique` | complete | 12 | 3.667 | 4.003 | 0.720 |
| `square-unique` | residual | 12 | 3.113 | 3.204 | 0.102 |
| `tall-consistent` | complete | 12 | 7.484 | 7.707 | 4.100 |
| `tall-consistent` | residual | 12 | 3.805 | 3.915 | 0.272 |
| `wide-affine` | complete | 12 | 5.963 | 6.608 | 2.635 |
| `wide-affine` | residual | 12 | 3.716 | 4.112 | 0.284 |

[All case medians and baseline deltas](bench-results/hex-row-reduce-mathlib-tactic-probes-2782ec3aeb30-chungus2.md), [complete raw evidence](bench-results/hex-row-reduce-mathlib-tactic-probes-2782ec3aeb30-chungus2.json.gz), and [certificate and artifact measurements](bench-results/hex-row-reduce-mathlib-tactic-probes-2782ec3aeb30-chungus2-certificates.json) retain all six samples, actual input and certificate bit heights, scaled integer entry counts, denominator counts, serialized sizes, emitted artifact sizes, axiom sets and source/toolchain/host provenance. Certificate byte counts measure the UTF-8 `reprStr` serialization of the input and witness; emitted Lean artifact sizes are recorded separately. Every accepted probe depends only on `propext`, `Classical.choice` and `Quot.sound`.

The informational entrywise proofs close all 14 selected small product/residual rungs, with all 84 samples passing. They prove the identical propositions using `fin_cases` and `norm_num`, without computing an inverse or complete solution space. [Their complete raw evidence](bench-results/hex-row-reduce-mathlib-tactic-probes-2782ec3aeb30-chungus2-normalization.json.gz) uses its own matched import-only baseline and the same six-round protocol.

| Family | Dimension | Component | Tactic median (s) | Normalization median (s) | Normalization max (s) | Closes |
|---|---:|---|---:|---:|---:|---|
| `dense-invertible` | 2×2 | product | 2.706 | 2.828 | 2.870 | yes |
| `dense-invertible` | 4×4 | product | 2.722 | 3.516 | 3.561 | yes |
| `pivot-swaps` | 2×2 | product | 2.704 | 2.827 | 2.838 | yes |
| `pivot-swaps` | 4×4 | product | 2.706 | 3.290 | 3.331 | yes |
| `rational-height` | 2×2 | product | 2.708 | 2.850 | 2.922 | yes |
| `rational-height` | 4×4 | product | 2.731 | 3.866 | 3.954 | yes |
| `deficient-affine` | 2×2 | residual | 2.705 | 2.814 | 2.833 | yes |
| `deficient-affine` | 4×4 | residual | 2.705 | 2.910 | 2.931 | yes |
| `square-unique` | 2×2 | residual | 2.707 | 2.820 | 2.855 | yes |
| `square-unique` | 4×4 | residual | 2.703 | 2.941 | 3.034 | yes |
| `tall-consistent` | 4×2 | residual | 2.706 | 2.826 | 2.842 | yes |
| `tall-consistent` | 8×4 | residual | 2.709 | 3.279 | 3.347 | yes |
| `wide-affine` | 2×4 | residual | 2.710 | 2.771 | 2.837 | yes |
| `wide-affine` | 4×8 | residual | 2.710 | 3.120 | 3.147 | yes |

The [development build archive](bench-results/hex-row-reduce-tactic-diagnostics.json.gz) preserves unpaired compilation and diagnostic logs, including the concurrent development builds that took 78–86 seconds for the largest-height inverses. Those builds lack the prescribed measurement protocol. The archive also retains the first source’s interrupted primary sweep and completed normalization sweep. The primary sweep was stopped to fix unresolved-metavariable dispatch, with its current arm explicitly terminated and all completed arms preserved. The archive is marked `release_quality: false` for the current implementation; nested complete reports retain their original source attribution. The complete paired evidence above is marked `release_quality: true`.

Reproduce from a clean checkout of the measured source commit, using new external output directories:

```bash
lake build
python3 scripts/bench/row_reduce_tactic_sweep.py --directory /tmp/hex-row-reduce-proof-evidence
python3 scripts/bench/row_reduce_tactic_sweep.py --normalization --directory /tmp/hex-row-reduce-normalization-evidence
```

Compiled algorithm performance belongs to `HexRowReduce`. These are build-only proof probes, with no Mathlib-importing benchmark executable. CI builds every generated module through the existing `HexStructuralTacticProofProbe` target. The ceiling is an operational bound on this host, not an asymptotic or portable timing claim.
