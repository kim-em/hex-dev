# HexPermGroup Profile Report

Profiles were recorded on `chungus2` (AMD EPYC 9455, Linux x86-64) from clean
commit `a07738e1f` with Lean 4.34.0-rc2. The command shape was:

```sh
LEAN_BENCH_PROFILE_KERNEL=1 python3 "$LEAN_BENCH_SAMPLY_HOME/scripts/profile_bench.py" \
  --bench-exe .lake/build/bin/hexpermgroup_bench \
  --bench-name Hex.PermGroupBench.NAME --param 0 \
  --target-nanos 1000000000 \
  --samply-args "--rate 999 --unstable-presymbolicate" \
  --label-filter kernel \
  --out /tmp/hex-profile-NAME-symbolized-0.json.gz
```

The external `lean-bench-samply` driver supplied `profile_bench.py`; the
repository's `scripts/profile/run_profile.sh` documents the same protocol. The
committed summaries at
`reports/bench-results/hex-perm-group-profiles-issue-10126.json` retain symbol
rankings, cost categories, clock evidence, sample counts, and sensitivity
results.

| Target | Timed ms | Samples | Allocation | Own code | Lean runtime | Dominant inclusive paths |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| `degreeGenerators` | 405.0 | 391 | 32.99% | 11.25% | 54.48% | `Build.build` 98.47%; `Build.State.scan` 77.75%; `insert` 69.05% |
| `certificateReplay` | 794.6 | 787 | 30.88% | 9.66% | 57.05% | action kernel 59.09%; domain replay 54.26%; `Chain.checkFrom` 31.13% |
| `finiteActions` | 677.9 | 679 | 31.96% | 9.72% | 56.85% | action kernel 67.45%; domain construction 62.44%; queue traversal 41.83% |
| `subgroupSearch` | 506.8 | 491 | 37.47% | 18.13% | 44.20% | `Search.solve` 98.57%; visits 98.37%; child collection 97.96% |
| `normalStructure` | 617.5 | 608 | 30.59% | 12.34% | 56.58% | series iteration 93.59%; derived build 89.97%; certificate construction 81.91% |
| `products` | 937.7 | 926 | 31.43% | 13.50% | 54.97% | chain build 97.73%; scan 89.09%; insert 84.88% |

Percentages may not sum to exactly 100 because the classifier retains an
`other` category. Construction's top self costs are allocation/free (32.99%),
Lean application/refcount paths, `lean_array_push` (7.93%), array generation
(4.60%), and `Perm.comp` (2.56%). This attributes the requested array, storage,
composition, sifting, orbit, and rebuild costs within the timed kernels.

The six profiles cover all thirteen registered families through their shared
dominant phases. `degreeGenerators` executes orbit construction, Schreier pair
scans, residual sifts, program allocation, and suffix rebuilds;
`certificateReplay` includes independent chain, word, and kernel replay;
`finiteActions` covers object arrays and queue growth; `subgroupSearch` covers
complete traversal; `normalStructure` covers nested chain rebuilds; and
`products` covers generator materialization at the actual product degree
followed by chain construction.
