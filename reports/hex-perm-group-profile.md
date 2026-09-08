# HexPermGroup Profile Report

Profiles were recorded on `chungus2` (AMD EPYC 9455, Linux x86-64) from clean
commit `2b73c89c3` with Lean 4.34.0-rc2. The command shape was:

```sh
LEAN_BENCH_PROFILE_KERNEL=1 python3 "$LEAN_BENCH_SAMPLY_HOME/scripts/profile_bench.py" \
  --bench-exe .lake/build/bin/hexpermgroup_bench \
  --bench-name Hex.PermGroupBench.NAME --param 0 \
  --target-nanos 1000000000 --samply-args "--rate 999" \
  --label-filter kernel --out /tmp/hex-profile-NAME-0.json.gz
```

The external `lean-bench-samply` driver supplied `profile_bench.py`; the
repository's `scripts/profile/run_profile.sh` documents the same protocol. The
committed summaries at
`reports/bench-results/hex-perm-group-profiles-issue-10126.json` retain symbol
rankings, cost categories, clock evidence, sample counts, and sensitivity
results.

| Target | Timed ms | Samples | Allocation | Own code | Lean runtime | Dominant inclusive paths |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| `degreeGenerators` | 778.6 | 767 | 29.86% | 15.12% | 53.98% | `Build.build` 97.26%; `Build.State.scan` 78.49%; `insert` 69.62% |
| `certificateReplay` | 582.2 | 569 | 27.94% | 10.37% | 57.82% | `Chain.checkFrom` 87.35%; orbit validation 39.37%; `Chain.sift` 20.56% |
| `finiteActions` | 576.3 | 563 | 36.59% | 7.99% | 52.04% | `Action.breadthFirst` 82.42%; queue scan 73.36%; queue visit 72.29% |
| `subgroupSearch` | 1044.3 | 1034 | 33.75% | 14.80% | 50.87% | `Search.solve` 99.81%; child collection and visits 99.42% |
| `normalStructure` | 953.8 | 947 | 31.36% | 16.37% | 51.74% | derived certificate 93.88%; normal close 84.69%; chain build 75.71% |
| `products` | 889.0 | 870 | 36.44% | 10.80% | 52.30% | chain build 93.10%; scan 65.17%; insert 55.98% |

Percentages may not sum to exactly 100 because the classifier retains an
`other` category. Construction's top self costs are allocation/free (29.86%),
Lean application/refcount paths, `lean_array_push` (7.43%), array generation
(5.48%), and `Perm.comp` (3.00%). This attributes the requested full-array,
storage, composition, sifting, orbit, and rebuild costs without relying on
whole-process startup samples.

The six profiles cover all thirteen registered families through their shared
dominant phases. In particular, `degreeGenerators` executes orbit construction,
Schreier pair scans, residual sifts, program allocation, and discarded-suffix
rebuilds; `certificateReplay` isolates checker work; `finiteActions` covers
object arrays and queue growth; `subgroupSearch` covers exponential traversal;
`normalStructure` covers nested chain rebuilds; and `products` covers generator
materialization at the actual product degree followed by chain construction.
