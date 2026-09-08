# HexPermGroup Performance Report

## Bench targets

`bench/HexPermGroup/Bench.lean` registers the thirteen required families. Each
is a deterministic mode-3 canonical case with a complete result check and an
operation-specific wall-clock ceiling.

| Family | Timed operation | Ceiling |
| --- | --- | ---: |
| `degree-generators` | Fresh checked construction from four degree-4 generators | 10 ms |
| `chain-shape` | Prepared cyclic/dihedral/symmetric chain metadata | 10 ms |
| `membership` | Prepared positive and negative sifts | 10 ms |
| `stabilizers` | Point and pointwise stabilizer construction | 20 ms |
| `containment` | Equal, strict, and failed subgroup tests | 10 ms |
| `enumeration` | Complete enumeration and rejected short cap | 10 ms |
| `element-access` | Prepared rank/unrank inverse check | 10 ms |
| `finite-actions` | Natural and repeated-tuple action orbits | 10 ms |
| `subgroup-search` | Complete intersection search and replay | 100 ms |
| `blocks` | Seeded invariant partition and primitivity | 10 ms |
| `normal-structure` | Normal closure and derived subgroup | 50 ms |
| `products` | Direct and imprimitive wreath products | 20 ms |
| `certificate-replay` | Prepared stabilizer-chain replay | 10 ms |

The action degree is an index in the Lean type, and these operation families
vary several independent dimensions rather than one scalar. Attempts to use
the runtime parameter as a degree either measure a finite type-dispatch wrapper
or repeat a fixed problem. Neither supplies a stable, independently derived
one-parameter wall-time law for the API. The ordered complexity rule therefore
selects mode 3. The worst-case work bounds remain in the library SPEC, and the
resource meter directly records points, Schreier pairs, sifts, certificate
nodes, image slots, and storage allocations.

## Verdicts

The clean scientific run used commit `6ddfbf566`, CPU 1 on `chungus2` (AMD
EPYC 9455, 96 logical CPUs), Lean 4.34.0-rc2, five repeats, and no random seed.
The exact command was:

```sh
taskset -c 1 .lake/build/bin/hexpermgroup_bench run \
  Hex.PermGroupBench.degreeGenerators Hex.PermGroupBench.chainShape \
  Hex.PermGroupBench.membership Hex.PermGroupBench.stabilizers \
  Hex.PermGroupBench.containment Hex.PermGroupBench.enumeration \
  Hex.PermGroupBench.elementAccess Hex.PermGroupBench.finiteActions \
  Hex.PermGroupBench.subgroupSearch Hex.PermGroupBench.blocks \
  Hex.PermGroupBench.normalStructure Hex.PermGroupBench.products \
  Hex.PermGroupBench.certificateReplay \
  --export-file reports/bench-results/hex-perm-group-issue-10126.json
```

Every expected hash matched and every repeat completed below its declared
ceiling. The committed JSON contains the environment, hashes, inner repeats,
RSS, and min/median/max values. Medians were:

| Family | Median |
| --- | ---: |
| `degree-generators` | 25.454 us |
| `chain-shape` | 75 ns |
| `membership` | 648 ns |
| `stabilizers` | 72.986 us |
| `containment` | 2.760 us |
| `enumeration` | 11.242 us |
| `element-access` | 921 ns |
| `finite-actions` | 5.750 us |
| `subgroup-search` | 544.166 us |
| `blocks` | 2.132 us |
| `normal-structure` | 118.470 us |
| `products` | 28.371 us |
| `certificate-replay` | 35.324 us |

`chain-shape`, `membership`, and `element-access` are intentionally small
prepared queries. Their inputs pass through `IO.Ref`, so the sub-microsecond
results do not come from closed-term evaluation. Construction, replay, and
queries are separate timed targets. `lake exe hexpermgroup_bench list` and
`lake exe hexpermgroup_bench verify` pass all thirteen registrations and form
the CI smoke gate.

## Comparator ratios

`GAP permutation groups via a persistent process` is the informational
comparator. It starts one persistent GAP 4.15.1 process,
warms the line protocol, prepares query groups once, and measures fresh
`Group`/`StabChain` construction separately. It uses GAP's default stabilizer
chain settings and records `Size`, membership, `Stabilizer`, `Intersection`,
`Blocks`, `NormalClosure`, `DerivedSubgroup`, `DirectProduct`, and
`WreathProductImprimitiveAction`. The exact command and output are:

```sh
python3 scripts/bench/perm_group_gap_bench.py \
  --output reports/bench-results/hex-perm-group-gap-issue-10126.json
```

| Comparable case | Hex / GAP time ratio |
| --- | ---: |
| Fresh construction | 0.18x |
| Prepared membership | 1.63x |
| Point stabilizer | 4.51x |
| Intersection | 130.68x |
| Seeded blocks | 0.66x |
| Direct plus wreath products | 0.79x |

The ratios describe these degree-4 canonical inputs and are not performance
contracts. The intersection gap is attributable to Hex's complete generic
search and replay path; GAP uses mature specialized group methods. GAP has no
comparable producer certificate or Lean kernel-replay surface, so no ratio is
reported for certificate construction or replay.

## Profile

Six clean timed-region profiles were captured at commit `2b73c89c3` with a
999 Hz `samply` schedule and one-second kernel batches. The filtered summary is
`reports/bench-results/hex-perm-group-profiles-issue-10126.json`; raw Firefox
Profiler files are developer-local under `/tmp/hex-profile-*-0.json.gz`. Every
profile passed clock calibration, the +/-5 ms sensitivity check, and the
minimum retained-sample rule. Full commands and attribution are recorded in
`reports/hex-perm-group-profile.md`.

The family coverage mapping is: construction covers `degree-generators` and
`chain-shape`; replay covers `membership`, `containment`, `enumeration`, and
`element-access`; stabilizer-chain construction and search cover `stabilizers`
and `subgroup-search`; action BFS covers `finite-actions` and `blocks`; derived
closure covers `normal-structure`; product construction covers `products`; and
prepared checker replay covers `certificate-replay`. The construction profile
includes full-array composition, orbit construction, sifting, recursive suffix
rebuilds, and word/program storage. Dominant inclusive costs map to registered
targets: `Build.State.scan`/`insert`, `Chain.checkFrom`/`sift`, action queue
visits, search child collection, normal closure, and product chain builds.

## Concerns

None.
