# HexPermGroup Performance Report

## Bench targets

`bench/HexPermGroup/Bench.lean` registers all thirteen required families as
deterministic mode-3 workloads. Each target checks its complete result and has
an operation-specific wall-clock ceiling.

| Family | Timed operation | Ceiling |
| --- | --- | ---: |
| `degree-generators` | Fresh S3, S4, and S5 construction, including redundant generators and fixed points | 20 ms |
| `chain-shape` | Prepared cyclic, dihedral, symmetric, alternating, and intransitive chain metadata | 10 ms |
| `membership` | Prepared positive, early-negative, and late-negative sifts | 10 ms |
| `stabilizers` | Point and pointwise stabilizer construction | 20 ms |
| `containment` | Equal, strict, and failed subgroup tests | 10 ms |
| `enumeration` | Complete elements and cosets at exact caps, plus rejected short caps | 10 ms |
| `element-access` | Rank/unrank, supplied-index sampling, sign, cycle type, and order above 64 bits | 20 ms |
| `finite-actions` | Tuple, subset, and partition orbits, image, and kernel | 20 ms |
| `subgroup-search` | Intersection, transporter, set stabilizer, centralizer, and normalizer | 200 ms |
| `blocks` | Several generated partitions and positive/negative primitivity cases | 10 ms |
| `normal-structure` | Join, abelianness, normality, closure, core, and soluble/perfect derived series | 200 ms |
| `products` | Direct and imprimitive wreath products, including empty, nonabelian, and fixed-block cases | 100 ms |
| `certificate-replay` | Separate chain, membership-program, and action-kernel replay checks | 20 ms |

The action degree is an index in the Lean type, and these operation families
vary several independent dimensions rather than one scalar. Attempts to use
the runtime parameter as a degree either measure a finite type-dispatch wrapper
or repeat a fixed problem. Neither supplies a stable, independently derived
one-parameter wall-time law for the API. The ordered complexity rule therefore
selects mode 3. The worst-case work bounds remain in the library SPEC, and the
resource meter directly records points, Schreier pairs, sifts, certificate
nodes, image slots, and storage allocations.

## Verdicts

The clean scientific run used commit `8ee2d1042`, CPU 3 on `chungus2` (AMD
EPYC 9455, 96 logical CPUs), Lean 4.34.0-rc2, five repeats, and no random seed.
The exact command was:

```sh
taskset -c 3 .lake/build/bin/hexpermgroup_bench run \
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
| `degree-generators` | 23.351 us |
| `chain-shape` | 124 ns |
| `membership` | 602 ns |
| `stabilizers` | 68.700 us |
| `containment` | 2.543 us |
| `enumeration` | 47.332 us |
| `element-access` | 51.127 us |
| `finite-actions` | 160.917 us |
| `subgroup-search` | 2.104 ms |
| `blocks` | 4.611 us |
| `normal-structure` | 585.758 us |
| `products` | 452.483 us |
| `certificate-replay` | 185.610 us |

`chain-shape`, `membership`, and `containment` are prepared queries. Their
inputs pass through `IO.Ref`, so the short results do not come from closed-term
evaluation. Construction, prepared queries, certificate production, and replay
are kept distinct inside the relevant targets. `lake exe hexpermgroup_bench
list` and `lake exe hexpermgroup_bench verify` pass all thirteen registrations
and form the CI smoke gate.

## GAP comparator

`GAP permutation groups via a persistent process` is the informational
comparator, using GAP 4.15.1. The driver warms the line protocol, prepares query
groups once, and measures fresh
`Group`/`StabChain` construction separately. It records the exact GAP methods
and options alongside the data. The command is:

```sh
python3 scripts/bench/perm_group_gap_bench.py \
  --output reports/bench-results/hex-perm-group-gap-issue-10126.json
```

| GAP operation | Per call |
| --- | ---: |
| Fresh `Group` plus `StabChain` | 107.401 us |
| Prepared membership | 344 ns |
| Prepared order | 32 ns |
| Point stabilizer | 12.801 us |
| Intersection | 2.663 us |
| Blocks | 2.715 us |
| Normal closure plus derived subgroup | 121.561 us |
| Direct plus wreath products | 28.957 us |

These operation-level GAP cases use the same canonical degree-4 inputs, but
the expanded Hex targets deliberately combine several cases and correctness
checks per required family. A ratio between those aggregate Hex targets and a
single GAP operation would therefore be misleading. GAP has no producer
certificate or Lean kernel-replay surface, so certificate construction and
replay have no comparator.

## Profile

Six clean timed-region profiles were captured at commit `a07738e1f` with a
999 Hz `samply` schedule and kernel-only batches. The filtered summary is
`reports/bench-results/hex-perm-group-profiles-issue-10126.json`; raw Firefox
Profiler files are developer-local under
`/tmp/hex-profile-*-symbolized-0.json.gz`. Every profile passed clock
calibration, the +/-5 ms sensitivity check, and the minimum retained-sample
rule. Full commands and attribution are recorded in
`reports/hex-perm-group-profile.md`.

The family coverage mapping is: construction covers `degree-generators` and
`chain-shape`; replay covers `membership`, `containment`, `enumeration`, and
`element-access`; stabilizer-chain construction and search cover `stabilizers`
and `subgroup-search`; action traversal covers `finite-actions` and `blocks`;
derived closure covers `normal-structure`; product construction covers
`products`; and prepared checker replay covers `certificate-replay`. The
construction profile includes array composition, orbit construction, sifting,
recursive suffix rebuilds, and word/program storage. Dominant inclusive costs
map to registered targets: `Build.State.scan`/`insert`, `Chain.checkFrom`,
action kernel/domain construction, search child collection, derived-series
rebuilds, and product chain builds.

## Concerns

None.
