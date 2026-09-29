# BKR root-count proof probes

The semantic probes apply `Replay.count_roots` to literal accepted graphs at
depths 1, 3, 5 and 7. Acceptance is proved in the existing `Accept` modules.
`Dag.check_replay` extracts a checked tree; the semantic theorem explicitly
binds that tree to the supplied graph's replay result and identifies
every returned count with the cardinality of the corresponding subset of the
actual roots of X²−1 in (0,2). The root set is defined independently of the
proposed counts. The proof uses the shared Sturm–Tarski semantics and the
Tau Ceti finite BKR foundation through the companion.

Each graph has depth+1 entries and twice-depth edges. Both child edges refer
to the preceding entry. Query lists have lengths 2, 8, 32 and 128, with every
query equal to the constant 2. Support size is one. Coefficient and witness
sizes stay fixed, and there is no coefficient extension. This family does
not cover increasing support, joint Thom queries, nested fields or descriptor
comparisons.

Each semantic module and its import-only baseline have identical imports.
The external runner `scripts/bench/sign_det_semantics.py` warms those imports,
then removes only the measured module's artifacts before rebuilding its
`olean` through Lake. Four rotated rounds alternate adjacent AB/BA order on
one automatically leased CPU. Host activity is recorded as context; samples
are not discarded for contention. Every completed arm is flushed to an
incremental log before validation, including failed arms. A complete run
retains compiler output, source and dependency identities, artifact sizes,
wall time, process resource observations and axiom inventories.

The paired difference includes theorem elaboration, ordinary kernel checking,
serialization, two axiom traversals (guarded and diagnostic), and variable
Lake/process overhead. It is
not a measurement of kernel checking alone. Acceptance and the foundation
proofs are warm dependencies; their initial compilation and literal checker
reduction are excluded. The existing [graph replay probes](sign-det-proof-model.md)
measure literal checking separately. Semantic theorem inventories are guarded
to contain only `propext`, `Classical.choice` and `Quot.sound`.

These are diagnostic observations, with no complexity verdict or absolute
performance budget. They do not establish all Phase-4 requirements. The
ordinary CI proof-probe target builds the examples; timing runs are external.

## Graph-bound observations

Source `0acfbaf3f4e0295e5a23ca24e4ab64e03ed443df` supplies 16 adjacent pairs
(32 fresh builds) on `chungus2`, automatically leased CPU 25, with one Lean
thread. Lean, Mathlib and Tau Ceti revisions match the original records below.
The repository and dependency checkouts were clean. The owned shared build
directory had no concurrent build during collection.

| Depth | Query positions | Import-only median (s) | Semantic median (s) | Median paired difference (s) |
|---|---:|---:|---:|---:|
| 1 | 2 | 2.673 | 2.761 | 0.092 |
| 3 | 8 | 2.668 | 2.763 | 0.087 |
| 5 | 32 | 2.665 | 2.762 | 0.100 |
| 7 | 128 | 2.672 | 2.774 | 0.100 |

Every candidate inventory is selected from its measured semantic namespace
and contains only the three standard axioms. Baselines have no inventory in
their measured namespace; replayed import diagnostics are excluded. All
32 completed arms and their full compiler outputs are retained.

Semantic `.olean` files contain 42,992–43,128 bytes, and their private files
contain 16,752–16,792 bytes. Median semantic-arm maximum resident sets are
1,729,996–1,730,132 KiB, including imports and the rebuild process. These are
not isolated theorem memory or allocated-byte measurements. The paired
observations do not establish a complexity bound, speedup or full Phase-4
coverage. This collection measures changed theorem statements and inventory
selection; it is not an unchanged rerun of the original collection.

- [Complete graph-bound measurement](bench-results/hex-sign-det-semantics-0acfbaf3f-chungus2.json).
- [Incremental graph-bound arm records](bench-results/hex-sign-det-semantics-0acfbaf3f-chungus2.json.samples.jsonl).

## Original observations

Source `8ba814887079ddf45e9682371d4565c49d3d2171` supplies 16 adjacent pairs
(32 fresh builds) on `chungus2`, automatically leased CPU 68, with one Lean
thread. Lean is 4.35.0-rc3, Mathlib is
`d870b9068518a0870842d15a0cd42637ec30b587`, and Tau Ceti is
`ff72a2e86930d5268476ee33d55ab054ed1c3ea5`. Repository and dependency
checkouts were clean. This checkout used the same owned `.lake` directory
as the height worktree; no other build in that directory ran during collection.

| Depth | Query positions | Import-only median (s) | Semantic median (s) | Median paired difference (s) |
|---|---:|---:|---:|---:|
| 1 | 2 | 2.666 | 2.762 | 0.060 |
| 3 | 8 | 2.652 | 2.717 | 0.055 |
| 5 | 32 | 2.651 | 2.747 | 0.097 |
| 7 | 128 | 2.659 | 2.747 | 0.085 |

The semantic `.olean` files contain 41,376–41,512 bytes, and their
`.olean.private` files contain 18,592–18,632 bytes. Baselines contain 1,576
and 96 bytes respectively. Median semantic-arm maximum resident sets are
1,728,612–1,729,592 KiB. These resource observations include the rebuild
process and imports; they do not isolate the theorem's memory usage or
measure allocated bytes.

All semantic guards passed. In these original records, the `axioms` field
contains the imported `Accept.checked` inventory: the runner selected the
first printed inventory. Candidate compiler outputs separately retain the
semantic theorem's inventory. The original theorem asserted the existence
of a checked tree with correct root counts; it did not state the equation
binding that tree to the supplied graph. These records therefore describe
that earlier theorem and runner, not the strengthened graph-bound probes.
The current runner selects only inventories from each measured namespace,
checks every inventory there, and expects none for import-only baselines. The observed paired
differences do not establish asymptotic behavior or a speedup. The imported
acceptance proofs already bind the full certificates, so these applications
need not unfold those certificates again as query count grows. No rerun or
null control was used.

Run the diagnostic with:

```sh
python3 scripts/bench/sign_det_semantics.py --output /tmp/bkr-semantic-probes.json
```

The output path must be fresh. The runner automatically selects and leases
its CPU. Raw records retain all completed observations, compiler output,
artifact sizes, source hashes, dependency identities and host context:

- [Complete measurement](bench-results/hex-sign-det-semantics-8ba814887-chungus2.json).
- [Incremental arm records](bench-results/hex-sign-det-semantics-8ba814887-chungus2.json.samples.jsonl).
