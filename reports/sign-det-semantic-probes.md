# BKR root-count proof probes

The semantic probes apply `Replay.count_roots` to literal accepted graphs at
depths 1, 3, 5 and 7. Acceptance is proved in the existing `Accept` modules.
`Dag.check_replay` extracts a checked tree; the semantic theorem identifies
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
serialization, axiom inspection and variable Lake/process overhead. It is
not a measurement of kernel checking alone. Acceptance and the foundation
proofs are warm dependencies; their initial compilation and literal checker
reduction are excluded. The existing [graph replay probes](sign-det-proof-model.md)
measure literal checking separately. Semantic theorem inventories are guarded
to contain only `propext`, `Classical.choice` and `Quot.sound`.

These are diagnostic observations, with no complexity verdict or absolute
performance budget. They do not establish all Phase-4 requirements. The
ordinary CI proof-probe target builds the examples; timing runs are external.
