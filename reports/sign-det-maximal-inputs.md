# Sign-determination inputs with maximal support

The fixture in `bench/HexSignDet/Maximal.lean` realizes every ternary word of
length `s` at a distinct integer root. Set `n = 3^s` and use the point product
with roots `0,…,n−1` as the head. The existing `HexPolyFast.InterpPlan` constructs
one query per coordinate, taking the prescribed values `−1,0,1` at those roots.
Sanity checks validate word count, distinctness, lengths and sign range.
The roots are distinct by construction; the constructor checks degree and
every head and query evaluation directly over `Rat`.

The point product has degree `n` and these `n` distinct roots. Consequently the
expected complete sign table has all `3^s` words with count one. The actual
reduced producer, unreduced producer and full reference solver must return
that exact ordered table. Full reference replay and the generally encoded
reduced graph must also accept. The fixture reports which validation failed and returns no input on failure. This known-root construction is independent of the Tarski variation
calculation; it does not prove arbitrary-field semantic replay soundness.

The inventory collected by the committed driver with an up-to-date executable
is retained under
[`data/sign-det-maximal/7f85749b9`](data/sign-det-maximal/7f85749b9), including
metadata, the executable hash and a reconstructible source archive. All three
completed inputs are retained. Earlier records from a temporary collector remain
under [`data/sign-det-maximal/247dfcc2c`](data/sign-det-maximal/247dfcc2c) and
[`data/sign-det-maximal/4b5e1b29e`](data/sign-det-maximal/4b5e1b29e); their metadata
uses an older format. The table below is identical in all retained records.

| Queries | Head degree / roots / realized conditions | Maximum matrix size | Query degree | Head coefficient bits | Query coefficient bits | Remainder coefficient bits | Query slots | Tree / graph nodes |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 3 | 3 | 1 | 2 | 1 | 2 | 3 | 1 / 1 |
| 2 | 9 | 9 | 7 | 17 | 12 | 19 | 15 | 3 / 3 |
| 3 | 27 | 27 | 25 | 92 | 81 | 133 | 45 | 5 / 5 |

Coefficient bits are the maximum numerator/denominator bit length of stored
rational coefficients. Remainder bits scan the stored query chains. These are
not peak intermediate bit counts; normalization, intermediate arithmetic,
other witness fields and allocation are not measured here. Graph edges are
0, 2 and 4, respectively. No nodes are shared in these three graphs.

These inventories are untimed correctness evidence. The fixed complete-workflow
measurements below supply separate timing observations; the broader families
and their coverage limits are described in [the performance report](sign-det-performance.md).
Benchmark fast checks and successful compilation do not supply timing evidence.

Reproduce the inventory with `lake build hexsigndet_bench` followed by
`.lake/build/bin/hexsigndet_bench inspect-maximal`. For source reproduction,
apply the recorded patch to its recorded base and verify every source hash
in `metadata.json`; the archive remains usable after rebases and squash merges.

Validation before the additional `verify` integration is retained under
[`data/sign-det-maximal/4b5e1b29e`](data/sign-det-maximal/4b5e1b29e). All three
inventories match the earlier record exactly, including the input and table
hashes. Its source archive reconstructs every recorded source hash from merged
base `a6cc38bf2`. This is another correctness inventory, with zero scientific
timing samples. The diagnostic refactor produces exactly the same successful inventories.
The existing
`verify` command checks the two-query, nine-root input before the registered
benchmark fast checks; this exercises a split node and nontrivial modular
reduction.

Collect a new revision-bound inventory with
`python3 scripts/bench/sign_det_maximal.py --output <new-directory>` after
committing the sources and building the executable. The driver leases one CPU,
retains raw output, reconstructs and checks every archived source hash, and
records the executable hash and host load. It rejects an existing output
directory or changed sources. After setup, collection and validation failures retain their output and metadata.

The record from this collector is retained under
[`data/sign-det-maximal/b8bbe9fd1`](data/sign-det-maximal/b8bbe9fd1).
All three inventories reproduce the earlier dimensions and hashes exactly.
Its metadata uses the shared source-archive schema, including the base,
patch application option and reconstruction check. This record also contains
zero scientific timing samples; earlier completed records remain unchanged.

The later [`7f85749b9` record](data/sign-det-maximal/7f85749b9) additionally
checks build freshness using `lake build --no-build hexsigndet_bench`, and
records matching executable hashes and source revisions before and after the
collection. Its archived sources include the collector regression tests.
All earlier records remain unchanged, including the first committed-collector
record linked above. None of these records supplies scientific timings.

## Complete workflow timings

The separate [fixed workflow collection](data/sign-det-maximal/workflow-9c6565e68e)
retains six trials for each of the three inputs, in trial-major order. The
`maximalOne`, `maximalTwo` and `maximalThree` registrations use LeanBench's
fixed harness, with warmup, one observation per invocation and a 0.1-second
inner-repeat target. Collection leases one CPU on the shared host and retains
every export, stdout, stderr and host-load observation. No timing law or
acceptance threshold is fitted to these three cases.

The warmup runs in a separate process. The 27-root observations have one
inner repetition and measure a first call in a fresh process; the smaller
cases are batches after auto-tuning in their measured process. They therefore
have different cache conditions. The table uses the arithmetic mean of the
two middle values across six observations, rather than LeanBench's upper-middle
convention. All original observations and configurations remain unchanged.

| Queries | Roots / realized sign conditions | Median complete-workflow time |
| ---: | ---: | ---: |
| 1 | 3 | 0.393 ms |
| 2 | 9 | 15.98 ms |
| 3 | 27 | 1.909 s |

The timed body calls the existing `buildMaximal`, including input interpolation,
domain preparation, reduced and direct producers, the full reference solve,
checks against every prescribed root/sign condition, certificate replay and
result hashing. These are whole-workflow observations, not isolated production
or matrix-checker timings and not a speed comparison between the algorithms.
The timed constructor checks the prescribed integer-root sign table by direct
evaluation. The retained input hashes also match the earlier `7f85749b9`
inventory; the export hash is the hash of the resulting `Option UInt64`.

The archived metadata records the measured executable hash and binds all source hashes to
a patch against a permanent merged base. The validation command
`python3 -m scripts.bench.sign_det_maximal_workflow_archive` checks the retained
bytes, all 18 observations, schedule, outputs and recomputed medians, and
reconstructs the measured sources. Reproduce a new collection after committing
sources and building with
`python3 scripts/bench/sign_det_maximal_workflow.py --output <new-directory>`.
The earlier untimed inventories remain unchanged.

The current registrations set expected result hashes so CI rejects error
results. The historical timing configuration had no registered expected hash;
its collector checked the observed hash against the separate successful
inventory. The archive validator accepts that specific historical configuration.
These three inputs do not establish general degree, coefficient-size,
witness-size or descriptor performance bounds; the other named families and
their limits are described in the consolidated report.
