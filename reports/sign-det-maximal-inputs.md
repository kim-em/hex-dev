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

This is an untimed input and correctness inventory. It adds maximal-support
coverage to the existing sparse family but contains no scientific timing
samples, complexity verdict or speedup claim. The broader degree, support,
coefficient-size, witness-size, nested-evidence, descriptor and performance
requirements in the SPEC remain open. The benchmark fast checks and successful
compilation do not discharge those requirements.

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
