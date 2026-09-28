# Sign-determination inputs with maximal support

The fixture in `bench/HexSignDet/Maximal.lean` realizes every ternary word of
length `s` at a distinct integer root. Set `n = 3^s` and use the point product
with roots `0,…,n−1` as the head. The existing `HexPolyFast.InterpPlan` constructs
one query per coordinate, taking the prescribed values `−1,0,1` at those roots.
The constructor checks the word count, distinctness, lengths and sign range,
then checks every head and query evaluation directly over `Rat`.

The point product has degree `n` and these `n` distinct roots. Consequently the
expected complete sign table has all `3^s` words with count one. The actual
reduced producer, unreduced producer and full reference solver must return
that exact ordered table. Full reference replay and the generally encoded
reduced graph must also accept. The fixture returns no input if any check
fails. This known-root construction is independent of the Tarski variation
calculation; it does not prove arbitrary-field semantic replay soundness.

The fixed inventory is retained under
[`data/sign-det-maximal/247dfcc2c`](data/sign-det-maximal/247dfcc2c), including
metadata, the executable hash and a reconstructible source archive. It was
collected with the automatically leased CPU 77 on the shared host. All three
completed inputs are retained.

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
gates in the SPEC remain open. The benchmark smoke checks and successful
compilation do not discharge those gates.

Reproduce the inventory with `lake build hexsigndet_bench` followed by
`.lake/build/bin/hexsigndet_bench inspect-maximal`. For source reproduction,
apply the recorded patch to its recorded base and verify every source hash
in `metadata.json`; the archive remains usable after rebases and squash merges.
