# Work in the small shared-root comparisons

The [timed examples](sign-det-shared-roots.md) compare the positive root of
P=X²−2 with two roots of Q=P(X−3)…(X−(n+2)), for n=1,2,3. This supplement
inspects the actual descriptors, both common products and all tables returned
by those callbacks. It collects no timings.

## Construction inventory

Each callback constructs eleven tables: three initial descriptors, four target
validations and four joint re-encodings. In this order, their moment counts are:

| Extra factors n | Initial descriptors | Four target validations | Four joint tables | Total table moments | Maximum table coefficient/witness bits |
| ---: | --- | --- | --- | ---: | ---: |
| 1 | 1/1/1 | 15/15/15/15 | 43/40/43/34 | 223 | 26 |
| 2 | 1/1/1 | 24/24/24/24 | 55/51/55/44 | 304 | 51 |
| 3 | 1/1/1 | 41/41/41/41 | 75/71/75/63 | 451 | 111 |

The bit maximum includes rational coefficients of table heads, queries,
query polynomials, signed-remainder chains and chain/reduction witnesses.
It excludes integer linear-algebra witnesses, common-product quotients and
interval endpoints. It is a maximum of stored operands, not an observed peak
of temporary arithmetic or allocation.

Each callback executes eleven `Sturm.prepare` calls, each constructing one squarefree
signed-remainder chain: three for initial descriptors, four for re-encoding
domains and four for target validation. Each table moment invokes
`Sturm.certifyPrepared` once, constructing one query chain. Thus the query-chain
construction counts are 223, 304 and 451 respectively, in addition to the
eleven squarefree-chain constructions. The two `CommonProduct.build` calls
start two explicit polynomial gcd calculations and make six explicit
`DensePoly.divMod` calls, excluding divisions internal to gcd. These are source
construction counts, not instrumented CPU calls or integer-normalization gcd
counts. Chain construction and moment reduction use positive pseudo-division.
The chains themselves are Euclidean remainder sequences; two explicit
common-product gcds are not a count of all remainder-sequence work.

The comparison constructors run four `checkReencoding` guards, two
`fullOrder` guards and two `CommonProduct.check` guards. Each common-product
guard checks four polynomial products. These guards are additional to the
eleven `buildPrepared` checks, and their work belongs to the timed callbacks.

### Derivative-work bounds

Source bounds also account for derivative construction without another timing
collection. Put d=n+2, let T be the total table moments above, and let J be the
sum of the four joint-table counts (160, 205 and 284). Count polynomial
`derivative` operations, not their individual coefficient multiplications.

`RawDescriptor.queries` constructs a full derivative list before selecting its
indices. There are seven descriptor builds. Each of the four re-encodings
accesses the target and source queries when constructing its joint list,
accesses the target queries in each row of the filter, accesses them again
when taking the selected word, and accesses both lists in `checkReencoding`.
The successful joint table has positive row counts summing to the d distinct
real roots of the common head Q. Its checked interpretation therefore bounds
its row count by d; this uses semantic correctness, not just matrix replay.
Thus there are at most 27+4d derivative-list accesses. Five
accesses have head P of degree two; the rest have head Q of degree d. Their
total polynomial-derivative count is at most 10+22d+4d². This includes lists
whose selected index list is empty under source evaluation. Compiler
optimizations can reduce executed work.

The eleven prepared domains and T query chains each construct one derivative
of their head, giving 11+T additional operations. For supplied replay,
`SignedRemainderChain.check` computes one head derivative. A node with a
matching domain cache checks the domain once and each query once; without
the cache it checks both domain and query per moment. The returned certificates
reuse their prepared domain's exact squarefree witness, so cache bindings
match. Each replay therefore needs at most twice its moment count in head
derivatives. The eleven builder replays and four extra joint replays contribute
at most 2(T+J). Domain caching happens within a node; this bound does not assume
one cache shared across the whole tree.

| n | Descriptor-query derivatives, upper bound | Chain construction derivatives | Replay derivatives, upper bound | Total, upper bound |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 112 | 234 | 766 | 1112 |
| 2 | 162 | 315 | 1018 | 1495 |
| 3 | 220 | 462 | 1470 | 2152 |

These are finite source-operation bounds for the successful callbacks, not
instrumented machine-call counts. Compiler hoisting and dead-code elimination
can reduce executed work. The bounds cover descriptor extraction, construction
and replay separately; they imply no general polynomial-degree or bit-time law.

The earlier construction counts include repeated work. There are only two distinct squarefree
chains: P once and Q ten times. All four target tables are identical; the
left joint table is also constructed twice. Those construction counts exclude
query-preprocessing and moment-reduction pseudo-divisions, post-construction
table checks, re-encoding guards and cached-domain checks. `buildPrepared`
checks all eleven tables; `checkReencoding` additionally checks the four joint
tables. The timed callbacks include this checking, so the construction counts
are not a decomposition of their elapsed times.

## Independent checks and provenance

The [validated record](data/sign-det-shared-root-work/validated/metadata.json)
retains native output, commands, exact source and binary hashes, a source
reconstruction patch and the oracle output. Its source snapshot is
7823a84ef8; metadata records the full revision and reconstructible base.
The [initial record](data/sign-det-shared-root-work/e9861712e4/metadata.json)
is also retained. That initial schema did not export the strict comparison's
head and common product; it does not establish the final validator's coverage.

The final oracle independently reconstructs P and Q with FLINT and checks both
common products, allowing scalar gcd normalization while retaining the exact
product identity. It counts the explicit roots ±sqrt(2),3,…,n+2 inside each
actual descriptor interval using rational squares, rejects endpoint roots,
and derives both equality and strict ordering from the selected roots.
It checks the schema of native table counts and bit maxima without claiming
to derive them independently. All three cases pass the archived oracle.
Fifteen adversarial/oracle unit checks passed locally at source 7823a84ef8;
that unit-test output is not part of the retained collector archive. Polynomial,
callback-digest and joint-count bindings agree
with the original timed inventory; this is not a new timing observation or a
claim that the diagnostic binary equals the timed binary.

Reproduce the inspection and oracle with:

```sh
lake build hexsigndet_bench
.lake/build/bin/hexsigndet_bench inspect-shared-roots-work > /tmp/shared-root-work.jsonl
python3 scripts/bench/sign_det_shared_root_work.py /tmp/shared-root-work.jsonl
python3 -m unittest scripts.bench.test_sign_det_shared_root_work
```

The Python checks require python-flint. Bench `verify` runs the native inventory
as a cheap correctness check; scientific timing claims remain in the separate
retained timing report. Neither this supplement nor those small cases prove a
bound for general polynomial gcds, nested fields or quantifier elimination.
