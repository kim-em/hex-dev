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

The source has eleven `Sturm.prepare` calls, each constructing one squarefree
signed-remainder chain: three for initial descriptors, four for re-encoding
domains and four for target validation. Each table moment invokes
`Sturm.certifyPrepared` once, constructing one query chain. Thus the query-chain
construction counts are 223, 304 and 451 respectively, in addition to the
eleven squarefree-chain constructions. The two `CommonProduct.build` calls
start two explicit polynomial gcd calculations and make six explicit
`DensePoly.divMod` calls, excluding divisions internal to gcd. These are source
construction counts, not instrumented CPU calls or integer-normalization gcd
counts. Chain construction and moment reduction use positive pseudo-division.

The counts include repeated work. There are only two distinct squarefree
chains: P once and Q ten times. All four target tables are identical; the
left joint table is also constructed twice. The inventory excludes
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
to derive them independently. All three cases and fifteen adversarial/oracle
unit checks pass. Polynomial, callback-digest and joint-count bindings agree
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
