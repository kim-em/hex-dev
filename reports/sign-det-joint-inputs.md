# Joint re-encoding inputs

For odd n at least three, use the source heads `X^n-1` and `X^n+1`, whose
unique real roots are 1 and -1. The shared gcd producer returns the literal constant -2, so the actual
common head is `-(X^(2n)-1)/2`, with exactly those two real roots. The fixture
retains that scaling and its reversed target derivative signs; it does not
substitute a monic normalization. The fixture in `bench/HexSignDet/Joint.lean`
constructs actual partial descriptors using the highest derivative's positive
sign, completes both through `Descriptor.buildCompletion`, and invokes the
actual cross-polynomial `Descriptor.buildComparison`. It checks the common
head literally and requires the result `gt`.

The implementation constructs two separate re-encoding tables. Each query list
contains the 2n target derivatives, the source defining equation, and its n
source derivatives, in exactly that order. Thus each has `s=3n+1` queries;
this is neither a combined list of both sources nor just the common head's
derivatives. The total query degree is `D=n(5n-1)/2`. The two source derivative
polynomial lists agree, but their defining equations and selected-root sign
vectors differ. They must retain separate bindings.

The reduced tables come directly from the two re-encoding evidence trees
returned by the comparison producer. The unreduced producer receives a prepared domain recomputed from
the same polynomial and interval and ordered query list. Both complete tables must
match direct rational evaluation at the known roots -1 and 1, each with count
one. The target descriptor words are checked at their selected roots. The
fixture checks actual graph replay and byte-decoded replay in both modes.
A full ternary reference would have `3^(3n+1)` columns and is not enumerated;
small-input reduced/full agreement has its separate existing evidence.

The independent Python validator reconstructs every literal polynomial,
source slot/sign vector and both complete tables using integer factorials
and evaluation, including the actual negative half-scale of the common head. It computes candidate dimensions recursively from the two
known-root restrictions before solving: leaf dimensions are three, and each
parent dimension is the product of the distinct child supports. Each query
polynomial is distinct, so exact DAG encoding cannot identify two nodes with
different query lists. It checks all tree/graph dimensions and edge counts.
The matrix inverse/denominator bits and certificate bytes are recorded positive
integers; the validator checks the query-witness bit maxima against the formulas
described below. Witness
bits scan stored query/reduction certificates, including quotient and scaling
fields; they are not peak intermediate values, allocated bytes or live memory.

`inspect-joint` selects degrees 3, 7, 15, 31 and 63; `inspect-joint N` selects
one development input. This is an untimed correctness and input inventory.
No timing registration or cost-model verdict follows from it. Separate completion, comparison/re-encoding, reduced/direct construction
and checking measurements, intermediate coefficient observations and allocation
coverage remain required for the joint-encoding Phase-4 evaluation.

This family varies query count, degree and coefficient size. Realized support
is always two and candidate matrices have at most four columns. Its constant
gcd removes no shared roots; both endpoints are infinite, and only the source
equation has a zero sign. It does not cover heads with more than two real roots
(support above two or matrices wider than four columns), shared roots or finite
endpoint constraints.

## Recorded inventory

The source revision `9651d8947017a7256694c13eebe60d242eb34d7f` supplies
all ten rows for the five degrees and both sources. Graph and byte replay
succeeded in both production modes. The independent validator checked all
literal polynomials, derivative words, complete tables and dimensions. The
archive reconstructs and verifies all 252 recorded local source hashes; the
collector also verifies build freshness and unchanged source and executable
hashes. This records zero scientific timing samples.

The table shows the left-source observations; the right-source witness-bit
counts and dimensions agree, while its serialized byte counts differ slightly.

| Source degree | Joint queries | Query slots | Maximum columns | Graph nodes | Reduced witness bits | Direct witness bits | Reduced bytes | Direct bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 10 | 56 | 4 | 19 | 9 | 19 | 38106 | 33328 |
| 7 | 22 | 128 | 4 | 43 | 36 | 74 | 147150 | 129918 |
| 15 | 46 | 272 | 4 | 91 | 107 | 218 | 568030 | 505153 |
| 31 | 94 | 560 | 4 | 187 | 284 | 571 | 2238009 | 1996784 |
| 63 | 190 | 1136 | 4 | 379 | 702 | 1409 | 8982781 | 8016166 |

The matrices remain bounded while polynomial degrees, stored witness bits and
serialized certificates grow. Every query has degree below the common head,
so reduction modulo that head cannot lower its degree. Reduced mode normalizes
monomials to ±X^k and stores their scale factors; its maximum is the normalization scale of the common head's constant
2n-th derivative, whose absolute value is `(2n)!/2`. In direct mode the initial
Sturm–Tarski remainder for its squared query has leading coefficient
`−n·((2n)!/2)²`; the chain stores that absolute value as its initial right scale.
This is the direct witness-bit maximum in the retained rows, and the validator
checks its formula. Normalizing first avoids storing that large product.
These are stored intermediate coefficients and scales, not measurements of the
largest temporary value reached during arithmetic. The additional evidence makes the reduced
serialized certificates larger. Neither observation measures time or allocation,
and this family cannot supply the required comparison of unreduced and
modulo-head moment construction on joint-encoding lists.

The [metadata](data/sign-det-joint/9651d8947/metadata.json) and
[raw inventory](data/sign-det-joint/9651d8947/inventory.jsonl) retain both source
bindings and every field. The retained patch reconstructs the measured source
against merged base `0ddbca525898432d311a80ebb97ee52427e111af`;
the recorded revision need not remain on a branch after rebasing. The retained
archive describes that exact source, not later revisions. Its Lake configuration
and report differ after rebasing and recording the inventory. Subsequent fixture
checks additionally retain the observed order, check the gcd factor literally,
and compare decoded replay tables with the root oracle. They do not change
these retained observations or establish a new collected-source claim. New
collections bind executable sources and validators, excluding the editable report.
To collect a new source-bound inventory,
commit the sources, build `hexsigndet_bench`, then run
`python3 scripts/bench/sign_det_joint.py --collect /tmp/unique-joint-output`.
The collector leases one CPU, records host activity and retains failed command
output; it does not select samples by host activity or run a timing campaign.
