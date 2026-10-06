# Coefficient operands in small nested infinitesimal tables

The diagnostic uses the existing canonical rational-function fields at depths
one and two over the rationals. It constructs complete BKR tables for P=X and
four or eight copies of the constant query equal to the newest positive
infinitesimal. P has the unique root zero; the complete answer is the all-positive
sign condition with count one. Actual defining polynomials, queries and
computed answers are included in each record and independently checked.

| Field depth | Queries | Observed coefficient calls | Maximum rational numerator/denominator bits | Maximum rational coordinate slots |
|---:|---:|---:|---:|---:|
| 1 | 4 | 1,097 | 1 | 3 |
| 1 | 8 | 2,305 | 1 | 3 |
| 2 | 4 | 1,097 | 1 | 5 |
| 2 | 8 | 2,305 | 1 | 5 |

These are small, untimed diagnostic observations. They show that these cases
use small coefficient operands while their representations contain more
rational coordinates at the higher depth. They do not establish a coefficient
growth law across arbitrary fields or inputs. The separate nested timing
measurements concern larger query lists and scalar signs; their constructor
and list-processing costs cannot be inferred from the bit maxima alone.

[`NestedTrace.lean`](../bench/HexSignDet/NestedTrace.lean) constructs only the
existing field instances. Local wrappers observe addition, subtraction,
multiplication, inverse, negation, natural casts and explicit signs supplied
to the generic table algorithms. Each returns the ordinary result unchanged;
`keep_eq` proves this independently of the observation Boolean. The native
observer updates a private counter and maxima. It is measurement code, not a
semantic premise. The returned table also passes the ordinary unobserved
checker.

For each observed coefficient operand/result, the size function traverses its
canonical recursive numerator/denominator representation. A coordinate slot
is one stored rational coefficient pair, including stored zeros and repeated
ones; maximum bit size concerns those pairs' integer components. Both maxima
include intermediate *outer* coefficient values not retained in the returned
table. They do not observe temporary values inside the existing field
arithmetic/sign dictionaries. Fixed rational leaf solving, integer matrix
arithmetic, index arithmetic, allocation and backend scratch are excluded.
The call count concerns the supplied generic operations only and may be
affected by compiler sharing. The executable rejects zero observed calls.

The independent oracle checks the actual canonical infinitesimal, head, query
polynomials and complete answer using their elementary mathematical meanings.
It checks counter/maxima schema, not the native measurements themselves.
Mutation tests reject changed polynomials, queries, signs, contexts, rejected
ordinary replay and missing observations.

```
lake build hexsigndet_nested_trace
.lake/build/bin/hexsigndet_nested_trace > /tmp/sign-det-nested-trace.jsonl
python3 scripts/bench/sign_det_nested_trace.py /tmp/sign-det-nested-trace.jsonl
python3 -m unittest scripts/bench/test_sign_det_nested_trace.py
```

[Records](bench-results/sign-det-nested-trace/observations.jsonl) and
[metadata](bench-results/sign-det-nested-trace/metadata.json) bind the source,
binary and output hashes. The small diagnostic and independent checks extend
the existing CI job. There is no timing comparison, new arithmetic instance,
tower implementation or Phase-4 attestation in this diagnostic.
