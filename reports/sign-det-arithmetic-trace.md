# Rational coefficient sizes in small shared-root comparisons

The diagnostic calls the existing BKR/Thom constructors with observed ordinary
rational operations. It compares the positive root of P=X²−2 with the same
root and the last integer root of
Q=P(X−3)…(X−(n+2)), for n=1,2,3. It constructs the three source descriptors,
four descriptors re-encoded on the common polynomial, and four joint tables.
All eleven returned table certificates also pass the ordinary, unobserved
rational checker. Equality and strict-order guards both pass.

| Extra factors n | Observed coefficient calls | Maximum normalized numerator/denominator bits | Binary-operation temporary integer bound |
|---:|---:|---:|---:|
| 1 | 86,461 | 35 | 71 |
| 2 | 173,869 | 75 | 151 |
| 3 | 377,557 | 161 | 323 |

These are diagnostic observations, not timings or a general scaling law.
Compiler sharing can affect call counts. No large measurement ladder is
needed to obtain these observations.

## What is observed

[`ArithmeticTrace.lean`](../bench/HexSignDet/ArithmeticTrace.lean) supplies local
addition, subtraction, multiplication, division, inverse, negation and natural
casts. Each wrapper computes the ordinary rational result, observes both
operands and the result, and returns the result unchanged. The explicit sign
operation also observes its input. No field instance, arithmetic algorithm or
query kernel is replaced. `keep_eq` proves that the observation Boolean cannot
change the returned value. The native observer only updates a private counter
and maximum; its implementation is measurement code, not a semantic premise.

The supplied operations cover generic polynomial arithmetic in preparation,
derivatives, query construction, pseudo-division, remainder chains,
normalization and common-product gcd/division on this route. The maximum
includes intermediate coefficient values that are absent from the retained
certificate. It excludes rational leaf matrix arithmetic and integer rank,
transport and matrix checks, which use their own fixed operations; their
source bounds are separate. Index arithmetic, allocation, live memory and
native big-integer scratch storage are also excluded. These are rational-field
cases, not measurements of nested algebraic coefficient arithmetic.

For a normalized operand numerator/denominator size of at most B bits, ordinary
`Rat.add`/`Rat.sub` form at most two products of B-bit integers and their sum;
`Rat.mul`/`Rat.div` cancel before multiplying. All coefficient integers formed
inside these binary operations therefore need at most 2B+1 bits. Inverse and
negation do not increase that bound. The last column is this source-derived
bound applied to the observed maximum; it is not a direct observation of
internal integer temporaries or backend scratch storage.

The standard checker runs outside the local observed operations. Its
acceptance and the independent exact polynomial/root oracle check the
mathematical subjects and outcomes. They do not independently validate the
native counter or maximum. The executable rejects zero observed calls so an
eliminated observer cannot silently produce a successful record.

## Reproduction and retained records

```
lake build hexsigndet_arithmetic_trace
.lake/build/bin/hexsigndet_arithmetic_trace > /tmp/sign-det-arithmetic-trace.jsonl
python3 scripts/bench/sign_det_arithmetic_trace.py /tmp/sign-det-arithmetic-trace.jsonl
python3 -m unittest scripts/bench/test_sign_det_arithmetic_trace.py
```

The oracle needs the existing python-flint dependency. It checks P and Q, their
exact gcd/product, the actual selected intervals and root orders using rational
squares and the known linear roots. Mutation tests reject changed subjects,
intervals, outcomes and missing observations.

[Observations](bench-results/sign-det-arithmetic-trace/observations.jsonl) and
[metadata](bench-results/sign-det-arithmetic-trace/metadata.json) bind the
retained output to the source revision, source hashes and native binary hash.
The existing CI job builds and runs the small diagnostic and its independent
checks. This does not establish a general polynomial-chain or nested-field
coefficient-growth theorem, timing law or Phase-4 attestation.
