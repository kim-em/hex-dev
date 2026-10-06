# Rational coefficient sizes in small shared-root comparisons

The diagnostic calls the existing BKR/Thom constructors with observed ordinary
rational operations. It compares the positive root of P=X²−2 with the same
root and the last integer root of
Q=P(X−3)…(X−(n+2)), for n=1,2,3. It constructs the three source descriptors,
four descriptors re-encoded on the common polynomial, and four joint tables.
The seven distinct descriptors and four joint tables also pass ordinary,
unobserved checks against their emitted polynomials, intervals, derivative
queries and count-one conditions. Both common products and full-word orders
are checked with ordinary operations; equality and strict-order guards pass.
The independent oracle identifies the emitted polynomials with P and Q.

| Extra factors n | Observed coefficient calls | Maximum normalized numerator/denominator bits | Binary-operation temporary integer bound |
|---:|---:|---:|---:|
| 1 | 86,461 | 35 | 71 |
| 2 | 173,869 | 75 | 151 |
| 3 | 377,557 | 161 | 323 |

These are diagnostic observations, not timings or a general scaling law.
Counts include input construction and the producers' own acceptance checks.
Compiler sharing can affect call counts. No large measurement ladder is
needed to obtain these observations.

## What is observed

[`ArithmeticTrace.lean`](../bench/HexSignDet/ArithmeticTrace.lean) supplies local
addition, subtraction, multiplication, division, inverse, negation and natural
casts. Each wrapper computes the ordinary rational result, observes both
operands and the result, and returns the result unchanged. The explicit sign
operation also observes its input. No field instance, arithmetic algorithm or
query kernel is replaced. Each of the eight operation counters is nonzero in
every case; their order is add, sub, mul, div, inv, neg, cast, sign. `keep_eq` proves that the observation Boolean cannot
change the returned value. The native observer only updates a private counter
and maximum; its implementation is measurement code, not a semantic premise.

Source inspection shows that the supplied operations reach generic polynomial arithmetic in preparation,
derivatives, query construction, pseudo-division, remainder chains,
normalization and common-product gcd/division on this route. Since P divides Q,
these gcds terminate after an exact division; they do not measure coefficient
growth in a nontrivial gcd remainder sequence. The maximum
includes intermediate coefficient values that are absent from the retained
certificate. It excludes rational leaf matrix arithmetic and integer rank,
transport and matrix checks, which use their own fixed operations; their
source bounds are recorded separately in [the consolidated evidence PR](https://github.com/kim-em/hex-dev/pull/10808). Index arithmetic, allocation, live memory and
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
native counter or maximum. The executable rejects any operation with zero recorded calls. The native
observer itself is marked `noinline` and `never_extract`. These checks detect
missing operation categories, not every possible compiler sharing decision.

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
[metadata](bench-results/sign-det-arithmetic-trace/metadata.json) record the
source revision, source hashes and native binary hash. CI verifies retained
output and source-blob hashes using a main commit plus an archived patch; the binary hash identifies the locally built
executable and is not compared with binaries rebuilt on other hosts. The
source revision is informational; reconstruction never needs the original
head commit. The initial schema and weaker subject checks remain in the linked archive's
`initial/` directory. Its counts and maxima agree with the expanded records.
The existing CI job builds and runs the small diagnostic and its independent
checks. This does not establish a general polynomial-chain or nested-field
coefficient-growth theorem, timing law or Phase-4 attestation.
