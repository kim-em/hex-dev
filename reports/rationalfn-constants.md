# Nested rational-function constants

The ordinary rational-function implementation constructs polynomial one as
`#[1]`, with its normalization supplied by the field law `1 ≠ 0`. Polynomial
embedding uses that direct denominator. One shares this polynomial between its
numerator and denominator; zero has an empty numerator and the direct denominator.
Natural casts and numerals zero and one reuse these instances. The compiler
replacements have ordinary kernel proofs of equality to the original stored
pairs, with no new axioms or admissions. The Mathlib field instance uses the same
cast and retains its proved equality with the computational field dictionary.

Let u(j) and z(j) count construction at extension depth j. The changed source
gives `u(j)=u(j−1)+Θ(1)` and `z(j)=u(j−1)+Θ(1)`, hence Θ(j). Destruction also
visits only the shared chain. The former branching recurrence has dominant
eigenvalue `2+√2`; its retained observations remain in the
[nested sign report](sign-det-nested-signs.md).

## Comparison protocol

The [runner](../scripts/bench/rationalfn_constants.py) declares six trial-major
rounds, adjacent before/after arms with alternating AB/BA order, a 100 ms inner
target and a 30-second child cap. It uses the pinned LeanBench child sampler
without changing field arithmetic. It leases one CPU, records host load,
retains every sample and checks clean source and executable hashes before and
after collection. Host activity does not remove samples or trigger retries.

| Operation | Extension depths | Timed work |
| --- | --- | --- |
| Zero and one | 2, 6, 10 | Ordinary numeral construction and destruction, plus fixed-size stored-pair length consumption. |
| Arithmetic consumer | 1, 2, 3 | Multiply the prepared fraction `(X+1)/(X−1)` by one, add zero, and hash its complete recursive coefficient arrays. |
| Scalar sign | 6, 9, 12 | Existing `Infinitesimal.sign` of the newest positive infinitesimal. |

Dictionary construction, operand preparation and complete literal encoding are
outside timing. Full constructor outputs and arithmetic outputs are separately
checked against independent expected coefficient arrays, including denominators;
shallow constructor lengths alone are not the correctness oracle. The arithmetic
comparison records representative elapsed times rather than asserting a scaling
law: internal coefficient work and recursive hashing vary with depth.

The constructor registration models Θ(d) for the changed source. The downstream
scalar sign registration separately models Θ(2^d), with its remaining constructor
and structural comparison costs accounted for in the
[derivation](sign-det-nested-signs.md). Paired ratios do not establish either
scaling law by themselves.

```sh
python3 scripts/bench/rationalfn_constants.py \
  --before /path/to/baseline-worktree --after /path/to/repaired-worktree \
  --output /path/to/new-captures
```

Both executables must be built from committed source; the baseline includes the
identical new measurement module without the arithmetic repair. Historical
observations are retained unchanged. HexOrderedFn's completed degree families
hold extension depth fixed at one, two or three, so their source bounds remain
valid; this repair changes constants on those families. No HexPoly or
HexOrderedFn implementation is changed.
