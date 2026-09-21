# Ordered rational-function proofs

`HexOrderedFnMathlib` proves containment for the exact rational bound
operations and the actual array Horner evaluator in `HexOrderedFn`. It proves
successful finite signs, per-query total signs, and derived approximation
containment, with integer signs explicitly related to Mathlib's
`SignType.sign`. The full contract is in
[hex-ordered-fn-mathlib](../SPEC/Libraries/hex-ordered-fn-mathlib.md).

Fix the Mathlib field's `Field.toGrindField` dictionary before forming a
`RationalFn K`; the field dictionary indexes its carrier. The tests
deliberately form their fractions under that dictionary, sharing the
polynomial inputs with the computational fixtures. Computational tests
separately exercise Lean core's rational field.

`Real.eval` evaluates a stored canonical fraction by total real division. It
is not an injective field homomorphism at an arbitrary subject.
`Real.finiteAttempt_sound` and `Real.sign?_sound` establish denominator
nonvanishing as well as the sign. Expression consumers must still retain all
original divisor premises: cancellation inside a formal fraction does not
justify cancelling a source divisor at its root.

Containment is sufficient for successful-trial soundness. Progress is a
separate premise of each total search. `Real.sign_of_attempt` uses a checked
finite success and sign uniqueness to prove the total result without reducing
its opaque accessibility proof. `Real.approx_contains` holds even for
nonpositive requests, which run the width-one search. It is separate from the
computational `Real.approx_width` theorem for positive requests.

```sh
lake build HexOrderedFnMathlib HexOrderedFnTests
```

The build includes ordinary-kernel proof tests, public axiom-dependency
checks, and finite comparisons at sqrt(2) with proved rational source bounds.
The sqrt(2) fixture supplies no transcendence assumption. Rational fixtures
here prove results for total searches with finite termination evidence.
`conformance/HexOrderedFn/Conformance.lean` executes those algorithms after
proof erasure on the separate core-field fixtures.

Phase 1 remains incomplete. The generic Horner/quotient convergence proofs,
universal progress, injective real evaluation and ordered-field instances,
Laurent/Hahn interpretation, Liouville integration fixture, checked source
transport, and separate Phase-4 proof evidence remain outstanding under
[#10376](https://github.com/kim-em/hex-dev/issues/10376).
