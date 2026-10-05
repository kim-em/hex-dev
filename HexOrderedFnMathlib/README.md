# Ordered rational-function proofs

`HexOrderedFnMathlib` proves containment for the exact rational bound
operations and the actual array Horner evaluator in `HexOrderedFn`. It proves
successful finite signs, per-query total signs, and derived approximation
containment, with integer signs explicitly related to Mathlib's
`SignType.sign`. The full contract is in
[hex-ordered-fn-mathlib](../SPEC/Libraries/hex-ordered-fn-mathlib.md).

The [OrderedFn manual chapter](https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-ordered-fn)
explains the public interpretation theorems beside their computational
operations, including the distinct hypotheses for finite signs and total
real extensions.

`Infinitesimal.embed` identifies rational functions with their Laurent series
in the lexicographically ordered Hahn field. The coefficient scan equals the
polynomial trailing coefficient; signs, normalization and comparisons agree
with this embedding. Scoped `LinearOrder`, `IsStrictOrderedRing` and core
ordered-ring instances make the rational-function field an ordered field.
`Infinitesimal.mapHom_sign` and `mapHom_strictMono` prove that the executable
coefficient map preserves signs and order under any ordered field embedding;
it also keeps constants and the infinitesimal indeterminate by the rational-function
map laws. This supplies the ordered coefficient transport needed when a tower
base is enlarged.

The indeterminate is positive and below every positive coefficient. Its
reciprocal exceeds every integer. At the next level, the new indeterminate
is below every natural power of the preceding one. `Hahn.mapHom` preserves
support, lowest exponent, leading coefficient and order, and commutes with
constant embeddings; `Infinitesimal.towerEmbed` gives the two-level model.

Fix the Mathlib field's `Field.toGrindField` dictionary before forming a
`RationalFn K`; the field dictionary indexes its carrier. `HexRationalFnMathlib.coreField_eq`
proves equality with the original core dictionary, allowing transport between
successive carriers. The tests use this equality, together with the rational
base case, to prove `δ < ε^n` for the carriers in the Mathlib-free test module.
Other semantic tests form their fractions under the Mathlib-derived dictionary.

`Real.eval` evaluates a stored canonical fraction by total real division.
Under relative transcendence, `Real.evalHom` is an injective field homomorphism
and agrees with Mathlib's rational-function evaluation. `Real.registration`
constructs a total provider registration from `Real.Valid`, a proposition
containing the semantic hypotheses. Embedding and subject witnesses erase
structurally from computation.
`Real.Extension` supplies the corresponding real order: install
`Extension.linearOrder` using `Extension.OrderValid`, and obtain
`Extension.strictOrderedRing` from containment and transcendence. `Extension.orderedRing` supplies the
core ordered-ring laws, and `Extension.coreField_eq` connects the core and
Mathlib field dictionaries by `rfl`. The Mathlib field instance is computable,
so ordinary expressions and successive real registrations compile in companion
contexts. Providers can be transported with checked
agreement of their embedding and subject.
`Real.finiteAttempt_sound` and `Real.sign?_sound` establish denominator
nonvanishing as well as the sign. Expression consumers must still retain all
original divisor premises: cancellation inside a formal fraction does not
justify cancelling a source divisor at its root.

Containment is sufficient for successful-trial soundness. `Real.horner_converges` proves narrowing by the actual Horner recurrence,
using explicit endpoint and product-width estimates. Quotient bounds narrow
away from zero. `Real.attempt_progress`, `approx_progress`, `sign_acc` and
`approx_acc` derive termination from containment, requested-width guarantees
and `RelativeTranscendence` over the entire predecessor field. `Real.sign_of_attempt` uses a checked
finite success and sign uniqueness to prove the total result without reducing
its opaque accessibility proof. `Real.approx_contains` holds even for
nonpositive requests, which run the width-one search. It is separate from the
computational `Real.approx_width` theorem for positive requests.

```sh
lake build HexOrderedFnMathlib HexOrderedFnTests hexorderedfn_liouville_test
.lake/build/bin/hexorderedfn_liouville_test
```

The build includes ordinary-kernel proof tests, public axiom-dependency
checks, and finite comparisons at sqrt(2) with proved rational source bounds.
The sqrt(2) fixture supplies no transcendence assumption. Rational fixtures
here prove results for total searches with finite termination evidence.
The Mathlib-free `conformance/HexOrderedFn/Conformance.lean` executes the core
fixtures. The separate `hexorderedfn_liouville_test` executable checks the
semantic integration after proof erasure.

The Liouville integration fixture proves containment and width for executable
rational partial sums of `liouvilleNumber 2`, transfers its transcendence from
integers to rationals, and exercises the registered total searches. Finite
attempt proofs establish the signs of `X-5/4`, `X-2` and their quotient;
compiled checks execute the total searches and derived approximation. The
fixture also checks provider transport, rejects wrong-subject evidence, and
adjoins a positive infinitesimal above the real field. A checked transport via
`ratField_eq` also runs the fixture on the core rational dictionary. A generic
second registration compiles under its relative-transcendence hypotheses, while
a finite outer query executes successive coefficient approximation without
postulating a second independent named constant.

The [computational performance report](../reports/hex-ordered-fn-performance.md)
records the runtime evidence. Downstream tower integration and clean/eager
normalization measurements are owned by hex-real-closure under
[#10378](https://github.com/kim-em/hex-dev/issues/10378).

The ordinary-kernel tests check the model and order laws and audit their axiom
dependencies. These theorem applications have no performance benchmark.
