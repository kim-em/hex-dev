# hex-ordered-fn-mathlib

Semantic companion for [hex-ordered-fn](hex-ordered-fn.md): exact rational
functions ordered by a computable transcendental real or by a positive
infinitesimal. It proves the two interpretations, ordinary field/order
correspondence and termination of real sign search from user-supplied correct
convergent approximations. The new declaration shapes below are required
contracts, not claims of existing checked implementations.

## Placement and executable carriers

`HexOrderedFnMathlib` imports `HexOrderedFn`, `HexRationalFnMathlib`,
`HexPolyMathlib` and Mathlib. No computational library imports this companion;
no existing input acquires a family dependency. `HexInterval` and
`HexIntervalMathlib` are not inputs. A future downstream adapter may connect
a separate enclosure library without becoming a prerequisite here.

Use namespace `Hex.OrderedFn`, with `Real` and `Infinitesimal` namespaces
matching the computational API. Modules are `Correspondence`, `Real`,
`Infinitesimal` and build-only `Tests`. The companion owns semantic proofs;
it supplies no approximation generator or analytic provider proof for named
constants such as π or e.

Fix `[Field K] [LinearOrder K] [IsStrictOrderedRing K]`. Choose
`Field.toGrindField` and `LinearOrder.toDecidableEq` before forming
`Hex.RationalFn K`, following
[hex-rational-fn-mathlib](../../HexRationalFnMathlib/SPEC/hex-rational-fn-mathlib.md).
Those dictionaries index the representation; keep them fixed through
conversions. Require actual executable coefficient arithmetic and decisions.
A noncomputable Mathlib order can model the semantics but cannot substitute
for a compiled coefficient comparison.

Both extensions reuse total RationalFn arithmetic and equality. Separate
opt-in wrappers/scopes carry their orders. Interpretations into ℝ or Hahn
series may be noncomputable; the runtime never evaluates those maps. The
existing representation and arithmetic correspondence are proved once and
reused. There are no raw coefficient operation records, per-operation
certificates or resource budgets to interpret.

The computational sign is an `Int` in `{-1,0,1}`. Relate it explicitly to
Mathlib's `SignType.sign`, using the integer images of `neg`, `zero`, `pos`.
In the statements below `sgn` denotes that integer-valued semantic sign.
Prove the compatibility once and reuse the ordered-field sign laws.

Executable sign/refinement follows the
[shared execution contract](../real-closure-execution.md). The core takes
only its rational-bound procedures and core-expressible progress proof.
This companion derives progress and order laws from containment, convergence
and relative transcendence, but order laws are not executable arguments.
Finite checked-success proofs can instantiate individual total searches in
Mathlib-free benchmarks; they do not replace the universal semantic integration
fixture or prove a whole constant registration.

## Inputs and proof ownership

Audit against the [pinned Mathlib](../../lake-manifest.json), revision
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa` for the declarations listed here.
Mathlib paths are package-relative.

| Input | Available result or local obligation |
| --- | --- |
| [HexRationalFnMathlib/Correspondence.lean](../../HexRationalFnMathlib/Correspondence.lean) | Existing `equiv`, `algEquiv`, `toRatFunc_injective`, canonical numerator/denominator and arithmetic correspondence. Compose these maps; do not create another normalization representation. |
| Mathlib `FieldTheory/RatFunc/AsPolynomial.lean` | Fraction-field evaluation and `algEquivOfTranscendental`; construct evaluation into the simple intermediate field or ℝ under relative transcendence and prove agreement with Hex. |
| Mathlib `RingTheory/LaurentSeries.lean` | Existing `RatFunc.coeToLaurentSeries`, `RatFunc.coe_X` and `RatFunc.algebraMap_apply_div`. Laurent series are `HahnSeries ℤ K`. |
| Mathlib `RingTheory/HahnSeries/Lex.lean`, `Summable.lean` | Lexicographic order and Hahn field structure. Prove correspondence with the executable lowest-coefficient scan here. |
| Mathlib trailing-degree and sign lemmas | `Polynomial.natTrailingDegree`, `Polynomial.trailingCoeff`, `trailingCoeff_mul` and `SignType` laws support the coefficient and sign bridges. |
| Caller approximation functions | Total Lean functions returning finite rational bounds, plus containment and effective convergence premises. These are explicit hypotheses, not analytic implementations supplied here. |
| This companion | Exact bound containment/Horner convergence, injective real evaluation, Hahn sign correspondence, total sign-search progress and field/order laws. |

No Tau Ceti real-algebra theorem is needed for these simple ordered
rational-function extensions. Ordered real-closure existence, IVT/Rolle,
Sturm–Tarski and Thom/BKR foundations retain their owners in the
[family proof table](../future-work.md#proof-ownership-and-public-surface).
An integer-exponent Hahn field is not claimed to be real closed.

## Real evaluation and exact bounds

Fix an order-preserving field embedding `ι : K →+* ℝ` and a real `τ`.
Write `E P := P.eval₂ ι τ`. Relative transcendence is

```text
∀ P : K[X], P ≠ 0 → E P ≠ 0.
```

This is transcendence over the embedded predecessor field, not merely over
ℚ. Under this hypothesis construct
`Real.evalHom : Hex.RationalFn K →+* ℝ`, with

```text
evalHom f = E (toPolynomial f.num) / E (toPolynomial f.den),
E (toPolynomial f.den) ≠ 0,
Function.Injective evalHom,
evalHom (C a) = ι a,     evalHom X = τ.
```

Compose the existing Hex equivalence with fraction-field evaluation. Prove
agreement with `RatFunc.eval ι τ` under these hypotheses and ordinary field
operations, including inverse at zero. Injectivity follows from the field
hom once denominator nonvanishing has justified its construction. No
comparison implementation uses real comparison internally.

The caller supplies computational `approxCoeff : K → Rat → Oracle.Bounds`
and `approxConst : Rat → Oracle.Bounds`, separate rational width proofs,
and separate containment proofs for the specific `ι,τ`. For a finite closed
bound `I`, define `Contains I x := (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)`.
The width theorem states `I.width ≤ δ` for every positive rational request;
the containment theorem states that the returned interval contains `ι a` or
`τ` for that same request. Both belong to the verified oracle contract.
Neither theorem is bundled into each approximation result or executed by the
bound evaluator. Containment alone suffices for a finite successful sign's
soundness; adding the width guarantee along `δ=2^(-n)` gives convergence to
the intended values. Width alone just bounds interval size and proves no
semantic assertion. Prove all composition against these exact functions.

Prove containment of exact rational singleton, negation, addition,
four-endpoint-product multiplication and successful intersection. When the
denominator bound excludes zero, prove containment of the minimum/maximum
of the four exact endpoint quotients. Dyadic to
rational conversion is exact; any rational-to-dyadic conversion must preserve
containment by outward rounding. These are elementary ordered-field lemmas
in this companion, using the small local bound type rather than an interval
library.

Define the interpreted Horner bound of each fixed polynomial from those
operations. Prove `Real.enclose_sound` from source containment and
`Real.horner_converges` from simultaneous coefficient/argument convergence.
Use the finite Horner recurrence, bounds on the source magnitudes and explicit
sum/product width estimates; polynomial continuity by itself does not prove
the bound algorithm narrows. If outward conversion is used, include its
vanishing rounding error. No fresh analytic theorem about τ is required.

## Sign search and the total ordered-field instance

`Real.attempt f n` first decides formal zero by the exact normalized numerator.
Otherwise it evaluates numerator and denominator bounds at precision n,
returning a sign when both are separated from zero. Under relative
transcendence, every nonzero polynomial encountered has nonzero evaluation.
Horner convergence therefore gives

```text
ApproximationCorrect ι τ approxCoeff approxConst →
ApproximationWidth approxCoeff approxConst →
RelativeTranscendence ι τ →
∀ f : RationalFn K, ∃ N, ∀ n ≥ N, (Real.attempt f n).isSome = true.
```

The formal-zero branch terminates algebraically without an approximation
call. For nonzero f the sign is the product of numerator and denominator
signs. Prove uniqueness and correctness of every successful attempt under
these hypotheses, then compose with the computational `firstSome_spec`.

The computational library proves accessibility of
`Next trial m n := m=n+1 ∧ trial n=none` from eventual success. This companion
supplies that premise for the actual `attempt` function. The resulting
`Real.sign` executes successive attempts under an erased accessibility proof;
it does not extract an arbitrary natural number from `Prop`, use classical
choice as a runtime procedure, or return a default sign. The companion does
not replace this computation with `SignType.sign` on real numbers.

Proof erasure makes this search executable but does not guarantee kernel
reduction: an opaque eventual-success theorem can block reduction of the
accessibility recursion. Provide a finite supplied-proof route as well as
the general correspondence theorem. Correct source bounds and exact Horner
arithmetic establish a successful attempt's sign; sign uniqueness and
`firstSome_spec` then prove the total sign has that value. Ordinary theorem
application checks this argument without reducing the unbounded search.
Tactic clients must support this route rather than rely on `by decide` for
the total sign. No coefficient-operation certificates are needed.

Prove the following headline statements, under the fixed dictionary,
embedding, containment, convergence and relative-transcendence assumptions:

| Statement | Conclusion |
| --- | --- |
| `Real.sign_eq` | `Real.sign f = sgn (evalHom f)`. |
| `Real.sign_zero` | `Real.sign f = 0 ↔ f = 0`. |
| `Real.compare_eq` | Comparing f and g agrees with comparing their images in ℝ. |
| `Real.eval_lt`, `eval_le` | The executable order is the pullback of real order. |
| `Real.C_lt` | `C a < C b ↔ a < b`. |
| `Real.approx_correct` | `Real.approx f δ` contains `evalHom f` and has width at most positive `δ`; these are separate theorems about the computational function. |

Use sign under negation/multiplication and positivity of sums to supply the
core ordered-ring/linear-order laws. Provide compatible Mathlib `Field`,
`LinearOrder` and `IsStrictOrderedRing` instances on the opt-in carrier, with
proved agreement with its executable core dictionaries. Field arithmetic
continues to be the existing total RationalFn arithmetic. No optional fueled
comparison becomes a coefficient operation for polynomial or tower algorithms.

Prove the total `Real.approx` used for successive extensions: numerator and
denominator bounds jointly converge, the denominator eventually excludes
zero, and the exact quotient bounds shrink to their real quotient. A finite
width test at the requested precision therefore succeeds eventually. The
same accessibility argument constructs the executable bound-returning search.
The formal zero case uses its exact singleton. Its containment/width theorem
supplies `approxCoeff` at the next real-constant level; over ℚ use singleton
bounds. Iteration requires relative transcendence over the complete current
field at every new constant, not just separate rational transcendence.

## Finite comparisons and boundary evidence

The separate `Real.sign? fuel` consumer may accept correct source bounds
without convergence or relative transcendence. It establishes nonzero
evaluation of the supplied normalized denominator before returning a sign.
Its success theorem concerns this fraction's evaluated value, not an
injective field embedding. Formal zero or a proved exact evaluation identity
can supply the numerator's zero sign once the denominator condition holds.
A singleton `[0,0]` gives such an identity by containment; a nondegenerate
zero-containing bound does not. Fuel exhaustion and a pole return no sign.

This distinction matters at a dependent subject. Evaluating the normalized
formal fraction `(X-c)/(X-c)=1` at c does not justify rewriting the original
real expression by cancellation there. A tactic or expression conversion
retains every nonzero source-divisor hypothesis used by its rewrite and
proves the original goal. Ordinary field arithmetic remains total and has
no per-operation guard protocol. The existing total `RatFunc.eval` convention
at poles is not a successful nonzero-denominator finite evaluation.

At a tactic or deserialization boundary, accepted source bounds must bind
the exact subject, predecessor embedding, registration identity/version,
endpoints and precision claim. The caller provides a proof of containment or
a finite checker with its soundness theorem. The generic companion composes
these facts with the already-proved bound/Horner/sign lemmas. It does not
require literal evidence for every coefficient addition or multiplication.
Wrong-subject or fabricated endpoint data cannot authenticate themselves.
Successful finite certificates are checked without executing an unbounded
approximation search in the kernel; source proof production remains the
caller's responsibility.

User-provided π/e examples are optional. The pinned audit does not provide
the individual transcendence theorems; even separate rational transcendence
would not prove the second constant transcendental over the first extension.
Finite supplied bounds can establish useful signs without these hypotheses,
while total field use retains all relative-transcendence and convergence
premises. This library supplies neither named-constant algorithms nor their
analytic proofs.

## Positive infinitesimal model

Set `H(K) := Lex (HahnSeries ℤ K)`, using the field structure from
`Summable.lean` and order from `Lex.lean`. Compose the ring embeddings

```text
Hex.RationalFn K ≃+* RatFunc K →+* LaurentSeries K →+* H(K).
```

The middle map already exists in Mathlib; the final map wraps the same series
in `Lex`. Prove `Infinitesimal.embed_injective`, `embed_C` and `embed_X`, with
constants at exponent zero and X at exponent one.

For a nonzero polynomial P, prove the first nonzero index found by the exact
scan is `P.natTrailingDegree` and its coefficient is `P.trailingCoeff`.
The embedded series has that order and leading coefficient. Thus a nonzero
fraction P/Q has order i−j and leading coefficient `P.coeff i / Q.coeff j`.
Using Hahn leading-coefficient order and field sign laws, prove

```text
Infinitesimal.sign f = sgn (embed f),
Infinitesimal.sign (P/Q) = sgn(P.coeff i) * sgn(Q.coeff j)  when P≠0,
Infinitesimal.sign 0 = 0.
```

The denominator sign is essential, even when Q is monic. Establish agreement
with existing RationalFn normalization and cancellation, then prove the
ordered-field laws and comparison by the sign of subtraction. Required
correspondences include

```text
C a < C b ↔ a < b,
0 < X ∧ ∀ a : K, 0 < a → X < C a,
f < g ↔ embed f < embed g,     f ≤ g ↔ embed f ≤ embed g.
```

For successive levels, iterate H and transport the preceding field's model
embedding coefficientwise. Bundle `HahnSeries.map` for an injective strictly
monotone coefficient hom and prove its embedding preserves and reflects
order: support and lowest index are preserved, and leading coefficients
map by that hom. Prove commuting constant embeddings. Consequently ε₂ is
smaller than every positive element of K(ε₁), including ε₁^m for positive m.

The formal indeterminate is transcendental by construction. The
integer-exponent Hahn field is not real closed: its exponent-one monomial
has no square root. Algebraic roots and the compatible real-closure model
are downstream obligations. The real-constant interface cannot follow a
positive infinitesimal over ℚ; the family's stages remain
`transcendental ≺ infinitesimal ≺ algebraic`.

## Conformance and Phase-4 evidence

This is `correspondence_only: true`, comparator absence class
**correspondence-only-layer**. HexOrderedFn owns runtime conformance and
benchmarks. Here use build-only proof tests of semantic conclusions:

- Existing RationalFn representation/arithmetic correspondence, inverse zero,
  cancellation, denominator signs and normalization invariance.
- Lowest-index scans, negative valuations, `1/(X-1)<0`, `0<ε<1/n` for positive
  integers n, `1/ε>n`, and successive infinitesimal inequalities.
- The corrected paper identity `(εx²−1)(εx³−1)=ε²x⁵−εx³−εx²+1`; do not
  assert its algebraic roots lie in the integer-exponent Hahn field.
- Exact rational source bounds and required finite comparisons at sqrt(2),
  using test-only rational bounds and a genuine proof of containment.
  Sqrt(2) is algebraic: it never instantiates relative transcendence or the
  total real-extension field. An unresolved `X²−2` test returns no sign
  unless separately justified exact-zero evidence is available.
- A subject 2 with narrowing nondegenerate bounds on `X−2`, contrasted with
  a certified singleton `[2,2]` giving an exact evaluation identity.
- Joint coefficient/constant refinement, small nonzero evaluations, closed
  bounds touching zero, poles and preserved source-divisor premises.
- Wrong subject/registration/endpoint evidence at the boundary, finite-fuel
  exhaustion, formal zero without approximation calls and a synthetic
  eventually successful trial for the executable accessibility search.

Also implement a required test-only caller oracle for `liouvilleNumber 2`.
The pinned Mathlib's
`Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber` provides
`transcendental_liouvilleNumber` over ℤ; transfer this to ℚ using
`IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ` from
`Mathlib.RingTheory.Localization.Integral`. Define executable rational
partial sums `q_n = ∑ i ∈ range (n+1), 1 / 2^(i!)` and return
`[q_n, q_n + 2 / 2^((n+1)!)]`. Identify the cast partial sum with
`LiouvilleNumber.partialSum`; its `remainder_pos`,
`partialSum_add_remainder` and `remainder_lt'` prove containment.
`Nat.self_le_factorial` gives width at most `2^(-n)`. Rational coefficient
bounds are exact singletons. These are test-local definitions and proofs,
not a public analytic-provider implementation obligation.

Instantiate the actual total real-extension interface with this oracle and
the proved hypotheses. Exercise its composed approximation/Horner/attempt/
total-sign path on `X-5/4` (positive), `X-2` (negative), and
`(X-5/4)/(X-2)` (negative), together with formal `X-X=0`, ordinary field
arithmetic, the resulting order, and containment/width of `Real.approx`.
Check finite successful attempts computationally, prove their agreement
with the total sign by the supplied-proof route, and include compiled
evaluation of the total sign so a replacement by an unrelated finite
checker cannot satisfy the test. The fixture belongs to the companion's
integration tests; it introduces no Mathlib import into the computational
library and no HexInterval dependency. The sqrt(2) and synthetic-search
tests do not substitute for this genuine transcendental instance.

Test generic total real sign/order theorems under their explicit hypotheses
and the concrete fixture under its proved premises. Inspect public axiom dependencies;
reject `sorryAx`, invented axioms and `native_decide`. Independent review
checks that actual executable sign/equality supplies the ordinary field/order
instances and that the termination proof applies to that same function.

Phase 4 adds [fresh-module proof evidence](../benchmarking.md#fresh-module-proof-evidence)
for representative model/order laws and optional real-sign boundary
certificates. Separate runtime approximation, finite proof generation,
elaboration and kernel checking. Prove and reuse arithmetic/Horner lemmas;
do not introduce per-operation coefficient certificate benchmarks or rerun
unbounded sign refinement in the kernel. Named-constant generation/analytic
provider performance is outside this contract.

The owner varies degree, coefficient height, lowest index, separation
precision and tower depth, with caller approximation cost attributed
separately. Use fixed trial-major shared-host schedules, automatic CPU
selection where supported, adjacent alternating comparisons, all completed
samples and at most one unchanged inconclusive rerun. Family tower8 and
other root workloads supply integration evidence; this companion contributes
coefficient model/sign correctness and boundary proof costs. No CI fan-out or
historical-paper timing threshold is introduced.
