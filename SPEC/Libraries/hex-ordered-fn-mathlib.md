# hex-ordered-fn-mathlib

Planned semantic companion for [hex-ordered-fn](hex-ordered-fn.md): real
evaluation, certified enclosure semantics and the positive infinitesimal order
on rational functions. It supplies the erased laws for the computational
library's executable total adapters and proves correspondence for its fallible
operation-record adapter. This is the individual design for
[#10316](https://github.com/kim-em/hex-dev/issues/10316), under the
[ordered-field family](../future-work.md#real-closures-of-ordered-fields).

New names and statements below are planned contracts, not existing Lean
declarations or checked Lean prototypes. Existing inputs are identified
separately. This SPEC adds no implementation, phase advancement, publication,
CI workflow, root algorithm, tactic or nonstandard-analysis claim.

## Placement and representations

`HexOrderedFnMathlib` imports `HexOrderedFn`, `HexRationalFnMathlib`,
`HexPolyMathlib`, `HexIntervalMathlib` and Mathlib. Keep the family's four
computational libraries and four companions. No input library, including
`HexRealAlgebraic`, acquires a dependency on this family. No computational
library imports this companion, Mathlib or Tau Ceti. Lower coefficient
callbacks enter through the shared operation record; they do not induce
imports of downstream selected-root implementations.

Use the namespace `Hex.OrderedFn` with `Real` and `Infinitesimal` namespaces
for the two orders. Planned companion modules are `Correspondence` (fraction
and operation-record interpretation), `Real` (evaluation and enclosures),
`Infinitesimal` (Hahn embedding and signs), `Total` (law packages and Mathlib
instances), and build-only `Tests`. Source-local SPEC placement follows
implementation; the current authoritative design is this file.

For the total carrier, fix `[Field K] [DecidableEq K] [LinearOrder K]
[IsStrictOrderedRing K]`. Use the lightweight field induced by that exact
Mathlib field before forming `Hex.RationalFn K`. The entire lightweight
instance indexes the representation; two dictionaries on the same carrier
are not interchangeable. Follow
[hex-rational-fn-mathlib](../../HexRationalFnMathlib/SPEC/hex-rational-fn-mathlib.md)
at every nested level. Retain executable arithmetic and comparison; semantic
maps into `ℝ` or Hahn series may be noncomputable and are never runtime
implementations. Separate opt-in wrappers/scopes carry the real and
infinitesimal orders; do not install conflicting global orders on
`RationalFn K`.

For fallible coefficients, use representatives `A`, a semantic ordered field
`K`, and an interpretation `v : A → K`, which need not be injective. No field,
order or semantic equality decision is assumed on `A`. Interpreted coefficient
arrays define polynomials in `K[X]`; checked semantic degrees establish all
trailing zeros and a nonzero leading coefficient, or certify the zero
polynomial. The shared `HexPoly` operation record and fallible degree,
division, gcd and extended-gcd routines are planned prerequisites of
[hex-sturm](hex-sturm.md), not existing capabilities of `DensePoly A`.

## Available inputs and missing bridges

Audit against [lake-manifest.json](../../lake-manifest.json), Mathlib revision
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`. Paths in the Mathlib rows below
are relative to that package, not proposed Hex modules.

| Input / owner | Available declaration or planned obligation |
| --- | --- |
| [HexRationalFnMathlib/Correspondence.lean](../../HexRationalFnMathlib/Correspondence.lean) | Existing `equiv`, `algEquiv`, `toRatFunc_injective`, `num_toRatFunc`, `den_toRatFunc`, `toRatFunc_C`, `toRatFunc_X`, operation correspondence, `normalize_spec` and `check_sound`. |
| [HexRationalFnMathlib/Eval.lean](../../HexRationalFnMathlib/Eval.lean) | Existing `eval_toRatFunc`, `eval?_eq_some`, `eval?_eq_none` and `eval?_normalize`, for evaluation back into `K`. Evaluation along a chosen `K →+* ℝ` needs the bridge specified here. |
| Mathlib `FieldTheory/RatFunc/AsPolynomial.lean` | Existing `RatFunc.eval`, conditional `eval_add`/`eval_mul`, `liftRingHom_C`/`liftRingHom_X`, and `algEquivOfTranscendental` with its evaluation and `X` equations. Use the fraction-field lift or the latter equivalence into the simple intermediate field; prove agreement with Hex here. |
| Mathlib `RingTheory/LaurentSeries.lean` | Existing `RatFunc.coeToLaurentSeries`, using `algebraMap (RatFunc K) (LaurentSeries K)`, `RatFunc.coe_X`, and `RatFunc.algebraMap_apply_div`. `LaurentSeries K` is `HahnSeries ℤ K`. |
| Mathlib `RingTheory/HahnSeries/Lex.lean` | Existing `LinearOrder` and `IsStrictOrderedRing` on the lex wrapper, `HahnSeries.lt_iff` and `leadingCoeff_pos_iff` (also negative/nonnegative variants). These concern Hahn series, not Hex's coefficient scan. |
| Mathlib `RingTheory/HahnSeries/Summable.lean` | Existing `HahnSeries.instField` for ordered abelian exponent groups and field coefficients; `Lex.lean` alone does not supply division. |
| [HexIntervalMathlib](hex-interval-mathlib.md) | Existing `Hex.Interval.Contains`, cut semantics and outward-arithmetic soundness. Registered source facts, their authentication, effective convergence and the new Horner evaluator's convergence must be connected here; containment alone supplies no progress theorem. |
| `HexOrderedFnMathlib` | New real evaluation/order correspondence, fallible record correspondence, Hahn embedding composition and lowest-coefficient bridge, enclosure convergence, replay quotation and total-search laws. |

No new abstract real-algebra theorem from Tau Ceti is an input to this
companion. The shared `hex-real-roots-mathlib` foundation owns the planned
`IsRealClosed ℝ` proof from real square roots and polynomial order/IVT lemmas;
this pin has no such instance. Real evaluation here needs only the ordinary
real ordered field. The existing
[IsRealClosed RealAlgebraicNumber](../../HexRealAlgebraicMathlib/RealClosed.lean)
serves the trivial tower downstream.

`hex-real-closure-mathlib` separately consumes the planned Tau Ceti existence
contract: every ordered field `K` embeds order-preservingly in an ordered
real closed field algebraic over the image of `K`. This is needed for an
algebraic infinitesimal ambient model, not for signs of rational functions.
Neither that theorem nor the bridges in this SPEC are assumed already
available; [#10300](https://github.com/kim-em/hex-dev/issues/10300) concerns
foundation delivery. IVT/Rolle, Cauchy indices, Thom signs and BKR completeness
remain with their owners in the family's
[proof-ownership table](../future-work.md#proof-ownership-and-public-surface).

## Fraction and operation-record correspondence

Write `P` and `Q` for the semantic numerator and denominator of an input.
A valid formal fraction has `Q ≠ 0`; denote it by `⟦P/Q⟧ : RatFunc K`.
Original expression-domain guards are additional data, not part of fraction
identity. Formal normalization does not discard them.

Under `CoefficientLaws`, accepted normalization/replay must imply

```text
Q ≠ 0, B.Monic, A*Q = P*B, S*A + T*B = 1,
⟦A/B⟧ = ⟦P/Q⟧,
A = RatFunc.num ⟦P/Q⟧, B = RatFunc.denom ⟦P/Q⟧.
```

Here `A,B,S,T` in the equations denote interpreted output/Bézout polynomials,
not raw coefficient representatives. Monicity ensures `B ≠ 0`; the Bézout
identity ensures coprimality. The zero result has semantic pair `(0,1)`.
Prove `normalize_sound`, `check_sound` and uniqueness of this interpreted
pair. Never conclude equality of raw arrays from equal interpretations.

Prove `operation_sound` for successful `add?`, `sub?`, `neg`, `mul?`, `inv?`,
`div?` and `pow?`: interpretation equals the corresponding `RatFunc K`
operation, with certified nonzero operands for checked inverse/division.
Successful equality is cross multiplication in `K[X]`; successful comparison
is the sign of the interpreted difference in the selected ordered model.
Certified zero inversion/division yields `domain`, whereas the total field
operation has `0⁻¹ = 0`. Agreement on nonzero inputs is required.

Specializing the record to a lawful total coefficient field must recover
`HexRationalFnMathlib.equiv`, its canonical components, operations and
`RationalFn.Cert.check` soundness. These are extensional agreements on
successful values and evidence; identical resource costs or identical failure
budgets are not required. On general representatives, lift the same semantic
fraction through the real or Hahn maps below. Soundness needs no injectivity
of `v`. A total field on those representatives requires a semantic quotient
or a faithful canonical carrier and executable lifted operations first;
this companion does not manufacture a `DecidableEq A` from interpretation.

## Real evaluation and enclosure soundness

Fix `ι : K →+* ℝ` and `StrictMono ι`, together with a named constant `τ : ℝ`.
Thus `ι` is an order-preserving field embedding. The context binds its exact
predecessor, constant identity, provider/version and interpretation to these
semantic parameters. A display name, hash or matching decimal is not proof
that two contexts or constants agree. Retained facts and reconstructed
certificates must resolve to the same registration and operands.

For `p : K[X]`, write `E p = p.eval₂ ι τ`. Define relative transcendence by

```text
RelativeTranscendence ι τ := ∀ p : K[X], p ≠ 0 → E p ≠ 0.
```

With the `K`-algebra structure on `ℝ` induced by `ι`, this is the usual
`Transcendental K τ` condition. It is relative to the embedded preceding
field, not just to `ℚ`. Under this hypothesis construct `Real.evalHom` of
shape `Hex.RationalFn K →+* ℝ`, composing the existing Hex equivalence with
Mathlib's fraction-field evaluation. Required `eval_spec`, `den_ne_zero`
and `eval_injective` statements are

```text
evalHom f = E (toPolynomial f.num) / E (toPolynomial f.den)
         = RatFunc.eval ι τ (HexRationalFnMathlib.toRatFunc f),
E (toPolynomial f.den) ≠ 0,
Function.Injective evalHom.
```

Prove evaluation of constants is `ι a` and evaluation of `X` is `τ`;
preserve zero, one, addition, subtraction, negation, multiplication, total
inverse/division and natural powers. These imply nonzero evaluation of every
nonzero formal fraction. The companion's `eval_lt` and `eval_le` identify
the executable total order with the pullback of real order; in particular
`C a < C b ↔ a < b`. Prove linear-order and ordered-ring laws without
replacing computational comparison with real comparison.

Without relative transcendence, retain a partial evaluation relation:
`Evaluates f r` means `E Q ≠ 0`, every retained source divisor evaluates
nonzero, and `r = E P / E Q`, including recursively checked coefficient
domains. Successful enclosures and signs concern this relation, even when
`E P = 0` for a nonzero formal polynomial. Mathlib's total `RatFunc.eval`
returns zero at a pole; that convention is not a successful evaluation here.
The canonical field element and its guarded source expression have distinct
contracts: `(X-c)/(X-c)` is formally `1`, but its source expression cannot
evaluate at `τ = ι c`. The same domain checks precede zero-numerator shortcuts.

Prove `Real.enclose_sound` for each accepted polynomial Horner enclosure and,
when exposed, fraction enclosure: the interval contains respectively `E P`
or the value of `Evaluates`. Quotient enclosures require certified denominator
separation and outward division. Sign checking can instead multiply the
numerator and denominator signs without interval division. Use
`Hex.Interval.Contains`, including open/closed cuts: an open lower cut at
zero certifies positivity, a closed lower cut at zero does not. A
zero-containing interval is not an equality proof. Zero signs need formal
coefficient-zero evidence or a separately replayed exact evaluation identity.

For either total coefficients or the operation record, the headline theorem
`Real.sign_sound` has shape

```text
CoefficientLaws ops → EnclosureLaws ctx → WellFormed ctx f →
Real.sign? n ctx f = ok s cert →
∃ r, Evaluates ctx f r ∧ CheckSound ctx cert ∧ s = sign r.
```

`WellFormed` asserts representation/context validity, not denominator
nonvanishing: success must establish all domains. `Real.check_sound` proves
the same semantic conclusion from accepted checker evidence, independently
of the producer. Successful comparison certifies the ordering of the two
valid operand values; different successful budgets/providers for the same
authenticated subjects agree. No transcendence, convergence or sufficient-fuel
hypothesis belongs in these success-soundness theorems.

## Positive infinitesimal model

Set `H(K) = Lex (HahnSeries ℤ K)`, with the field from `Summable.lean` and
order from `Lex.lean`. Constants are `toLex (HahnSeries.single 0 a)` and
`ε = toLex (HahnSeries.single 1 1)`. Construct the ring embedding

```text
Hex.RationalFn K ≃+* RatFunc K →+* LaurentSeries K →+* H(K).
```

The middle arrow is Mathlib's existing `algebraMap`; the final arrow wraps
the same series in `Lex`. Prove `Infinitesimal.embed_injective`, `embed_C`
and `embed_X`, using `RatFunc.coe_X` for the exponent-one monomial. Do not
replace this input with a proposed new RatFunc-to-Hahn embedding. The new
work is composition with Hex and correspondence with executable operations.

For a nonzero polynomial `P`, let `i` be its lowest nonzero index. Prove its
embedded series has order `i` and Hahn leading coefficient `P.coeff i`.
For `Q ≠ 0` with lowest index `j`, the nonzero fraction has order `i-j`
and leading coefficient `P.coeff i / Q.coeff j`. Consequently
`Infinitesimal.sign_sound` and its checker form state

```text
sign(embed(P/Q)) = 0                                      if P = 0,
sign(embed(P/Q)) = sign(P.coeff i) * sign(Q.coeff j)         otherwise.
```

Interpret `embed(P/Q)` through `RatFunc K` for the operation-record adapter.
An accepted lowest-index certificate proves all earlier coefficients zero
and the selected coefficient nonzero; raw array positions are not enough.
Prove the polynomial coefficient bridge locally, then use Mathlib's
`leadingCoeff_pos_iff` and field laws for the quotient sign. Denominator
monicity does not imply positive sign: `1/(X-1) < 0` in this order.
Establish invariance under all valid normalization and common-factor
cancellation, including the zero numerator case.

Prove `Infinitesimal.C_lt`, `X_lt`, `embed_lt` and `embed_le`:

```text
C a < C b ↔ a < b,
0 < X ∧ ∀ a : K, 0 < a → X < C a,
f < g ↔ embed f < embed g,     f ≤ g ↔ embed f ≤ embed g.
```

The computational order is the sign of subtraction. These correspondences
supply totality, antisymmetry, translation invariance and positive-product
laws; the Hahn comparison itself is not executed. Prove compatibility with
negation, inverses of nonzero values, and preservation of predecessor signs.

For successive levels, iterate `H` on the semantic ordered field and embed
the preceding rational-function carrier coefficientwise into that model.
Equivalently first model each extension in `H` of its immediate carrier,
then transport coefficients into the iterated ambient model; prove the
commuting constant embeddings. Thus `ε₂` is smaller than every positive
embedded element of `K(ε₁)`, including `ε₁^m` for every positive integer `m`.
Context order is part of the interpretation and cannot be permuted silently.

This field is not real closed: an exponent-one monomial has no square root
in the integer-exponent Hahn field. No order-preserving embedding of it into
`ℝ` exists. Algebraic infinitesimal roots require the separate downstream
real-closure existence contract. A real-evaluation context cannot follow a
positive infinitesimal over `ℚ`; the family retains its stage restriction
`transcendental ≺ infinitesimal ≺ algebraic`.

## Failure, progress and the total law package

The bounded API and checker keep the computational diagnostic sum:

| Result | Semantic contract |
| --- | --- |
| `ok value evidence` | All input/context/domain obligations for this operation are checked; correspondence and replay soundness apply. |
| `exhausted reason` | Insufficient fuel/resources, unresolved coefficient/domain/sign or missing usable enclosure; no sign, equality or invalidity follows. |
| `domain reason evidence` | A checked mathematical violation, such as a zero original divisor or zero denominator; does not mean merely containing zero. |
| `invalid reason` | Rejected malformed input, mismatched context/provenance or refuted replay; not a theorem about the represented value. |

Fuel zero exhausts before callbacks. With positive fuel, bounded preflight
precedes domains and arithmetic, propagating the first failure with its
operation path. Unread input after exhaustion is not certified well-formed.
Every producer, callback and checker terminates on arbitrary inputs under
structural fuel and the finite size, precision, endpoint and evidence limits;
recursive coefficient calls also descend the tower. No result discards an
original domain guard or substitutes a default value for failure.

Keep `CoefficientLaws`, `EnclosureLaws` and `ReplayLaws` separate from
`OperationProgress`, `OracleConvergence` and `CofinalSchedule`, with the exact
meanings in the [computational SPEC](hex-ordered-fn.md#bounded-results-evidence-and-resources).
This companion proves model soundness from the first two. `ReplayLaws` also
requires every successful producer to supply finite evidence accepted with
sufficient replay resources. The computational `sign_checks` supplies an
eventual replay envelope without starting a fresh approximation search.
The companion must turn accepted finite evidence into a kernel theorem with
all registered analytic source facts discharged. Runtime endpoints or a
Boolean sign alone are not that theorem; a caller that supplies unproved
source propositions gets only a theorem conditional on them.

For real progress, every coefficient and `τ` must have containing finite
enclosures with a computable schedule reaching width at most `2^(-k)` for
each requested `k`. Prove `Real.horner_converges`: for each finite polynomial,
simultaneous coefficient/argument refinement and vanishing outward-rounding
error make the output width tend to zero. Continuity of polynomial evaluation
alone is not a proof that a particular interval algorithm narrows. Use the
finite Horner recurrence and interval arithmetic error bounds; jointly refine
all coefficient, denominator and retained-domain expressions. For each
nonzero evaluation, a sufficiently narrow containing interval separates zero.
Formal-zero inputs use eventual coefficient-zero/normalization evidence.

Under these conditions require the companion's `Real.sign_isSome`:

```text
RelativeTranscendence ι τ → CoefficientLaws ops → EnclosureLaws ctx →
ReplayLaws ctx ops → OperationProgress ops → OracleConvergence ctx →
CofinalSchedule limits →
∀ f, Valid ctx f → ∃ N, ∀ n ≥ N,
  (Real.sign? (limits n) ctx f).isSome = true.
```

`Valid` includes valid coefficients, well-formed finite context and nonzero
formal denominators and original divisors. Relative transcendence supplies
their real nonvanishing; it does not validate a formally zero divisor.
`limits n` eventually admits every finite requirement and retains already
admitted work, with fair refinement. Fixed caller caps or arbitrary
nonconvergent providers do not meet these hypotheses. The corresponding
`Infinitesimal.sign_isSome` needs coefficient/operation/replay progress and
a cofinal schedule but no real embedding, oracle convergence or relative
transcendence: each finite coefficient scan resolves under predecessor
progress. Bounded predecessor exhaustion must still propagate.

Construct `SearchLaws : Prop` for the computational total adapter with these
specific fields, for its chosen executable operations and sign function:

- Preservation of the validated carrier/domain invariants by every operation;
  agreement with field arithmetic, including total inverse at zero and
  checked inverse/division on nonzero inputs.
- Exclusion of `domain` and `invalid` on validated inputs under the lawful
  provider/record contracts; all remaining failures are exhaustion.
- Eventual success for every validated operation needed by the adapter,
  including sign/comparison, normalization and replay, along the chosen
  cofinal schedule; successful certificates satisfy the replay contract.
- Uniqueness of successful signs; `sign_eq_zero` (`s(f)=0 ↔ f=0`),
  `sign_one`, `sign_neg`, `sign_mul`, and `sign_add`
  (`s(f)=+1 ∧ s(g)=+1 → s(f+g)=+1`), where `s` is the checked total sign.
  Signs take exactly the three values `-1,0,+1`. Arithmetic laws and these
  sign laws establish the order defined by signing subtraction.

`Real.searchLaws` discharges this package using injective real evaluation
and the progress theorem. `Infinitesimal.searchLaws` uses the Hahn embedding
and finite scans. The computational accessibility recursion follows
`Step m n := m = n+1 ∧ run n is exhausted`. Eventual success gives
`Acc Step n`; recursion runs increasing budgets and returns the first
success, eliminating impossible domain/invalid branches by the laws.
Prove `search_spec` gives an actual finite successful run, then compose with
`sign_checks` and `sign_sound`. The existential threshold is used only in
the accessibility proof, never extracted by classical choice as runtime fuel.

The total API exposes core `LE`, `LT`, decidable comparison,
`Std.IsLinearOrder`, `Std.LawfulOrderLT` and `Lean.Grind.OrderedRing` alongside
`Lean.Grind.Field`. Here supply compatible Mathlib `Field`, `LinearOrder`
and `IsStrictOrderedRing` instances on the opt-in carriers, proving agreement
with those executable dictionaries. `OrderedRing` alone is not totality.
No `partial`, `unsafe`, opaque trusted callback or new axiom implements search.
A certified computable bound is an alternative only if it bounds the entire
pipeline and proves success there.

## Named constants and limits of completeness

The pin has the analytic part of Lindemann–Weierstrass, not the theorems
`Transcendental ℚ Real.pi` or `Transcendental ℚ (Real.exp 1)`. Keep these as
explicit hypotheses for corresponding total modes. Separate proofs of both
would still not establish relative transcendence of `e` over embedded
`ℚ(π)`, or joint algebraic independence of `π,e`. No total `ℚ(π,e)` ordering
is claimed without that additional hypothesis.

Certified bounded enclosures remain useful for both constants together,
including `π-4 < 0`, and formal identities after all original domains are
certified. Exact-zero proofs can extend this fragment, but unresolved
relations exhaust. This is successful-result soundness, not a completeness
promise. General transcendental reals also need effective certified
approximation data: transcendence alone does not supply an executable oracle.

## Conformance and Phase-4 evidence

This is planned as `correspondence_only: true`, comparator absence class
**correspondence-only-layer**. Computational conformance and performance owner:
`HexOrderedFn`. Its SPEC owns the pinned Z3 `MkInfinitesimal`, `Pi`, `E` and
arithmetic/sign comparisons, rational/python-flint cases and shared-host
runtime measurements. This companion has no separate compiled benchmark
or new user tactic. Its build-only tests must prove the semantic conclusions,
not merely compare two runtime outputs.

Required proof examples and adversarial replay cases include:

- Constants, zero, `X`, nontrivial normalized fractions, both denominator
  signs, common factors, checked versus total zero inversion, and agreement
  of the total-field and fallible-record interpretations.
- Distinct representatives of a semantic zero, certified trailing zeros,
  false degree/Bézout/monicity witnesses, and an unresolved earlier
  coefficient before a later nonzero one. No structural equality shortcut.
- Lowest coefficients at different indices, negative valuation, `1/(X-1)<0`,
  `0<ε<1/n` for positive integers `n`, `1/ε>n`, and two/three nested levels
  with `ε₂<ε₁^m` for fixed positive `m`.
- The corrected paper identity
  `(εx²−1)(εx³−1) = ε²x⁵−εx³−εx²+1`, as polynomial arithmetic over this
  ordered coefficient field. Its algebraic roots and derivative/Thom signs
  belong downstream; this companion must not assert their membership in
  `HahnSeries ℤ K`.
- Real enclosure success without transcendence, tiny nonzero numerator and
  denominator values, non-dyadic coefficients, open versus closed zero cuts,
  and joint coefficient/constant refinement. Small singleton rational facts
  can prove exact zero; intervals merely containing zero cannot.
- `0/0`, a real pole and a cancelled source divisor at its zero, including a
  zero numerator with invalid domain. An oracle for rational `2` on `X-2`
  with only nondegenerate zero-containing enclosures and no equality witness
  exhausts; an authenticated exact-zero witness can succeed. Neither case
  provides a field embedding.
- Wrong subjects, forged source bounds, stale providers/contexts, inconsistent
  purported enclosures, malformed certificates and zero/insufficient budgets
  at every nested producer/checker boundary. Legitimate fixed caps may keep
  exhausting; progress tests use the specified cofinal schedule.

Test `Real.sign_sound` without a transcendence hypothesis and instantiate
`Real.searchLaws` only under an explicit relative-transcendence assumption.
Do not invent a concrete unconditional total `π,e` instance for tests.
For each public bridge and law-package constructor, inspect axiom dependencies
and reject `sorryAx` or any new axiom; `native_decide` is banned. Imported
planned foundations must be proved before an implementation claims discharge.

Phase 4 reuses the owner's arithmetic/sign benchmarks and adds fresh-module
proof evidence for representative real, infinitesimal and nested-record
certificates: separate production, executable replay, elaboration and kernel
checking; record proof/evidence size, retained cells, dependency sharing and
lower-level replay composition. Do not rerun normalization or approximation
search in kernel replay. Show both accepted and rejected/exhausted replay
remain within their stated resource contracts. Follow
[benchmarking.md](../benchmarking.md#fresh-module-proof-evidence), with
Mathlib-free compiled benches and separately reported companion build costs.

The owner's fixed trial-major measurements vary degree, coefficient height,
lowest nonzero index, separation precision and tower depth. Comparisons use
adjacent alternating `AB`/`BA` arms, automatic CPU selection where supported,
all completed shared-host samples, at most one unchanged inconclusive rerun,
and one representative profile for attribution. Host activity is context,
not a reason to discard runs or wait for an idle core. Family `tower8`,
MetiTarski and root workloads supply downstream integration evidence; this
companion claims only their coefficient arithmetic/sign/replay contribution.
The [paper](https://www.cl.cam.ac.uk/~gp351/infinitesimals.pdf)'s historical
runtimes are not acceptance thresholds. No CI fan-out is introduced.
