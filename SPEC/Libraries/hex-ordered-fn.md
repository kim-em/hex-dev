# hex-ordered-fn

Exact ordered rational-function extensions by user-supplied computable real
constants and by positive infinitesimals. Both extensions use ordinary total
`RationalFn K` arithmetic. A transcendental sign is computed by refining
correct convergent approximations until separated from zero; an infinitesimal
sign is the sign of the lowest nonzero coefficient. This is the computational
part of the [ordered-field family](../future-work.md#real-closures-of-ordered-fields),
with semantic proofs in [hex-ordered-fn-mathlib](hex-ordered-fn-mathlib.md).

The API and theorem shapes below are required contracts. They are not claims
that the new declarations are already implemented or checked Lean prototypes.

## Placement and dependencies

`HexOrderedFn` depends on `HexRationalFn`, `HexPoly` and `HexPolyFast`.
It uses their exact arithmetic directly. It does not import `HexSturm`,
`HexSignDet` or `HexRealClosure`; those libraries can consume its ordered
fields. No existing input library gains a dependency on this family.
`HexOrderedFnMathlib` imports this library, `HexRationalFnMathlib`,
`HexPolyMathlib` and Mathlib. Computational code imports neither Mathlib nor
Batteries and introduces no trusted extern.

The namespace is `Hex.OrderedFn`. Modules are:

| Module | Responsibility |
| --- | --- |
| `Basic` | Opt-in carriers around `RationalFn`, embeddings and ordinary arithmetic reuse. |
| `Oracle` | Finite exact bounds and the interface to user-supplied approximation procedures. |
| `Infinitesimal` | Lowest-coefficient signs and successive infinitesimal extensions. |
| `Real` | Polynomial bound evaluation, sign refinement and proof-founded total comparison. |

The family tower builder enforces `transcendental ≺ infinitesimal ≺ algebraic`.
The real-constant constructor needs a real-embedded predecessor field; it
cannot follow a positive infinitesimal over `ℚ`. The simple infinitesimal
extension remains generic over an ordered field.

`HexInterval` and `HexIntervalMathlib` are not dependencies. This library
owns only the exact finite-bound arithmetic needed by Horner evaluation.
A future adapter may connect another enclosure library downstream. No
approximation generator or analytic proof for `π`, `e` or another named
constant is a deliverable here.

## Exact coefficient and fraction arithmetic

Use the existing [rational-function carrier](../../HexRationalFn/SPEC/hex-rational-fn.md)
`Hex.RationalFn K`, with `[Lean.Grind.Field K] [DecidableEq K]`. Its numerator
and denominator are canonical `DensePoly K` values, its denominator is monic,
and their monic gcd is one. Reuse normalization, cross-cancellation, equality,
addition, negation, multiplication, inversion, division and powers directly.
`HexRationalFn/Basic.lean` supplies `den_ne_zero`, `eq_iff` and `num_eq_zero`;
`HexRationalFn/Field.lean` supplies the field instance. The field convention
is `0⁻¹ = 0`.

The ordered predecessor interface adds `LE`, `LT`, `Std.IsLinearOrder`,
`Std.LawfulOrderLT`, `Lean.Grind.OrderedRing`, `DecidableLE` and `DecidableLT`.
These are Lean-core classes, with executable decisions. `OrderedRing` alone
does not supply a linear order. A classical noncomputable comparison is not
an implementation of the required executable field. A total sign operation
returns an `Int` in `{-1,0,1}` and agrees with these comparisons.

Use separate opt-in wrappers or scoped instances for the real and
infinitesimal orders on the same rational-function arithmetic. Do not install
conflicting global orders on `RationalFn K`. Normal forms, field arithmetic
and their laws are proved once; individual additions, multiplications or gcd
steps do not return certificates or consume a common resource budget.
Polynomial algorithms use the ordinary total computational operations/sign,
with order laws in their interpretation theorems; see the
[execution contract](../real-closure-execution.md).

Formal zero is an algebraic decision: `f=0` iff its normalized numerator is
zero. It does not wait for a real approximation. Coefficient equality must
be genuine equality of the lawful prealgebraic carrier used by `RationalFn`.
The stage order places these rational-function extensions before algebraic
adjunctions; do not instantiate `RationalFn` on raw selected-root syntax.
Algebraic base enlargement rebuilds and transports the staged context.

## User approximations and exact finite bounds

`Oracle.Bounds` contains rational endpoints `lower, upper : Rat` and a proof
that `lower ≤ upper`. It represents a finite closed bound. Use core exact
rational arithmetic: singleton, negation, endpoint addition and multiplication
by the minimum/maximum of the four endpoint products. Intersection may return
`none` for inconsistent bounds. For a denominator bound excluding zero,
quotient bounds use the minimum/maximum of the four exact endpoint quotients;
this conditional bound operation is separate from total field division. Dyadic inputs can be converted exactly;
optional rational-to-dyadic output must round outwards. No general interval
solver, propagation engine or floating-point endpoint test is required.

For a predecessor field `K`, the caller supplies computational functions and
separate proof functions. They are not proof-producing approximation calls:

```text
approxCoeff : K → Rat → Oracle.Bounds
approxConst : Rat → Oracle.Bounds
approxCoeff_width : ∀ a δ, 0 < δ → (approxCoeff a δ).width ≤ δ
approxConst_width : ∀ δ, 0 < δ → (approxConst δ).width ≤ δ
```

The positive rational `δ` is the requested width. Nonpositive requests are
outside the accuracy contract; the functions themselves are total. Each
bound has ordered rational endpoints. Width proofs concern rational data and
are independently usable without Mathlib. They are separate from returned
intervals and are used only in proofs that need them.

The verified oracle interface also requires validity for the specific values
being approximated. In a real interpretation with `ι : K →+* ℝ` and `τ : ℝ`,
the caller supplies separate containment proofs:

```text
approxCoeff_contains : ∀ a δ, 0 < δ → Contains (approxCoeff a δ) (ι a)
approxConst_contains : ∀ δ, 0 < δ → Contains (approxConst δ) τ
```

Here `Contains I x` means `(I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)`.
Width without containment proves neither sign soundness nor convergence to
these values. Both guarantees are required for the verified oracle contract;
keeping them separate lets computation call only `approxCoeff`/`approxConst`.
The companion states the containment contract and proves its composition.
It does not implement the caller's constant-specific approximation or proofs.

At refinement index `n`, request `δ = 2^(-n)` from every coefficient and the
constant. The width guarantees give the effective convergence schedule.
A supplier using another schedule can implement this requested-width adapter.
Every approximation call terminates; there is no per-arithmetic-call failure
protocol or hidden external process. The resulting outer search terminates
under containment, width guarantees and relative transcendence.

Compute a bound for a polynomial by exact Horner arithmetic, using the same
requested precision for `τ` and every coefficient in that finite polynomial.
Refine all of them as precision increases. Refining only the new constant
while keeping approximate coefficients fixed does not ensure convergence.
A formal rational coefficient has an exact singleton bound, including when
it is not dyadic. Cached bounds bind the exact coefficient, constant and
context; reuse must preserve those identities.

The companion proves containment of each elementary bound operation once,
then containment and shrinking width of the complete Horner evaluation.
An enclosing bound with positive lower endpoint certifies positivity; a
negative upper endpoint certifies negativity. A nondegenerate bound containing
zero proves neither zero nor a nonzero sign. A certified singleton `[0,0]`
*does* establish exact zero and can serve as an evaluation identity in the
optional finite comparison and tactic interfaces.

## Transcendental sign and totality

The real context is relative to the entire preceding field. Its hypothesis is

```text
RelativeTranscendence ι τ :=
  ∀ P : K[X], P ≠ 0 → (P.map ι).eval τ ≠ 0.
```

It supplies the injective evaluation of `K(X)` at `τ`. Transcendence merely
over `ℚ` is insufficient after adjoining another constant. Under this
hypothesis every nonzero numerator and every normalized denominator has
nonzero evaluation. The total sign algorithm returns zero immediately on a
formally zero numerator. Otherwise it refines numerator and denominator
Horner bounds and multiplies their separated signs. Denominator monicity
does not determine its evaluation sign.

`Real.attempt f n : Option Int` is one finite computation at precision `n`:
formal zero gives `some 0`; otherwise strictly separate both evaluated
polynomials from zero and return their sign product, or return `none` if
those bounds do not decide the sign. This is a helper for sign search, not
a partial coefficient operation. Each call uses ordinary exact arithmetic.
The companion proves the required progress shape:

```text
ApproximationCorrect ι τ approxCoeff approxConst →
ApproximationWidth approxCoeff approxConst →
RelativeTranscendence ι τ →
∀ f : RationalFn K, ∃ N, ∀ n ≥ N, (Real.attempt f n).isSome = true.
```

Here correctness is containment for all inputs and positive requests;
`ApproximationWidth` is the pair of separate width guarantees above. Their
composition with `2^(-n)` gives convergence. The conclusion follows from
Horner convergence and nonzero evaluations, with formal zero handled
algebraically. Correctness alone does not imply progress.

Use a small proof-founded search, with the following Lean statement shapes
(successful signs are integers in `{-1,0,1}`):

```lean
def Next (trial : Nat → Option Int) (m n : Nat) : Prop :=
  m = n + 1 ∧ trial n = none

theorem next_acc (trial : Nat → Option Int)
    (eventually : ∃ N, ∀ n ≥ N, (trial n).isSome = true)
    (n : Nat) : Acc (Next trial) n

def firstSome (trial : Nat → Option Int) (n : Nat)
    (h : Acc (Next trial) n) : Int

theorem firstSome_spec (trial : Nat → Option Int) (n : Nat)
    (h : Acc (Next trial) n) :
    ∃ m, n ≤ m ∧ trial m = some (firstSome trial n h)
```

`firstSome` evaluates `trial n`, returns the successful sign, or recurses at
`n+1` using the accessible successor justified by the equation `trial n=none`.
To prove `next_acc`, fix a success threshold only inside the proof and use
`N-n` as the decreasing measure on failure steps; a failure at `n≥N` is
impossible. Express the executable recursion through Lean's well-founded
recursion on `{n : Nat // Acc (Next trial) n}`, with relation
`InvImage (Next trial) Subtype.val`. Accessibility of each value follows
from `InvImage.accessible Subtype.val` applied to its stored proof. The
recursive call decreases by `⟨rfl, trial_n_eq_none⟩`; this is well-founded
recursion, not structural elimination of the `Acc` proof into `Int`.
Start the per-input total `Real.sign f` at zero using `next_acc` for `attempt f`.
Also provide `acc_of_success`: a checked `trial N = some s` gives accessibility
from any `n ≤ N`. Its proof inducts on `N-n`; a failure at `N` contradicts
the checked success. The executable loop is unchanged, and `N` is an erased
proof witness, not a runtime bound. A universal oracle registration supplies
the per-input proof for all queries; finite witnesses supply only their stated
queries and cannot manufacture a universal field registration.
Proofs erase: runtime performs the increasing refinement, never classical
selection of a fuel from an existential proposition. No `partial`, `unsafe`,
axiom or opaque trusted search callback implements this algorithm.

Compiled execution erases the accessibility proof; kernel reduction does
not. An opaque eventual-success theorem can prevent `firstSome` from
reducing, so `by decide` is not a promised proof route for total real signs.
Provide ordinary equation/specification lemmas and a supplied-proof route:
finite certified bounds prove the successful attempt's sign, and uniqueness
with `firstSome_spec` identifies it with the total result. Tactic replay must
accept this finite sign proof instead of requiring kernel evaluation of the
unbounded search. These are sign-boundary proofs, not certificates for
individual field operations.

The computational declaration takes a core-expressible progress/accessibility
premise as an erased argument. This is a proof interface for termination under
the paper's hypotheses, not an additional mathematical termination obstacle. The companion constructs it from the concrete
approximation and transcendence assumptions, proves sign uniqueness and
order laws, and supplies the corresponding erased laws to the core instances.
`Real.compare f g` signs `f-g`. The resulting wrapper has ordinary total
field arithmetic, executable equality/comparison and ordered-field laws;
tower polynomial kernels consume the underlying ordinary operations/sign.
They do not need the order-law proof to execute.

To support successive real-constant extensions, also provide
`Real.approx f δ : Oracle.Bounds` for positive requested width `δ`,
with the same split between computation and its width/containment theorems. Refine numerator
and denominator bounds until the denominator excludes zero and their quotient
bound has width at most `δ`. The exact quotient-bound formula and
continuity away from zero prove eventual success. Use the same accessibility
construction, now returning a bound. Formal zero has the exact singleton
bound. This derives the next level's `approxCoeff` from the preceding level,
starting with rational singleton bounds over ℚ; callers need only supply the
new constant's approximation and laws at each stage. No infinitesimal field
is passed to this real approximation interface.

## Optional finite comparison and proof boundaries

`Real.sign? fuel` makes finitely many precision attempts and returns a sign
only when justified, otherwise `none`. Besides strict separation it may use
an exact-zero identity, including a singleton Horner bound, as described below. A zero fuel performs no approximation
call. Fuel limits the number of attempts, not the running time of a caller's
approximation function. This convenience API is independent of the total
ordered-field instance and is never installed as the coefficient interface
for Sturm, BKR or tower arithmetic.

Finite successful evaluation needs correct source bounds, not convergence
or transcendence. It checks that the chosen denominator is nonzero at `τ`;
a pole or unresolved denominator yields no sign. A formally zero numerator
can return zero once this denominator condition is established. A certified
singleton result also proves exact evaluation zero. In the absence of
relative transcendence, this concerns evaluation of the supplied normalized
fraction, not a field embedding of all `RationalFn K` into `ℝ`.

Evaluation of an original expression is a separate boundary contract.
Cancellation can erase a source divisor: `(X-c)/(X-c)` is the formal field
element one, while the original expression evaluated at `τ=ι(c)` does not
justify that cancellation. A tactic translating an expression must retain
and prove every nonzero divisor premise needed by its rewrites, including
when its normalized numerator is zero. This does not add guards to ordinary
field addition/multiplication or replace total field inversion.

When a tactic or serialized oracle result supplies finite bounds, validate
its exact subject, coefficient embedding, constant/provider identity and
version, endpoints and requested precision. Accept containment only through
a caller-provided theorem or a kernel-reducible checker with a soundness
theorem. Direct use under universally proved approximation laws needs no
certificate for each arithmetic operation. A sign certificate may record the
finite source bounds actually used and the final separation; the companion
quotes their correctness using the proved Horner theorem without rerunning
unbounded sign search in the kernel. Wrong subjects or fabricated endpoints
are rejected at this boundary.

The user may supply approximations for `π` or `e`. The library bundles none.
Total use requires their stated relative-transcendence hypotheses, which the
pinned Mathlib audit does not discharge; separate rational transcendence
would still not justify a total `ℚ(π,e)` order. Finite supplied bounds can
nevertheless certify examples such as `π<4` without that hypothesis.

## Infinitesimal order

For a nonzero polynomial, scan upward to its first nonzero coefficient using
exact coefficient equality. This scan terminates within the stored array
length. For `f=P/Q`, let `i,j` be the first nonzero numerator and denominator
indices when `P≠0`. Define

```text
signε(f) = 0                              if P=0,
signε(f) = sign(P[i]) * sign(Q[j])         otherwise.
```

Use both coefficients: even a monic denominator can have negative lowest
coefficient, as `1/(X-1)<0` shows. The denominator is nonzero by the existing
RationalFn invariant. This total sign requires no approximation or search.
Prove normalization invariance and the sign laws once, then obtain comparison
by signing subtraction on an opt-in wrapper.

The companion embeds `RationalFn K` through `RatFunc K` and `LaurentSeries K`
into `Lex (HahnSeries ℤ K)`. The constant embedding preserves order and the
new `X` satisfies `0<X<C a` for every positive `a:K`. Iterate the construction:
`ε₂` is smaller than every positive element of `K(ε₁)`, including `ε₁^m` for
positive integers m. Extension order is part of the context. The formal
indeterminate is transcendental by construction, not an additional assumed
fact about a computable real.

Integer-exponent Hahn series are not real closed; an exponent-one monomial
has no square root there. Algebraic roots, stage management and enlargement
after algebraics belong to hex-real-closure. This companion requires no
abstract-real-closed-field theorem from Tau Ceti.

## Conformance and Phase-4 evidence

Pin Z3 and retain provenance for `MkInfinitesimal`, applicable arithmetic and
comparison cases from the paper, and caller-supplied real-constant cases.
`Pi`/`E` examples are optional when the caller supplies source evidence; they
do not create a provider implementation obligation. Rational cases also
cross-check python-flint and exact fraction arithmetic. Compare exact signs
and identities, not decimal displays.

Required checks include:

- Ordinary RationalFn arithmetic/normalization, zero and field inverse at
  zero, nontrivial cancellation, denominator signs and degree growth.
- Lowest indices, `1/(X-1)<0`, several infinitesimals, `1/ε>n`, and
  `ε₂<ε₁^m`; the corrected identity
  `(εx²-1)(εx³-1)=ε²x⁵-εx³-εx²+1` as coefficient arithmetic.
- Finite real comparisons using rational subjects and a required irrational
  test subject `sqrt(2)`, with exact rational source bounds proved in test
  code. The irrational case tests only finite successful signs, never a
  transcendental field instance. The relation `X²-2` can remain undecided
  without exact-zero evidence; no false transcendence assumption is allowed.
- A dependent subject `2` with nondegenerate narrowing bounds on `X-2`;
  finite search returns none. A certified singleton `[2,2]` instead supplies
  exact-zero evidence. A bound merely containing zero proves no equality.
- Joint coefficient/constant refinement, small nonzero numerator/denominator,
  non-dyadic rational singletons, denominator poles and original expression
  divisor conditions at the tactic boundary.
- Formal-zero total sign without approximation calls, finite-fuel exhaustion,
  consistent successful results at different precisions, malformed source
  evidence and wrong subject/context/version rejection.

Prove total-search correctness/progress generically under its real hypotheses;
concrete algebraic test subjects cannot discharge relative transcendence.
Use a terminating synthetic trial to test the executable `firstSome` helper.
The [companion](hex-ordered-fn-mathlib.md#conformance-and-phase-4-evidence)
must also supply a test-only Liouville-number fixture exercising the actual
approximation, Horner bounds, attempt, total sign, order and derived
approximation together. This is a required integration test, not a bundled
constant provider or a Mathlib dependency of this library. Fixtures use
small `decide` checks where kernel reduction is available, ordinary proofs
for total signs with opaque progress premises, and `#guard`/compiled
independent comparisons for execution; `native_decide` is banned. Extend the
existing single CI job.

Phase 4 separates ordinary fraction arithmetic, infinitesimal scans,
transcendental sign/element approximation, Horner bound arithmetic and optional boundary
certificate checking. Vary degree, coefficient height, first nonzero index,
precision needed for separation and tower depth. Count approximation calls,
visited coefficients, exact-bound operations and intermediate bit sizes.
For concrete per-input sign/approximation measurements, instantiate the actual
total search with core-checked finite success witnesses as in the
[execution contract](../real-closure-execution.md#transcendental-search-is-a-separate-obligation).
Time the full search, including earlier failures, not the witness endpoint.
Such measurements do not establish a universal transcendental registration;
retain the companion integration fixture for that distinct obligation.
Report caller approximation cost separately; no named-constant generator
benchmark is required and no precision bound in degree alone is claimed.
Compare with existing RationalFn arithmetic and measure clean versus eager
normalization on identical expressions and outcomes. The family's `tower8`,
MetiTarski and other tower workloads contribute integration measurements;
root isolation remains the downstream owner's responsibility.

Use the shared-host fixed trial-major schedule, automatic CPU selection when
supported, adjacent alternating `AB`/`BA` comparisons, retained completed
samples and at most one unchanged inconclusive rerun. Provide one attribution
profile. Kernel/tactic boundary proof evidence belongs to the companion and
is measured separately; ordinary runtime arithmetic needs no per-operation
certificate benchmark. Historical paper timings are not acceptance thresholds.
