# hex-ordered-fn

Planned Mathlib-free orders on rational functions: evaluation at a certified
computable real constant and the order of a new positive infinitesimal.
Both use the same fraction arithmetic. Bounded evaluation returns checked
sign evidence or an explicit failure; total ordered fields require additional
termination and faithfulness laws. This SPEC specifies the design contract
of [the ordered-field family](../future-work.md#real-closures-of-ordered-fields)
and [#10315](https://github.com/kim-em/hex-dev/issues/10315).

All new names and statement shapes below are planned contracts, not existing
Lean declarations or checked Lean prototypes. No implementation, phase change,
publication, CI workflow, root-isolation algorithm or tactic is introduced by
this SPEC. The companion has its own directive,
[#10316](https://github.com/kim-em/hex-dev/issues/10316).

## Placement and dependencies

Keep the family's four computational libraries and four companions.
`HexOrderedFn` depends on `HexRationalFn`, `HexPoly`, `HexPolyFast`
and `HexInterval`. The shared coefficient-operation record and fallible
polynomial routines belong below the family in `HexPoly`, as specified by
[the Sturm directive](https://github.com/kim-em/hex-dev/issues/10311).
They are missing infrastructure, not existing `DensePoly` capabilities.
`HexOrderedFn` consumes that record without importing `HexSturm`,
`HexSignDet` or `HexRealClosure`; lower-level callbacks are explicit
parameters. `HexRealClosure` is a consumer. Existing input libraries,
including `HexRealAlgebraic`, acquire no dependency on this family.

The namespace is `Hex.OrderedFn`. Planned modules are:

| Module | Responsibility |
| --- | --- |
| `Basic` | Shared fraction/context views, coefficient-record adapter and result/evidence types. |
| `Normalize` | Bounded semantic normalization, arithmetic and certificate replay. |
| `Oracle` | Constant identity, enclosure providers, provenance and precision schedules; no order instances. |
| `Infinitesimal` | Lowest-coefficient signs, predecessor embeddings and successive infinitesimals. |
| `Real` | Bounded interval sign evaluation, comparison and domain checking. |
| `Total` | Executable proof-founded search and opt-in core order instances. |

Do not duplicate `RationalFn` arithmetic into the two order modules. Oracle
machinery has its own module; infinitesimal sign evaluation does not invoke a
real approximation of the infinitesimal. Contexts distinguish constant names,
predecessor embeddings and the order of extension. The family tower builder
owns the stage restriction `transcendental ≺ infinitesimal ≺ algebraic`.
The real module requires an ordered embedding into `ℝ`; it cannot accept a
predecessor field containing a positive infinitesimal over `ℚ`.

`HexOrderedFnMathlib` imports this library, `HexRationalFnMathlib`,
`HexPolyMathlib`, and `HexIntervalMathlib` where their correspondence theorems
are used.
Mathlib analysis, `RatFunc`, Hahn-series models and Mathlib field/order
instances live there. No computational import of Mathlib, Batteries or Tau
Ceti is allowed. There is no new algebraic typeclass or trusted extern.

## Carriers and shared arithmetic

### Lawful total carriers

The existing [rational-function representation](../../HexRationalFn/SPEC/hex-rational-fn.md)
is `Hex.RationalFn K` with `[Lean.Grind.Field K] [DecidableEq K]`:
canonical `DensePoly K` numerator and denominator, monic denominator and
monic gcd equal to one. `HexRationalFn/Basic.lean` proves `den_ne_zero`,
`eq_iff` (cross multiplication) and `num_eq_zero`;
`HexRationalFn/Field.lean` supplies `instField`. Use these operations directly
when their hypotheses hold. No separate canonical fraction implementation is
needed for that path.

The two orders use separate opt-in wrappers or scoped adapters around this
carrier, retaining its arithmetic. Do not install conflicting global orders
on `RationalFn K`. Total predecessor orders use `LE`, `LT`, decidable
comparison, `Std.IsLinearOrder`, `Std.LawfulOrderLT` from `Init.Data.Order`,
and `Lean.Grind.OrderedRing` alongside `Lean.Grind.Field`. `OrderedRing`
alone does not imply a total order. The real order additionally needs
injective evaluation, which is supplied by relative transcendence below.

### Bounded or noncanonical coefficients

Let `A` be coefficient representatives, with interpretation `⟦·⟧ : A → F`
in a lawful ordered field `F`. Interpretation need not be injective.
The shared operation record supplies zero/one, arithmetic, checked inversion,
sign/zero evidence and their bounded evaluators. Its law package relates
successful operations to `F`; it is an algorithm parameter, not a competing
field/order typeclass. No `DecidableEq A`, `Decidable (a < b)`, or field
instance on raw representatives may stand in for semantic equality.

Store polynomial coefficients as arrays, with checked semantic degree:
every coefficient above the reported degree is certified zero in `F`, and
the reported leading coefficient is certified nonzero; the zero case
certifies every coefficient zero. Existing `DensePoly A` requires structural
zero decisions and cannot directly provide this interface. Lower-field
certificates, including future selected-root certificates, are consumed
through the record without a reverse library import.

The operation-record fraction adapter belongs here. A checked fraction has
semantic numerator `P : F[X]` and denominator `Q : F[X]`, with `Q ≠ 0`.
Normalization produces arrays `a,b` and a replay certificate establishing

```text
Q ≠ 0,  B is monic,  A*Q = P*B,  S*A + T*B = 1,
where A,B,S,T are the interpreted output and Bézout arrays.
```

Semantic degrees and coefficient equality witnesses justify every identity.
Monicity includes the nonzero denominator condition; zero output has
semantic pair `(0,1)`. These are semantic normal forms: two output arrays
need not be structurally equal when `A → F` is noninjective. Prove uniqueness
of the interpreted pair, not uniqueness of raw representatives. Equality of
fractions is certified cross multiplication, using semantic coefficient zero
tests. A syntactically nonzero coefficient can represent zero.

Follow the cancellation algorithms of `HexRationalFn`, implementing their
steps with the shared bounded division/gcd/extended-gcd routines: addition
cancels denominator gcds,
multiplication cross-cancels, inversion establishes numerator nonzero, and
normalization rescales by a certified nonzero leading coefficient. Do not
hide a call to a total `DensePoly` gcd behind the bounded adapter. Every
coefficient operation, degree test, exact division, gcd descent and replay
step consumes a bounded allowance. An unresolved zero, inverse, exactness or
normalization check returns exhaustion; a refuted proposed certificate is
invalid. No failure substitutes zero or an unnormalized pair.

Planned `normalize?`, `add?`, `sub?`, `mul?`, `inv?`, `div?`, `pow?` and
`compare?` return the result type below. `inv?` and `div?` reject a certified
zero divisor. Only the lawful total field adapter exposes the field convention
`0⁻¹ = 0`; it proves agreement with checked inversion on nonzero inputs.
`compare? f g` signs `f-g` and propagates failures from arithmetic and sign
checking. Agreement with existing `RationalFn` normalization, arithmetic and
`Cert.check` is required when the record is instantiated by a total field.

### Expression domains

Keep original expression-domain obligations alongside fractions, outside the
canonical fraction identity. A formal fraction requires a nonzero polynomial
denominator; real evaluation requires its value to be nonzero as well.
Every original divisor, including one cancelled by normalization, retains a
nonvanishing obligation. Thus `(X-c)/(X-c)` normalizes formally to `1`, but
its original expression is not evaluable at `c`. Distinguish evaluation of a
canonical field element from evaluation of a guarded source expression.
Even a zero numerator shortcut must first validate the relevant denominator
and original domain obligations. All coefficient expression domains recurse
into preceding levels.

## Bounded results, evidence and resources

Use a diagnostic sum with constructors `ok value evidence`, `exhausted reason`,
`domain reason evidence`, and `invalid reason`. Here `domain` certifies a
mathematical violation, such as a zero divisor; `invalid` rejects malformed
input or failed authentication/replay. A missing proof or an interval that
contains zero is not proof of a domain violation: it yields exhaustion.
Expose `Result.isSome` as true exactly for `ok`; do not erase diagnostic
failures into an `Option` at the public boundary.

Internally, use hex-poly's common `Hex.PolyOps.Result` and residual `Budget`.
The public diagnostic sum is a wrapper, with this explicit mapping: preserve
`ok` and `exhausted`; map `rejected` to `invalid`; map an internal `invalid`
carrying checked evidence of a mathematical domain violation to `domain`;
and map malformed or context-invalid inputs to `invalid`. Preserve the
residual counters on every outcome, including failed child calls. Distinguish
these cases using structured constructors and typed domain evidence, never by
parsing a diagnostic string. Only checked outcomes may be wrapped: an untrusted
producer selecting a domain-failure constructor is not a certified violation.

`Sign` has `negative`, `zero`, `positive`; successful `compare?` returns the
corresponding ordering of its two operands. Certificates identify the exact
context, operands, coefficient interpretation, domain obligations and sign.
They contain lower-level sign/identity evidence, normalization and degree
witnesses, and either lowest-coefficient data or enclosure derivations.
Runtime arithmetic and a runtime sign are not proof evidence by themselves.
A bounded `check?` replays the certificate using the shared record and the
registered enclosure rules. Its acceptance soundness has no convergence or
transcendence hypothesis. Analytic source facts are supplied by proved
provider rules in the companion, never by trusting returned endpoints.

Keep the following law packages distinct:

- `CoefficientLaws` relates successful arithmetic, degree, equality and sign
  checks to the coefficient interpretation. It asserts no eventual success.
- `EnclosureLaws` establishes containment and subject/provenance authenticity
  for accepted source facts and interval derivations. It asserts no convergence.
- `ReplayLaws` requires that each successful lower-level producer supplies a
  finite certificate accepted by its checker with sufficient resources.
- `OperationProgress` asserts eventual success of the required coefficient,
  normalization and replay operations on their valid inputs.
- `OracleConvergence` supplies the effective approximation schedules, and
  `CofinalSchedule` states that the chosen resource envelopes eventually
  admit every finite requirement and retain already admitted work.

The first three suffice for soundness and replay with sufficient resources;
the remaining packages govern search completeness. The computational
layer proves `sign_checks`, under the replay laws and a cofinal schedule:

```text
ReplayLaws ctx ops → CofinalSchedule limits →
sign? n ctx f = ok s cert
  → ∃ M, ∀ m ≥ M, (check? (limits m) ctx f s cert).isSome = true.
```

Provide a computable sufficient replay envelope from the successful run's
finite certificate and callback replay bounds. Checking consumes the retained
facts and derivations; it must not start a fresh approximation/sign search.
This producer/checker contract also applies to normalization and arithmetic
certificates, following `RationalFn.certify_checks`. Insufficient replay
resources still return exhaustion. Kernel proof quotation is a companion
obligation, distinct from the executable checker's acceptance.

`sign? fuel ctx f` is structurally recursive on natural fuel, including
nested callback invocations and normalization; a public limits record also
caps input/trace size, coefficient-array work, tower depth, precision,
endpoint height/alignment, retained certificate cells and replay work.
Fuel zero returns `exhausted fuel` before any callback. With positive fuel,
a deterministic bounded preflight validates context and raw input, then
checks domains and performs the requested operation. A stopped preflight
returns exhaustion, without claiming that unread input is valid or invalid.
Propagate the first encountered failure with its operation path; do not return
partial arithmetic or a partial sign. Preflight resource-expensive integer
shifts, allocations and certificate decoding as in `hex-interval`.

Callbacks must be pure terminating Lean computations with explicit budgets;
all recursive work obeys the same decreasing allowance or an explicitly
charged sub-budget. A tower callback decreases level as well. Each refinement
and coefficient operation is charged, including callbacks that fail. An
arbitrary `IO` callback, foreign process or non-preemptible interval scheduler
callback does not meet this bounded protocol just because the outer loop has
fuel. External fixture generators are testing tools, not runtime providers.
Fuel bounds logical work; it does not assert a host-independent wall-clock
limit for individual big-integer operations.

## Infinitesimal order

For nonzero `P`, `lowest? P` returns an index `i`, evidence that all earlier
coefficients vanish, and the nonzero sign of `P[i]`. It must stop with
exhaustion on an unresolved earlier coefficient; it cannot skip it. Scanning
all coefficients with zero evidence returns a certified zero polynomial.
The denominator scan must certify a nonzero coefficient.

For `f=P/Q`, define

```text
signε(f) = 0                         if P = 0,
signε(f) = sign(P[i]) * sign(Q[j])    otherwise,
```

where `i,j` are the respective lowest nonzero indices and multiplication is
in `{-1,0,1}`. Use both coefficients. A monic denominator can have negative
lowest coefficient: `1/(X-1)` is negative at a positive infinitesimal.
No real enclosure or numerical value of `ε` participates in this algorithm.

Required theorem shapes, under the coefficient law package, are:

- `lowest_sound` (computational): every successful scan certifies exactly
  the stated zeros and first nonzero coefficient, or all-zero polynomial.
- `sign_sound` (companion): a successful sign equals the sign in the ordered
  model below; this requires valid fraction/domain evidence but no
  approximation oracle.
- `sign_isSome` (computational, under predecessor progress laws): valid finite
  fractions and eventually successful predecessor operations have a sufficiently large resource envelope making every later
  run successful. Total predecessor operations give a finite coefficient
  scan; bounded predecessor exhaustion propagates.
- `sign_eq_zero`, `sign_mul`, and `sign_add` (companion model theorems,
  supplied as erased laws to the computational total adapter): zero iff the
  fraction is zero, multiplication multiplies signs, and a sum of positive fractions is
  positive, for the total lawful adapter. Also prove compatibility with
  negation and invariance under valid fraction normalization.
- `C_lt` and `X_lt` (companion): the constant embedding preserves and reflects
  order,
  and `0 < X ∧ ∀ a : K, 0 < a → X < C a`.

Iterate the extension over its immediately preceding ordered field. Thus
`0 < ε₂ < ε₁^m` for every positive integer `m`, and more generally `ε₂ < a`
for every positive `a ∈ K(ε₁)`. The ordering is determined by tower order;
permuting infinitesimal levels does not preserve the named order contract.

## Real constants and enclosure provenance

A real context fixes an order-preserving field embedding `ι : F → ℝ`, a
constant identity and a semantic real `τ`. The runtime registry key contains
the provider name, version and preceding context identity; the companion ties
that exact key to `τ` and `ι`. A matching display name, hash or decimal value
is not sufficient evidence that two constants or contexts are the same.
Persisted replay resolves the same registration and rejects changed versions,
operands, embeddings, precision claims and stale context references.

The `Oracle` protocol supplies finite certified dyadic enclosures for `τ`
and for every preceding coefficient used by either polynomial or any domain
obligation. A reply records its subject, requested effort/precision, actual
precision, source theorem/rule identity and derivation dependencies. Interval
containment is justified by replay; a callback cannot assert it. Reuse
`Hex.Interval` outward arithmetic and its resource checks, not floating-point
endpoint tests. The oracle-to-sign integration and convergence laws are new
work; the existing scheduler alone does not establish them.

For totality, each source supplies an effective schedule: for every requested
`k : Nat`, a computable effort bound eventually produces a containing finite
interval of width at most `2^(-k)`. Include recursive coefficient approximation,
source computation, rounding and endpoint resource requirements. Intersect
compatible successive enclosures or use a deterministic refinement schedule;
reject certified-empty intersections for a purported common subject. Valid
coefficient and constant enclosures jointly refine; fixing coefficient
precision while refining only `τ` does not meet the convergence contract.

`Real.sign?` first checks the fraction and all expression domains, certifies
formal zero when available, and otherwise evaluates numerator and denominator
by interval Horner arithmetic. A lower endpoint above zero, or an open lower
cut at zero, certifies positivity; the symmetric upper-cut test certifies negativity. Closed
endpoints at zero do not certify a nonzero sign.
Refine both evaluations until separated from zero. A zero numerator sign
requires formal coefficient-zero/identity evidence or a separately replayed
exact evaluation-zero certificate; an interval merely containing zero cannot
prove equality. Denominator separation proves nonvanishing. Exact denominator
zero yields `domain`; persistent uncertainty yields `exhausted`.

Successful nonzero signs multiply numerator and denominator signs, without
needing interval division. Rational coefficient enclosures must be outward:
non-dyadic rationals are not dyadic singletons. Cached expression enclosures
are reusable only with their subject and provenance; repeated occurrences may
share facts but interval dependency can still delay separation.

Let `Pι(τ)` denote evaluation after mapping every coefficient through `ι`.
The companion must prove `eval_sound` and `sign_sound` of the following shape:

```text
EnclosureLaws ctx ∧ CoefficientLaws ops ∧ WellFormed ctx f
  ∧ sign? n ctx f = ok s cert
  → ValidDomains ctx f ∧ CheckSound ctx cert
    ∧ s = sign(Pι(τ) / Qι(τ)).
```

`WellFormed` concerns the representation and context references, not real
nonvanishing. `ValidDomains` concludes `Qι(τ) ≠ 0` and nonvanishing of every
original source divisor from the checked evidence. Thus success establishes
the domains even on the zero-numerator and cancelled-divisor paths; callers
do not need to prove those facts separately. The computational checker proves
its conditional replay/composition laws;
the companion discharges real enclosure semantics. No transcendence,
convergence or sufficient-fuel premise is allowed in success soundness.
Under these hypotheses distinct successful runs agree even if they use
different precision schedules or certificates.

## Eventual success and the total adapter

For an embedded preceding field, the relative transcendence condition is

```text
∀ P : F[X], P ≠ 0 → P.map(ι).eval(τ) ≠ 0.
```

This is transcendence over `ι(F)`, not a statement only about rational
coefficients. It makes formal rational-function evaluation injective and
ensures nonzero formal denominators do not vanish. For valid guarded inputs,
formal nonzero certificates for all original divisors are also required;
transcendence cannot make a formally zero divisor valid.

With this hypothesis, enclosure soundness and effective convergence, plus
lawful eventually successful coefficient arithmetic/zero tests, normalization
and replay, require `Real.sign_isSome`:

```text
RelativeTranscendence ι τ → EnclosureLaws ctx → CoefficientLaws ops →
ReplayLaws ctx ops → OracleConvergence ctx → OperationProgress ops →
CofinalSchedule limits →
∀ f, Valid ctx f → ∃ N, ∀ n ≥ N, (sign? n ctx f).isSome = true.
```

Here `Valid` includes well-formedness, valid coefficient inputs and nonzero
formal denominators for the fraction and all retained source guards.
`sign? n` means the deterministic run using a cofinal resource schedule
`limits n`: every finite fuel, precision, input, arithmetic and evidence
requirement is eventually admitted, and admitted successful finite work
remains available in later runs. Fixed caller caps do not satisfy this theorem.
Fair refinement reaches every coefficient and domain obligation. On formal
zero inputs, successful normalization/zero evidence terminates the zero path;
on nonzero inputs, polynomial continuity and finite simultaneous enclosure
convergence eventually separate numerator, denominator and required divisors.
Bounded mode without relative transcendence may still succeed and is sound;
unresolved algebraic relations need not ever succeed.

`Total` takes executable bounded operations and a separate `SearchLaws : Prop`
package proving validity preservation, failure exclusion, eventual success
for each valid input, and the sign/arithmetic laws. The companion constructs
this package under the hypotheses above. No real number or analytic proof
must enter the runtime data path. The Mathlib-free termination construction
is an accessibility recursion, not selection of a fuel by classical choice:

1. For fixed valid `f`, define `Step m n` to mean `m = n+1` and the run at
   budget `n` returned exhaustion.
2. Prove `Acc Step n` for every `n` from eventual success: for an existential
   threshold `N`, an exhaustion step has `n < N`, so `N-n` strictly decreases.
   Eliminate the existential only while proving this proposition.
3. Define executable `search n (h : Acc Step n)` by running `sign? n`.
   Return its checked sign on `ok`. Recurse at `n+1` on `exhausted`, using the
   accessible successor. `domain` and `invalid` are impossible for this
   validated input under the law package; eliminate them by their proofs.
4. Start at zero. Prove `search_spec`: the returned sign has an accepted
   certificate from some finite run and agrees with the semantic sign.

Under `SearchLaws` and `Valid ctx f`, the computational statement is

```text
search ctx f = (s, cert) → ∃ n, sign? n ctx f = ok s cert.
```

Together with `sign_checks` and the companion's `sign_sound`, this gives
accepted replay, domain validity and the semantic sign of the total result.

Accessibility proofs erase; runtime computes the increasing search, never an
arbitrary witness extracted from `Prop`. This gives terminating Lean recursion
without `partial`, `unsafe`, `axiom` or an opaque trusted search callback.
The total API uses validated typed inputs; raw validation failures stay in
the bounded API. A certified computable separation bound may replace search
only if it bounds the entire pipeline, including coefficient/normalization
and replay work, and proves success at the computed resource envelope.
An arbitrary fuel, a bare approximation callback or a proof of mere enclosure
containment cannot construct the total adapter.

Use this sign to define `<` and `≤` by the sign of subtraction on a lawful
field carrier, prove totality, antisymmetry and ordered-ring laws, and provide
the core classes named above. Raw noncanonical representatives first need a
semantic quotient or a proved faithful canonical carrier, executable lifted
operations and an equality decision for that carrier. This SPEC does not
install an order on the representatives themselves.

The [pinned Mathlib audit](../future-work.md#ordered-rational-functions-and-termination)
finds no `Transcendental ℚ Real.pi` or
`Transcendental ℚ (Real.exp 1)` theorem. `π` and `e` therefore expose certified
bounded modes and explicitly conditional total modes. Even separate proofs
over `ℚ` would not justify a total `ℚ(π,e)` order: adjoining the second
constant requires transcendence over the embedded first extension. No
unresolved comparison becomes equality, zero, or a default ordering.

## Companion model and proof ownership

Use [the pinned revision](../../lake-manifest.json)
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`. The following are dependencies and
proof obligations, not assertions that all correspondence is already proved:

| Source / owner | Available input or required statement |
| --- | --- |
| `HexRationalFnMathlib/Correspondence.lean` | Existing `HexRationalFnMathlib.equiv` with `RatFunc K`, operation correspondence, and canonical normalization/certificate agreement. |
| Mathlib `RingTheory/LaurentSeries.lean` | Existing `RatFunc` embedding into `LaurentSeries K = HahnSeries ℤ K` and `RatFunc.coe_X = single 1 1`. |
| Mathlib `RingTheory/HahnSeries/Lex.lean`, `Summable.lean` | Existing lexicographic ordered-ring and Hahn-field infrastructure. |
| `HexOrderedFnMathlib` | Compose the fraction embedding with the lex wrapper; prove injectivity, constant embedding, lowest-coefficient sign correspondence, normalization invariance, ordered-field laws and `X_lt`. Iterate `Lex (HahnSeries ℤ K)` for successive infinitesimals. |
| `HexIntervalMathlib` and registered analytic providers | Certified real containment for dyadic operations and source enclosures; each constant package must prove its own effective convergence. |
| `HexOrderedFnMathlib` | Prove real evaluation preserves field operations under relative transcendence, injectivity, polynomial-enclosure convergence, sign soundness and `sign_isSome`; construct the erased total-search law package. Prove bounded semantic normalization corresponds to `RatFunc F` even when representatives are noninjective. |
| Shared `HexPoly` adapters, specified by `hex-sturm` | Fallible semantic degree, division, gcd and extended gcd with bounded execution, successful-result laws and eventual success under the corresponding coefficient laws. |
| Tau Ceti / `hex-real-closure-mathlib` | Ordered real-closure existence belongs downstream; no additional abstract real-closed-field theorem is imported by this library's companion. |

The Hahn model has constants at exponent zero and the new infinitesimal at
exponent one. Its `ℤ` exponent group does not give a real closed field.
Do not claim square roots, algebraic closure operations or an embedding of
this non-Archimedean ordered field into `ℝ`. The family's Tau Ceti ownership
table places ordered real-closure existence in the real-closure companion,
with statement shape: every linearly ordered field admits an algebraic,
order-preserving embedding into an ordered real closed field. Polynomial
IVT/Rolle, Cauchy-index and Thom results are owned by the other family
companions. None is an assumption needed to compute the sign of a rational
function here. Missing foundations tracked by
[#10300](https://github.com/kim-em/hex-dev/issues/10300) do not block this SPEC.

## Conformance and adversarial cases

Conformance fixtures record the context/tower, oracle identities and versions,
inputs, exact expected sign or failure class, budgets and replay evidence.
Pin Z3 and record fixture provenance for `MkInfinitesimal`, `Pi`, `E` and
comparison/arithmetic cases from the paper's `basic.py`. Z3 agreement is a
differential check, never proof of transcendence or oracle correctness.
Rational-only cases cross-check exact Python fractions/python-flint and the
existing real-algebraic API where applicable. Require exact signs and
identities, not matching printed decimal approximations.

Required cases include:

- Zero and constants; numerator/denominator monomials of different valuations;
  `1/(X-1) < 0`; invariance under a common nonzero polynomial factor and
  normalization; large initial strings of zero coefficients.
- Two and three infinitesimal levels, including `ε₂ < ε₁^m`, positive rational
  bounds, `1/ε > n`, and sign preservation for predecessor embeddings.
- The corrected paper identity
  `(εx²-1)(εx³-1) = ε²x⁵-εx³-εx²+1` as polynomial arithmetic over the ordered
  coefficient field. Its three algebraic roots and derivative/Thom tests
  belong to the downstream root libraries, not this rational-function API.
- Semantic-zero coefficients with distinct raw syntax; zero trailing
  coefficients; a failed lower-level zero test before a later nonzero entry;
  false Bézout, degree, monicity and cross-multiplication certificates.
- `0/0`, a zero polynomial denominator, a real pole, and `(X-c)/(X-c)` at `c`
  with its original guard retained; formal identity success after all domains
  are certified. Test checked zero inversion separately from total field
  inversion at zero.
- Both signs of denominator evaluation; very small nonzero numerators and
  denominators; non-dyadic coefficient enclosure; coefficients whose coarse
  enclosures prevent separation even after the new constant is refined.
- Independent certified bounds for `π` and `e`, including a sign such as
  `π-4 < 0`, without assuming their relative transcendence. A dependent
  constant such as an oracle for rational `2` tested on `X-2`, supplying only
  nondegenerate zero-containing result enclosures and no identity/equality
  witness, must exhaust. A second fixture with a certified singleton `[2,2]`
  may derive an exact-zero certificate and succeed. Neither fixture may
  manufacture a field embedding.
- Zero-containing, unbounded, empty, nonconvergent and forged enclosures;
  wrong constant identity, stale version/embedding, malformed replay, and
  mutually inconsistent purported facts. Structural well-formedness alone
  must not authenticate semantic containment or convergence.
- Zero fuel and one-step-short limits in every nested callback, normalization,
  interval operation, input/trace check and replay path. Exhaustion has no
  equality consequence. Valid finite successes agree across larger cofinal
  budgets; fixed precision caps may keep exhausting.

Small literal checks use `decide`/`#guard`; larger fixture campaigns use
compiled emitters and independent comparisons. `native_decide` is banned.
Negative certificates must be tested at replay boundaries as well as producer
entry points. No external test oracle becomes a runtime dependency.
When implemented, register the new Z3 oracle through
[the existing oracle script](../testing.md#adding-a-new-oracle), within the
existing single CI job. Operations without an external analogue, including
provenance rejection and resource failures, still need direct Lean checks
and explicit non-coverage tracking under [the testing contract](../testing.md).

## Phase-4 evidence requirements

Use the [shared benchmarking discipline](../benchmarking.md). Keep bench
imports Mathlib-free; measure kernel/analytic replay separately. Before
accepting a representation or normalization policy, report:

| Workload | Required measures and comparison |
| --- | --- |
| Infinitesimal sign | Vary polynomial degree, first nonzero index and tower depth; count coefficient tests, recursive calls and evidence size. Scanning costs are linear in visited coefficients, with recursive coefficient cost reported separately. |
| Fraction arithmetic | Vary degree, coefficient height and common factors; compare bounded record and total `RationalFn` adapters on the same lawful inputs. Record gcd/exact-division work and intermediate coefficient sizes. |
| Real sign | Vary precision needed for separation, denominator proximity to zero and number/depth of preceding coefficients. Record every refinement, interval operation, requested/achieved precision, endpoint size and exhaustion. No uniform precision bound in degree alone is claimed. |
| Normalization policy | Adjacent clean denominator-one versus eager-normalization arms on the same expressions, with identical sign/domain results; report size and gcd work, not just time. |
| Certificate handling | Separate production, replay, retained/deduplicated cells and nested coefficient evidence; show malformed and exhausted replay remains bounded. |

The planned `tower8`, degree-15 MetiTarski, `nlsat.py` and
Rioboo/Strzeboński family workloads supply downstream integration evidence.
This library contributes arithmetic/sign attribution; root counts, sorted
roots, multiplicities and isolation completeness remain their owners'
requirements. The paper's historical timings are not acceptance thresholds.
Use lean-bench's fixed trial-major schedule, automatically selected CPU
pinning where supported, retain every completed shared-host sample, and
alternate adjacent `AB`/`BA` arms for comparisons. Permit at most one unchanged
rerun after an inconclusive result. Record host activity as context and supply
one representative Phase-4 profile to attribute costs. No new CI fan-out or
requirement to wait for an idle host is introduced.
