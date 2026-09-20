# hex-real-closure-mathlib

Selected-root semantics, ordered-field correspondence, complete roots and
finite-sign realization for [hex-real-closure](hex-real-closure.md).

## Status and placement

This is the planned companion required by
[#10318](https://github.com/kim-em/hex-dev/issues/10318), within the
[real-closure family](../future-work.md#real-closures-of-ordered-fields).
New declaration names and formulas below are mathematical/API contracts,
not available declarations or checked Lean prototypes. No implementation,
phase advancement, publication, tactic, CAD/coverings algorithm or
nonstandard-analysis result is introduced by this SPEC.

`HexRealClosureMathlib`, namespace `Hex.RealClosure`, imports
`HexRealClosure`, `HexPolyMathlib`, `HexSturmMathlib`, `HexSignDetMathlib`,
`HexOrderedFnMathlib`, `HexRealAlgebraicMathlib` and Mathlib, with the explicit
Tau Ceti foundation below. Shared real-roots and interval correspondence
comes through the preceding companions. Keep four computational libraries
and four companions. No computational library imports this companion,
Mathlib or Tau Ceti; no existing input, including hex-real-algebraic, gains
an import of this family. Coefficient callbacks are lower-level operation
records, not reverse imports of selected-root implementations.

Planned modules are `Model`, `Correspondence`, `Split`, `Roots`, `Union`,
`Specialize`, `Repr` and build-only `Tests`. The computational owner supplies
executable algorithms, bounded records and checkers. This companion proves
representation-specific correspondence and discharges their semantic law
packages; it does not replace executable operations with classical choices.
Follow [proof-debt policy](../design-principles.md#proof-debt-does-not-cross-the-layer-boundary).
Source-local SPEC placement follows implementation.

## Semantic parameters and foundations

For relative semantics fix

```text
[Field K] [LinearOrder K] [IsStrictOrderedRing K]
[Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
ι : K →+* R,       hι : StrictMono ι.
```

The field hom is injective. No Archimedean, rational separation or ordinary
topological connectedness hypothesis is implicit. `K` is the semantic
coefficient field of the current level; `B` below denotes the fixed base
before any algebraic adjunctions. Interpret valid raw coefficients `C` in
`K` by a map which need not be injective, then map polynomials along `ι`.
Use the same `CoeffOps`, `FieldOps`, context and interpretation throughout
a statement. Semantic degree evidence supplies either zero or a nonzero
leading coefficient and zeros above the claimed degree; storage length and
syntactic equality cannot substitute for it. Use the computational `Sign`
with the explicit `SignType` translation from hex-ordered-fn-mathlib.

For a bounded real-constant context without relative transcendence, only
the validated expressions and their certified original denominator guards
are interpreted. Do not infer an embedding of the entire formal rational
function field from successful evaluations: specialization may kill a
nonzero polynomial. Arithmetic success soundness uses local interpretation
laws. Global field embeddings, faithful equality and total adapters require
the stronger hypotheses stated below.

The audit baseline is Mathlib revision
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa` in
[lake-manifest.json](../../lake-manifest.json).

| Owner | Input and availability |
| --- | --- |
| Mathlib `FieldTheory/IsRealClosed/Basic.lean` | Existing class and `IsRealClosed.of_linearOrderedField`: nonnegative elements are squares and odd-degree polynomials have roots. This pin does not supply ordered real-closure existence or an `IsRealClosed ℝ` instance. |
| Tau Ceti through [hex-real-roots-mathlib](../../HexRealRootsMathlib/SPEC/hex-real-roots-mathlib.md#shared-foundation-and-proof-ownership) and [hex-sturm-mathlib](hex-sturm-mathlib.md) | Planned polynomial IVT/Rolle, signed-remainder/Cauchy-index identity, and their Hex query/replay bridges. Include common gcds, zero query, positive scaling, root-free finite endpoints and infinities. |
| Tau Ceti through [hex-sign-det-mathlib](hex-sign-det-mathlib.md) | Planned Thom injectivity/order, actual-count moment identity and support-preserving recursive BKR reduction; Hex complete-table, descriptor, comparison and re-encoding correspondence. |
| [hex-ordered-fn-mathlib](hex-ordered-fn-mathlib.md) | Planned real evaluation under relative transcendence, successful enclosure soundness, progress, rational-function/Hahn embedding and lowest-coefficient sign correspondence. |
| hex-real-roots-mathlib | Planned `IsRealClosed ℝ`, proved from existing real square roots and polynomial order/IVT lemmas. Use this shared instance for real transcendental bases. |
| [hex-real-algebraic-mathlib](../../HexRealAlgebraicMathlib/SPEC/hex-real-algebraic-mathlib.md) | Existing `RealAlgebraicNumber` ordered field and real-closed instance, comparison, root and Repr correspondence; use it for the rational base. |
| Tau Ceti, consumed here | Additional ordered algebraic real-closure existence statement specified next; needed for unconditional algebraic infinitesimal models. |
| This companion | Selected-root quotient/descent, splitting and live-context transport, Yun/root correspondence and termination laws, compatible algebraic union, specialization and finite-sign realization, trivial-tower and Repr agreement. |

The additional existence contract has the following exact mathematical shape,
with universe levels chosen explicitly when it is implemented:

```text
For every ordered field K, there exist a field R with a linear order,
IsStrictOrderedRing R and IsRealClosed R, and ι : K →+* R, such that
StrictMono ι and ∀ x : R, ∃ p : Polynomial K, p ≠ 0 ∧ p.eval₂ ι x = 0.
```

The last clause is algebraicity over the embedded base, equivalently
`Algebra.IsAlgebraic K R` for the algebra structure induced by `ι`. The
order on `R` must extend the given order on `K`; an abstract unordered
algebraic extension is insufficient. This is an additional foundation beyond
the univariate theorem list of
[#10300](https://github.com/kim-em/hex-dev/issues/10300), not a theorem
supplied by that list or by the pin. Foundation delivery belongs to Tau Ceti;
Hex must not undertake a second absolute Artin–Schreier construction or
introduce an axiom to stand in for it.

Until that import exists, statements with a supplied `R,ι` remain relative.
`Lex (HahnSeries ℤ K)` supplies an ordered field model of a positive
infinitesimal, not its algebraic real closure: the exponent-one monomial has
no square root in that integer-exponent field. Apply the existence contract
to the ordered infinitesimal base when an ambient algebraic model is needed.
The real Taylor-sign fragment and the finite literal replay realization route
below have no such prerequisite. They establish finite real conclusions, not
an ambient infinitesimal model or unconditional symbolic field instances.

## Selected roots and the semantic field

A valid algebraic level has a semantically nonzero squarefree polynomial
`p` of positive degree and a descriptor binding its predecessor context,
open interval (possibly infinite) and indexed derivative signs. Finite
endpoints are root-free. The descriptor's denotation theorem is

```text
Root.denote: ValidDescriptor p d → ∃! α : R, Selected (p.map ι) d α.
```

`Selected` includes evaluation zero, strict interval membership and every
specified derivative sign. Partial encodings require count-one evidence;
full encodings require existence. Complete partial encodings before using
the imported Thom order rule. Different defining polynomials require the
sign-det common squarefree-product comparison, not comparison of raw sign
vectors or overlap of isolating intervals.

An element is a polynomial representative `q(α)` over the predecessor
field, recursively interpreted. Degree below `degree p` is not required.
For valid elements set `a ≈ b` iff `eval a = eval b`. Prove equivalence,
congruence of successful operations, and the following statements:

| Planned statement | Required conclusion |
| --- | --- |
| `Element.eval_add`, `eval_neg`, `eval_mul` | Successful operations on valid operands denote the corresponding ambient operations and preserve validity/domain guards. |
| `Element.sign_sound`, `compare_sound` | Accepted bounded signs/orders equal the ambient sign/order, including the zero/equal cases. |
| `Element.eq_iff` | With complete sign laws, the executable zero test on `a-b` is true iff `eval a=eval b`. Bounded exhaustion proves neither equality nor inequality. |
| `Value.eval_injective` | Evaluation from the quotient of valid representatives by `≈` is injective and its image at one algebraic level is exactly `K(α)`. |
| `Value.field`, `Value.ordered` | Executable operations descend to the quotient, with field and linear ordered-ring laws; the evaluation field hom is strictly monotone. |

A reducible `K[X]/(p)` is not this field. At `p=(X-1)(X+1)`, `α=1`,
`X-1` denotes zero despite its nonzero remainder. Prove executable quotient
lifting, equality and progress before installing total instances. Align the
chosen Lean-core field/order dictionaries with Mathlib through evaluation.
The total inverse has `0⁻¹=0`; the checked nonzero inverse rejects zero.
Rational-base ambient existence is discharged by `RealAlgebraicNumber`;
real-base existence uses the shared `IsRealClosed ℝ` instance. Infinitesimal
field laws remain relative to a supplied model until Tau Ceti existence lands.
In every case executable totality separately requires the coefficient progress
laws, including relative transcendence where the real adapter needs it.
Semantic maps may be noncomputable; runtime quotient operations use the
computational search and split, with erased termination/law evidence.

Clean arithmetic correspondence retains integral base coefficients and
recursive denominator-one representatives. Prove denominator clearing with
nonvanishing guards and its sign correction. Positive-scaled pseudo-remainders
preserve the needed signs, while value transport retains the scalar identity.
No proof may assume monic defining polynomials or eager reduction of all
representatives. A negative scalar requires explicit sign correction.

## Splitting, transport and enlargement

`Element.inv_sound` follows the actual inversion algorithm. For selected
`α`, squarefree `p`, and certified `q(α)≠0`, a checked `g=gcd(p,q)` gives
`g(α)≠0`. With `h=p/g`, prove `h(α)=0`, squarefreeness of `h` and
`gcd(h,q)=1`. A nonconstant gcd gives `1≤degree h<degree p`; constant gcd
needs no persistent change. Accepted `A*q+B*h=1` yields inverse `A(α)`.
For a pseudo-Bézout identity with right side `c≠0`, the inverse is `A(α)/c`,
with checked scalar inversion. The returned value times the original is one.

`Context.transport_sound` quantifies over the full finite live context DAG,
not just the inverted element. Re-encode `α` using derivatives of **h**,
retaining joint selection evidence with the old descriptor. Transport every
live representative, downstream defining polynomial, selected root, interval,
sign, domain guard and cache claim in predecessor order. Required diagrams
commute with denotation, and embeddings preserve equality and strict order.
Prove identity/composition of transport extensionally. Bind evidence to full
context versions and literal operands; a hash or a copied derivative vector
is not evidence. Persistent updates commit only after all requested transports
succeed; otherwise old contexts remain valid. Old handles cannot be used in
new contexts without transport. Pure local inversion and a persisted split
must give equal quotient values.

At a fixed level of initial degree `d`, there are at most `d-1` nontrivial
persistent splits. Sum those bounds over a fixed tower; this is not a bound
on future adjunctions or the cost of repeatedly recomputing a local split.

For base enlargement, let `R/B` be the supplied ordered algebraic real
closure. If the initial ambient field was merely real closed (for example
`ℝ` over a real transcendental base), first replace it by its algebraic
subfield `U` from `Union.realClosed` below and call that field `R`. Form
ordered `R(δ)` with `δ` positive infinitesimal over **all** of `R`, and apply the same existence contract to obtain `R'`. The composite
`R → R(δ) → R'` preserves previous selected roots and their order literally.
Prove `R'/B(δ)` algebraic using algebraicity of `R/B` and transitivity.
Rebuild computational stages as `B(δ)` followed by transported algebraic
levels; never append an infinitesimal after an algebraic level.

`Context.enlarge_sound` also proves agreement with the staged order: every
positive element algebraic over an ordered base has a smaller positive base
element, so an infinitesimal over that base is smaller than all positives in
its ordered algebraic extension. Prove this algebraic bound locally, along
with descriptor preservation under the embeddings; do not silently assume a
uniqueness-of-real-closure theorem. Enlargement changes the fixed base for
the union construction below.

## Complete roots, failures and termination

`Yun.decompose_sound` proves the computational owner's new characteristic-zero
Yun recurrence correct using derivative, gcd and exact-division correspondence. Successful
nonzero output has `F=u*∏ fᵢ^mᵢ`, `u≠0`, positive distinct multiplicities,
nonconstant squarefree pairwise coprime factors, and
`degree F=∑ mᵢ*degree fᵢ`. Zero is a separate result; constants have no
factors. Product equality alone proves neither multiplicities nor completeness.
Yun's remaining-multiplicity measure decreases even when an iteration emits
nothing and the current polynomial's degree does not decrease.

For `rootsWith ctx limits f = ok S`, `roots_sound` states:

```text
S = all  iff  F = 0.
If S = finite [(a₁,m₁),…,(aₖ,mₖ)], then F ≠ 0,
  eval a₁ < … < eval aₖ,
  ∀ x : R, F.eval x = 0 ↔ ∃ i, eval aᵢ = x,
  ∀ i, 0 < mᵢ ∧ mᵢ = F.rootMultiplicity (eval aᵢ).
```

Outputs may extend the coefficient tower; use their common ambient model and
explicit embeddings. Nonzero constants give the empty finite result. The
`all` case has no finite list of multiplicities. Do not require the real
multiplicities to sum to `degree F` when nonreal roots exist.

Prove coverage through capped root-bound attempts, capped bisection and full
derivative sign determination on every unresolved interval. No finite bound
is required for success of the complete fallback; a finite bound does not
imply dyadic separation. Root split points are emitted once, removed by
certified deflation, and excluded from pending open intervals. Restore Yun
multiplicities, compare factors through joint descriptors, and prove no
omitted roots or duplicates. Query/BKR correctness is consumed through the
preceding companions, not reproved as a new analytic foundation here.

The failure contract matches the computational owner exactly:

| Outcome | Semantic contract |
| --- | --- |
| `ok` | All domain checks and claimed postconditions hold, including full root coverage. No diagnostic prefix can masquerade as complete output. |
| `invalid` | A certified precondition/domain violation: e.g. zero checked inversion, invalid descriptor/stage or incompatible raw handle. Validation may instead exhaust. |
| `exhausted` | Insufficient resources or unresolved coefficient decision; no conclusion about zero, root absence or mathematical impossibility. Local bound/bisection slice exhaustion falls back; global exhaustion propagates. |
| `rejected` | Malformed/false evidence, wrong certificate context/version or failed producer invariant. Rejection does not refute the underlying mathematical claim. |

Preserve ordered-fn's certified `domain` reason when mapping it to `invalid`;
map malformed evidence to `rejected` and retain exhaustion. Validate all
contexts and guards even on zero/constant shortcuts.

`terminates` covers every bounded call, including malformed inputs and zero
budget. Measures are tower depth for coefficient calls, semantic degree for
Euclidean loops, remaining multiplicity for Yun, fixed caps for bound search
and bisection, finite BKR recursion and literal size for replay. Check sizes
and references before allocation. `roots_isSome` and analogous operation
progress statements additionally require complete coefficient decisions,
evidence production/transport and replay laws. For a monotone cofinal schedule
of **all** resource limits require `∃ N, ∀ n≥N, succeeds (limits n)`.
Executable total search uses the owner's accessibility-based `SearchLaws`
construction, not classical choice of a successful fuel or a `partial` loop.

At real-constant levels, progress needs certified convergent enclosures and
transcendence relative to the embedded preceding field. Individual hypotheses
for `π` and `e` do not imply the joint condition for `ℚ(π,e)`; those theorems
are not on the pin. Successful bounded signs need only their validated
certificates. No total field on raw bounded syntax follows from that soundness.

## Compatible algebraic union

Fix the ordered base `B` and its embedding into supplied real closed `R`.
Take all finite compatible algebraic towers inside `R` with that base map.
Finite collections of towers have a common finite extension by adjoining
their generators in `R`. Prove selected-root presentations can describe the
needed algebraic generators: in characteristic zero their minimal polynomial
is squarefree, and a full Thom descriptor singles out the chosen root.
This is semantic existence; bounded certificate production remains conditional
on progress laws.

Identify presentations by equality in compatible extensions, prove coherence,
and embed their union `U` as the subfield of `R` consisting of elements
algebraic over `B`. Prove both inclusions, arithmetic/order compatibility and
`∀ x : U, IsAlgebraic B x`. An arbitrary chosen chain of towers is insufficient;
the system must contain all finite adjunctions (or prove the corresponding
closure property).

For `x≥0` in `U`, take an ambient square root (zero separately, the positive
root when `x>0`); it is algebraic over a finite tower containing `x`, hence
over `B`, so lies in `U`. For an odd-degree polynomial over `U`, put its
finitely many coefficients in a common tower. Its ambient root is algebraic
over that tower and hence over `B`. Thus `Union.realClosed` discharges
exactly the two premises of `IsRealClosed.of_linearOrderedField`.
If the supplied `R/B` is algebraic, also prove `U=R` under the embedding.
A finite tower is not asserted real closed, and this relative construction
does not establish existence of `R` independently of the foundation.

## Finite-sign realization

The tower owner constructs sections/sectors; this companion proves their
meaning. Fix an ordered field `F`, `ι : F →+* ℝ` with `StrictMono ι`, real
boundaries `a<b` (possibly infinite), and a finite family `Q ⊂ F[X]`.
Boundary elements must belong to a specified compatible real algebraic
extension of `F` or be supplied as real coefficients with their embedding
laws. A symbolic model extends the same ordered coefficient/boundary field;
its infinitesimals and algebraic choices have compatible ambient embeddings.
For bounded real constants without relative transcendence, take `F=ℝ` with
the identity embedding (or the actual generated real subfield), and supply
certified evaluation of the finitely used coefficients and original domain
guards. This is proof-level coefficient interpretation, not an executable
field of all reals or a faithful embedding of formal constant syntax. Finite
realization soundness thus needs no relative-transcendence hypothesis.
There is no embedding of its full non-Archimedean field into `ℝ`.

A sector certificate includes boundary order and completeness/adjacency:
no nonzero member of `Q` has a root in the open cell. Zero polynomials retain
zero sign. It records the sample's strict cell membership and all requested
signs. `Sample.realize` concludes

```text
∃ x : ℝ, a < x ∧ x < b ∧
  ∀ q ∈ Q, sign ((q.map ι).eval x) = certifiedSign q.
```

Omit an inequality at an infinite endpoint. Include any parameter equations,
root selections and guards used to interpret `Q`; if those parameters are
symbolic, the conclusion existentially quantifies their real realizations
as well. Fixed real constants remain fixed. An infinitesimal literal alone
cannot discharge this existential.

For `r+ε`, with `r` real and coefficients interpreted in `ℝ`, write the finite
Taylor polynomial `q(r+t)=∑ cⱼ tʲ`. A nonzero `q` has a first nonzero `cₖ`;
for all sufficiently small positive real `t`, the sign is `sign cₖ` by
continuity of the remaining factor. Identically zero polynomials stay zero.
The ordered-fn lowest-coefficient rule gives the same symbolic sign. Intersect
finitely many neighborhoods and include `t<b-r` when the upper boundary is
finite; for a left sample `r-ε`, require `t<r-a` at a finite lower boundary
and include the parity factor from `t↦-t`. This proof uses
real continuity and finite coefficients without constructing a real closure
of a Hahn field. For `±1/ε`, use leading-coefficient signs and degree parity,
a common real tail bound and finite boundary inequalities. Ordinary midpoint,
ray and whole-line samples have direct membership proofs.

Nested algebraic samples require the following **local** specialization
lemmas, not an unlisted model-completeness or transfer theorem.

`Query.transport`: a real interpretation of the finite guarded coefficient
and endpoint data which preserves the recorded arithmetic identities,
equalities, signs and nonzero guards transports an accepted query replay to
a valid real query with its claimed integer `Γ.count`. This is a finite-data
lemma; no field hom on all raw expressions is required. Include every leading
coefficient, positive scale, endpoint order/nonroot and squarefreeness witness.
It applies both to small-parameter specialization and to evaluation of
polynomial representatives at an already realized selected algebraic root.
In the latter case zero identities hold at that root, not necessarily as
literal identities over a rational-function field.

`Query.specialize`: for a finite accepted Tarski replay `Γ` over `F(ε)`,
with `F` ordered-embedded in `ℝ` and signs certified by the lowest-coefficient
rule, there exists `η>0` such that every real `0<t<η` preserves its guards and

```text
TaQ(f_t,p_t;I_t) = Γ.count.
```

Collect every nonzero rational-function sign used in the replay. Their lowest
nonzero coefficients give one finite real neighborhood. Polynomial identities
specialize identically after denominator guards; apply `Query.transport`.
This specialization is only on the finite guarded data, not a field hom
`F(ε) → ℝ`. In a supplied symbolic ambient model, query soundness also gives
`Γ.count=TaQ(f,p;I)`, recovering the computational SPEC's relative
`Query.specialize` contract. Applying transport to every query in a BKR replay
preserves its full table and support, not merely an invertible submatrix.

`Sample.specialize`: for a finite acyclic tower replay, collect lower-level
coefficient obligations recursively. At each algebraic adjunction preserve
the joint selected condition: the defining polynomial, descriptor and every
consumer constraint must hold at **one** real root. A single joint table
with a positive filtered count suffices. Alternatively, transport tables
sharing the same descriptor's count-one filter at the same parameter choices;
uniqueness identifies their roots and combines their sign claims. Different
descriptors require checked re-encoding/root equality before this combination.
Thus already certified `signAt` tables can supply joint evidence without
rerunning sign determination. Separate existential roots for individual
signs without a common unique selection are insufficient.

Transported equal roots, nonzero guards, parameter equations and cell
boundaries belong to that same finite evidence. For multiple infinitesimals,
specialize earlier levels first, then choose the next sufficiently small
positive parameter; its neighborhood may depend on all earlier choices.
For algebraic levels evaluate representatives at the selected real root and
apply `Query.transport` to the next level's query identities and zero/sign
certificates. This yields the relative contract from the computational SPEC:

```text
ValidTowerReplay Γ ∧ Realizes model Γ →
  ∃ (t₁,…,tₙ : ℝ) (α₁,…,αₖ : ℝ),
    (∀ i, 0<tᵢ) ∧ Φ(t₁,…,tₙ,α₁,…,αₖ).
```

Here `Φ` is exactly the finite recorded conjunction of equations, guards,
selected-root conditions, cell inequalities and requested signs over the
fixed real-embedded base. `Realizes model Γ` means the supplied compatible
ambient embeddings interpret each context and every recorded claim correctly.
Input interpretation and lower checker laws are explicit hypotheses.

Also prove `Sample.realizeReplay`: acceptance of this finite syntactic replay
and its authenticated real base-coefficient evidence implies the same real
existential **without** `Realizes model Γ`. Interpret the replay directly in
`ℝ`, using `Query.transport`, small-parameter specialization and complete
count-one table correspondence inductively. This stronger literal-evidence
route needs the shared `IsRealClosed ℝ` instance and univariate query/Thom/BKR
foundations, but not ordered real-closure existence for an infinitesimal
field. It supplies the real-valued consumer contract without constructing or
quoting an unused symbolic ambient model. The relative corollary additionally
identifies the realized signs with the symbolic denotations.

These induction and transport lemmas are local proof deliverables. They
preserve finitely many infinitesimal inequalities, never their universal
scheme simultaneously. If the requisite finite evidence is unavailable,
bounded export exhausts or uses an ordinary-point backend.

The [coverings literal format](hex-coverings.md#literal-samples-and-checked-export)
can receive denotation-preserving exports of rational-base algebraic samples.
An actual transcendental/infinitesimal coordinate needs a richer downstream
format or a separately checked finite-sign replacement; the latter is not
equality-preserving export. Future real-valued tactics consume only the
transitive evidence needed for the final real coefficient/realization claims,
retaining every prerequisite guard. No tactic integration is implemented here.

## Trivial towers, reconstruction and adversarial examples

With no transcendental or infinitesimal levels, interpret the compatible
algebraic towers in `RealAlgebraicNumber`. `Trivial.compare_eq` agrees with
`RealAlgebraicNumber.compare`, hence `AlgebraicNumber.realCompare`, using
[the existing comparison theorem](../../HexRealAlgebraicMathlib/Basic.lean).
`Trivial.roots_eq` agrees extensionally with `RealAlgebraicPoly.roots`,
including `all`, increasing order and exact multiplicities, by
[`contains_roots_iff`, `roots_all_iff`, `roots_sorted`, `roots_multiplicity`](../../HexRealAlgebraicMathlib/Roots.lean).
It covers coefficients in the rational-base algebraic fragment, not only
integer polynomials. Prove conversion round trips and arithmetic agreement;
both the delegated backend and generic backend obey these statements.
Do not copy the zero-polynomial empty-array convention of a convenience API.

`Repr.roundtrip` requires the same authenticated constant registry, context
DAG, stage order, coefficients, intervals and derivative signs, and a
sufficient resource envelope. Reading emitted constructor data succeeds and
preserves denotation and selected-root identity, modulo explicit context
isomorphisms; incidental caches need not match. Prove reader success and
semantic round trip separately, composing the existing rational-base
[Repr correspondence](../../HexRealAlgebraicMathlib/Repr.lean).
A changed oracle registration/version, missing guard or stale reference is
rejected; display decimals are not reconstruction data.

For a positive infinitesimal `ε` over an ordered base, prove the universal
statement `∀ n : ℤ, (n : R)<1/ε` and, for the selected positive square root,
`0<ε<sqrt(ε)<1`. For positive `n`, compare `ε` with the positive base element
`1/n`; nonpositive `n` follow from positivity. The square-root inequalities
use `0<ε<1` and order on nonnegative squares. These are statements in the
ambient extension, not universally realizable inequalities in `ℝ`.

Validate the corrected [paper Example 3](https://www.cl.cam.ac.uk/~gp351/infinitesimals.pdf):

```text
P = (εX²-1)(εX³-1) = ε²X⁵-εX³-εX²+1.
roots(P) = [-ε^(-1/2), ε^(-1/3), ε^(-1/2)], all multiplicity one.
```

Fractional powers here name unique positive roots/inverses, not an assumed
analytic power operation on `R`. Put `u=ε^(-1/3)`, `v=ε^(-1/2)`; then
`1<u<v`. Since `P'''=60ε²X²-6ε`, its signs at `u,v` are negative and
positive respectively (`ε*u²` is the positive cube root of `ε`, smaller
than `1/10`). Thus the positive roots can share `(0,+∞)` while Thom data
separates them. No extra negative cubic root is present.

## Replay, conformance and Phase-4 evidence

`Replay.check_sound` turns accepted bound literals into the statements above;
`Replay.checks` gives a computable sufficient replay envelope for successful
producer output under child laws. Replay validates identities and evidence;
it never reruns root isolation, gcd search, BKR production or approximation.
Structural checks reject cycles and forward/missing references. Charge nested
calls, decoding, coefficient proof arithmetic and allocation to one parent
budget; check claimed sizes before expanding data.

Make composition costs explicit. If level `d` has local replay cost `L_d`,
`m_d` coefficient-proof references and lower-level upper bound `T_(d-1)`,
an unshared upper bound is `T_d ≤ L_d + m_d*T_(d-1)` (use the sum of actual child costs
for unequal children). Serialized evidence satisfies the analogous recurrence.
A checked DAG may share identical bound claims, but report both unique node
count and expanded reference work; kernel quotation must also preserve or
account for sharing. There is no constant-cost coefficient oracle or blanket
polynomial bound in tower depth. Bound total bytes, nodes, depth, integer
bit lengths, array/matrix dimensions and cumulative arithmetic fuel; resource
exhaustion is explicit and cannot accept partial evidence.

Follow [testing](../testing.md) and [benchmarking](../benchmarking.md).
This companion is planned as `correspondence_only: true`, comparator absence
class **correspondence-only-layer**. `HexRealClosure` owns computational
conformance, pinned fixtures and runtime measurements; this companion has no
core `Conformance.lean` or separate compiled runtime benchmark. Build-only
proof examples check semantic conclusions; bulk correspondence sweeps belong
in the conformance tree's optional `CrossCheck` module.
Use computational Z3 fixtures (pinned version/command/input/output) for
infinitesimal signs, selected roots and comparisons, and python-flint plus
Hex's independent real-algebraic path on rational cases. A differential oracle
is not proof evidence; multiplicities absent from its output require separate
exact checks. Companion conformance must also produce kernel-checked theorem
instances and negative checker regressions for:

- Zero/constants, repeated factors, semantic leading cancellation, zero
  roots and exact multiplicities; Yun iterations with no degree drop.
- Example 3, `sqrt(ε)>ε`, integer inverse bounds, multiple infinitesimals,
  infinite roots, and `(X-ε)(X-2ε)` inside finite bounds without dyadic separation.
- Reducible `p=(X-1)(X+1)` at `1`: zero of `X-1`, rejection of its checked
  inverse, successful inversion of `X+1` after splitting, and preserved live
  downstream roots. Also `(X²-2)(X²-3)` at `sqrt(2)` inverting `X²-3`, which
  requires a shorter, recomputed derivative encoding.
- Non-monic clean definitions and high-degree representatives; negative
  scale mistakes, false Bézout/Yun identities, stale context evidence and
  local versus persistent split agreement.
- Root endpoints/deflation, failed dyadic bounds, zero bisection budget and
  complete fallback; omitted realizable BKR rows and incompatible root choices.
- All section/sector types, enlargement after algebraics, joint nested
  realization, missing denominator/boundary/consumer constraints, and rejection
  of a symbolic infinitesimal offered directly as a real witness (`invalid`
  for an unsupported raw export; `rejected` for fabricated real-witness evidence).
- Trivial backend agreement, Repr round trips, forged/nonconvergent enclosures,
  unresolved constant relations, invalid stages, cyclic DAGs and nested exhaustion.

Phase 4 separates computational production from proof evidence. Runtime
`tower8` isolation and clean-versus-eager normalization ablation belong to
the Mathlib-free owner; correlate their coefficient sizes, gcd work, depth,
split count and certificates with this companion's replay measurements.
Use fresh-module proof probes for elaboration, kernel replay, proof/serialized
size, peak memory and axiom audits, including nested specialization and failed
replays. No `native_decide`, introduced axiom or trusted oracle is permitted.
Measure depth/degree/sign-family size, sharing and lower-level evidence work
separately. Record one representative attribution profile when Phase 4
requires it; do not hide coefficient proof costs in an outer timing.

Run on the shared host with automatic CPU selection where supported, fixed
trial-major schedules, adjacent alternating AB/BA comparisons, every completed
sample retained and at most one unchanged inconclusive rerun. Host activity
is context, not a sample exclusion criterion. Absolute times are observations;
CI timeouts and the paper's historical timings are not scientific targets.
Extend existing CI scripts when implementation reaches conformance; this
SPEC adds no workflows or measurements and advances no phase.
