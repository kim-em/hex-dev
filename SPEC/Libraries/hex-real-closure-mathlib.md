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
Tau Ceti foundation below. Shared real-roots correspondence comes through
the preceding companions. Real-constant approximation procedures and their
soundness/progress evidence are supplied by callers through hex-ordered-fn;
there is no dependency on `HexInterval` or `HexIntervalMathlib`. Analytic
constant-provider implementations and proofs are outside this family. Keep
four computational libraries and four companions. No computational library imports this companion,
Mathlib or Tau Ceti; no existing input, including hex-real-algebraic, gains
an import of this family. Generic polynomial kernels consume ordinary total representation operations;
they do not import selected-root implementations.

Planned modules are `Model`, `Correspondence`, `Split`, `Roots`, `Union`,
`Specialize`, `Repr` and build-only `Tests`. The computational owner supplies
executable total algorithms and result checkers. This companion proves
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
before any algebraic adjunctions. Executable polynomials are `DensePoly E`
for the canonical-zero representation `E`. Interpret coefficients in `K`,
reflect zero to preserve degree, and map along `ι`. The representation map
need not be injective. Canonical-field specializations retain the existing
HexPolyMathlib correspondence. Signs are
integers in `{-1,0,1}`, translated explicitly to `SignType`.

The predecessor has executable total operations before this algebraic level
is constructed; this companion establishes their ordered-field interpretation. A real transcendental predecessor obtains
its order from the caller's approximation correctness, convergence and relative
transcendence hypotheses via ordered-fn. Optional bounded expression-level
sign attempts without those hypotheses do not provide the field `K`. A tactic
may separately consume a finite certified real inequality without constructing
such a coefficient field.

The audit baseline is Mathlib revision
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa` in
[lake-manifest.json](../../lake-manifest.json).

| Owner | Input and availability |
| --- | --- |
| Mathlib `FieldTheory/IsRealClosed/Basic.lean` | Existing class and `IsRealClosed.of_linearOrderedField`: nonnegative elements are squares and odd-degree polynomials have roots. This pin does not supply ordered real-closure existence or an `IsRealClosed ℝ` instance. |
| Tau Ceti through [hex-real-roots-mathlib](../../HexRealRootsMathlib/SPEC/hex-real-roots-mathlib.md#shared-foundation-and-proof-ownership) and [hex-sturm-mathlib](hex-sturm-mathlib.md) | Planned polynomial IVT/Rolle, signed-remainder/Cauchy-index identity, and their Hex query/replay bridges. Include common gcds, zero query, positive scaling, root-free finite endpoints and infinities. |
| Tau Ceti through [hex-sign-det-mathlib](hex-sign-det-mathlib.md) | Planned Thom injectivity/order, actual-count moment identity and support-preserving recursive BKR reduction; Hex complete-table, descriptor, comparison and re-encoding correspondence. |
| [hex-ordered-fn-mathlib](hex-ordered-fn-mathlib.md) | Planned real evaluation under relative transcendence, sign soundness/progress conditional on caller-supplied approximation laws, rational-function/Hahn embedding and lowest-coefficient sign correspondence. |
| hex-real-roots-mathlib | Implemented `Real.instIsRealClosed`, proved from existing real square roots and polynomial order/IVT lemmas. Use this shared instance for real transcendental bases. |
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

The computational owner uses canonical-zero representatives `Element ctx`,
not an already lawful field. Follow the
[execution contract](../real-closure-execution.md): prove interpretation of
actual arithmetic and sign, zero reflection, and polynomial degree/operation
correspondence. The map from representatives need not be injective. These
proofs do not enter the executable constructors or readers.

Prove this by tower induction. Sign determination at the current root uses
only predecessor operations and their established interpretation. Define
`a ≈ b` by equal selected-root denotations and prove equivalence to the
computational zero-sign-of-difference test (`Element.eq_iff`). A `Root.Laws`
lemma may organize the proof but is not a core construction requirement.
Construct `Value ctx` as the semantic quotient, then prove operation descent,
executable equality and field/order laws. Do not assume a current-level field
instance to justify the operations used to construct it.

| Planned statement | Required conclusion |
| --- | --- |
| `Element.eval_add`, `eval_neg`, `eval_mul` | Operations denote the corresponding ambient operations. |
| `Element.sign_sound`, `compare_sound` | Total signs/orders equal ambient sign/order, including zero/equality. |
| `Element.eq_iff` | The executable zero test on `a-b` is true iff `eval a=eval b`. |
| `Value.eval_injective` | Evaluation from the quotient of polynomial representatives by `≈` is injective and its image at one algebraic level is exactly `K(α)`. |
| `Value.field`, `Value.ordered` | Executable operations descend to the quotient, with field and linear ordered-ring laws; the evaluation field hom is strictly monotone. |

A reducible `K[X]/(p)` is not this field. At `p=(X-1)(X+1)`, `α=1`,
`X-1` denotes zero despite its nonzero remainder. Prove executable quotient
lifting, equality and the termination measures before installing total instances. Align the
chosen Lean-core field/order dictionaries with Mathlib through evaluation.
Build the Mathlib instances with the same executable operations and verify
`Field.toGrindField` recovers the selected core instance definitionally, as
`HexRealAlgebraicMathlib.Instances` does; verify order decisions likewise.
These instances are on the semantic quotient, not the raw representation.
The total inverse has `0⁻¹=0`; the checked nonzero inverse returns `none` exactly on zero.
Rational-base ambient existence is discharged by `RealAlgebraicNumber`;
real-base existence uses the shared `IsRealClosed ℝ` instance. Infinitesimal
field laws remain relative to a supplied model until Tau Ceti existence lands.
Executable totality uses predecessor representation operations and the
structural/size bounds in the execution contract. Real-constant search alone
retains its erased progress premise. Semantic maps may be noncomputable;
quotient operations lift the same computational sign and split algorithms,
with their companion descent proofs.
Prove this construction by tower induction: sign determination at the current
root uses only predecessor field operations; local inversion uses that sign
and predecessor gcd/xgcd. No operation invokes an as-yet-unconstructed
current-level field instance, and the quotient relation cannot be replaced
with congruence modulo a reducible defining polynomial.

Clean arithmetic correspondence retains integral base coefficients and
recursive denominator-one representatives. Prove denominator clearing with
nonvanishing guards and its sign correction. Positive-scaled pseudo-remainders
preserve the needed signs, while value transport retains the scalar identity.
No proof may assume monic defining polynomials or eager reduction of all
representatives. A negative scalar requires explicit sign correction.

## Packing and the rational selected-root slice

For the computational descriptor check `valid d`, quantify every scalar
correspondence theorem over `valid d = true` and the interpreted predecessor
context. Prove check soundness and existence/uniqueness of the selected root;
do not infer these from the raw data type. The rational finite-interval slice
uses `HexRealRootsMathlib.sturmCount_eq_card_roots`, with positive degree and
rational squarefreeness. Supply primitive-part root preservation and
squarefreeness of gcd divisors before using it for zero testing. Interval
refinement gives general rational-algebraic sign here; generic infinitesimal
semantics requires the abstract-field sign-determination development.

Required packing statements are `pack_sound` (evaluation is unchanged),
`pack_zero` (stored zero iff selected-root evaluation is zero), and
`pack_clean` (clean inputs remain clean under the specified policy). Prove
monic-clean remainder retention satisfies these statements and its degree
bound; general non-monic storage has no such bound. Prove the checked
irreducibility fast path agrees with general selected-root zero testing.
Do not turn an optimization's precondition into a restriction on all valid
squarefree descriptors. Any batched ring-operation implementation proves the
same interpreted result as the ordinary scalar-packing implementation.

Scalar zero/arithmetic/sign correspondence, inversion/splitting/transport,
and instantiation of shared polynomial correspondence are separately
verifiable proof obligations. The generic division/gcd transfer lemmas need
no injectivity; this companion discharges their zero-reflection and operation
preservation premises. xgcd, derivative and Horner bridges must concern the
existing algorithms. The rational slice can be proved in ℝ independently of
the not-yet-available arbitrary-real-closed-field foundation, but cannot
substitute for that foundation in the general tower theorems.

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
is not evidence. Persistent refinements return the new immutable context together with all
requested transports; old contexts remain valid. Prove denotation preservation for dependent
polynomials, endpoints, re-encoded roots and live values, as well as identity
and composition of the transport maps. A stale literal binding remains
invalid even for an operand whose serialization did not change. Old handles cannot be used in
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

## Complete roots and termination

`Yun.decompose_sound` proves the computational owner's new characteristic-zero
Yun recurrence correct using derivative, gcd and exact-division correspondence.
Its executable termination premise and this theorem both require the ordered
coefficient field (or an explicit characteristic-zero field hypothesis); the
contract does not extend to arbitrary positive-characteristic fields.
Nonzero output has `F=u*∏ fᵢ^mᵢ`, `u≠0`, positive distinct multiplicities,
nonconstant squarefree pairwise coprime factors, and
`degree F=∑ mᵢ*degree fᵢ`. Zero is a separate result; constants have no
factors. Product equality alone proves neither multiplicities nor completeness.
Yun's remaining-multiplicity measure decreases even when an iteration emits
nothing and the current polynomial's degree does not decrease.

For `roots f = S`, `roots_sound` states:

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

`terminates` proves the actual recursive measures: tower induction for
coefficient decisions, degree for Euclidean loops, remaining multiplicity for
Yun, fixed finite bounds for Cauchy attempts and bisection, finite BKR recursion
and literal size for replay. Every valid polynomial has a complete output;
there is no cofinal schedule of global resource limits and no user threshold.
The only unbounded search is predecessor transcendental sign, whose
accessibility proof comes from ordered-fn's caller approximation laws. Prove
termination of transport by predecessor DAG order and persistent splitting by
the strict defining-degree decrease. A polynomial's root existence alone does
not establish executable termination.

Raw constructors check mathematical stage, descriptor and context conditions,
returning `Option`; prove rejection/acceptance exactly characterizes those
declared conditions. Registry loading retrieves supplied oracle laws; it does
not decide convergence, relative transcendence or equality of arbitrary
constant descriptions. Replay is a Boolean check of supplied finite result evidence,
with separate soundness/completeness under its coefficient facts. Neither
boundary changes the total coefficient arithmetic. An internal invariant
failure is a bug to exclude by proof, not an allowed failure of `roots`.

At real-constant levels, total order requires caller-supplied certified
approximations, convergence and transcendence relative to the embedded
preceding field. Individual hypotheses for `π` and `e` do not imply the joint
condition for `ℚ(π,e)`; those theorems are not on the pin. Named demonstrations
remain conditional on caller evidence; this companion supplies no analytic
provider. Optional bounded sign attempts have separate soundness from finite
certificates, but cannot be installed as coefficient field operations.

## Compatible algebraic union

Fix the ordered base `B` and its embedding into supplied real closed `R`.
Take all finite compatible algebraic towers inside `R` with that base map.
Finite collections of towers have a common finite extension by adjoining
their generators in `R`. Prove selected-root presentations can describe the
needed algebraic generators: in characteristic zero their minimal polynomial
is squarefree, and a full Thom descriptor singles out the chosen root.
This is semantic existence. Executable total root production additionally
uses the exact coefficient structures and the termination proof above.

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
For a separate tactic accepting finite real coefficient evidence without
relative transcendence, its proof-level instance may take `F=ℝ` with the
identity embedding and those evidence hypotheses. This does not equip all reals
or formal constant syntax with an executable ordered-field instance. Such finite
realization soundness does not itself require relative transcendence.
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
scheme simultaneously. The exporter constructs the requisite finite evidence or chooses an
ordinary-point backend with a direct membership/sign proof.

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

`Repr.roundtrip` requires the same authenticated caller-supplied constant
registry, context DAG, stage order, coefficients, intervals and derivative signs. Reading emitted constructor data succeeds and
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

`Replay.check_sound` turns accepted result literals into the statements above;
`Replay.checks` proves produced certificates pass under their coefficient-fact
proofs. Replay validates polynomial identities, query chains, matrix equations,
support and selected-root evidence; it never reruns root isolation or BKR
production. These are result certificates, not proof-returning field operations.
A compiled total checker can decide coefficient facts using the ordinary exact
field. Kernel replay must support supplied proofs of those exact facts, composed
from child queries and finite caller approximation evidence: proof-founded
transcendental sign may contain opaque accessibility evidence and need not
reduce in the kernel. For reducible coefficient domains the same path can avoid repeating
expensive sign search. State and prove both checker interpretations agree.
Structural checks reject cycles and forward/missing references.

Make composition costs explicit. If level `d` has local replay cost `L_d`,
`m_d` coefficient-proof references and lower-level upper bound `T_(d-1)`,
an unshared upper bound is `T_d ≤ L_d + m_d*T_(d-1)` (use the sum of actual
child costs for unequal children). Serialized evidence satisfies the analogous
recurrence. A checked DAG may share identical claims; report unique nodes and
expanded reference work, and preserve or account for sharing in kernel
quotation. There is no constant-cost coefficient oracle or blanket polynomial
bound in tower depth. Measure bytes, nodes, depth, integer bit lengths and
array/matrix dimensions; these are complexity obligations, not an alternative
fallible arithmetic interface.

Follow [testing](../testing.md) and [benchmarking](../benchmarking.md).
`HexRealClosure` owns executable constructors, readers, algorithms, closed
tower conformance and Mathlib-free benchmarks. This companion is
`correspondence_only: true`: it proves their interpretation, semantic quotient
laws and validity/completeness. Build-only proof examples and optional
`CrossCheck` modules audit those statements; they do not supply erased law
arguments merely to run the algebraic algorithms.

For infinitesimal bases the semantic proofs require actual Tau Ceti ordered
real-closure existence and univariate correctness. A Hahn field alone or a
roadmap is not that proof. Core differential tests may run before these
proofs land; their success must not be reported as proof completion.

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
- Root endpoints/deflation, failed dyadic bounds, a policy omitting bisection and
  complete fallback; omitted realizable BKR rows and incompatible root choices.
- All section/sector types, enlargement after algebraics, joint nested
  realization, missing denominator/boundary/consumer constraints, and rejection
  of a symbolic infinitesimal offered directly as a real witness (no raw export for an unsupported coordinate; the checker rejects
  fabricated real-witness evidence).
- Trivial backend agreement, Repr round trips, forged/nonconvergent enclosures,
  optional inconclusive sign attempts, invalid stages and cyclic DAGs.

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
