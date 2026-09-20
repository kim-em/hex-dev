# hex-real-closure

Selected-root algebraic towers, exact arithmetic and complete real-root
isolation over ordered coefficient fields, including infinitesimal bases.

## Status, scope and placement

This planned computational library completes the
[real-closure family](../future-work.md#real-closures-of-ordered-fields).
Names and statements below are required mathematical/API shapes, not existing
or checked Lean declarations. This SPEC introduces no implementation, target,
phase advancement or publication. The companion has its own directive
[#10318](https://github.com/kim-em/hex-dev/issues/10318).

`HexRealClosure`, namespace `Hex.RealClosure`, consumes `HexPoly`, `HexSturm`,
`HexSignDet`, `HexOrderedFn` and `HexRealAlgebraic`. Rational-function
infrastructure is supplied below these inputs. Real constants use caller-supplied
approximation procedures and their certified rational bounds through
hex-ordered-fn's interface. This family does not depend on `HexInterval` or
`HexIntervalMathlib`, and supplies no built-in analytic constant providers.
The computational library and all its imports remain Mathlib-free. `HexRealClosureMathlib`
imports it, the companions of the inputs it uses, Mathlib and the explicitly
listed Tau Ceti foundations. Mathlib instances and analytic correspondence
live there. Keep the family's four computational libraries and four companions;
no existing input gains an import of this family. CAD, coverings and `rcf`
are downstream clients, never dependencies.

The division of responsibility is:

| Input/owner | Contract used here |
| --- | --- |
| [hex-poly](../../HexPoly/SPEC/hex-poly.md) | Exact `DensePoly K` arithmetic, degree, derivative, division and gcd/xgcd over lawful fields. Generic characteristic-zero Yun decomposition is owned here. |
| [hex-sturm](hex-sturm.md) | Ordered-field Tarski queries, root counts and Tarski replays, using the shared signed-remainder kernel in hex-real-roots. |
| [hex-sign-det](hex-sign-det.md) | Complete BKR tables and single-polynomial descriptors: validation, root identity/order, sign at a root and re-encoding. |
| [hex-ordered-fn](hex-ordered-fn.md) | Exact rational-function fields, caller-supplied certified real-constant approximations, infinitesimal orders and proof-founded total coefficient search. |
| [hex-real-algebraic](hex-real-algebraic.md) | Independent rational-base fast path; exact comparison and sorted roots with multiplicities. |
| This library | Generic characteristic-zero Yun decomposition, staged contexts, executable ordered-field carriers, selected-root arithmetic, splitting/transport, root isolation, tower sampling and exploration. |

The [number-field SPEC](../../HexNumberField/SPEC/hex-number-field.md)
provides precedent for lazy selected roots, but its fixed irreducible,
complex-embedded fields are not the generic tower representation.
[`SimpleRealRoot`](../../HexRealRoots/SimpleRealRoot.lean) uses integer
polynomials and a rational separation bound; interval overlap there cannot
be transplanted to infinitesimal towers.

## Semantic parameters and executable fields

Fix an ordered field `K` and an order-preserving field embedding `ι : K →+* R`
into an ordered real closed field. In the companion, `R` has
`[Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]`;
`K` has the first three structures. Ambient existence is an explicit
foundational obligation, not a runtime oracle. Polynomials are `DensePoly K`,
interpreted coefficientwise through `ι`; their degree is `DensePoly.degree?`.

The executable coefficient interface is the ordinary total one used by sturm:
`[Lean.Grind.Field K] [LE K] [LT K] [Std.IsLinearOrder K]`
`[Std.LawfulOrderLT K] [Lean.Grind.OrderedRing K] [DecidableEq K]`
`[DecidableLE K] [DecidableLT K]`. Signs are integers in `{-1,0,1}`.
There are no evidence-returning arithmetic callbacks, global resource budgets,
or field instances on raw representatives. Registered transcendental fields
must supply the exact total order from hex-ordered-fn, conditional on the
caller's approximation correctness, convergence and relative-transcendence
hypotheses. An optional bounded sign attempt cannot supply coefficient order.

Construct the tower by induction on its extension list. The predecessor
already has lawful executable field/order operations before adjoining a root.
Hex-sign-det over that predecessor supplies total sign at a validated root.
For its descriptor `d` and defining polynomial `p`, write
`s(q) = SignDet.signAt d q` on predecessor polynomials. The core declares a
proof-only `Root.Laws d : Prop` about this function, before constructing the
new quotient. It requires the ordinary signs of constants, negation and
products; signs in `{-1,0,1}`; zero sign of `p`; closure of zero-sign
polynomials under addition; and positivity of a sum of a positive-sign and
a nonnegative-sign polynomial. These statements mention only the predecessor
field and the actual sign algorithm, never the field instance they construct.
The companion proves them from `signAt_correct` and the descriptor's selected
root interpretation. This is the proof-only law-adapter pattern used by
[HexRealAlgebraic.Laws](../../HexRealAlgebraic/Laws.lean), with the laws stated
before quotient construction to avoid circularity.

Under `[Root.Laws d]`, the core proves selected-root equivalence, operation
congruence and sign descent, constructs the quotient, and derives executable
`DecidableEq`, `DecidableLE`, `DecidableLT` and the ordinary core field/order
instances. All polynomial and quotient algebra in this implication is proved
in the core; the semantic witness for `Root.Laws d` belongs to the companion
and requires the selected-root interpretation in an ordered real closed ambient
field. Rational and real-embedded bases need no additional ambient-existence
assumption. Infinitesimal bases require the missing Tau Ceti existence contract;
the Hahn model alone does not supply it. All cases still require the imported
sign-determination correctness proofs. Raw inversion uses only predecessor
gcd/xgcd and root signs.
Its inverse identity and congruence follow in the constructed quotient ring
before installing the field instance; inversion does not assume the field law
it is meant to establish. Only then form `DensePoly` over the new value type.

A context carries these erased proofs with its constructed stages.
`Context.adjoin ctx d (laws : Root.Laws d)` receives the proof explicitly;
instance search is not expected to manufacture it for a runtime descriptor.
Root isolation and readers that construct new typed contexts likewise take
the erased theorem `∀ d, Root.Laws d` for the predecessor field; the companion
supplies it from the fixed ambient interpretation. The runtime validator
checks finite descriptors, not infinitely many laws. Consequently a
closed algebraic-tower application must have those proofs available at
instantiation: a Mathlib-free declaration parameterized by the laws is not a
closed Mathlib-free application. Proof erasure preserves executable arithmetic
but does not remove the elaboration/import requirement. No proof-debt
assumption is an implementation. Runtime operations cannot choose
representatives or inverses noncomputably. Every sign needed by a level's
sign algorithm belongs to a strictly earlier level.

Field operations keep a fixed context. Temporary gcd splitting is local to
inversion; persistent refinements and base enlargement use explicit embeddings
and transport. `Context` packages the constructed carrier, its predecessor
embeddings and stage; this dependent packaging does not replace lawful field
instances with an alternative coefficient-operation framework.

## Staged contexts and selected-root identity

An opaque `Context` records a finite ordered list of extensions, their parent
identities, coefficient embeddings and replay provenance. Enforce stages
`transcendental ≺ infinitesimal ≺ algebraic`: any number of real constants,
then any number of infinitesimals, then any number of selected algebraic roots.
An algebraic extension is over the whole preceding field, not just the
original rational base. Each new infinitesimal is positive and smaller than
every positive element of its immediately preceding field.

A checked algebraic level contains a semantically nonzero squarefree
polynomial `p` of positive degree and a valid hex-sign-det descriptor `d`.
The descriptor binds `p`, the exact coefficient context, an open interval
with finite predecessor-field or infinite endpoints, and indexed derivative
signs. Its constraint selects exactly one root `α` in `R`. Finite endpoints
are not roots of `p`. A partial Thom encoding requires count-one evidence;
a full encoding still requires existence. Overlapping intervals or matching
raw derivative vectors from different polynomials do not establish identity.
Use `SignDet.compare` and its common squarefree-product re-encoding.

An `Element ctx` stores a polynomial representative `q(α)` at the top
algebraic level, over the predecessor quotient carrier. No bound
`degree q < degree p` is a representation invariant. Embedded predecessor
elements are constant polynomials. Equality means equality of denotations,
computed by the certified zero sign of the difference at the selected root.
In particular, a reducible `K[X]/(p)` is generally not a field and is not the
public carrier. For `p=(X-1)(X+1)` selecting `α=1`, `X-1` denotes zero while
its remainder modulo `p` is nonzero.

For a context equipped with these law proofs, define `Value ctx` as the
quotient of polynomial representatives by selected-root equality. Its semantic
image is `K(α)` at a single level. The core's equivalence, congruence and
executable equality theorems are conditional on `Root.Laws d`; the companion
discharges that premise and transports Mathlib instances along interpretation.
Use quotient lifting of the actual executable operations, not classical
selection of representatives or a noncomputable inverse. Inversion of zero
in this total field is zero. A checked inverse returns `none` exactly on zero.

In the lifted equality procedure, first check whether the same-context
representatives are literally equal; if so, return equality immediately.
Otherwise compute the zero sign of their difference at the selected root.
Structural inequality never implies semantic inequality. Prove the optimized
result equivalent to selected-root equality and invariant under replacement
of representatives. Nested literal comparisons must imply predecessor value
equality; hash equality alone is insufficient. This avoids unnecessary BKR
calls for identical representatives during polynomial normalization.

Operations on different contexts require a checked common extension and
embeddings preserving both selected-root interpretations. Never equate root
names or silently identify contexts. All handles and certificates bind the
full context version and operands; hashes may index caches but cannot replace
literal identity/equality checks. A context owns an immutable predecessor DAG.
Splitting or enlargement returns a new context plus explicit transport;
old handles remain valid only in their old context.

## Clean arithmetic and splitting

At the base, clean coefficients are integers (rationals with denominator one).
Recursively, clean values are denominator-one polynomials with clean
coefficients at rational-function or algebraic levels. Clean is a representation
predicate, not a claim that every field value is an algebraic integer.
Addition, negation and multiplication preserve clean representations before
optional reduction. Fractions outside this predicate are allowed.

Use signed pseudo-remainders with checked positive scaling and the shared
kernel's sign conventions. Reduction by a monic clean defining polynomial is
permitted when useful. Do not eagerly divide by a non-monic defining
polynomial or make it monic merely to store every element below its degree.
Local gcd/field computations may invert coefficients when required; do not
replace persistent clean definitions with their monic versions. Clear denominators for root/query work with nonvanishing and
sign evidence. A root-set-preserving negative scalar still changes query or
derivative signs and needs the corresponding correction. Positive-scaled
pseudo-remainders preserve signs at roots, not literal values; arithmetic
transport must carry the full identity including the scale.

For a checked inverse of `q(α)`:

1. Decide `q(α) ≠ 0` by total sign determination. For the total field inverse,
   return zero when this test is false; the checked nonzero inverse returns
   `none`. Some other root of `p` making `q` nonzero is irrelevant.
2. Compute `g=gcd(p,q)` using the predecessor field operations. Since `g | q`,
   `g(α) ≠ 0`. If `degree g>0`, set `h=p/g` by exact division, retain
   `p=g*h`, and prove `h(α)=0`, `h` squarefree and `gcd(h,q)=1`. Squarefreeness
   of `p` is essential to the last claim. Consume the validated descriptor’s
   executable witness that the monic gcd of `p` and `p.derivative` is one;
   core derivative/divisibility identities derive coprimality of `h` and `q`
   from it. A semantic squarefree assertion without this bridge is insufficient.
   With constant gcd keep `h=p`.
3. Re-encode the same root for `h` using **derivatives of h** via
   `SignDet.reencode`. Retain the old descriptor and joint selection
   evidence; copying the old Thom vector is invalid. A root-free old interval
   remains root-free for the factor, or the whole line can be used.
4. Transport every live element, coefficient, descriptor and downstream
   algebraic level, including cached signs and domain guards, in predecessor
   order. Prove embeddings commute with interpretation and preserve root
   identity, equality and order. Changed literals require certificate transport or recomputation. Construct
   the new immutable context and all requested transports together; old
   handles remain valid in their original context.
5. Compute extended gcd `A*q+B*h=1` and return `A(α)`. A pseudo-xgcd result
   `A*q+B*h=c`, `c≠0`, instead gives `A(α)/c` after checked scalar inversion.
   Certify the product with the original operand is one.

A nontrivial split has `1 ≤ degree h < degree p`; for a fixed level initially
of degree `d`, at most `d-1` persistent nontrivial splits occur. For a fixed
tower the bound is the sum of those bounds, not a bound over future appended
levels. One squarefree split removes every common factor needed for this
inverse. Pure quotient inversion may compute a temporary `h,A` and return the
polynomial `A` interpreted at the original `α`, with scalar adjustment when
needed. It need not mutate the quotient's context. Prove recomputed and
persisted splits give equal values; persistence is an optimization, not a
prerequisite for field laws.

## Characteristic-zero Yun decomposition

`Yun.decompose (f : DensePoly K)` is total new infrastructure owned here,
under the ordinary ordered-field hypotheses above (hence characteristic zero).
Both its termination and correctness require this hypothesis; a bare
`Lean.Grind.Field K` is insufficient. Use the existing exact field gcd,
derivative and division routines; prove each
claimed exact division from the recurrence invariants.

Its output is either `zero`, exactly when `F=0`, or a nonzero scalar
`u` and factors `(fᵢ,mᵢ)` with distinct positive multiplicities, nonconstant
squarefree factors, pairwise coprimality, and

```text
F = u * ∏ᵢ fᵢ ^ mᵢ,      ∑ᵢ mᵢ * degree(fᵢ) = degree(F).
```

Nonzero constants have the empty factor list and `u=F`. Multiplicity is in the
original polynomial, not the squarefree part. Normalization may use monic
working factors or clean scalar multiples; record all units in the product
identity and never force stored tower definitions monic.

One required algorithm is Yun's recurrence. For positive-degree `F`, set
`a=gcd(F,F')`, `v=F/a`, `w=F'/a`, `i=1`. While `v` is nonconstant, compute
`t=w-v'`, the monic `z=gcd(v,t)`, emit `(z,i)` when nonconstant, and set
`v=v/z`, `w=t/z`, `i=i+1`. All divisions are exact by the invariants. Units
are accumulated into `u`; using the monic `z` convention gives `u=lc(F)`.
The invariant identifies the remaining factors of multiplicity at least `i`;
in characteristic zero the loop finishes within `degree F` iterations, even
when an iteration emits no factor and `degree v` stays unchanged. A decreasing
remaining-multiplicity weight supplies the proof; gcd subloops separately
use semantic degree descent. Do not claim strict degree descent of `v` on
every iteration. Positive characteristic is outside this contract.

An optional result replay verifies product, multiplicities, scalar, degrees,
squarefreeness and pairwise gcd witnesses. Product equality alone cannot
certify multiplicities or completeness. False identities are rejected; ordinary
Yun arithmetic does not return a certificate at each operation.

## Root isolation and termination

`roots (f : DensePoly (Value ctx))` returns a complete `RootSet`: `all` exactly for a
semantically zero polynomial, or a finite strictly increasing list of distinct
selected roots with positive multiplicities in `F`. Constants other than zero
give the empty finite list. `all` carries no finite multiplicities and must
never be converted silently to an empty list. A root entry carries its
extension context and embedding of the input coefficients. List comparisons
use compatible extensions; callers can request one common context.

Use exact degree/equality and Yun decomposition. Remove
zero roots by checked powers of `X`, remembering their multiplicity; zero is
emitted once. For each remaining squarefree factor `p`:

1. Try a finite list of strict dyadic root bounds. With `n=degree p`,
   try `B=2^j` for `1≤j≤2*(n+1)`. An optional total height estimator may
   supply one additional candidate. Check `B>1` and
   `|aᵢ| < (B-1)*|aₙ|` for every `i<n` using exact coefficient order.
   This strict Cauchy test avoids coefficient inversion solely for the bound.
   If no candidate passes, continue on `(-∞,+∞)`. Each comparison is total;
   no search for a finite Archimedean bound is required.
2. On a certified `(-B,B)`, use root counts for at most `2*(n+1)` bisection
   nodes as an internal fast-path policy. Keep count-one descriptors and
   retain every interval still containing multiple roots for fallback.
   A finite bound does not imply dyadic separation: `(X-ε)*(X-2ε)` has two
   roots within `(0,1)` which no rational dyadic cut between them separates.
3. If a split point is a root, emit it once, remove its linear factor with
   exact-division evidence from the active squarefree polynomial, and
   transport pending descriptors/counts to the deflated polynomial. The
   remaining open subinterval endpoints are then root-free. Previously
   emitted roots are excluded explicitly; their original multiplicities
   are retained. Never pass a root endpoint to the open Sturm query.
4. Run `SignDet.roots` with **all derivatives** on every unresolved
   interval, using the proved root-domain invariant to eliminate its `Option`
   guard. This applies regardless of whether a finite bound was obtained. With no
   bound, run it on the whole line. Complete BKR support and Thom injectivity
   give one descriptor per root without a rational separator.
5. Merge factor lists using certified joint descriptor comparison, restore
   zero and multiplicities, and certify order, disjointness and coverage.
   Pairwise coprimality prevents factor lists from sharing roots; a duplicate
   after certified decomposition indicates failed producer evidence.

These internal finite policies may be replaced with equivalent deterministic
ones preserving coverage. They do not expose a user threshold and cannot
return a partial list. BKR completes every remaining interval, including the
whole line when a finite rational bound is unavailable. Root isolation may
extend the coefficient tower; it does not assert all roots lie in that field.

Termination is proved by tower induction for coefficient decisions, degree
for Euclidean loops, remaining multiplicity for Yun, the explicit finite
bound/bisection counts, and finite derivative/BKR recursion. It is not justified
by existence of roots alone. Transcendental coefficient sign uses the separate
ordered-fn accessibility proof from caller approximation laws. Algebraic
inversion calls only predecessor arithmetic plus sign determination over the
predecessor; it never invokes inverse recursively at its own level. Persistent
splits decrease the stored defining degree. These measures give executable total
operations without a global fuel search, `partial` or classical runtime choice.

## Public operations and validity

| Operation | Result |
| --- | --- |
| `Context.constant`, `Context.infinitesimal` | Staged extension from a lawful caller oracle registration or an infinitesimal, with predecessor embedding. Stage constraints are typed premises. |
| `Context.adjoin ctx d laws` | Algebraic context and generator for a validated squarefree selected-root descriptor and explicit `laws : Root.Laws d`. |
| `Value ctx` | Constructed quotient carrier with total exact field/order instances, executable equality and sign. |
| `Value.add`, `neg`, `mul`, `inv`, `sign`, `compare` | Ordinary total operations in the fixed context; `inv 0=0`. |
| `Value.inv?` | Convenience `Option` inverse, `none` exactly when the input is zero. |
| `Context.transport`, `enlarge` | New context and explicit embeddings/transports of the requested live DAG; compatible validated input gives a total result. |
| `Yun.decompose`, `roots` | Total decomposition or complete ordered root set; constructing output contexts additionally takes the erased root-law theorem for their descriptors. |
| `Sample.section`, `sector` | Validated section/sector samples with the finite-sign contract below. |
| `certify`, `Replay.check` | Result certificates for queries, BKR tables, selected roots, splitting, root lists or samples; Boolean validation of supplied finite data. |

Raw syntax readers and mathematical domain validators may return `Option`:
invalid descriptors, stage order or incompatible references are rejected. A
registry lookup retrieves the caller's already supplied oracle and proof
premises; a reader cannot decide convergence or relative transcendence.
The core reader requires the erased root-law theorem for every field where it
adjoins a root; the companion owns a wrapper supplying these theorems.
Validation of a descriptor alone does not create its law proof.
Compatibility checks concern the declared context embeddings, not arbitrary
equality of unrelated oracle descriptions. Total
field operations operate on the validated carrier and do not carry those
failures. Mathematical invalidity, malformed replay and an optional bounded
approximation attempt are distinct boundary concerns, not a replacement
coefficient-result framework. Exact field equality determines all polynomial
zero/degree decisions, including cancellation in different representations.

Certificates are produced for mathematical results needed by consumers.
Replay checks their polynomial identities, scales, endpoint and coefficient
sign facts, and table/selection equations. It does not rerun root isolation or
BKR production. Coefficient facts can be checked using the ordinary exact
operations or, at the tactic boundary, discharged by supplied kernel proofs
from child queries and caller approximation evidence. No arithmetic operation
must return a proof trace. Nested proof dependencies are child-before-parent;
finite DAG checks reject cycles, stale references and malformed encodings.

## Shared samples and base enlargement

The shared interface for [#10301](https://github.com/kim-em/hex-dev/issues/10301)
and [#10303](https://github.com/kim-em/hex-dev/issues/10303) is owned here.
It exposes opaque contexts and embeddings, ordered root lists with
multiplicities, root identity/comparison, polynomial sign at roots, and section
and sector samples with replay. Consumers use hex-sign-det descriptors through
this interface; hex-sign-det does not own tower enlargement or cell samples.

A section request gives a valid descriptor. A sector request gives ordered
adjacent boundaries `a<b` (possibly infinite), a finite polynomial family `Q`,
and evidence that no nonzero member of `Q` has a root in `(a,b)`. Zero
polynomials are allowed and have constant zero sign. Supply boundary order
and completeness of the boundary root list, not just two chosen roots.
The result includes the sample context, input embedding, strict membership
and signs of every member of `Q` at the sample. A midpoint in a common root
context handles bounded sectors; `a+1`, `b-1` and `0` handle rays and the whole
line. Dyadic samples are an optional Archimedean backend, not a generic
separation requirement.

An infinitesimal backend may use `r+ε` or `±1/ε`. After algebraics exist,
`Context.enlarge` rebuilds the infinitesimal base before those levels,
then transports each selected root in order into a compatible real closure
of the enlarged base. For the companion model, if `R` is the old algebraic
real closure of `B`, form the ordered rational-function field `R(δ)` with
`δ` infinitesimal relative to all of `R`, and apply the same ordered
real-closure existence theorem to obtain `R'`. Old interpretations embed
literally through `R → R(δ) → R'`; no unlisted uniqueness-of-real-closure
theorem is assumed. Since `R/B` is algebraic, `R'/B(δ)` is algebraic too.
Computationally reconstruct the staged base `B(δ)` and revalidate transported
root descriptors/certificates in predecessor order.

Enlargement preserves embeddings, root identity and all previous comparisons,
and returns a new context; appending an infinitesimal after an algebraic
level is invalid. Prove the stage order agrees with this stronger model:
every positive element of a finite ordered algebraic extension has a smaller
positive bound from the old base, so being infinitesimal relative to that
base also makes `δ` smaller than all those algebraic positives. Algebraicity
and preservation of order are hypotheses; the stage tag alone is no proof.

To export a sample as evidence about ordinary reals, require a separate
finite-sign realization contract. For a real-embedded coefficient field `K`,
real boundaries `a<b`, finite `Q ⊂ K[X]`, and a sample `s` in an ordered
extension preserving these data, `Realization.check` must establish

```text
∃ x : ℝ, a < x ∧ x < b ∧ ∀ q ∈ Q, sign(q.map(ι).eval(x)) = sign(q(s)).
```

Omit the corresponding inequality at an infinite endpoint. This theorem is
about a fixed finite family in its intended cell, not an embedding of a
non-Archimedean field into `ℝ`. For `r+ε`, replay the first nonzero Taylor
coefficient for each polynomial at `r` and obtain a common positive real
neighborhood; handle identically zero polynomials separately. For `±1/ε`,
leading signs and a common real root bound yield a real tail. Include the
finite boundary inequalities among the obligations. A real midpoint/ray sample
has direct membership evidence.

Nested algebraic infinitesimal samples require simultaneous realization of
all parameter equations, selected-root conditions, nonzero guards and signs
used by the consumer. `HexRealClosureMathlib` owns the following new local
specialization lemmas, consuming ordered-fn's lowest-coefficient sign rule
and sturm/sign-det correspondence; no abstract transfer or model-completeness
theorem is silently imported.

`Query.specialize`: let `F` embed as an ordered subfield of `ℝ`, let `ε` be
positive infinitesimal over `F`, and let `p,f,I` over `F(ε)` have a valid
finite Tarski replay `Γ`. Then there exists `η>0` such that, for every real
`0<t<η`, all denominators and domain guards in `Γ` remain valid on replacing
`ε` by `t`, and

```text
TaQ(f_t,p_t;I_t) = TaQ(f,p;I).
```

Include endpoint order/nonroot, squarefreeness witnesses, nonzero leading
coefficients and every scale sign in the finite obligations. Prove this by preserving the signs of the
finitely many nonzero rational functions in the replay, using their lowest
nonzero coefficients, and then applying shared query soundness. Exact zero
identities specialize identically; coefficient representation domains are
retained. The same argument on every query in a finite BKR replay preserves
its complete table, selected-root counts and Thom conditions.

`Sample.specialize` extends this to a finite selected-root tower and replay
DAG: after specializing its coefficient obligations, the next algebraic level
has a real root satisfying the prescribed descriptor and **all** required
signs, by the preserved joint table's positive count. Choose that root and
continue in predecessor order. For nested infinitesimals, first collect the
finite lower-level coefficient-sign obligations recursively. Realize those
obligations before choosing the next small positive parameter; the permitted
neighborhood may depend on all earlier choices. If `Φ` is the finite
conjunction of recorded equations, descriptor constraints, guards, cell
inequalities and consumer signs over the real-embedded base, the theorem is

```text
ValidTowerReplay Γ ∧ Realizes model Γ
  → ∃ (t₁,…,tₙ : ℝ) (α₁,…,αₖ : ℝ),
      (∀ i, 0<tᵢ) ∧ Φ(t₁,…,tₙ,α₁,…,αₖ).
```

The hypotheses include the shared interpretation/checker laws and compatible
ambient embeddings. No claim preserves *all* infinitesimal inequalities at
once; only the finitely recorded constraints are specialized. This induction
and joint-table correspondence are local proof deliverables, not consequences
of IVT alone. The exporter must construct this finite evidence, or use the ordinary-point
backend with its direct membership and sign proof. A symbolic sample alone
can never discharge a real existential.

For coverings, implement a checked exporter to the existing
[literal integer-polynomial and isolated-parameter format](hex-coverings.md#literal-samples-and-checked-export),
with coefficient-sign replay and correspondence. Direct denotation-preserving
export to that format applies to rational-base algebraic samples. A sample
with an actual transcendental or infinitesimal coordinate has no such export.
Replacing it by a real algebraic sample requires separate finite-sign
realization plus checks of that replacement's cell and formula obligations;
it is not an equality-preserving export. General real-constant contexts need
a richer downstream certificate interface. These contracts supply producers
and proofs, not CAD projection, coverings search or a tactic.

## Compatible towers and headline theorems

Fix the transcendental/infinitesimal base and an ambient ordered real closed
algebraic extension. Compatible finite algebraic towers denote subfields of
that ambient field, with the same base embedding and selected-root choices.
Any finite collection has a common finite extension obtained by adjoining
its finitely many generators in the ambient field. Quotient the union of
presentations by equality in compatible extensions. Prove coherence of
transport and executable equality across these presentations.

Every union element is algebraic over the fixed base. A positive element's
square root and a root of any odd-degree polynomial over the union belong to
a further finite tower: the finitely many coefficients first lie in a common
tower, and the required ambient root is algebraic over it. Thus the union is
real closed and algebraic over the base. A single finite tower need not be
real closed. Enlarging the infinitesimal base changes this fixed-base union
and requires the explicit embeddings above.

Required theorem shapes, with the semantic parameters and coefficient laws above:

| Planned statement | Hypotheses and conclusion |
| --- | --- |
| `Element.eval_add`, `eval_mul`, `sign_sound` | Executable arithmetic/sign agrees with selected-root interpretation for every valid operand. |
| `Element.eq_iff` | Executable zero sign of `a-b` iff denotations agree; lifted equality iff equality in `Value ctx`. |
| `Element.inv_sound` | Selected squarefree root and nonzero `q(α)` give `eval(inv q)*eval(q)=1`; total inversion maps zero to zero. |
| `Context.transport_sound` | Refinement/enlargement preserves interpretations, selected roots, order and compositional transport for all live handles. |
| `Yun.decompose_sound` | Exact zero case or the stated product, unit, degree, squarefree and coprime properties. |
| `roots_sound` | `all` iff `F=0`; finite results are strictly increasing, contain exactly all real roots in `R` and carry each root's exact positive multiplicity. |
| `terminates` | The explicit recursive measures justify the total algorithms on lawful fields; no finite-bound or rational-separation hypothesis is needed. |
| `Replay.check_sound`, `checks` | Accepted result literals imply their claims; certificates produced for valid results pass the checker under the corresponding coefficient-fact proofs. |
| `Query.specialize`, `Sample.specialize` | Finite replay signs/guards specialize at small positive real parameters; joint tables realize recorded nested constraints. |
| `Sample.realize` | Finite-sign evidence proves the ordinary-real existential, including parameter realization where needed. |
| `Value.field`, `Value.ordered`, `Union.realClosed` | Under `Root.Laws` at each selected-root level, quotient descent and executable equality give core field/order laws. The companion supplies those premises, Mathlib instances and real-closedness of the compatible algebraic union. |
| `Trivial.compare_eq`, `Trivial.roots_eq` | Rational-base comparison, arithmetic, `all`, sorted roots and multiplicities agree with the independent real-algebraic path. |

## Imported foundations and local correspondence

Use the [family ownership table and pinned audit](../future-work.md#proof-ownership-and-public-surface)
at Mathlib revision `1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`.
No planned foundational contract is an available theorem merely because it
has a name in a SPEC.

| Owner | Imported or locally proved obligation |
| --- | --- |
| Tau Ceti, consumed by this companion | **Additional requested foundation:** every linearly ordered field `K` has an ordered real closed field `R` and an order-preserving field embedding `ι : K →+* R`, with `R` algebraic over `ι(K)`. Existence is missing on the pin and is explicit work alongside [#10300](https://github.com/kim-em/hex-dev/issues/10300). |
| Tau Ceti through real-roots/sturm companions | Polynomial IVT and Rolle; signed-remainder/Cauchy-index identity with common factors and infinite endpoints. Consume the shared kernel's soundness; do not reprove a second Sturm–Tarski foundation here. |
| Tau Ceti through sign-det companion | Thom injectivity/order, sign-count moment identity and correctness of support-preserving BKR reduction. Consume complete descriptor and sign-table correspondence. |
| hex-ordered-fn-mathlib | Real evaluation under relative transcendence, sign soundness/progress conditional on caller approximation laws, Hahn-series infinitesimal embedding and ordered-field laws. An integer-exponent Hahn field is not real closed. |
| hex-real-roots-mathlib | Reuse the implemented `Real.instIsRealClosed` from `HexRealRootsMathlib.RealClosed`; the shared companion supplies the instance missing from the pinned Mathlib. |
| hex-real-algebraic-mathlib | Existing rational-base real closed carrier; compose its arithmetic/order/root correspondence for the trivial path. |
| hex-real-closure-mathlib | Prove Yun correspondence, selected-root quotient and executable descent/equality, splitting and context transport, termination laws, ordered complete root lists, `Query.specialize`/`Sample.specialize` and finite-sign realization, and compatible-union real-closedness relative to the supplied ambient model. |

Computational proofs cover literal identities, finite control flow and
degree invariants, checker composition and conditional laws. Companion proofs
connect these to mathematical roots and discharge the semantic law packages.
No unproved core theorem is imported across the boundary as a proof; follow
[the proof-debt rule](../design-principles.md#proof-debt-does-not-cross-the-layer-boundary).
No axiom or new trusted external arithmetic/oracle boundary is introduced.

## Exploration and downstream integration

Provide staged exploration with caller-registered computable real constants,
infinitesimals, arithmetic, checked inversion, comparison and polynomial
`roots`. A constant registration supplies its approximation procedure and
replayable soundness evidence; total operations additionally require the
specified effective progress and relative-transcendence laws. No particular
analytic constant or approximation algorithm is built in.

For example, a caller supplying certified procedures for `π,e` may make
bounded sign attempts on registered expressions and certify `π<4` and `e>2`.
With the total-field hypotheses they may adjoin `ε` and selected positive
roots of `X²-ε`. These named-constant demonstrations are conditional examples,
not provider implementation or proof obligations of this family. The
infinitesimal examples also run over `ℚ`: demonstrate `0<ε<sqrt(ε)<1`,
`1/ε>n` for fixed integers, and a second infinitesimal smaller than every fixed
positive power of the first. Adding it after selecting a square root exercises
enlargement and root transport. Examples are planned `#eval` demonstrations,
not nonstandard-analysis tactics.

Total modes for `π` and `e` are explicitly conditional: the pin lacks their
individual transcendence theorems, and even both separately would not justify
transcendence of the second over the field generated by the first. Bounded
certified signs need no algebraic-independence assumption. Retain all original
divisor guards in optional expression-level attempts; an unresolved relation
returns no sign. These attempts cannot be used as a tower coefficient field.
The caller supplies the new constant approximation and laws; ordered-fn derives
the coefficient approximation procedure for subsequent real extensions. The
family proves composition from those contracts; it does not implement or prove
analytic approximation providers. An adapter to an interval library would be
separate future work and is not a dependency or deliverable here.

`Repr` emits reconstructible constructor syntax with the context DAG, named
constant provider/version registrations, infinitesimal order, polynomial
coefficients, root intervals and indexed Thom signs. The checked reader binds
all dependencies and rejects changed registrations or stale references.
`repr_roundtrip` says that re-reading emitted data with the same caller-supplied
registry succeeds and preserves denotation/root identity; caches
need not match. Decimal display is not a reconstruction format. A conditional
total mode reuses its law package rather than serializing proofs of
transcendence as runtime data.

For a trivial transcendental/infinitesimal base, delegate supported work to
`RealAlgebraicNumber.compare` (which uses `AlgebraicNumber.realCompare`) and
`RealAlgebraicPoly.roots`. If the generic route is chosen, prove
`Trivial.compare_eq`/`roots_eq` and differential conformance after conversion.
Preserve `RealRootSet.all`; the existing `ZPoly.realAlgebraicRoots` convenience
array has an empty-array convention for zero and is not the complete API to
copy. Do not impose generic tower overhead or new imports on that library.

Downstream `rcf` integration still needs real-valued coefficient reification,
registered constant/domain proofs, nested coefficient-sign replay, kernel
quotation and the finite-sign realization exporter. Its current integer-only
replay cannot consume these contexts unchanged. It may certify statements
such as `∀ x : ℝ, x² > π-4` when the caller supplies a certified `π<4`
source through its constant registration; no completeness covers unresolved
constant relations. Emit only evidence required by the final real statement.
This SPEC implements neither a tactic nor multivariate CAD/coverings.

## Conformance and Phase-4 evidence

Core conformance exercises algorithms at coefficient fields whose instances
are available in core, including base-field query/descriptor computations.
Closed `Value ctx` applications, nested root isolation and checked context
reading require the companion's root-law witnesses. Their executable
instantiation and conformance entry points belong to the companion and reuse
the same core algorithms; they do not introduce another arithmetic backend.
The public `Context` deliberately packages a lawful field from its first
algebraic level. Law-free single-root descriptor computations remain available
through hex-sign-det without pretending to construct that field.

Closed algebraic-tower fixtures over infinitesimal bases, including `tower8`,
transported/nested roots and field-valued exploration, are blocked on the
actual ordered-real-closure existence theorem as well as sign-determination
correctness. This is a proof delivery gate, not a new hypothesis to postulate
in tests. Raw descriptor computations over `ℚ(ε)` can run independently once
the predecessor ordered-field instances exist. Keep every required fixture;
do not declare family conformance complete while the gated cases are missing.

Follow [testing](../testing.md) and [benchmarking](../benchmarking.md).
Pin Z3 and record commit/version, generator command, exact input and output,
context/order and fixture provenance for its `MkInfinitesimal`,
`MkRoots` and comparisons. Z3 `Pi`/`E` comparisons are optional cases enabled
only when the caller supplies matching certified approximation procedures;
their presence in the external API does not require built-in Hex providers. Use
the
[Z3 RCF API](https://github.com/Z3Prover/z3/blob/master/src/api/python/z3/z3rcf.py)
as a differential oracle, not a runtime dependency or proof of transcendence.
Where its root API omits multiplicities, recover them independently from the
exact input or rational factorization; do not attribute an unreturned count
to Z3. Rational cases cross-check python-flint and Hex's real-algebraic path.
Compare exact signs, arithmetic identities, ordered selected roots and
multiplicities, never just decimal strings.

Required fixtures include:

- Zero, nonzero constants, semantic trailing zeros, `X^m`, repeated factors
  with gaps in multiplicities, and mixed zero/nonzero roots. Exercise Yun
  iterations whose gcd is constant and emit nothing, and exact cancellation across different polynomial representatives.
- The corrected [paper](https://www.cl.cam.ac.uk/~gp351/infinitesimals.pdf)
  example `(εX²-1)(εX³-1)=ε²X⁵-εX³-εX²+1`: roots in order
  `-ε^(-1/2), ε^(-1/3), ε^(-1/2)`. The two positive roots share `(0,+∞)`
  but have negative and positive third-derivative signs respectively.
- Infinite roots relative to the rationals, finite bounds with inseparable
  dyadic root pairs, failed bound attempts, roots at split points and a policy omitting
  bisection with complete fallback. Vary internal policies and require the
  same complete result.
- Reducible `p=(X-1)(X+1)` at `α=1`: semantic zero of `X-1`, checked inverse
  failure for it, and successful inverse of `X+1` after replacing `p` by
  `X-1`. Also split `p=(X²-2)(X²-3)` at `sqrt(2)` when inverting `X²-3`;
  the new derivative encoding has different length. Retain downstream roots,
  elements, signs and guards; reject stale certificates at every level.
- Non-monic clean `2X²-1`, representatives above its degree, negative leading
  coefficients/scales, clean versus eager arithmetic, recomputed versus
  persistent splitting and equality across different presentations.
- Two/three infinitesimal levels, base enlargement after algebraics, all
  section/sector types, non-adjacent boundary rejection and finite-sign
  realization at real points. Reject an infinitesimal literal offered as a
  real witness, incomplete parameter transport or a missing sign constraint.
- Rejection of forged constant evidence, missing expression divisor guards,
  malformed DAGs, false Bézout/Yun certificates and a sign table omitting a
  realizable condition. Optional bounded sign attempts remain outside field
  arithmetic; nonconvergent oracles cannot supply its law premises.
- Reconstructible `Repr`, changed oracle registration, partial descriptors,
  differing polynomials naming the same root, and rational trivial-route
  agreement including `all` and multiplicities.

Reproduce the family's `basic.py`, degree-15 MetiTarski and `y³+x³+1` cases
from `nlsat.py`, `tower8.py`, and Rioboo/Strzeboński workloads with recorded
provenance. A case using a real constant records the caller-supplied
approximation procedure and its law assumptions; when that input is unavailable,
record the case as unsupported rather than adding an analytic provider or
silently substituting a different constant. Cases without an external analogue need direct literal checks
and explicit non-coverage records. Use small `decide` checks only for
kernel-reducible operations; total transcendental sign may use opaque
accessibility evidence and cannot rely on that route. Use ordinary theorem
proofs from finite sign evidence for such cases, alongside `#guard` checks
and compiled fixture campaigns. Evaluation checks are not kernel proofs;
`native_decide` is banned. Future oracle
registration extends the existing single CI job, not new workflows.

Phase 4 must report `tower8` isolation and an adjacent clean-versus-eager
normalization ablation with identical inputs and semantic outcomes. Record
coefficient bit sizes and stored degrees, scalar inversions, gcd/xgcd work,
splits/transports, bound attempts, bisection nodes, BKR query/matrix work,
coefficient-sign calls and evidence size. Separate Yun, query production,
BKR solving, coefficient signs, isolation, serialization and kernel replay.
Measure trivial-path delegation against the existing real-algebraic backend
and the midpoint/dyadic versus infinitesimal sample alternatives for #10301.

For a factor of degree `n`, bound attempts and bisection nodes are linear in
`n` under the stated policy. Fallback uses at most a linear number of pending
intervals, each with `n` derivatives; charge the full hex-sign-det bounds per
interval, plus joint comparisons and transport. This bounds outer algebraic
work, not coefficient precision or total bit cost. If a level needs `bℓ`
child certificates, report the unshared recurrence
`Sℓ ≤ Sℓ,local + bℓ*max Sℓ₋₁` and the analogous replay-time recurrence.
Certificates are finite DAGs with earlier-node references only and strictly
lower-level coefficient dependencies. Shared checking charges each distinct
node plus every edge, binding exact contexts and literals; unshared checking
charges every occurrence. Replay checks supplied result evidence without fresh root isolation or BKR
production. Tactic clients can provide coefficient-sign proofs to avoid fresh
approximation search. Measure bytes, nodes, arithmetic and operand sizes, and
reject cycles/forward references before expansion.

Keep bench imports Mathlib-free and replay measurements separate. Use
lean-bench's fixed trial-major schedule, automatic CPU selection where
supported, adjacent alternating `AB`/`BA` comparisons, and retain every
completed sample with host activity as context. Allow at most one unchanged
rerun after an inconclusive result and supply one representative attribution
profile. Historical paper timings are not host-independent targets or CI
budgets. No quiet-core preflight or retry-until-clean rule is introduced.
