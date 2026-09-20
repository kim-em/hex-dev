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
`HexSignDet`, `HexOrderedFn` and `HexRealAlgebraic`. Rational-function and
interval infrastructure is supplied below these inputs. The computational
library and all its imports remain Mathlib-free. `HexRealClosureMathlib`
imports it, the companions of the inputs it uses, Mathlib and the explicitly
listed Tau Ceti foundations. Mathlib instances and analytic correspondence
live there. Keep the family's four computational libraries and four companions;
no existing input gains an import of this family. CAD, coverings and `rcf`
are downstream clients, never dependencies.

The division of responsibility is:

| Input/owner | Contract used here |
| --- | --- |
| [hex-poly](../../HexPoly/SPEC/hex-poly.md#fallible-coefficient-operations) | Planned fallible coefficient records, semantic polynomial degree, positive pseudo-division, gcd/xgcd and exact division. Existing `HexPoly.Field` has total field routines, not this adapter or generic Yun decomposition. |
| [hex-sturm](hex-sturm.md) | Ordered-field Tarski queries, root counts and coefficient evidence, using the shared signed-remainder kernel in hex-real-roots. |
| [hex-sign-det](hex-sign-det.md) | Complete BKR tables and single-polynomial descriptors: validation, root identity/order, sign at a root and re-encoding. |
| [hex-ordered-fn](hex-ordered-fn.md) | Guarded fractions, certified real-constant enclosures, infinitesimal orders and proof-founded total coefficient search. |
| [hex-real-algebraic](hex-real-algebraic.md) | Independent rational-base fast path; exact comparison and sorted roots with multiplicities. |
| This library | Generic characteristic-zero Yun decomposition, staged contexts, tower coefficient-record adapters, selected-root arithmetic, splitting/transport, root isolation, tower sampling and exploration. |

The [number-field SPEC](../../HexNumberField/SPEC/hex-number-field.md)
provides precedent for lazy selected roots, but its fixed irreducible,
complex-embedded fields are not the generic tower representation.
[`SimpleRealRoot`](../../HexRealRoots/SimpleRealRoot.lean) uses integer
polynomials and a rational separation bound; interval overlap there cannot
be transplanted to infinitesimal towers.

## Semantic parameters and executable records

Fix an ordered field `K` of characteristic zero and an order-preserving field
embedding `ι : K →+* R` into an ordered real closed field. In the companion,
`R` has `[Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]`;
`K` has the first three structures. A coefficient law package interprets valid
raw representatives in `K`. All polynomials in semantic statements are mapped
coefficientwise through this interpretation and `ι`. Ambient existence is an
explicit foundational obligation, not a runtime oracle or an instance assumed
available on the pin.

Use `Hex.PolyOps.CoeffOps`, `FieldOps`, `Limits`, `Budget`, `Result` and
`CheckResult`. Polynomial storage over raw coefficients is a finite array
with checked semantic degree, separate from `DensePoly C`. Structural zeros,
array length and equality of syntax do not decide semantic degree or equality.
Every arithmetic/sign/zero/inversion callback terminates with evidence or a
failure; one parent budget pays for nested calls, validation and replay.

A total semantic carrier may use
`[Lean.Grind.Field K] [LE K] [LT K] [Std.IsLinearOrder K]`
`[Std.LawfulOrderLT K] [Lean.Grind.OrderedRing K] [DecidableEq K]`
`[DecidableLE K] [DecidableLT K]`, exactly as in hex-sturm. An ordered ring
alone does not supply a total order. No such instances are installed on raw
representatives or on bounded approximation callbacks. Successful-result
soundness needs interpretation and evidence laws; eventual success additionally
needs progress of every coefficient operation and evidence producer.

This library provides `Context.coeffOps` and `Context.fieldOps` for valid
`Element ctx` representatives, together with validity, interpretation,
arithmetic and evidence/replay law packages; progress laws require the stated
coefficient-completeness hypotheses. The `sign` callback is
`Element.signWith`; `zeroTest` tests its certified zero case, and checked `inv`
is `Element.invWith`. Arithmetic and validation recurse over predecessor
levels; evidence dependencies strictly decrease level when a sign computation
calls its coefficients. `ExactOps` is an optional adapter obtained by checked
nonzero inversion and multiplication. Supply the complete record for
`Value ctx` only after executable quotient descent and total-search laws are
proved; it succeeds on valid operation inputs, including the nonzero premise
for checked inversion. Callback results keep one fixed public context: temporary splits can
remain local, while persistent splits require the explicit transport below.
These records instantiate hex-sturm and hex-sign-det without either importing
the tower implementation.

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
Use `SignDet.compareWith` and its common squarefree-product re-encoding.

An `Element ctx` stores a polynomial representative `q(α)` at the top
algebraic level, recursively over predecessor representatives. No bound
`degree q < degree p` is a representation invariant. Embedded predecessor
elements are constant polynomials. Equality means equality of denotations,
computed by the certified zero sign of the difference at the selected root.
In particular, a reducible `K[X]/(p)` is generally not a field and is not the
public carrier. For `p=(X-1)(X+1)` selecting `α=1`, `X-1` denotes zero while
its remainder modulo `p` is nonzero.

For total coefficients and proved search laws, define `Value ctx` as the
quotient of valid representatives by selected-root equality. Its semantic
image is `K(α)` at a single level. Prove the relation is an equivalence,
operations respect it, and the executable sign/equality test descends and
decides quotient equality. Use quotient lifting of the actual executable
operations, not classical selection of representatives or a noncomputable
inverse. The computational law package supplies the erased premises for core
field/order instances; the companion proves it and transports Mathlib
instances along the interpretation. Inversion of zero in this total field is
zero. The raw checked nonzero inverse instead rejects a certified zero.

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
Local gcd/field computations may invert coefficients when required; record
those operations and do not replace persistent clean definitions with their
monic versions. Clear denominators for root/query work with nonvanishing and
sign evidence. A root-set-preserving negative scalar still changes query or
derivative signs and needs the corresponding correction. Positive-scaled
pseudo-remainders preserve signs at roots, not literal values; arithmetic
transport must carry the full identity including the scale.

For a checked inverse of `q(α)`:

1. Certify `q(α) ≠ 0` by sign determination. An unresolved sign exhausts; a
   certified zero is invalid for this operation, even if some other root of
   `p` makes `q` nonzero.
2. Compute `g=gcd(p,q)` with divisibility and gcd evidence. Since `g | q`,
   `g(α) ≠ 0`. If `degree g>0`, set `h=p/g` by checked exact division, retain
   `p=g*h`, and prove `h(α)=0`, `h` squarefree and `gcd(h,q)=1`. Squarefreeness
   of `p` is essential to the last claim. With constant gcd keep `h=p`.
3. Re-encode the same root for `h` using **derivatives of h** via
   `SignDet.reencodeWith`. Retain the old descriptor and joint selection
   evidence; copying the old Thom vector is invalid. A root-free old interval
   remains root-free for the factor, or the whole line can be used.
4. Transport every live element, coefficient, descriptor and downstream
   algebraic level, including cached signs and domain guards, in predecessor
   order. Prove embeddings commute with interpretation and preserve root
   identity, equality and order. Changed literals require checked evidence
   transport or recomputation. Commit a persistent context update only after
   this entire operation succeeds; failure leaves the old context usable.
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

`Yun.decomposeWith ops limits f` is new infrastructure owned here. The generic
`HexPoly.Field` routines supply neither this routine nor fallible semantic
coefficient equality. Use the shared fallible gcd, derivative and exact-division
adapters; specialize to existing total `DensePoly` routines only with lawful
total coefficient instances and correspondence.

Successful output is either `zero`, exactly when `F=0`, or a nonzero scalar
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
`v=v/z`, `w=t/z`, `i=i+1`. All divisions are exact with certificates. Units
are accumulated into `u`; using the monic `z` convention gives `u=lc(F)`.
The invariant identifies the remaining factors of multiplicity at least `i`;
in characteristic zero the loop finishes within `degree F` iterations, even
when an iteration emits no factor and `degree v` stays unchanged. A decreasing
remaining-multiplicity weight supplies the proof; gcd subloops separately
use semantic degree descent. Do not claim strict degree descent of `v` on
every iteration. Positive characteristic is outside this contract.

The checker verifies product, multiplicities, scalar, degrees, squarefreeness
and pairwise gcd evidence. Product equality alone cannot certify multiplicities
or completeness. Valid raw input whose degree/zero tests exhaust has no
factorization result. False exact-division or gcd witnesses are rejected.

## Root isolation and termination

`rootsWith ctx limits f` returns a checked `RootSet`: `all` exactly for a
semantically zero polynomial, or a finite strictly increasing list of distinct
selected roots with positive multiplicities in `F`. Constants other than zero
give the empty finite list. `all` carries no finite multiplicities and must
never be converted silently to an empty list. A root entry carries its
extension context and embedding of the input coefficients. List comparisons
use compatible extensions; callers can request one common context.

Validate contexts and semantic degree, then use Yun decomposition. Remove
zero roots by checked powers of `X`, remembering their multiplicity; zero is
emitted once. For each remaining squarefree factor `p`:

1. Attempt a strict finite dyadic root bound using bounded work. With
   `n=degree p`, first allow one candidate from available certified coefficient
   enclosures/heights, then try `B=2^j` for `1≤j≤2*(n+1)`. Check `B>1` and
   `|aᵢ| < (B-1)*|aₙ|` for every `i<n`. This is the strict Cauchy inequality
   without coefficient inversion solely to try a bound. A data-derived
   candidate lets small-degree, large-height Archimedean inputs use bisection;
   its construction, including obtaining a lower bound on `|aₙ|`, is capped.
   Charge all attempts to a separate, capped slice of the parent's resources.
   If the bound cannot be certified in that slice,
   including unresolved coefficient signs or non-Archimedean coefficients,
   continue with `(-∞,+∞)`. Local bound-search exhaustion is inconclusive,
   not root-search failure; global exhaustion still propagates. No unbounded
   doubling or approximation loop is allowed here.
2. On a certified `(-B,B)`, use root counts and at most `2*(n+1)` bisection
   nodes as a fast path, with a capped bisection resource slice. Certify empty
   intervals or count-one descriptors; retain every unresolved interval.
   If a split-point zero test or child root count is undecided within that
   slice, retain the parent interval unresolved and do not use the unverified
   endpoint. Only exhaustion of the global budget fails the whole call.
   A finite bound does not imply dyadic separation: `(X-ε)*(X-2ε)` has two
   roots within `(0,1)` which no rational dyadic cut between them can separate.
3. If a split point is a root, emit it once, remove its linear factor with
   exact-division evidence from the active squarefree polynomial, and
   transport pending descriptors/counts to the deflated polynomial. The
   remaining open subinterval endpoints are then root-free. Previously
   emitted roots are excluded explicitly; their original multiplicities
   are retained. Never pass a root endpoint to the open Sturm query.
4. Run `SignDet.rootsWith` with **all derivatives** on every unresolved
   interval, regardless of whether a finite bound was obtained. With no
   bound, run it on the whole line. Complete BKR support and Thom injectivity
   give one descriptor per root without a rational separator.
5. Merge factor lists using certified joint descriptor comparison, restore
   zero and multiplicities, and certify order, disjointness and coverage.
   Pairwise coprimality prevents factor lists from sharing roots; a duplicate
   after certified decomposition indicates failed producer evidence.

These numerical policies may be replaced by other deterministic bounded
policies with the same fallback and coverage invariant. No accuracy threshold,
maximum refinement depth or caller preference can make a successful result
incomplete. A bounded call may exhaust, but cannot return a partial list as a
complete `RootSet`. An optional diagnostic prefix must have a separate type.
Isolation of roots of a polynomial over a finite tower may extend that tower;
it does not assert all roots already lie in the coefficient field.

Termination has separate measures: finite tower depth for coefficient
callbacks; semantic degree for Euclidean loops; remaining multiplicity for
Yun; capped bound attempts and bisection nodes; finite derivative/BKR recursion;
and literal size for replay. Total coefficient forms use structural finite
work and, when necessary, the accessibility-based search construction from
hex-ordered-fn with an erased `SearchLaws : Prop` package. Eventual success
under a cofinal schedule covers arithmetic, signs, context transport and
certificate production, not just outer fuel. It supplies accessibility of
successive exhausted attempts; no `partial`, classical choice of a runtime
fuel, or trusted opaque search is allowed.

## Public operations and failures

The following bounded operation shapes all return evidence and residual
budget through the common `PolyOps.Result`:

| Operation | Successful result |
| --- | --- |
| `Context.constantWith`, `Context.infinitesimalWith` | Staged extension with the ordered-fn oracle registration or infinitesimal order contract and coefficient embedding. |
| `Context.adjoinWith ctx d` | Algebraic context and generator from a valid squarefree selected-root descriptor. |
| `Context.coeffOps`, `fieldOps` | Bounded certificate-producing tower coefficient callbacks and their law packages; total record specialization on `Value ctx` requires proved descent/progress. |
| `Element.addWith`, `negWith`, `mulWith` | Polynomial representatives, with arithmetic/domain evidence; embed compatible operands first. |
| `Element.invWith` | Checked inverse of a certified nonzero element, with split and transport evidence. |
| `Element.signWith`, `compareWith` | Certified sign or order at the selected roots, including exact semantic equality. |
| `Context.transportWith`, `enlargeWith` | New context, explicit embeddings and transports for every requested live handle. |
| `Yun.decomposeWith`, `rootsWith` | Decomposition or complete ordered root set under the contracts above. |
| `Sample.sectionWith`, `sectorWith` | Selected section or sector sample and the finite-sign evidence described below. |
| `Replay.checkWith` | Accepted, rejected or exhausted replay; acceptance alone makes Boolean `check` true. |

Use `invalid` for a certified domain/precondition violation (including zero
checked inversion, invalid stage, invalid descriptor or incompatible context),
`exhausted` for insufficient work or an unresolved coefficient decision, and
`rejected` for false/malformed evidence or an internal producer invariant
failure. Invalid input may exhaust during validation, but must not succeed.
Wrong certificate context/version is rejected; a raw stale handle is invalid
unless explicit transport is requested. `ok` never hides a failed domain
check, even for a zero numerator or constant polynomial.

The ordered-fn frontend has its own `domain`/`invalid` diagnostics. Its adapter
maps a certified `domain` failure to shared `invalid`, malformed or failed
replay to shared `rejected`, and exhaustion unchanged, retaining the original
reason and evidence. Checked invalid context/stage failures remain `invalid`.
This translation is explicit; downstream callers do not mistake unknown
signs or authentication failures for mathematical zero.

Every bounded path, including malformed inputs and zero fuel, terminates.
Validate references and allocation bounds before traversing or expanding
untrusted data. The total API is on validated semantic values with proved
progress laws; it supplies total field inverse with `inv 0=0`, exact compare,
and complete roots. Raw constructors keep their failure results. Field division
at zero and checked division are distinct entry points.

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
`Context.enlargeWith` rebuilds the infinitesimal base before those levels,
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
of IVT alone. If the required evidence is unavailable, bounded export exhausts
or the producer chooses the ordinary-point backend. A symbolic sample alone
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

Required theorem shapes, with the semantic parameters and adapter laws above:

| Planned statement | Hypotheses and conclusion |
| --- | --- |
| `Element.eval_add`, `eval_mul`, `sign_sound` | Valid operands and successful bounded operations imply arithmetic/sign agreement with interpretation. No oracle convergence is needed for success soundness. |
| `Element.eq_iff` | Under total sign/equality laws, the executable zero sign of `a-b` iff their denotations agree; lifted equality iff equality in `Value ctx`. |
| `Element.inv_sound` | Valid selected squarefree root, certified `q(α)≠0`, and accepted split/Bézout evidence imply `eval(inv q)*eval(q)=1`. |
| `Context.transport_sound` | Accepted refinement/enlargement and valid live handles imply commuting interpretations, preserved root identity/order and compositional transport. |
| `Yun.decompose_sound` | Accepted result has the exact zero case or product, unit, degree, squarefree and coprime properties stated above, in characteristic zero. |
| `roots_sound` | Successful `all` iff `F=0`; successful finite result has strictly increasing roots, each root's exact positive multiplicity, and contains every real root in the supplied `R`. For nonzero `F`, membership iff `F(x)=0`. |
| `roots_isSome` | Valid inputs, complete lawful coefficients/replay, and a cofinal resource schedule imply eventual success at every larger envelope. Total forms return the complete result with no bound/separation hypothesis. |
| `Replay.check_sound`, `checks` | Accepted literals imply their claimed semantic facts; a successful producer yields a certificate accepted at a computable sufficient replay envelope, under child replay laws. |
| `Query.specialize`, `Sample.specialize` | Finite replay signs and guards specialize at sufficiently small positive real parameters; joint table counts realize the recorded nested algebraic constraints. |
| `Sample.realize` | Accepted finite-sign realization evidence implies the ordinary-real existential above, including parameter realization where needed. |
| `Value.field`, `Value.ordered`, `Union.realClosed` | Quotient descent/equality and progress laws give executable core field/order laws; compatible algebraic union has positive square roots and odd-degree roots. Mathlib correspondence/instances belong in the companion. |
| `Trivial.compare_eq`, `Trivial.roots_eq` | Interpretation into `RealAlgebraicNumber` preserves comparison, arithmetic, `all`, sorted finite roots and multiplicities on the rational-base fragment. |

Root completeness here is the postcondition of **successful** bounded output;
it does not assert every bounded call succeeds. Prove termination, successful
soundness, invalid-result soundness and eventual success separately.

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
| hex-ordered-fn-mathlib | Real evaluation under relative transcendence, certified-enclosure sign soundness/progress, Hahn-series infinitesimal embedding and ordered-field laws. An integer-exponent Hahn field is not real closed. |
| hex-real-roots-mathlib | Prove `IsRealClosed ℝ` from pinned real square-root and polynomial IVT/order results. The pin supplies no such instance. |
| hex-real-algebraic-mathlib | Existing rational-base real closed carrier; compose its arithmetic/order/root correspondence for the trivial path. |
| hex-real-closure-mathlib | Prove Yun correspondence, selected-root quotient and executable descent/equality, splitting and context transport, termination laws, ordered complete root lists, `Query.specialize`/`Sample.specialize` and finite-sign realization, and compatible-union real-closedness relative to the supplied ambient model. |

Computational proofs cover literal identities, finite control flow, budget and
degree invariants, checker composition and conditional laws. Companion proofs
connect these to mathematical roots and discharge the semantic law packages.
No unproved core theorem is imported across the boundary as a proof; follow
[the proof-debt rule](../design-principles.md#proof-debt-does-not-cross-the-layer-boundary).
No axiom or new trusted external arithmetic/oracle boundary is introduced.

## Exploration and downstream integration

Provide staged exploration with registered `π`, `e`, infinitesimals,
arithmetic, checked inversion, comparison and polynomial `roots`. For example,
build a bounded real-constant context containing `π,e`, certify `π<4` and
`e>2` from enclosures, then adjoin `ε` and selected positive roots of
`X²-ε`. Demonstrate `0<ε<sqrt(ε)<1`, `1/ε>n` for fixed integers, and a second
infinitesimal smaller than every fixed positive power of the first. Adding
that second infinitesimal after selecting a square root exercises enlargement
and root transport. Examples are planned `#eval` demonstrations, not
nonstandard-analysis tactics.

Total modes for `π` and `e` are explicitly conditional: the pin lacks their
individual transcendence theorems, and even both separately would not justify
transcendence of the second over the field generated by the first. Bounded
certified signs need no algebraic-independence assumption. Retain all original
divisor guards through cancellation; unresolved relations exhaust rather than
becoming equality. Named constants and predecessor coefficients both require
certified enclosures and progress for a total adapter.

`Repr` emits reconstructible constructor syntax with the context DAG, named
constant provider/version registrations, infinitesimal order, polynomial
coefficients, root intervals and indexed Thom signs. The checked reader binds
all dependencies and rejects changed registrations or stale references.
`repr_roundtrip` says that re-reading emitted data with the same registry and
sufficient resources succeeds and preserves denotation/root identity; caches
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
such as `∀ x : ℝ, x² > π-4` using `π<4`; no completeness covers unresolved
constant relations. Emit only evidence required by the final real statement.
This SPEC implements neither a tactic nor multivariate CAD/coverings.

## Conformance and Phase-4 evidence

Follow [testing](../testing.md) and [benchmarking](../benchmarking.md).
Pin Z3 and record commit/version, generator command, exact input and output,
context/order, budgets and fixture provenance for its `MkInfinitesimal`, `Pi`,
`E`, `MkRoots` and comparisons. Use the
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
  iterations whose gcd is constant and emit nothing, and failed coefficient tests.
- The corrected [paper](https://www.cl.cam.ac.uk/~gp351/infinitesimals.pdf)
  example `(εX²-1)(εX³-1)=ε²X⁵-εX³-εX²+1`: roots in order
  `-ε^(-1/2), ε^(-1/3), ε^(-1/2)`. The two positive roots share `(0,+∞)`
  but have negative and positive third-derivative signs respectively.
- Infinite roots relative to the rationals, finite bounds with inseparable
  dyadic root pairs, failed bound attempts, roots at split points and zero
  bisection budget with complete fallback. Vary work policies and require the
  same complete result on success.
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
- Exhausted, nonconvergent or forged constant enclosures, missing original
  divisor guards, unresolved equality, zero work at nested calls, malformed
  DAGs, false Bézout/Yun certificates and a sign table omitting a realizable
  condition. Test producer and replay failures separately.
- Reconstructible `Repr`, changed oracle registration, partial descriptors,
  differing polynomials naming the same root, and rational trivial-route
  agreement including `all` and multiplicities.

Reproduce the family's `basic.py`, degree-15 MetiTarski and `y³+x³+1` cases
from `nlsat.py`, `tower8.py`, and Rioboo/Strzeboński workloads with recorded
provenance. Cases without an external analogue need direct literal checks
and explicit non-coverage records. Use small `decide`/`#guard` checks and
compiled fixture campaigns; `native_decide` is banned. Future oracle
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
charges every occurrence. Replay checks supplied evidence without fresh root
isolation or approximation search. Budget bytes, nodes, arithmetic and operand
sizes globally, and reject cycles/forward references before expansion.

Keep bench imports Mathlib-free and replay measurements separate. Use
lean-bench's fixed trial-major schedule, automatic CPU selection where
supported, adjacent alternating `AB`/`BA` comparisons, and retain every
completed sample with host activity as context. Allow at most one unchanged
rerun after an inconclusive result and supply one representative attribution
profile. Historical paper timings are not host-independent targets or CI
budgets. No quiet-core preflight or retry-until-clean rule is introduced.
