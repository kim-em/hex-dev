# hex-sturm-mathlib

Correspondence and literal replay soundness for the ordered-field
Sturm–Tarski frontend in [hex-sturm](../../HexSturm/SPEC/hex-sturm.md).

## Status, scope and dependencies

`HexSturmMathlib/Domain.lean` proves the exact semantic domain equivalence
for `query` and `prepare`, exact prepared input bindings, validity of every
prepared domain, finite/infinite endpoint guards, and ordinary/prepared
certificate acceptance. These results apply to noninjective coefficient
interpretations without field or order instances on representation storage.
`HexSturmMathlib/Rational.lean` proves whole-`Option` equality of the rational and
integer/dyadic queries on finite ordered dyadic intervals after positive
denominator clearing. The domain proof
covers zero/repeated-root heads and finite endpoint roots for ordered dyadic
intervals. The value proof compares arbitrary accepted remainder chains by
positive scaling, including singleton chains and nonconstant terminal gcds;
it does not require a root-sum theorem. `check_rat_value` proves equality of
values for arbitrary accepted certificates on the corresponding inputs.
Ordinary-kernel tests instantiate the generic theorems on canonical rationals and noncanonical
representatives and inspects their axioms.

`Reduced.lean` proves whole-`Option` equality of `queryReduced` and `query`,
and equality of reduced and ordinary prepared values. It reduces the query
modulo the head using the existing remainder-only division; the shared
`Tarski.rootSum_mod` theorem proves that evaluations at head roots are
unchanged. In addition to the ordinary query interpretation hypotheses,
coefficient division must preserve field division. No new root representation
or Tarski computation is introduced.

`Compare.lean` proves `check_congr` for arbitrary accepted field certificates
and `query_congr` for the whole producer `Option`, including invalid domains
and infinities. Both allow positive scaling of the polynomial inputs and
noninjective interpretations into a common ordered field.
`HexSturm.Transport` owns executable denominator clearing and integer embedding.
`DenominatorClearing.lean` proves integer-checker acceptance of a supplied
rational certificate cleared at its bound finite dyadic interval.
`IntCast.lean` proves acceptance of integer-to-rational embedding, including
infinite endpoints. Both preserve the full literal context and accepted value;
the target input bindings are the cleared or embedded polynomials. Clearing
recomputes exact signs and variations at the supplied interval; its acceptance
theorem requires the original certificate to bind that interval. Neither
translation calls polynomial division, gcd, or a chain producer.

The ordinary `HexSturmMathlib` target exposes proved root-sum/replay semantics,
root counts, nonnegativity and degree bounds, and singleton-root signs through
the shared hex-real-roots-mathlib foundation. The theorem for arbitrary
accepted certificates has no producer-success hypothesis. All these results
use only Lean's standard logical axioms. Independent scaffolding reviews are
retained in `status/`; ordinary-kernel correctness checks are complete. Phase
attestation in `libraries.yml` records Phase 4, after the core and its direct
dependencies; the [readiness audit](../../reports/real-closure-prerequisites.md)
records that evidence. The named headline `query_iff` and the independent prepared and
checker contracts are exposed by the public umbrella. The `HexSturmMathlibTests` target builds
the ordinary companion checks under `HexSturmMathlib/Tests`. Semantic axiom
guards remain in regression modules under `adapters/` and build
through `HexQuerySemantics`. This theorem-only layer has no dedicated Phase-4 timing
deliverable under the current policy.

`Soundness.lean` is part of this companion and its public umbrella. This
companion is not yet released. Its pinned HexRealRootsMathlib dependency
carries the shared Tau Ceti foundation; no computational package depends
on a proof companion or Tau Ceti. Publication remains separate from
monorepo API availability.

`HexSturmMathlib` imports `HexSturm`, `HexPolyMathlib` and
`HexRealRootsMathlib`. The shared signed-remainder theorem, representation and
positive-scaling bridges, and shared replay soundness live in
[hex-real-roots-mathlib](../../HexRealRootsMathlib/SPEC/hex-real-roots-mathlib.md#shared-foundation-and-proof-ownership).
Its Tau Ceti import and general integer/dyadic specialization are confined to
that Mathlib companion. The companion module `RealClosed.lean` proves
`IsRealClosed ℝ` independently. This companion proves the field frontend's domain guards,
endpoint sign operations, query-proof composition and root-count API
against the shared theorem, instantiating its domain and embedding as
`D := K` and `j := ι`. A field is an admissible domain instance; the shared
theorem does not require every domain to be a field. Neither proof nor
arithmetic kernel is duplicated.

No computational dependency points back to a companion. In particular,
hex-real-roots-mathlib does not import HexSturm or HexSturmMathlib, and no
existing input library (including hex-real-algebraic) imports this family.
Extension-specific coefficient checkers are supplied by downstream owners
through the lower-level interfaces. BKR/Thom semantics belong to
hex-sign-det-mathlib; real-closure construction belongs to
hex-real-closure-mathlib. Root isolation, CAD, coverings, new tactics and
nonstandard-analysis claims are outside this library.

## Semantic parameters and data invariants

Use arbitrary types `K,R` with these Mathlib hypotheses:

```text
[Field K] [LinearOrder K] [IsStrictOrderedRing K]
[Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
ι : K →+* R
hι : StrictMono ι
```

A field homomorphism is injective; `hι` additionally fixes the compatible
order. Do not identify `R` with `ℝ`, require `K` to be real closed, or require
roots to lie in `ι(K)`. No Archimedean, completeness-of-order, metric or
ordinary interval-connectedness hypothesis is allowed. Existence of an
ambient `R,ι` is a separate Tau Ceti obligation consumed by the real-closure
companion; these theorems are conditional on the supplied model.

Canonical computational fields use the existing HexPolyMathlib correspondence.
For noncanonical representation coefficients `E`, follow the
[execution contract](../../SPEC/real-closure-execution.md): a map `eval : E → K`
preserves actual operations/sign and reflects zero, without being injective.
Prove coefficientwise degree, derivative, arithmetic and division correspondence
for `DensePoly E`, then compose with `ι`. Semantic replay identities use zero
differences. Classical decisions belong only to semantic proofs. The tower
companion establishes the interpretation, not an executable-constructor law
argument. Do not confuse structural equality with equality in `K`.

Use `sgn : R → Int` with values `-1,0,1`. Exact decisions agree with this
semantic sign. A tactic may supply finite lower-level certificates or proofs
of precise coefficient identities/signs, preserving selected-root,
constant/oracle and embedding identities. Compose those proofs into the
shared replay theorem instead of rerunning expensive sign search during
kernel checking. They form a finite acyclic derivation, with no self-dependent
query claims. This is a proof boundary; ordinary coefficient arithmetic
returns values, not evidence or residual resources.

The coefficient interpretation also preserves `NatCast`; the computational
sign parameter is explicitly related to semantic sign. Prove that a computed
nonzero constant gcd is equivalent to the squarefree guard under these
hypotheses. Do not require its normalized representative to be literally one.
New shared pseudo-remainder correspondence belongs to the upstream owner;
this companion composes it with the frontend proof. Literal context bindings
and semantic polynomial identities have distinct soundness obligations.

## Endpoints and query semantics

The shared `Endpoint E` has `negInf`, `finite E`, `posInf`. Here finite
endpoints are elements of `K` and map through `ι`. The extended order puts
`negInf` below every finite endpoint and `posInf` above it. Strict `a<b`
excludes equal or reversed endpoints, including equal infinities. Finite
comparison is the sign of a difference, with corresponding evidence.

For valid inputs define `Domain(P;a,b)` by `P≠0`, `Squarefree P`, `a<b`, and
`P` nonvanishing at each finite endpoint in `K`. Prove equivalence to those
guards after mapping to `R`; squarefreeness transport uses characteristic
zero/separability, not a squarefree predicate on raw arrays. In particular,
nonzero constants satisfy the domain's polynomial guards. Zero and
nonsquarefree heads fail even if `F=0` or the initial remainder vanishes.

Define `Roots(P;a,b)` as the finite set obtained from `(Pᴿ.roots.toFinset)`
by keeping roots strictly between the mapped endpoints. At an infinite
endpoint the corresponding inequality is unrestricted. For `P≠0`, prove
membership equivalent to evaluation zero and the two endpoint inequalities.
Define

```text
TaQ(F,P;a,b) : Int = ∑ α ∈ Roots(P;a,b), sgn (Fᴿ.eval α).
```

This is a sum over distinct roots. It permits arbitrary `gcd(P,F)`;
common roots contribute zero. Negative sums are valid results. Root count
is `TaQ(1,P;a,b)`, not its absolute value or a truncated subtraction.

Finite endpoint signs use exact Horner evaluation. A nonzero chain entry
`S` has sign `sgn S.leadingCoeff` at `+∞`, and
`(-1)^S.natDegree * sgn S.leadingCoeff` at `−∞`. The shared theorem justifies
these algebraic infinity signs over arbitrary ordered real closed `R`.
Zero intermediate evaluations are deleted before counting adjacent sign
changes. `V(a),V(b)` are natural numbers, but the result is
`(V(a) : Int) - (V(b) : Int)`.

The open interval convention differs from the existing derivative
`ZPoly.sturmCount` on `(a,b]`. Prove agreement only under both finite
endpoint-root-free guards; preserve the existing API and its upper-root
behavior. No refactoring of `Sturm.IsSturmChain` is required.

## Shared theorem consumed here

The owning companion specifies the complete
[abstract recurrence and replay contract](../../HexRealRootsMathlib/SPEC/hex-real-roots-mathlib.md#abstract-signed-remainders).
The semantic chain starts at `Pᴿ`, positively reduces `Fᴿ*(Pᴿ)'` modulo
`Pᴿ`, then uses positive-scaled negative remainders, strict nonzero degree
descent and a terminal zero-remainder identity. A zero initial remainder
uses `[Pᴿ]`. A nonconstant terminal gcd is admissible. Under the domain
guards its variation drop equals `TaQ`.

Tau Ceti supplies polynomial IVT, Rolle and the signed-remainder identity,
including infinite endpoints and arbitrary common gcd, through the pinned
foundation named in the [owning companion's contract](../../HexRealRootsMathlib/SPEC/hex-real-roots-mathlib.md#shared-foundation-and-proof-ownership).
The companion semantic modules prove correspondence with the checked Hex data.
Ordinary derivative-seeded
`Sturm.IsSturmChain` has incompatible root-flank and root-free-tail conditions;
it cannot establish this signed sum.

## Required frontend theorems

Theorems below use the `HexSturmMathlib` namespace. Domain, representation
and rational/integer correspondence live in the companion library. Root-sum
semantics (`query_iff`, `query_spec`, `query_sound`, `queryPrepared_sound`,
`countPrepared_sound`, `countPrepared_nonneg`, `check_sound`, `rootCount_eq`,
`query_bound`, `query_sign`) and exact natural-count conversion live in the
ordinary companion target and its public umbrella. `HexQuerySemantics`
retains the semantic regression modules. The companion is not yet released.
Assume the operation-preserving, zero-reflecting interpretation
in the lawful semantic field described above.

| Theorem | Hypotheses and conclusion |
| --- | --- |
| `prepare_sound` | A returned prepared object establishes `Domain(P;a,b)` and binds exactly its head and endpoints. |
| `withEndpoints_isSome` | Retargeting a prepared head succeeds exactly when `Domain(P;a,b)` holds at the new endpoints. The core `PreparedDomain.withEndpoints_bindings` theorem separately preserves the literal head, sign and squarefree chain. |
| `withEndpoints_domain` | The actual retargeted object has a valid domain at the requested endpoints. |
| `query_spec` | `query p f a b = some q` implies `Domain(P;a,b)` and `q = TaQ(F,P;a,b)` for every supplied `R,ι,hι`. |
| `query_iff` | `query p f a b = some q` if and only if `Domain(P;a,b)` and `q = TaQ(F,P;a,b)` for every supplied `R,ι,hι`. |
| `queryPrepared_sound` | The prepared query computes the same mathematical sum for its bound domain and any `f`. |
| `countPrepared_sound` | The actual prepared query-one operation equals `Roots(P;a,b).card`, interpreted as an integer. |
| `countPrepared_nonneg` | The actual prepared integer count is nonnegative under the lawful coefficient interpretation, before conversion to `Nat`. |
| `check_sound` | An accepted finite certificate implies domain validity and the claimed query equality through the shared replay theorem; no producer-success hypothesis is needed. |
| `query_isSome` | `(query p f a b).isSome ↔ Domain(P;a,b)`. All coefficient decisions are total; computed degree bounds suffice. |
| `rootCount_isSome` | `(rootCount p a b).isSome ↔ Domain(P;a,b)`. Nonnegativity of the query of `1` makes conversion failure unreachable. |
| `rootCount_eq` | `rootCount p a b = some n` implies `n = Roots(P;a,b).card`. |
| `query_bound` | `|TaQ| ≤ Roots.card ≤ P.natDegree`; nonzero constant heads give zero. |
| `query_sign` | Under the domain and `Roots(P;a,b)={α}`, the query equals `sgn(Fᴿ.eval α)`. |
| `certify_checks` | Certificates produced on the domain pass replay and have the same value as `query`. |
| `certifyCountPrepared_checks` | The certificate made using the stored query-one chain passes ordinary literal replay for the current endpoints and supplied context. |
| `query_congr` | Order-preserving field maps and transported endpoints preserve the entire query result and domain validity. |
| `check_congr` | Accepted certificates for positive-scaled inputs have equal values; produced-certificate acceptance gives whole-`Option` rational/integer agreement despite different normalizers. |
| `query_rat_eq` | Rational coefficients and finite dyadic endpoints agree, after positive denominator clearing, with the whole `Option` returned by `ZPoly.tarskiQuery`. |

The local squarefree guard proof may use a nonzero constant gcd of `P,P'`,
a degree-zero fraction-field pseudo-gcd, or checked `A*P+B*P'=1`.
It must include nonzero constants. An arbitrary common gcd of `P,F` is not
this guard and must not be rejected. The bound and singleton theorems concern
semantic root sets; they do not introduce root enumeration into the runtime.

`query_sound` is the value-only projection of the combined `query_spec` contract.

## Headline correctness theorem

`HexSturmMathlib.query_iff` in `Soundness.lean` is the headline for the ordinary
Sturm query. It characterizes the complete returned `Option`: a particular
integer is returned exactly when the domain holds and it is the signed sum
over the distinct roots in the open interval. Thus failure occurs exactly
outside the domain. The lawful interpretation hypotheses permit noninjective
coefficient storage without field or order instances on the storage, and any
ordered real closed semantic field.

`query_isSome`, `query_spec` and `query_sound` compose into this theorem.
Prepared-query, natural-count, arbitrary-certificate and transport results in
the table are independently required public contracts: they describe stored
domains, exact natural conversion, supplied evidence and representation changes
which the ordinary query does not expose. They retain their ordinary-kernel
axiom guards. The headline itself and its noninjective-storage instantiation
have guards in `adapters/HexSturmMathlib/Tests/Replay/Semantics.lean`.
These regression guards build through `HexQuerySemantics`. The theorem itself
builds in the ordinary companion and is exported by its public umbrella; the
source import integration from #10575 is merged. Final split-package publication
and consumer checks remain with #10575. Naming the theorem is not Phase-4
attestation.

### Root-count boundary

`query_count` identifies every successful query of `1` with the cardinality of
the distinct-root set under the companion's operation/sign-preserving,
zero-reflecting interpretation into an ordered real closed field.
`query_nonneg` therefore proves nonnegativity of the actual computed answer.
`Hex.Sturm.rootCount` maps the query through `Int.toNat`; `rootCount_query`
proves the exact round trip `(n : Int) = value`, so no lawful query answer is
clamped. `rootCount_eq` identifies the natural answer with the root-set
cardinality, and `rootCount_isSome` preserves the existing query domain
without adding a failure case or a caller-supplied correctness premise.

`HexRealRootsMathlib.Tarski.check_singleton` and `check_constant` prove zero
values directly from checked data, including constant-head queries of `1`.
The existing real-only results remain available:
`Sturm.isChain_of_replay` in `HexRealRootsMathlib/LiteralChain.lean` establishes
a derivative Sturm chain over `Polynomial ℝ`, and its count theorem uses
`Sturm.IsSturmChain.sturm_Ioc`. `sturmCount_eq_card_roots` and
`rootCount_eq_card_roots` in `ChainCorrespond.lean` prove the existing integer
Sturm APIs. These results have a fixed real coefficient field and real root
flank hypotheses. They cannot be instantiated at an arbitrary ordered field
or a non-Archimedean coefficient interpretation. The new generic backend
congruence theorem requires a common interpreted field; it does not manufacture
an embedding of an arbitrary ordered field into `ℝ`.

The effective specializations are proved now in `TarskiCount.lean`:
`integer_sturmChain` connects the checked recurrence to the existing real Sturm
theorem (strict derivative degree removes the initial quotient);
`integer_check_count` and `integer_check_total` prove finite-interval and whole-line
counts for arbitrary accepted integer query-one certificates;
`integer_query_count` and `integer_query_nonneg` apply to the actual integer
producer. `query_rat_count` and `query_rat_nonneg` in `Rational.lean` transport
finite dyadic-interval counts to the rational frontend after positive clearing.
These use the existing real foundation, not a new analytic proof.

`rootCount_sturm` in `Rational.lean` identifies every successful natural
count on a finite dyadic interval with the existing `ZPoly.sturmCount` after
positive denominator clearing, including accepted nonzero constants. The success
hypothesis supplies squarefreeness; callers need no additional degree or
squarefreeness premise.
Success entails both endpoint-root-free guards. The half-open API's behavior
at an upper root is preserved.

The existing integer root-count APIs and their proofs remain available.
The general `Hex.Sturm.rootCount` uses the same shared query computation.

## Integer/dyadic specialization and positive clearing

`ZPoly.tarskiQuery_eq` and `IntTarskiCertificate.check_sound` stay in
the companion module `HexRealRootsMathlib.TarskiReal`, specialized from
the shared theorem with the integer embedding and exact dyadic endpoints
in `ℝ`. The integer ring kernel
requires no `Field Int`. The generic rational frontend reaches infinities;
the preserved public integer query still takes a finite `DyadicInterval`.

For `P,F : Polynomial ℚ`, choose positive integers `dP,dF` and integer
polynomials `Pz,Fz` such that

```text
map Int→ℚ Pz = C(dP) * P
map Int→ℚ Fz = C(dF) * F.
```

Prove that roots, squarefreeness over `ℚ`, finite endpoint guards and query
signs are preserved. Integer content does not invalidate `Pz=4*X`. Moreover
`Fz*Pz'` interprets as `dF*dP*(F*P')`. Thus both domains coincide and
`query_rat_eq` includes invalid `none` cases, not just equal successful
values. Zero polynomials may use clearing factor one. Negative factors are
not admissible clearing evidence.

Translate accepted certificates by positively clearing denominators of chain
entries, quotients and scale data and re-establishing every initial,
three-term and terminal identity. Translate semantic degree, guard and sign
evidence as well; a shared positive-scaling lemma alone does not check an
entire frontend certificate. Prove accepted-certificate transport in both
directions (integer to rational by embedding). Do not assert identical
certificates or identical construction/checking costs. Native optimized integer
content/Horner operations require upstream correspondence to the shared
kernel; this frontend theorem must not introduce another chain algorithm.

## Failure, termination and completeness

The public query has `Option` solely for mathematical invalidity: zero or
nonsquarefree head, unordered endpoints or a finite root endpoint. Prove the
guards equivalent to the semantic domain, including constant heads and zero
query shortcuts. A false replay rejects the proposed certificate; it cannot
establish absence of a mathematical query value.

All field operations and equality/order decisions are total. Pseudo-division
and Euclidean chains terminate by strict degree descent, with the cancellation
and chain-length bounds in the computational SPEC. There is no caller budget
or bounded coefficient callback. The source extension must justify its total
sign procedure before instantiating this frontend. Merely having a bounded
approximation attempt does not supply such an instance.

Replay terminates on every finite certificate, validates all lengths and
identities, and never regenerates a chain or isolates roots. Tactic-oriented
replay composes supplied finite proofs of expensive coefficient signs rather
than performing oracle refinement. Structural shape validation and ordinary
elaborator execution limits do not require a shared arithmetic resource API.
Prove soundness and domain-exact completeness of query, acceptance of produced
certificates, and soundness of independently supplied certificates. None of
these theorems assumes an Archimedean separation bound.

## Conformance and Phase-4 evidence

Follow [testing.md](../../SPEC/testing.md) and share the computational owner's exact
fixtures. Bridge tests instantiate the universal theorem, exercise accepted
and rejected literal proofs, and audit the final axiom set. Do not replace a
proved universal correspondence by a fixture-only soundness claim. Existing
Mathlib facts and planned Tau Ceti imports must be distinguished in proof
probes; no `axiom`, `native_decide`, trusted external result or proof debt
across the core/companion boundary is allowed.

Required adversarial coverage includes:

- `P=X²-1` on the whole line with `F=1,-1,0,X,X-1`, giving
  `2,-2,0,0,-1`; the last requires a nonconstant terminal gcd. Include no-real-root
  heads, high-degree `F`, `F` divisible by `P`, negative leading coefficients,
  nonzero constants and `P=4*X` under the integer specialization.
- Zero/nonsquarefree heads even with `F=0`; equal/reversed endpoints and
  invalid infinity pairs; roots at either finite endpoint; half-open count
  agreement only with its additional guards; zero intermediate endpoint signs.
- Equal field values with different extension representatives, false degree/parity,
  wrong initial product, negative/zero scales, altered quotients, missing
  terminal identity, false squarefree evidence and negative clearing factors.
- Foreign-context, stale, cyclic, malformed and self-dependent evidence;
  valid representation transports and positive denominator replay translation.

Use pinned python-flint exact selected-root signs for rational fixtures and
compare the integer/rational frontends, recording seeds and oracle provenance.
When ordered-extension instances exist, downstream integration tests instantiate the
same theorem at a non-Archimedean `R` for the corrected
[de Moura–Passmore example](https://www.cl.cam.ac.uk/~gp351/infinitesimals.pdf)
`P=(εX²−1)(εX³−1)`, with `ε` positive infinitesimal: whole-line count `3`,
positive count `2`, and query of `P'''` on `(0,+∞)` equal to `0`, with opposite
signs at the two positive roots. Include multiple infinitesimal levels and
nested certificates. These are downstream tests against pinned Z3 RCF data,
not imports back into this companion or claims about arbitrary `0<ε<1`.

Phase 4 follows [the repository evidence tracks](../../PLAN/Phase4.md#evidence-tracks).
This companion supplies correspondence theorems, not a tactic or proof
generator, so Phase 4 adds no proof-track deliverable. Its existing correctness
tests build ordinary-kernel replay examples, including rational,
integer, noninjective and nested coefficient cases, rejected evidence and
transitive axiom audits. Ordinary theorem applications do not require timing
sweeps. Producer, coefficient-sign and endpoint arithmetic measurements belong
to Mathlib-free benches in hex-sturm/hex-real-roots; no executable benchmark
imports this companion.

The [semantic replay report](../../reports/sturm-tarski-semantics.md) retains
existing theorem-application observations and their limited scope. Those
observations impose no continuing fresh-module sweep requirement. Additional
proof-cost measurements must resolve a named replay/quotation design choice
or an observed bottleneck, under the shared-host measurement policy. A CAS
query time is not a Lean proof-checking baseline. Full BKR, `tower8` isolation
and normalization ablations remain the respective family owners' requirements.
