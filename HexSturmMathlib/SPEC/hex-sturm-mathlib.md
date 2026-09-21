# hex-sturm-mathlib

Correspondence and literal replay soundness for the ordered-field
Sturm–Tarski frontend in [hex-sturm](../../HexSturm/SPEC/hex-sturm.md).

## Status, scope and dependencies

`HexSturmMathlib/Domain.lean` proves the exact semantic domain equivalence
for `query` and `prepare`, finite/infinite endpoint guards, and produced
certificate acceptance. These results apply to noninjective coefficient
interpretations without field or order instances on representation storage.
Conformance instantiates them on canonical rationals and noncanonical
representatives and inspects their axioms.

The root-sum/replay semantics, root-count and singleton-sign theorems,
whole-Option denominator-clearing/backend agreement and Phase-4 proof evidence
below remain required. Their foundation must be delivered through
hex-real-roots-mathlib; no axioms or conditional stand-ins supply the missing
Sturm–Tarski theorem. No release or phase completion is claimed.

`HexSturmMathlib` imports `HexSturm`, `HexPolyMathlib` and
`HexRealRootsMathlib`. The shared signed-remainder theorem, representation and
positive-scaling bridges, and shared replay soundness live in
[hex-real-roots-mathlib](../../HexRealRootsMathlib/SPEC/hex-real-roots-mathlib.md#shared-foundation-and-proof-ownership).
That companion alone imports the Tau Ceti univariate foundation for these
queries. It retains the integer/dyadic specialization and proves
`IsRealClosed ℝ`. This companion proves the field frontend's domain guards,
endpoint adapters, query-proof composition and root-count API
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

Imports requested from Tau Ceti by
[#10300](https://github.com/kim-em/hex-dev/issues/10300) are polynomial IVT,
polynomial Rolle and the signed-remainder/Cauchy-index identity, including
infinite endpoints and arbitrary common gcd. These are named mathematical
obligations, not assumed available Lean declarations or new axioms. The
[owner's audit and real instance contract](../../HexRealRootsMathlib/SPEC/hex-real-roots-mathlib.md#real-specialization)
record what the Mathlib pin actually supplies. Ordinary derivative-seeded
`Sturm.IsSturmChain` has incompatible root-flank and root-free-tail conditions;
it cannot establish this signed sum.

## Required frontend theorems

Names below live under `Hex.Sturm`, except upstream names explicitly
identified. Assume the operation-preserving, zero-reflecting interpretation
in the lawful semantic field described above.

| Theorem | Hypotheses and conclusion |
| --- | --- |
| `prepare_sound` | A returned prepared object establishes `Domain(P;a,b)` and binds exactly its head and endpoints. |
| `query_sound` | `query p f a b = some q` implies `Domain(P;a,b)` and `q = TaQ(F,P;a,b)` for every supplied `R,ι,hι`. |
| `queryPrepared_sound` | The prepared query computes the same mathematical sum for its bound domain and any `f`. |
| `Replay.check_sound` | An accepted finite certificate implies domain validity and the claimed query equality through the shared replay theorem; no producer-success hypothesis is needed. |
| `query_isSome` | `(query p f a b).isSome ↔ Domain(P;a,b)`. All coefficient decisions are total; computed degree bounds suffice. |
| `rootCount_isSome` | `(rootCount p a b).isSome ↔ Domain(P;a,b)`. Nonnegativity of the query of `1` makes conversion failure unreachable. |
| `rootCount_eq` | `rootCount p a b = some n` implies `n = Roots(P;a,b).card`. |
| `query_bound` | `|TaQ| ≤ Roots.card ≤ P.natDegree`; nonzero constant heads give zero. |
| `query_sign` | Under the domain and `Roots(P;a,b)={α}`, the query equals `sgn(Fᴿ.eval α)`. |
| `certify_checks` | Certificates produced on the domain pass replay and have the same value as `query`. |
| `query_congr` | Order-preserving field maps and transported endpoints preserve the entire query result and domain validity. |
| `query_backend_eq` | Lawful optimized realizations of the shared kernel agree on the whole `Option`; certificate translation need not preserve literal arrays. |
| `query_rat_eq` | Rational coefficients and finite dyadic endpoints agree, after positive denominator clearing, with the whole `Option` returned by `ZPoly.tarskiQuery`. |

The local squarefree guard proof may use a nonzero constant gcd of `P,P'`,
a degree-zero fraction-field pseudo-gcd, or checked `A*P+B*P'=1`.
It must include nonzero constants. An arbitrary common gcd of `P,F` is not
this guard and must not be rejected. The bound and singleton theorems concern
semantic root sets; they do not introduce root enumeration into the runtime.

## Integer/dyadic specialization and positive clearing

`ZPoly.tarskiQuery_eq` and `TarskiReplay.check_sound` stay in
hex-real-roots-mathlib, specialized there from the shared theorem with the
integer embedding and exact dyadic endpoints in `ℝ`. The integer ring kernel
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
When extension adapters exist, downstream integration tests instantiate the
same theorem at a non-Archimedean `R` for the corrected
[de Moura–Passmore example](https://www.cl.cam.ac.uk/~gp351/infinitesimals.pdf)
`P=(εX²−1)(εX³−1)`, with `ε` positive infinitesimal: whole-line count `3`,
positive count `2`, and query of `P'''` on `(0,+∞)` equal to `0`, with opposite
signs at the two positive roots. Include multiple infinitesimal levels and
nested certificates. These are downstream tests against pinned Z3 RCF data,
not imports back into this companion or claims about arbitrary `0<ε<1`.

Phase 4 uses the [fresh-module proof evidence](../../SPEC/benchmarking.md#fresh-module-proof-evidence)
track for ordinary kernel replay: build fresh measured modules with warm
imports, record source/toolchain hashes, theorem axiom sets, emitted artifact
sizes, wall time and host activity. Sweep head/query degree, coefficient and
endpoint sizes, chain length, extension depth and nested evidence size;
include valid and rejected replay probes. Separate producer,
coefficient-sign and endpoint arithmetic measurements in Mathlib-free benches
owned by hex-sturm/hex-real-roots from elaboration and kernel proof costs.
No ordinary bench target imports this companion.

Compare matched rational/integer replay paths and positive-clearing transport;
record arithmetic/guard/translation costs separately and include one
representative attribution profile. Use fixed trial-major schedules and
adjacent alternating `AB`/`BA` comparisons on the shared host, keep every
completed sample, and permit at most one unchanged inconclusive rerun. A CAS
query time is not a Lean proof-checking baseline. Full BKR, `tower8` isolation
and normalization ablations remain the respective family owners' requirements.
This SPEC supplies requirements, not performance measurements or phase claims.
