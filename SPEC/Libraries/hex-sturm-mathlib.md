# hex-sturm-mathlib

Correspondence and literal replay soundness for the ordered-field
Sturm–Tarski frontend in [hex-sturm](hex-sturm.md).

## Status, scope and dependencies

This is a planned companion in the
[real-closure family](../future-work.md#real-closures-of-ordered-fields).
The APIs and theorem names below are required statement shapes, not existing
or checked Lean declarations. This SPEC registers no source target, phase,
release or CI workflow. Computational interfaces are specified by hex-sturm;
this companion interprets them in Mathlib and proves their correspondence.

`HexSturmMathlib` imports `HexSturm`, `HexPolyMathlib` and
`HexRealRootsMathlib`. The shared signed-remainder theorem, representation and
positive-scaling bridges, and shared replay soundness live in
[hex-real-roots-mathlib](../../HexRealRootsMathlib/SPEC/hex-real-roots-mathlib.md#shared-foundation-and-proof-ownership).
That companion alone imports the Tau Ceti univariate foundation for these
queries. It retains the integer/dyadic specialization and proves
`IsRealClosed ℝ`. This companion proves the field frontend's domain guards,
endpoint adapters, coefficient-evidence composition and root-count API
against the shared theorem. Neither proof nor arithmetic kernel is duplicated.

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

For raw coefficients `C`, a context `ctx` supplies a validity predicate and
a denotation of valid representatives in `K`. A convenient statement shape
is `denote : {c : C // Valid ctx c} → K`; proof irrelevance makes the chosen
validity proof immaterial. The `CoeffOps`/`FieldOps` law packages interpret
successful operations and accepted evidence, rather than installing field
or order instances on `C`. Interpret a valid array `p` as
`P = ∑ i < p.size, Polynomial.C (denote p[i]) * X^i` in `Polynomial K`;
write `Pᴿ = P.map ι`. Interpret `f` similarly as `F,Fᴿ`.

The shared representation bridge proves addition, multiplication, negation,
derivative, evaluation and coefficientwise equality correspondence. The
field extension of the laws proves that successful checked inversion of a
nonzero operand denotes its inverse. The total-carrier adapter must prove
that its Lean-core operations and comparisons are the same as these
Mathlib operations; two unrelated instances on the same type do not suffice.
Runtime decisions stay executable. Classical decisions may define semantic
root sets in proofs but never implement the computational adapter.

Successful semantic degree evidence means exactly:

- `none`: `P=0` (all stored coefficients denote zero);
- `some d`: `P≠0`, `P.natDegree=d`, coefficient `d` is nonzero and all higher
  stored coefficients denote zero.

The outer operation result distinguishes success from exhaustion. Structural
array size or structural equality of representatives cannot prove a degree
or zero claim. Mapping along `ι` preserves degree and nonzeroness. A raw
leading coefficient can denote zero without being structurally zero.

Every accepted coefficient claim binds context, operation, operands, result
and sign/zero value. Shared soundness interprets `PolyOps.Sign` by the integer
values `-1,0,1`; write `sgn : R → Int` for the corresponding semantic sign.
A sign must be established by a kernel-reducible checker with a proved
soundness theorem, or a proof of that exact claim. A runtime comparison,
opaque external oracle or unresolved zero test is not such evidence.
Composition here proves that lower-level accepted evidence discharges the
shared theorem's hypotheses. It preserves embeddings, selected-root and
constant/oracle identities and tower levels. After a dynamic split, cached
evidence requires an explicit denotation-preserving transport. Nested
certificates form a finite acyclic structure, with child soundness proved
before parent soundness; a query cannot certify its own coefficient sign.

## Endpoints and query semantics

The shared `Endpoint E` has `negInf`, `finite E`, `posInf`. Here finite raw
endpoints denote elements of `K` and map through `ι`. The extended order puts
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
`Sturm.IsSturmChain` has incompatible root-flank and constant-tail conditions;
it cannot establish this signed sum.

## Required frontend theorems

Names below live under `Hex.Sturm`, except for the upstream names explicitly
identified. Suppress residual budgets/work counters in these statement shapes;
all bounded equalities refer to the actual result including those fields.
Assume the operation/evidence laws above. Inputs to a successful or accepted
result acquire validity from its checked guards, not from an unchecked
certificate assertion.

| Theorem | Hypotheses and conclusion |
| --- | --- |
| `prepare_sound` | `prepareWith … = ok domain evidence` implies valid input context and `Domain(P;a,b)`; its prepared object binds exactly `p,a,b,ctx`. Gcd or Bézout evidence proves squarefreeness after interpretation. |
| `query_sound` | `queryWith … p f a b = ok q cert` implies validity, `Domain(P;a,b)` and `q = TaQ(F,P;a,b)` for every supplied `R,ι,hι`. Derive this through the shared kernel correspondence. |
| `queryPrepared_sound` | Successful prepared query has the same conclusion for its bound context/head/endpoints and validated `f`; deserialized prepared data first passes replay. |
| `Replay.check_sound` | `Replay.checkWith … p f a b q cert = accepted` implies validity, domain and the same query equality, by `QueryReplay.check_sound` in hex-real-roots-mathlib and local endpoint/coefficient-evidence composition. A Boolean `check=true` implies accepted. No producer-success hypothesis is needed. |
| `query_invalid` | An `invalid` result proves an invalid input context, or, given valid inputs, `¬ Domain(P;a,b)`. Failure of an internal helper on already validated data is `rejected`, never evidence of an invalid domain. |
| `query_isSome` | For a lawful total adapter with complete decisions and computed fuel, `(query p f a b).isSome ↔ Domain(P;a,b)`. `none` has exactly this domain meaning only for this total interface. |
| `rootCount_eq` | Successful `rootCountWith … = ok n cert` implies domain and `n = Roots(P;a,b).card`; similarly for `rootCount = some n`. Derive it from query of `1` and the checked conversion to `Nat`. |
| `query_bound` | Under the domain, `|TaQ(F,P;a,b)| ≤ (Roots(P;a,b).card : Int) ≤ (P.natDegree : Int)`; nonzero constant heads give zero. |
| `query_sign` | Under the domain and `Roots(P;a,b)={α}`, a successful query equals `sgn (Fᴿ.eval α)`. |
| `query_congr` | Context/representation transports preserving coefficient and endpoint denotations preserve completed query values. They transfer success only with suitable completeness/budget hypotheses. |
| `query_backend_eq` | Lawful backends using the shared kernel agree on completed values; total adapters agree on the whole `Option`. Equality of bounded outcome tags requires a budget-accounting relation as well. |
| `query_rat_eq` | At rational coefficients and finite dyadic endpoints, positive denominator clearing gives equality of the whole total `Option` with `ZPoly.tarskiQuery`, and accepted replay transport as below. |

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
directions (integer to rational by embedding), with sufficient target budget
and checked size limits. Do not assert identical certificates, identical
bounded costs, or acceptance at the same budget. Native optimized integer
content/Horner operations require upstream correspondence to the shared
kernel; this frontend theorem must not introduce another chain algorithm.

## Failure, termination and completeness

Preserve `PolyOps.Result` (`ok`, `invalid`, `exhausted`, `rejected`) and
`CheckResult` (`accepted`, `rejected`, `exhausted`) exactly as specified in
hex-sturm and hex-poly. Diagnostics are not a stable enumeration. Invalid
contexts, zero/nonsquarefree heads, unordered endpoints and finite root
endpoints cannot return a query value, including on shortcut branches.
Testing invalidity may itself exhaust. Unresolved coefficient equality,
insufficient work/allocation/evidence budget and incomplete sign evidence
produce exhaustion, not a sign, zero, root count or invalidity proof.
False/malformed supplied certificates are rejected. An internally produced
negative root count or failed replay is an implementation error reported as
rejected, never clamped to zero.

All callbacks terminate on raw and invalid inputs. Each finite scan is bounded
by stored length; pseudo-division decreases certified semantic degree or
explicit fuel. For nonzero divisor `B`, a division of `A` needs zero leading
cancellations if `A=0` or `deg A<deg B`, otherwise at most
`deg A-deg B+1`. After initial reduction a degree-`n` head has at most `n+1`
nonzero chain entries and at most `n` further divisions including terminal
zero; the constant case has none. Squarefreeness checking has its own
Euclidean degree bound. Raw storage scans and nested coefficient work must
also be charged; degree alone does not bound those costs.

One parent budget covers guards, arithmetic, allocation and every nested
coefficient certificate. Check literal sizes before multiplication/allocation;
reject missing/extra identities, oversized chains and cyclic evidence.
Replay terminates by literal size and the recursive evidence measure without
coefficient search, refinement, gcd computation, factorization or root
isolation. It checks supplied arithmetic identities and signs. Fuel zero
permits success only after a stopping condition has been established.

Soundness of successful/accepted results needs only sound fallible operations
and checkers. Total-adapter domain-exact success additionally needs complete
executable decisions and a proof that computed fuel suffices. Eventual success
in bounded mode requires completeness of all invoked arithmetic, sign/zero
and evidence producers plus sufficient budgets; increasing a budget alone
is no theorem of success. No completeness is promised for unresolved
transcendental relations, and no rational root-separation bound is used.

## Conformance and Phase-4 evidence

Follow [testing.md](../testing.md) and share the computational owner's exact
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
- Raw structurally nonzero coefficients denoting zero, false degree/parity,
  wrong initial product, negative/zero scales, altered quotients, missing
  terminal identity, false squarefree evidence and negative clearing factors.
- Exhaustion at each guard, arithmetic and nested evidence stage;
  foreign-context, stale, cyclic, oversized and self-dependent evidence;
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

Phase 4 uses the [fresh-module proof evidence](../benchmarking.md#fresh-module-proof-evidence)
track for ordinary kernel replay: build fresh measured modules with warm
imports, record source/toolchain hashes, theorem axiom sets, emitted artifact
sizes, wall time and host activity. Sweep head/query degree, coefficient and
endpoint sizes, chain length, extension depth and nested evidence size;
include valid, rejected and exhausted replay probes. Separate producer,
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
