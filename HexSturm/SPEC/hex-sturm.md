# hex-sturm

Ordered-field Sturm–Tarski queries and root counts, using the shared signed
pseudo-remainder and literal replay kernel in `hex-real-roots`.

## Status, scope and placement

The computational frontend is implemented in `HexSturm/Basic.lean`, using the
shared query producer and literal checker. It provides `prepare`, `query`,
`queryPrepared`, `certify`, `certifyPrepared` and `Replay.check`, with explicit
coefficient signs and finite/infinite endpoints. `Prepared` has a private
constructor and retains its sign operation, head, endpoints and validated
squarefree chain. `orderSign` is the canonical ordered-coefficient sign adapter. The frontend
uses ordinary coefficient inversion to divide each remainder by its positive
absolute leading coefficient, preserving negative leading signs. The shared
integer backend retains its content normalization.

The [companion](../../HexSturmMathlib/SPEC/hex-sturm-mathlib.md) proves exact
semantic domain equivalence, produced-certificate acceptance, prepared-query
agreement and whole-`Option` rational/integer agreement on finite ordered dyadic
intervals after positive denominator clearing. Root-sum/replay semantics,
`rootCount`, singleton/sign bounds, general backend correspondence, literal
certificate translation and remaining Phase-4 evidence are still required.
No release or phase completion is claimed.

`HexSturm` depends on `HexPoly` and `HexRealRoots`, with no Mathlib or
Batteries import. Its namespace is `Hex.Sturm`. Its substantive work is
field-domain and squarefreeness validation, finite and infinite endpoint
adapters, query proof composition, and root counts. Ordinary
ordered-domain pseudo-division lives in
[hex-poly](../../HexPoly/SPEC/hex-poly.md#ordered-domain-pseudo-division);
the ring-only query/replay algorithm lives in
[hex-real-roots](../../HexRealRoots/SPEC/hex-real-roots.md#shared-ordered-domain-kernel).
Both integer and field frontends invoke that algorithm. No upstream input
library imports this family. In particular `hex-real-algebraic` remains an
independent rational-base implementation.

`HexSturmMathlib` imports this library, `HexPolyMathlib` and
`HexRealRootsMathlib`, and consumes the shared abstract theorem through the
last of these. Only companions import Mathlib or Tau Ceti. BKR matrices,
complete sign tables and Thom encodings belong in `hex-sign-det`; extension
construction and isolation in `hex-real-closure`; coefficient orders and
approximation protocols in `hex-ordered-fn`. There is no root-search,
Archimedean separation, CAD, coverings, or tactic completeness claim here.

## Coefficients and evidence

Use the shared [execution contract](../../SPEC/real-closure-execution.md).
The canonical specialization uses the usual Lean-core field/order classes.
The representation specialization uses ordinary total arithmetic, structural
`DecidableEq`, canonical zero and an executable sign. Both call the same
`DensePoly` signed-remainder/query kernel. Representation types receive no
false field/order instances; lawful-field hypotheses belong to interpretation
and correctness theorems. The field need not be real closed or Archimedean.

The pseudo-remainder kernel needs no coefficient division: its interpretation
is a nontrivial ordered commutative domain. Integers are an actual instance;
no `Field Int` is required. For noncanonical coefficients, semantic polynomial
identities test zero differences, while structural equality is only a fast
path. Degree and trailing-zero normalization use the unique stored zero.
No parallel polynomial AST or second Tarski primitive is introduced.

Transcendental coefficients supply total sign with the caller's core-expressible
progress witness. Optional bounded sign attempts cannot serve as coefficient
signs. There is no propagation of oracle exhaustion through Sturm arithmetic.

Prove ordinary arithmetic and order correspondence once. A query replay
carries the polynomial identities and signs needed by the query theorem.
For expensive extension signs a tactic can supply finite lower-level sign
certificates or proofs of the exact claims, tied to their root/constant
context, instead of rerunning sign search in the kernel. This proof interface
does not alter coefficient addition or multiplication. Child sign proofs
precede parent query proofs; a query cannot certify its own assumptions.
Cached facts transported across a split require a denotation-preservation
proof.

The shared operation list explicitly includes natural casts for derivatives,
and ordered entry points receive `sign : E → Int`; no field/order instance
is inferred on representation coefficients. A normalized gcd is compared
with one semantically, never by structural equality of noncanonical leading
coefficients. The simpler squarefree guard tests a nonzero constant gcd.
Replay polynomial identities use zero differences; only provenance and
input/operand bindings use literal equality. Persistent context refinement
requires fresh bindings even when operand literals remain unchanged.

## Endpoints, domain and public operations

Use `Endpoint E := negInf | finite E | posInf`, with the common data type in
hex-real-roots. The canonical field adapter takes `E = K`; a representation adapter uses
its coefficient type `E` and the explicit sign interface;
the integer kernel adapter keeps `E = Dyadic`. The preserved public
`ZPoly.tarskiQuery` takes only a finite `DyadicInterval`. Integer-coefficient
queries at infinity use this field frontend after embedding coefficients in
`Rat`; no `Field Int` instance or new public integer entry point is required.
Infinity ordering is structural; finite comparison uses the field order.
The interval input is an ordered pair.
Every entry point establishes `a < b` in the extended order. Thus equal or
reversed endpoints, including equal infinities, are invalid.

Write `P,F` for interpreted polynomials. `Domain p a b` means `P ≠ 0`, `P`
is squarefree over `K`, `a < b`, and `P(a), P(b)` are nonzero wherever the
endpoints are finite. Nonzero constants are squarefree. Establish the domain
before shortcuts for constants, `f=0`, or a zero initial remainder. In
particular, reject nonsquarefree `p`; do not silently replace it by its
squarefree part or count multiplicities. A caller may explicitly perform
squarefree decomposition in its owning library.

The required public operations use the same shared arithmetic kernel:

| Operation | Result and responsibility |
| --- | --- |
| `prepare p a b` | Validate the mathematical domain and return `Option (Prepared E)`. The prepared object binds the head and endpoints. |
| `query p f a b` | Return `Option Int`; `none` exactly when the domain fails. |
| `queryPrepared domain f` | Return the query for an already validated domain. |
| `rootCount p a b` | Query `f=1`, returning `Option Nat` with the same domain. Prove nonnegativity before conversion; never clamp an unexpected negative value. |
| `certify p f a b` | Run the shared kernel while retaining its literal query certificate. Return `none` on the same invalid domain. |
| `certifyPrepared context domain f` | Retain the literal query certificate while reusing the prepared squarefree chain and binding the supplied context. |
| `Replay.check` | Check a supplied finite certificate; return `Bool`, false on malformed or incorrect data. |

No operation takes a caller resource budget. Squarefreeness uses the existing
plain field gcd of `P,P'`, testing that it is a nonzero constant, or a plain
pseudo-gcd with nonzero constant terminal remainder. Neither route computes
Bézout accumulators when only a gcd is needed. A replay can carry
`A*P+B*P'=1` instead; this is a query-level guard witness, not a requirement
that ordinary arithmetic return evidence. Prepared objects are opaque;
untrusted serialized data is revalidated before reuse.

The query semantics are in any ordered real closed extension `R` with an
order-preserving field embedding `ι : K →+* R`. Let `Roots(P;a,b)` be the
finite set of distinct roots of `P.map ι` strictly between the interpreted
endpoints. Then

```text
TaQ(F,P;a,b) = ∑ α ∈ Roots(P;a,b), sign ((F.map ι).eval α) : Int.
```

Roots need not lie in `K`. Universal quantification over `R,ι` makes the
query independent of the chosen ordered real closed extension. Nonzero
constant `p` gives zero. Negative query values are valid. The query of `1` counts distinct roots; it is nonnegative
and at most `degree P`, and `|TaQ| ≤ rootCount ≤ degree P`. For an interval
with exactly one root `α`, the query is precisely the sign of `F(α)`.
Finite-endpoint queries are open intervals. Today's `ZPoly.sturmCount`
counts `(a,b]` and admits an upper root; preserve that separate API. Agreement
with it requires both endpoints root-free. Keep the existing
`Polynomial ℝ` `Sturm.IsSturmChain` proofs and derivative replay intact.

## Signed remainders and literal replay

The shared kernel begins with `s₀=P`. It reduces `F*P'` before starting the
chain and records

```text
u*(F*P') = A*P + v*s₁,       u>0, v>0,
s₁=0 or degree s₁ < degree P.
```

For a zero remainder use `[P]` and the identity `u*(F*P')=A*P`; the result
is zero. A nonzero constant head also uses this branch, after the guards.
Otherwise each three-term step and final division satisfy

```text
lᵢ*sᵢ = Qᵢ*sᵢ₊₁ - rᵢ*sᵢ₊₂,       lᵢ>0, rᵢ>0,
l*sₘ₋₁ = Q*sₘ,                         l>0.
```

All displayed equations are polynomial identities under interpretation.
Entries are nonzero, degrees strictly decrease, and the terminal gcd may be
nonconstant. Common roots of `P,F` contribute zero, not an error. Only
positive rescaling/content removal preserves this certificate convention;
independently making every entry positive-leading is unsound.

Backends may use exact content division or signed subresultant normalization
to control coefficient growth. Field backends can divide by nonzero
coefficients using ordinary field inversion. These are optimized realizations of the
same kernel, requiring backend equality and the same positive identities.
If a subresultant factor is negative, the backend must correct the affected
entry's sign and all associated identities, recording positive absolute scale
factors; merely replacing a negative factor by its absolute value is invalid.
Replay checks the resulting identities without rerunning normalization.

At a finite endpoint, evaluate each entry by exact Horner arithmetic through
the adapter. At `+∞` its sign is the sign of its leading coefficient; at
`−∞` multiply that sign by `(-1)^degree`. Delete zero signs and count adjacent
sign changes as a `Nat`; the query is explicitly
`(V(a) : Int) - (V(b) : Int)`.
Zeros in intermediate entries at finite endpoints are valid. The head's
nonvanishing is a separate domain guard.

Replay contains literal inputs/context, guarded domain evidence, the chain,
initial quotient/scales, every step quotient/scale, terminal identity,
degrees, endpoint signs and claimed variations/value.
Check every identity coefficientwise, positive scale, nonzero entry, array
length and degree bound. In the singleton branch there is no fictitious
second entry or terminal pair; the initial zero identity is required.
Acceptance also checks the guards and variations. No producer, gcd search,
root isolation, or factorization runs during replay. Tactic replay uses
supplied finite proofs for expensive coefficient identities/signs rather than
restarting refinement or recursive sign determination. Ordinary exact
coefficient arithmetic is justified by its existing correctness theorems.

For `n=degree P`, accepted chains have at most `n+1` nonzero entries. The
checker rejects missing or extraneous identities and chains exceeding the
mathematical degree bound. It terminates by finite certificate structure;
malformed data cannot return a query value.

## Failure, termination and completeness

All coefficient arithmetic and decisions are total. The public `Option`
expresses precisely the query's mathematical domain: nonzero squarefree
head, strictly ordered endpoints and no finite root endpoints. These guards
are checked before constant or zero-query shortcuts. Invalidity is not a
resource-exhaustion result. A false replay means that the proposed certificate
failed verification, not that the mathematical query is undefined.

Polynomial loops terminate by degree descent. Pseudo-division by nonzero `B`
needs at most `deg A-deg B+1` cancellations when `A≠0` and `deg B≤deg A`,
and none otherwise. After the initial reduction a degree-`n` head has at
most `n+1` nonzero chain entries and at most `n` further divisions including
the terminal zero. The constant case has no such divisions. Squarefree
checking has its own Euclidean degree bound. A computed fuel implementation
must prove the bound sufficient; running out is not a user-visible result.

Prove `query_isSome` exactly on the domain, producer soundness, produced
certificate acceptance and replay soundness. Termination of a supplied
coefficient field's decisions is part of having that executable interface.
The extension owner proves it; Sturm does not add oracle budgets or assume
that increasing a budget proves success. No root separation bound is used.
Resource limits of an elaborator or host remain execution controls outside
these mathematical operations.

## Required correspondence and specialization theorems

The following are statement shapes. The core and companion structures on
`K` must have identical operations and order. Let `ι : K →+* R` be
order-preserving, with `[Field R] [LinearOrder R] [IsStrictOrderedRing R]`
and `[IsRealClosed R]` on the Mathlib side.

| Statement | Required conclusion / owner |
| --- | --- |
| `query_sound` | `query p f a b = some q` implies `Domain p a b` and `q = TaQ(F,P;a,b)`; companion. |
| `Replay.check_sound` | Accepted replay implies the same domain and query equality; companion via the shared replay theorem. |
| `query_isSome` | `(query p f a b).isSome ↔ Domain p a b`; executable guard/termination proof here, interpretation in companion. |
| `certify_checks` | Certificates produced on the domain pass replay and carry the same value as `query`. |
| `rootCount_eq`, `query_sign` | Count equals `Roots.card`; a singleton root set gives the evaluation sign; companion. |
| `query_congr` | Order-preserving field maps and transported endpoints preserve query results, including domain validity. |
| `query_backend_eq` | Optimized total backends agree on the whole `Option`; positive-rescaling correspondence translates certificates without requiring literal array equality. |
| `query_rat_eq` | Positive denominator clearing at rational coefficients and dyadic endpoints agrees, including `none`, with `ZPoly.tarskiQuery`; companion. |

For the last theorem choose positive integers `dP,dF` separately so that
`Pz=dP*P` and `Fz=dF*F` have integer coefficients. Nonzero roots,
squarefreeness, endpoint guards and evaluation signs are preserved. Moreover
`Fz*Pz' = dF*dP*(F*P')`, a positive scaling. Clear intermediate coefficient
and quotient denominators with positive multipliers, translate every initial,
three-term and terminal identity, and translate the guard and sign evidence.
Require both frontends' replay soundness and accepted-certificate transport;
identical producer certificates are not required. Zero polynomials can use
clearing factor one. A negative clearing factor is not an admissible adapter.
The integer frontend retains its public type, integer content removal and
exact dyadic Horner optimizations; it does not acquire a `Field Int` instance.

The foundation is imported once, through
[hex-real-roots-mathlib](../../HexRealRootsMathlib/SPEC/hex-real-roots-mathlib.md#sturm-tarski-correspondence).
The family audit at Mathlib revision
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa` does not supply the required generic
real-closed-field foundation or `IsRealClosed ℝ`. Required Tau Ceti imports
are polynomial IVT on `[a,b]`, Rolle between distinct roots, and the signed
remainder/Cauchy-index identity equating variation drop to the above finite
sum, including infinite endpoints, common factors and zero initial remainder;
root counting is its `F=1` specialization. These are planned imports requested
by [#10300](https://github.com/kim-em/hex-dev/issues/10300), not available
Lean theorem names or assumptions silently installed as axioms.

Hex locally proves ordinary polynomial correspondence, pseudo-division and
positive-scaling correspondence, literal replay soundness and integer
specialization in real-roots and its companion. That companion also proves
`IsRealClosed ℝ` from Mathlib's real square-root and polynomial order/IVT
results. HexSturm proves frontend guards, generic endpoint and denominator
adapters, and coefficient-evidence composition. Ambient real-closure existence
for arbitrary `K` is a separate Tau Ceti obligation consumed by
`hex-real-closure-mathlib`; this API's semantics are conditional on a supplied
`R,ι` until that obligation is discharged. It does not construct that field.

## Conformance and Phase-4 evidence

Follow [testing.md](../../SPEC/testing.md): every operation has typical, edge and
adversarial cases, with serialized coefficient contexts, seeds and expected
exact results. Integer/rational fixtures compare both frontends and
python-flint exact selected-root signs. Pin oracle versions and provenance;
never use printed decimals as expected signs. Lower-level pseudo-division,
gcd/xgcd identities and total-adapter agreement also have fixtures in hex-poly;
shared recurrence/replay cases live in hex-real-roots.

Required cases include:

- `P=x²-1` on `(-∞,+∞)`: queries of `1,-1,0,x,x-1` give `2,-2,0,0,-1`.
  The last has a proper common factor and a nonconstant terminal gcd.
- `F` divisible by `P`, high-degree `F` requiring initial reduction, and
  negative leading coefficients; leading-term cancellation between equal algebraic
  field elements with different stored representatives.
- Nonzero constant, zero and nonsquarefree `P`, each also with `F=0`, and
  integer `P=4*x`, which is squarefree over `ℚ` despite its content;
  equal/reversed intervals, all permitted infinity combinations, finite root
  endpoints, and a root only at the half-open API's upper endpoint.
- Zero intermediate endpoint signs, wrong initial products, nonpositive
  scales, altered quotients/parities/degree evidence, omitted terminal steps,
  oversized arrays, false squarefreeness witnesses and false coefficient signs.
- Incorrect supplied coefficient signs and equality claims,
  foreign-context/stale evidence, and positive versus negative denominator
  clearing. Reject cyclic certificate references at decoding.

When extension adapters exist, require downstream integration fixtures for the
corrected [de Moura–Passmore example](https://www.cl.cam.ac.uk/~gp351/infinitesimals.pdf)
`P=(εx²−1)(εx³−1)`: counts on the whole line and `(0,+∞)` are `3` and `2`;
the query of `P'''` on `(0,+∞)` is `0`, with opposite signs at the two
positive roots. This tests non-Archimedean queries without claiming that a
rational isolating interval can separate those roots. Include multiple
infinitesimal levels and nested coefficient certificates, supplied downstream
without a reverse import. Pin Z3's RCF API for these differential fixtures;
BKR/Thom reconstruction and the family's full `tower8` isolation benchmark
remain their owners' obligations.

The registered input families are `head-degree` (Chebyshev heads `T_n` with
query `1` on `(-2,2)`) and `query-degree` (fixed head `x²-2`, query `x^m+1`
on `(-2,2)`). They exercise normal degree descent and initial reduction,
respectively; the additional sweep dimensions below remain required.

Phase 4 measures domain/squarefree checks, initial reduction, subsequent chain
production, endpoint evaluation, coefficient signs and literal replay
separately. Sweep `degree P`, `degree F`, coefficient bit size, endpoint size,
chain length, extension depth and nested evidence size. With classical dense
arithmetic a conservative query bound after validation is
`O((degree F+1)*degree P + (degree P)^3)` ring operations for positive-degree
`P`, excluding coefficient-oracle cost; finite endpoint work is bounded by
the sum of chain lengths. This is not a bit-complexity promise. Record peak
coefficient sizes, gcd work, coefficient calls and certificate bytes; use the
actual polynomial lengths and certificate sizes for replay costs.

Compare the total rational adapter with the optimized integer/dyadic backend
on identical queries; correctness agreement is gating. Pinned python-flint
and Z3 end-to-end comparisons are informational where they expose comparable
queries; record any lack of a matching query surface rather than timing root
isolation as if it were query evaluation. No external system supplies a
comparable Lean kernel proof surface. Replay uses the companion's
[fresh-module proof evidence](../../SPEC/benchmarking.md#fresh-module-proof-evidence)
track, with ordinary kernel checking and axiom inspection; executable benches
remain Mathlib-free. Include valid and rejected nested replay probes and one
representative profile attributing arithmetic versus coefficient-sign cost.
Follow the shared-host fixed trial-major and adjacent alternating `AB`/`BA`
schedules, retain every completed sample, and allow at most one unchanged
rerun of an inconclusive result. No performance measurements or phase
advancement are claimed by this design document.
