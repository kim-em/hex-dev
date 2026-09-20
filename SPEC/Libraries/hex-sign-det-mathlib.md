# hex-sign-det-mathlib

Exact sign-table semantics, literal replay soundness and Thom root identity
and ordering for [hex-sign-det](hex-sign-det.md).

## Status, scope and dependencies

This is a planned companion in the
[real-closure family](../future-work.md#real-closures-of-ordered-fields).
Names and formulas below are required statement shapes, not existing or
checked Lean declarations. This SPEC registers no target, phase or release.

`HexSignDetMathlib`, in namespace `Hex.SignDet`, imports `HexSignDet`,
`HexSturmMathlib`, `HexPolyMathlib`, `HexMatrixMathlib`,
`HexRowReduceMathlib` and `HexRankMathlib`, plus the Tau Ceti foundations
specified below. [hex-sturm-mathlib](hex-sturm-mathlib.md) supplies query,
domain and coefficient-evidence correspondence through the shared
hex-real-roots-mathlib primitive. Do not duplicate Sturm–Tarski here.
The matrix companions supply representation, rank and rational linear
algebra; their computational libraries remain Mathlib-free.

No computational library imports a companion or Tau Ceti. Existing
polynomial, rational-function, real-root, interval and real-algebraic
libraries remain inputs with no reverse family dependency. Extension
adapters supply coefficient laws through the lower-level interfaces;
this companion does not import tower implementations. Tower field laws,
dynamic splitting of all live elements, multiplicities, real-closure
existence and sector realization belong to hex-real-closure-mathlib.
CAD, coverings, tactic integration and nonstandard-analysis claims are
outside this library.

## Semantic parameters and representations

Every root theorem quantifies over arbitrary `K,R` with

```text
[Field K] [LinearOrder K] [IsStrictOrderedRing K]
[Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
ι : K →+* R
hι : StrictMono ι
```

The field homomorphism is injective and `hι` preserves order. Neither `K`
real closed nor `R=ℝ` is required. No Archimedean, metric, ordinary
connectedness or rational-separation hypothesis is allowed. Existence of
`R,ι` is a separate family foundation; these statements are conditional on
that supplied model.

Raw coefficients `C` have a context `ctx`, a validity predicate and
`denote : {c : C // Valid ctx c} → K`. The interpretation need not be
injective. Consume the shared
[fallible operation records](../../HexPoly/SPEC/hex-poly.md#fallible-coefficient-operations)
and their laws for successful arithmetic, sign/zero decisions, checked
inversion and accepted evidence. Interpret valid coefficient arrays as
polynomials over `K`, then map along `ι`; below `P,Qᵢ,H` denote those
polynomials over `R`. Semantic degree evidence, derivative construction,
products, equality and endpoint comparisons must agree with this map.
Stored length and structural equality are not semantic degree or equality.

Alongside the imported foundations and query correspondence below, soundness
needs only laws for successful fallible operations and evidence.
Totality additionally needs complete executable decisions and evidence
production on the semantic carrier. The total adapter must identify its
Lean-core field/order operations with the Mathlib ones. Never install a
field or decidable semantic equality on raw representatives because their
bounded operations sometimes succeed. For selected-root coefficients,
equality is equality of evaluation at that root; total field laws belong
on the semantic quotient with lawful executable operations. In particular,
squarefree reducible `p` does not make `K[X]/(p)` a field. Constructing that
selected-root quotient and its field operations remains the tower
companion's responsibility.

Evidence binds context, embedding, operand/result literals and claims.
Changing a defining polynomial or coefficient context requires checked
transport preserving denotation, including selected-root and oracle
identities. A runtime sign callback alone is not evidence. Nested replay
must be finite and acyclic, with lower-level coefficient evidence justified
before its use in a table theorem.

## Domains, counts and literal data

Consume hex-sturm's `Domain(P;I)`: nonzero squarefree `P`, an open interval
`I=(a,b)` with `a<b`, endpoints in the embedded coefficient field or `±∞`,
and no root at either finite endpoint. Let `Z=Roots(P;I)` be its finite
set of distinct roots. Its membership predicate is evaluation zero and
strict endpoint inequalities; `#Z≤P.natDegree`. Root zero is included.

For an ordered list `Q` of length `s`, put `Sign={-1,0,1}` and define

```text
signs(Q,α)[i] = sgn(Qᵢ.eval α),
c(σ) = #{α ∈ Z | signs(Q,α)=σ} : Nat,       σ ∈ Signˢ.
Support(Q,Z,S) := ∀ α∈Z, signs(Q,α)∈S.
```

`S` is a finite set of candidate sign vectors, serialized as a distinct
ordered array. It may contain unrealized conditions. A complete sparse
`SignTable` retains exactly the positive counts, with distinct well-shaped
rows and total lookup zero on omitted conditions. Its semantic contract is
`∀ σ, T.count σ=c(σ)`, so every omitted condition is unrealizable,
`∑ T.count=#Z`, and there are at most `#Z` rows. Serialization order on
sign vectors is distinct from root order.

Duplicate, zero and constant query polynomials are valid indexed queries.
For `s=0` the only condition is the empty vector, whose count is `#Z`.
A nonzero constant head or root-free domain gives the empty sparse table.
Check all contexts and domain guards before any empty/zero shortcut:
zero/nonsquarefree heads, equal/reversed intervals and root endpoints are
invalid even with no queries.

A table replay carries bound input literals, complete child tables, moment
exponents, query evidence, count vectors, selected row/column indices,
integer inverse witnesses and pruning evidence as specified by hex-sign-det.
Counts are natural numbers; rational solver output requires exact
integrality and nonnegativity before conversion. Check lengths, distinct
columns, exponent ranges and every index before arithmetic or allocation.

## Imported foundations and ownership

Follow the [family audit and ownership table](../future-work.md#proof-ownership-and-public-surface)
at Mathlib revision `1cf325a0cf67aca2b04d76b5380ff6a9e410aefa` in
[the manifest](../../lake-manifest.json). `IsRealClosed` and
`IsRealClosed.of_linearOrderedField` exist; the generic Thom, BKR and
Sturm–Tarski foundations below are planned imports requested by
[#10300](https://github.com/kim-em/hex-dev/issues/10300), not available
Lean declaration names or permitted axioms. The pin supplies neither
ordered real-closure existence nor `IsRealClosed ℝ`. The latter is owned
by hex-real-roots-mathlib; the former by Tau Ceti for the real-closure
companion. Hex already has
[`IsRealClosed RealAlgebraicNumber`](../../HexRealAlgebraicMathlib/RealClosed.lean)
for rational-base semantics, without making that downstream implementation
an import here.

The fallible `CoeffOps`/`FieldOps` and semantic-degree routines are planned
hex-poly infrastructure, not capabilities of its existing total field API.
The shared query/replay implementation belongs to hex-real-roots and the
field frontend to hex-sturm; their planned companions must establish query
and evidence soundness before it can be consumed here. This companion owns
the missing literal matrix interpretation, support induction, descriptor
completion and re-encoding correspondence specified below. Writing this SPEC
does not assume those implementations or Tau Ceti proofs have landed.

### Actual-count moment identity

Import the following abstract identity for finite `Q` and `Z` as above.
For `e∈{0,1,2}ˢ`, define

```text
Fₑ = ∏ᵢ Qᵢ^eᵢ,
t[e] = ∑ α∈Z, sgn(Fₑ.eval α) : Int,
M[e,σ] = ∏ᵢ (σᵢ : Int)^eᵢ,       0^0=1.
t[e] = ∑ σ∈Signˢ, M[e,σ] * (c(σ) : Int).
```

In particular, for **any** selected rows and candidate set `S` with
`Support(Q,Z,S)`, the restricted actual-count vector satisfies `M*c=t`.
There is no restriction to invertible matrices in this identity. Include
empty lists/products, empty root sets, zero query values and common roots.
Actual counts are defined from `Z`, independently of the proposed solution.

### Recursive support-preserving BKR reduction

Import abstract correctness of the finite recursive reduction with these
explicit premises and conclusions:

- The empty-list support is `{()}` and singleton support is all three
  signs. Both cover every root's condition.
- Complete child supports for ordered sublists `Q₁,Q₂` on the **same**
  root set give support `S₁×S₂` for their concatenation.
- Given complete candidate support, actual moments, an injective square
  moment matrix and a solution `v` of `M*v=t`, the solution equals the
  restricted actual counts. Removing exactly its zero columns preserves
  support. All positive columns remain.
- Induction over the finite split tree yields exact counts and complete
  support at every retained node, not only at the root.

Producer completeness additionally uses invertibility of the tensor product
of the children's retained matrices, giving a parent system with concatenated
exponent rows. Restricting an invertible matrix to the positive columns
preserves column independence; a square row basis then exists and retains
the corresponding moment equations. These existence facts justify production
of the next certificate. Checker soundness instead uses each supplied
inverse identity directly. The certificate format requires square matrices
and validation of the retained row basis even though count uniqueness alone
needs only a left inverse. A failed retained-basis check is `rejected`; a
successful check prepares the next node without adding a root-count premise.

These are abstract mathematical premises on finite matrices and counts,
not assumptions that an untrusted replay satisfies them. Any additional
pre-solve pruning rule must have a proved implication from complete input
support and explicit reduction premises to complete retained support;
local replay must discharge every premise. A final reduced solve cannot
justify its own discarded columns. Row-basis existence uses ordinary
linear algebra from the matrix companions, not another real-algebra
foundation. Hex proves the elementary root restriction to child sign
vectors and the literal-to-abstract recursion correspondence locally,
consuming this abstract reduction theorem rather than redeveloping BKR.

### Thom injectivity and order

For nonzero `P` of degree `n>0`, define the full encoding of a root `α` by
`θP(α)[j]=sgn(P⁽ʲ⁾.eval α)` for `1≤j≤n`, using formal iterated derivatives.
Import injectivity of `θP` on roots of `P`. Also import the order rule:
for distinct roots `α,β`, let `k` be the largest index with unequal signs.
Then `k<n`, the common sign `u` at `k+1` is nonzero, and

```text
α<β ↔ (u=+1 ∧ θP(α)[k]<θP(β)[k]) ∨
       (u=-1 ∧ θP(β)[k]<θP(α)[k]),
```

where sign order is `-1<0<1`. Equal full encodings are equivalent to equal
roots. The highest derivative sign is retained even though it is constant.
These statements concern realized encodings of the same polynomial;
Thom injectivity does not supply existence of a root for an arbitrary vector.

## Local checker correspondence

Prove `Replay.check_sound` by induction over the actual accepted replay.
Acceptance includes the domain and coefficient guards; no producer-success
hypothesis is needed. The proof must follow this order at each node:

1. Establish support before solving. At leaves use the full ternary set
   (or empty-vector set). At a combination, invoke child soundness and
   the root-restriction lemma, checking exact query-list concatenation,
   candidate Cartesian product, context, head and interval agreement.
2. Interpret every moment through hex-sturm-mathlib's
   `Replay.check_sound`/`queryPrepared_sound`. Validate factor indices and
   exponents. For reduced moments, check each identity
   `u*(Gprev*F)=B*P+v*Gnext`, with `u,v>0` and `Gnext=0` or
   `degree Gnext<degree P`, where `F` is the next certified query factor.
   Consume HexSignDet's conditional positive-scaling sign lemma and
   discharge its coefficient laws in the ambient field; induction from
   `Gprev=1` identifies the final query with `Fₑ`'s moment.
   It need not preserve values. Constants use certified zero root count
   rather than a degree-negative remainder. No expanded high-degree
   product is needed to replay a reduction chain.
3. Map the literal matrix and vector into integer/rational matrices,
   respecting all row/column permutations. Check `A*M=d*Id`, `d≠0`,
   and `M*v=t`. The imported moment identity gives `M*c=t` on the
   already established complete support. Hence `d*(v-c)=0` and `v=c`.
   The existing [RankCert](../../HexRank/Cert.lean) checks a right-inverse
   identity `B*adj=denom*Id` on a selected minor, as well as a rank
   factorization. Prove its permutation and left-inverse adapter or
   check `A*M=d*Id` directly; never identify the formats by fiat.
4. Apply abstract reduction correctness with these discharged premises.
   Remove only certified zero counts, retain every positive column and
   check the selected square row basis for reuse by the parent. Establish
   both exact retained counts and support for the next step.

An empty candidate set requires independent `#Z=0` evidence, from an
accepted complete child/leaf or a root-count query. The `0×0` system is
vacuous. Neither inverse identities nor agreement of total counts replaces
support induction. The computational library proves finite checks and
conditional invariants; this companion supplies their semantic premises.
No theorem may depend on unfinished computational proofs across the boundary.

## Descriptors, completion and changed polynomials

A raw descriptor `d` contains its coefficient context, `p,I`, distinct
indices `J⊆{1,…,n}` and the corresponding signs `τ`, where
`n=P.natDegree` is the checked semantic degree, not stored array length. Define

```text
Selected(d) = {α∈Roots(P;I) | ∀ j∈J, sgn(P⁽ʲ⁾.eval α)=τ[j]},
Valid(d) := valid inputs ∧ Domain(P;I) ∧ wellFormed(J,τ) ∧
            Selected(d).card=1.
```

Define `root(d,hd) : R` only for `hd : Valid(d)`, as the unique selected
root; there is no default root for invalid syntax. Prove its membership,
uniqueness and independence of the validity proof. Validation's complete
table on the selected derivatives equates the claimed count with this
cardinality. Count zero and count greater than one are distinct invalid
cases. Constants have no valid descriptors. Empty `J` is valid exactly
when the interval contains one root; it does not mean missing signs are zero.

Completion determines all formal derivatives, filters by the original
constraints and returns the unique matching full encoding with count one.
Prove equality of selected roots and every returned derivative sign.
**Complete partial descriptors before applying Thom order.** A sign-at-root
call uses joint sign determination on the selected derivatives and query
`q`; filtering to the descriptor's count-one condition proves the returned
sign is `sgn(q.eval root(d))`. A singleton-interval Tarski shortcut needs
`#Roots(P;I)=1`, not merely `Selected(d).card=1`.

For identical polynomial literals in the same context, completed encodings
compare by the imported rule, even across different valid intervals. For
other literals, including semantically equal arrays or scalar multiples,
use checked joint re-encoding. Construct a squarefree union polynomial
`U=P₁*P₂/gcd(P₁,P₂)`, up to a certified nonzero scalar, and prove its root
set is the union. Check gcd/exact-division identities and squarefreeness;
a product with common factors is not an admissible head.

On the whole line determine signs of all derivatives of `U`, both old
heads, their selected derivatives and `X-a,X-b` for every finite old
endpoint. Filter for the old head zero, descriptor signs and strict
endpoint signs. Prove each filtered set is precisely `Selected(dᵢ)`, so
its unique full `U` encoding denotes the same root. The whole-line domain
avoids an old endpoint being a root of the other head. Comparison of the
two new encodings then establishes all three order cases.

The separate `reencodeWith d h I'` contract requires a valid target domain
and proves that the selected source root belongs to `Roots(H;I')`, where
`H` interprets the target `h`. Use the source head `P` on its interval
with queries for its selected derivatives, `H`, all derivatives of `H`
and target endpoint polynomials. Filter to the source descriptor's count-one
condition, then check that the target head sign is zero and the finite target
endpoint signs are strictly inside `I'`. This establishes target membership
and the full encoding without a union-polynomial gcd. On success the new full descriptor has the same
root and derivative signs of the target `h`, not reused signs of `P`.
Failure of target membership is invalid; uncertainty is exhaustion.
This is the bridge used when a dynamic split changes the defining
polynomial. Preserving all live tower values under that split remains a
downstream obligation, not a field law on descriptor syntax.

## Headline correspondence and completeness

These names refine the computational SPEC in `Hex.SignDet`. Suppress
residual budget/counter fields in the formulas, but retain them in the
actual bounded API. All conclusions use the semantic parameters and law
packages above, universally in the supplied `R,ι,hι`.

| Theorem | Required statement |
| --- | --- |
| `determine_correct` | `determineWith … = ok T cert` implies valid inputs, domain and `∀ σ, T.count σ=c(σ)`, including omitted conditions. |
| `Replay.check_sound` | An accepted literal table/descriptor/operation replay implies its entire corresponding postcondition, including complete support and guards, without trusting the producer. Boolean `check=true` implies acceptance. |
| `validate_correct` | Successful `validateWith d` implies `Valid(d)` and equality of its certified count with `Selected(d).card`. For the total adapter validation succeeds iff `Valid(d)`. |
| `complete_correct` | Successful completion returns a valid full descriptor with the same root and all its formal derivative signs. |
| `signAt_correct` | Successful `signAtWith d q` implies valid `d,q` and result `sgn(q.eval root(d))`. |
| `compare_correct` | Successful comparison implies valid compatible inputs and returns `lt`, `eq`, `gt` iff the respective relation holds between selected roots, for same or different heads. |
| `reencode_correct` | Successful re-encoding implies source and target validity, target membership and equality of selected roots. |
| `roots_correct` | A successful list contains valid full descriptors, their roots are strictly increasing, and every `α∈Z` occurs exactly once. Thus its length is `#Z`; it is empty exactly when `Z` is empty. |
| `determine_invalid`, `descriptor_invalid` | An `invalid` result establishes the operation-specific invalid-input predicate below; a failed internal invariant is never a proof of invalid input. |
| `determine_isSome` | Under total-adapter completeness, `(determine …).isSome` iff all inputs are valid and the domain holds. Each other total operation has the corresponding equivalence below. |
| `result_congr` | Denotation-preserving coefficient/context and descriptor transports preserve completed semantic results. Transfer of success needs completeness and sufficient budgets; bounded outcome tags need not coincide. |

Enumeration completeness follows by applying table completeness to all
`n` derivatives: every root has an encoding, injectivity makes each positive
count one, and Thom comparison sorts these encodings. This proof uses no
numerical isolation. Rational specialization must agree with the existing
hex-real-algebraic root identity, signs and order under their embeddings;
put integration tests downstream so this obligation creates no reverse import.

## Failure and termination

Preserve the common `PolyOps.Result` and `CheckResult` contracts:

| Outcome | Meaning |
| --- | --- |
| `ok value evidence` / `accepted` | All relevant guards and evidence checks succeeded and the semantic postcondition holds. |
| `invalid reason` | A certified invalid context/representation or failure of the operation's mathematical input predicate. |
| `exhausted reason` | Work, arithmetic, allocation or evidence budget exhausted, or coefficient equality/sign remains unresolved. No invalidity, zero, root, count or equality is asserted. |
| `rejected reason` | Supplied evidence is malformed/false, or an internal invariant/replay check fails. This is not mathematical nonexistence. |

The input predicates are: valid coefficients and `Domain` for `determine`
and `roots`; `Valid(d)` for `validate` and `complete`; additionally a valid
query for `signAt`; two valid descriptors in a common compatible context
(with checked transport when needed) for `compare`; and a valid source,
valid target domain and selected-root target membership for `reencode`.
These define exactly the `none` cases of total `Option` forms. Malformed
indices/sign lengths, unrealized or ambiguous descriptors and incompatible
contexts without transport fail the corresponding predicate. Invalidity
checks can themselves exhaust. Diagnostics/first-error precedence are not
semantic guarantees. Singular matrices or negative/nonintegral solved counts
on validated input are internal errors, not an invalid mathematical domain.

All bounded producers and checkers terminate on arbitrary raw input,
including zero fuel and malformed evidence. Recursion splits nonempty query
lists strictly; empty/singleton bases are explicit. Derivative, product,
row-selection, sorting and index loops have finite length/degree bounds.
Gcd/division and Tarski calls inherit semantic-degree descent and terminating
callbacks. No loop searches indefinitely for a rational separator. Fuel zero
permits success only after all required checks have completed.

Replay checks supplied finite identities and signs; it does not rerun row
search, gcd search, isolation or coefficient refinement. Validate sizes and
references before allocation; reject cyclic/forward references. Same-level
table recursion decreases query-list length and nested coefficient evidence
refers to strictly lower levels. One budget covers all nodes, edges, bytes,
operand bit sizes and arithmetic, without resets in children. Acceptance
caches bind exact literals and context. With sharing, charge every distinct
checked node plus references; without sharing, charge each occurrence.

The computational [production and checking bounds](hex-sign-det.md#production-and-checking-bounds)
apply: `2s-1` nodes for `s>0`, retained support at most `N=#Z`, combination
dimension at most `N²`, and leaf dimension three. For candidate dimension
`r`, inverse checking uses `O(r³)` integer operations and `M*c=t` uses
`O(r²)`; constructing entries additionally charges the sign-vector length.
These are operation counts, not bit complexity. Raw leading-zero storage
and coefficient work must also be charged. Nested unshared replay obeys
`Tℓ≤Tℓ,local+bℓ*max Tℓ₋₁` and the corresponding size recurrence, where
`bℓ` bounds lower-level subcertificates. Top-matrix size alone is insufficient.

Total forms require lawful total coefficient decisions, complete evidence
producers and proof that computed finite work bounds suffice, including row
basis construction and every nested call. Eventual bounded success on valid
input additionally quantifies over sufficient limits for every child.
Sound accepted results need none of these completeness assumptions.
Increasing fuel alone does not resolve an unknown transcendental identity;
no totality claim is made for such incomplete adapters.

## Conformance and Phase-4 evidence

Follow [testing](../testing.md) and the computational owner's exact fixtures.
Bridge probes instantiate universal correspondence and check ordinary kernel
replay plus final theorem axiom sets. Planned foundations must stay visibly
separate from existing declarations; neither `axiom`, `native_decide` nor
unfinished core proofs may substitute for the correspondence.

Required positive and adversarial cases include:

- `P=X²-1`, `Q=[X,X-1]`: exactly `(-1,-1)` and `(1,0)`, count one each.
  Include repeated/zero/constant queries, empty query lists, `P=X`, nonzero
  constant heads and `P=X²+1`. Test invalid heads and endpoints even on
  shortcut branches and raw nonzero coefficients denoting zero.
- Omitted support with matching totals: for `P=X²-1`, `Q=[X]`, candidate
  `{+1}`, row `{0}`, count/moment `2`, `M=A=[1]`, `d=1` satisfies both
  matrix identities and the total. Reject the absent support derivation.
  Also reject empty support without zero-root evidence, altered child
  products/domains/contexts, missing or reordered query positions,
  unjustified zero pruning and deletion of positive columns.
- Wrong exponent/`0^0`, row permutations, dimensions, inverse witnesses,
  negative/nonintegral counts, bad reduced-product identities and zero or
  negative scales. Reduced and unreduced moments must agree semantically.
- Full unrealized encodings, partial encodings selecting zero or two roots,
  valid empty constraints on singleton intervals and invalid empty ones on
  larger intervals. For `P=X³-X`, roots `-1,0` have vectors `(+,-,+)` and
  `(-,0,+)`: lexicographic comparison is wrong. Include negative leading
  coefficients and completion before comparison.
- `X-1` and `X-2` have equal derivative vectors but different roots;
  `X²-2` and `(X²-2)(X-3)` share roots and require gcd removal.
  Include overlapping/disjoint descriptor intervals, endpoints that are
  roots only of the other head, distinct raw literals denoting equal
  polynomials, scalar multiples, successful changed-head re-encoding and
  failed target membership. Test stale derivative/context evidence.
- Exhaustion at every stage, truncated/oversized/cyclic evidence, missing
  coefficient signs and nested valid/rejected certificates. Reject forged
  coefficient evidence even when matrix arithmetic is internally consistent.

Rational fixtures use pinned python-flint exact signs and the existing
hex-real-algebraic API; small lists compare recursive BKR with the full
ternary solver. Record oracle versions, seeds and provenance. Downstream
extension fixtures use pinned Z3 RCF and the corrected
[de Moura–Passmore example](https://www.cl.cam.ac.uk/~gp351/infinitesimals.pdf)
`P=(εX²−1)(εX³−1)`. For positive infinitesimal `ε`, the ordered roots are
`−ε^(-1/2), ε^(-1/3), ε^(-1/2)`; on `(0,+∞)`, `Q=[P''']` has signs
`-1,+1` each of count one. Complete those partial descriptors and compare
them without a rational separator. An empty constraint there is invalid.
Use multiple infinitesimal levels and nested evidence without importing
towers here. Decimal approximations and a mere `0<ε<1` hypothesis do not
establish these infinitesimal claims.

Phase 4 uses [fresh-module proof evidence](../benchmarking.md#fresh-module-proof-evidence):
measure fresh proof modules with warm imports and ordinary kernel checking;
record source/toolchain hashes, axiom sets, proof artifact/certificate sizes,
wall time and host activity. Sweep degree, query count, realized support,
coefficient/witness bits, extension depth and nested evidence size. Include
valid, rejected and exhausted probes, completion, sign-at-root and expensive
cross-polynomial re-encoding. Measure support/pruning proof cost separately
from moment interpretation, matrix replay and nested coefficient evidence.

Compare reduced/full small-case replay, reduced/unreduced moment replay and
same-head/joint-encoding paths on matched workloads. Runtime production,
Tarski queries, coefficient signs, matrix solving and gcd work are measured
by Mathlib-free benches owned by the computational libraries; no ordinary
bench imports this companion. Record matrix dimensions, query counts, DAG
nodes/edges, peak bits and allocation. External CAS time is not a proof-checking
baseline. Include one representative attribution profile. Use fixed
trial-major schedules, adjacent alternating `AB`/`BA` comparisons, one
selected CPU where supported, retain every completed shared-host sample and
allow at most one unchanged rerun after an inconclusive result. The family's
`tower8` isolation and clean/eager normalization ablation remain downstream
integration requirements. This SPEC supplies evidence requirements, not
measurements or phase advancement.
