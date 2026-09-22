# hex-sign-det

BKR univariate sign determination and single-polynomial Thom root descriptors,
with complete sign tables and literal replay certificates.

## Status and placement

This development computational library belongs to the
[real-closure family](../../SPEC/future-work.md#real-closures-of-ordered-fields).
The [README](../README.md) records the implemented replay surface. API names
and theorem statements below remain required shapes unless implemented there;
registration does not claim phase completion. The combined computational and
companion assignment is [#10377](https://github.com/kim-em/hex-dev/issues/10377).

`HexSignDet`, in namespace `Hex.SignDet`, depends on `HexSturm`, `HexPoly`,
`HexMatrix`, `HexRowReduce` and `HexRank`. Matrix construction and exact
rational solving reuse HexMatrix and HexRowReduce; row selection and rank
certificates reuse HexRank. BKR-specific support and descriptor certificates
live here.
`HexSignDetMathlib` imports this library, `HexSturmMathlib`,
`HexPolyMathlib`, `HexMatrixMathlib`, `HexRowReduceMathlib` and
`HexRankMathlib`, with Tau Ceti foundations imported only in companions. These dependencies are acyclic.

[hex-sturm](../../SPEC/Libraries/hex-sturm.md) owns ordered-field Tarski queries, domain guards and
exact coefficient arithmetic over the one shared kernel in hex-real-roots.
It has consumers needing no sign matrix, and must not import this library.
Existing polynomial, rational-function and real-algebraic libraries
remain inputs with no reverse family imports. In particular this design does
not change `hex-real-algebraic` into a generic tower implementation.

This library owns complete sign tables, descriptors, identity, order, sign
at a selected root and their replays. `hex-real-closure` owns tower contexts,
coefficient embeddings, dynamic splitting and transport, squarefree
factorization with multiplicities, base enlargement and section/sector sample
construction. Downstream CAD/coverings clients consume that tower interface;
no cell representation, multivariate BKR quantifier elimination, nonstandard
analysis tactic, or sector-sampling algorithm is specified here.

## Coefficients, domains and table semantics

Use `DensePoly E` and the ordinary total operations/sign of the shared
[execution contract](../../SPEC/real-closure-execution.md). A canonical ordered field
is a specialization. Noncanonical selected-root coefficients have structural
equality and canonical zero, not a fabricated `Field` instance. The companion
interprets them in the ordered field `K`, preserving operations/sign and
reflecting zero. This preserves polynomial degree despite noninjectivity.

Signs are integers `-1,0,1`; validate literal codes. Semantic identities in
replay use zero differences. Structural equality is a sufficient fast path
only. There is no downstream RCF sign type or coefficient-operation record.
Transcendental sign requires its caller progress witness; finite attempts
cannot substitute for a total coefficient sign.

For mathematical statements, fix an ordered real closed field `R` and an
order-preserving field embedding `ι : K →+* R`. In the companion this means
`[Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]`.
Write `P,Qᵢ` for polynomials mapped coefficientwise to `R`. The statements are
universal in `R,ι`; existence of such an extension is a separate family
foundation, not an executable assumption or an available instance on the pin.

`Domain p I` is hex-sturm's prepared domain: `p` is semantically nonzero and
squarefree, `I=(a,b)` has `a<b`, and finite endpoints are not roots of `p`.
Endpoints are elements of `K` or `±∞`. Let `Z` be the finite set
of distinct roots of `P` in this open interval. The query list `Q` is ordered
and has length `s`; duplicate, constant and zero polynomials are allowed.
A sign condition is a length-`s` vector in `Sign={-1,0,1}`. Define

```text
count(σ) = #{ α ∈ Z | ∀ i < s, sign(Qᵢ(α)) = σᵢ } : Nat.
```

A `SignTable` is opaque, with a sparse array of distinct conditions and
strictly positive `Nat` counts. Its total lookup returns zero for omitted
conditions. Completeness means this lookup equals `count(σ)` for **every**
condition, including omitted ones. Consequently the sum is `#Z ≤ degree P`,
and there are at most `#Z` output rows. Sorting table rows in the fixed order
`-1<0<1` only makes serialization deterministic; it is not root ordering.
Certificate count vectors include zeros and are nonnegative integers; exact
rational intermediate solutions must be proved integral and nonnegative
before conversion. Never round, truncate or clamp them.

Nonzero constant `p`, or any valid interval with no roots, gives an empty
sparse table and zero lookup everywhere. For `s=0`, the full candidate set has
one empty condition, with count `#Z`; the sparse output contains it exactly
when `#Z>0`. Its moment product is `1`. A root at zero is an ordinary distinct
root, not removed here. Zero or nonsquarefree `p`, reversed/equal endpoints
and finite root endpoints are invalid even when `Q` is empty or zero. Check
the domain before taking these shortcuts.

Natural casts, powers, derivative coefficients and finite comparisons use
the shared operation/sign interface explicitly. Monicity, coprimality and
polynomial replay equations are statements under interpretation; a computed
gcd need not be literally the polynomial one. The matrix entries and counts
are ordinary integers/rationals, so their matrix identities retain literal
exact equality. Context refinement changes the binding of root descriptors
and child queries even when their serialized polynomial operands coincide.
Re-encode/transport with checked evidence; do not reuse a stale support table.

## Moments and complete support certificates

Fix the row/column orders explicitly in every certificate. For exponent
vectors `e ∈ {0,1,2}ˢ` and candidate conditions `σ`, use

```text
Fₑ = ∏ᵢ Qᵢ^eᵢ,
t[e] = TaQ(Fₑ,P;I) : Int,
M[e,σ] = ∏ᵢ (σᵢ : Int)^eᵢ,     with 0^0 = 1,
M * c = t.
```

Products and their coefficient interpretations are checked, not merely named
by a hash. A reduced moment uses the certified reduction below to establish
the same signs on roots, rather than claiming literal equality to `Fₑ`.
Every moment uses hex-sturm's prepared-query API with exactly the same `p`,
interval and coefficient field. A requested BKR certificate includes its
Tarski result replays; ordinary arithmetic does not return evidence records. Common
roots with `Fₑ` are allowed and contribute zero. Do not substitute derivative
root counts for general Tarski queries.

For positive-degree `p`, the producer can reduce each query polynomial and
subsequent product modulo `p`, keeping moment representatives of degree
less than `n`. Record each reduction as

```text
u*(Gprev*H) = B*p + v*Gnext,     u>0, v>0,
Gnext=0 or degree Gnext<n.
```

Here `H` is the next query factor (each occurring `eᵢ` times), or its
previously certified reduction. Start from `Gprev=1`; a query-polynomial
reduction is the same identity with that initial value. At every root of
`p`, the signs of `Gnext` and `Gprev*H` agree. Induction therefore identifies
the final Tarski query with the specified moment, even though positive
scalings need not preserve the polynomial's value. Exact field remainders
are the special case `u=v=1`. Positive pseudo-remainders reuse the shared
ordered-domain routines without forcing inversion or monic normalization. Replay
checks all intermediate identities, positive scales, degree bounds, factor
indices and exponents. A negative or unverified scale is not admissible.
No unreduced product must be expanded to check this chain. Nonzero constant
`p` uses its certified zero root count instead of degree-`<0` remainders.

For one polynomial, rows `0,1,2` and columns `-1,0,1` give

```text
M = [ 1  1  1 ]
    [-1  0  1 ]
    [ 1  0  1 ].
```

The full matrix is its tensor power (the empty-list matrix is `[1]`). A square
system of dimension `r` carries an integer matrix `A` and integer `d≠0` with
`A*M=d*Id`. Check this equality and literal `M*c=t` by integer arithmetic.
This establishes uniqueness over the rationals, hence over integer counts.
Reuse `Hex.Matrix.RankCert` and `checkRank` from
[hex-rank](../../HexRank/Cert.lean) for row selection and nonsingular minors.
The existing identity is `B*adj=denom*Id`, a right inverse, and its row/column
indices may be permuted. The adapter must prove the permutation and
left-inverse translation to `A*M=d*Id` (or check that identity directly);
these formats are not literally identical. Rank certificates certify only
linear algebra, never the completeness of sign support.
Another witness format needs a proved equivalent checker. Matrix dimensions,
indices, exponent ranges, distinct columns and exact count casts are checked
before use. A claimed nonsingular submatrix alone establishes no completeness.

The producer uses a balanced binary split of the query list. Each replay node
binds the exact ordered sublist, root domain and context, and carries:

1. **Leaf support:** the full ternary support and three query replays. An
   empty-list root uses the one-condition system and the query of `1`.
2. **Internal-node support:** accepted complete child tables. Every realized
   parent condition restricts to realized child conditions, hence lies in their
   Cartesian product, in concatenation order. Carry the child certificates
   and verify that the candidate columns are precisely that product. Check
   that the parent's ordered query list is exactly the concatenation of the
   child lists, and that both children's `p`, interval and coefficient context
   are identical to the parent's. Duplicate query polynomials remain separate
   indexed positions; no position may be omitted or reordered.
3. **Solve (every node):** moment rows, their query replays, `M*c=t`,
   nonnegative integral counts and the invertibility witness on this complete candidate support.
4. **Reduction (every node):** remove columns whose counts have just been
   certified zero. Retain all positive columns. Select independent moment rows on the retained
   columns and certify the resulting square matrix's invertibility for reuse
   by a parent. Row selection does not delete any positive column.

A concrete finite construction uses the Cartesian product of the children's
retained exponent rows at combination. Its candidate matrix is the tensor
product of their invertible matrices, hence is invertible. After zero-column
removal, the remaining columns are independent, so exact row selection can
choose a square invertible minor. Query values for retained rows are reused;
removed zero columns contribute nothing to their equations. This supplies a
complete producer without enumerating all `3^s` conditions. It also specifies the row-rank existence obligation.

Any optimization that prunes *before* this solve must provide certified zero
counts from an already complete table or a checked instance of a proved
support-preserving reduction. A reduction rule has premises establishing
`∀ α∈Z, signs(Q,α)∈S` and a conclusion establishing membership in its retained
`S'`, with replay evidence for every premise. The final system cannot justify
its own omitted columns. A generic claim that a named BKR optimization is
correct is not a replay. The recursive support derivation is mandatory even
if the reduced system is invertible and its proposed counts sum to `#Z`.

An empty support must have independent evidence of `#Z=0`, from a complete
child/leaf table or the root-count query. Its `0×0` equations are vacuous and
cannot supply that evidence. The full ternary solver is a small-case reference
and conformance oracle; it is not the production fallback for large `s`.

## Thom descriptors and selected-root operations

For `n=degree P>0`, a raw `Descriptor` contains the coefficient context, `p`,
`I`, and an ordered list of distinct derivative indices `J ⊆ {1,…,n}` with
signs `τ`. `p=0` is implicit at the selected root; it is not a derivative
slot. A full descriptor uses every index `1,…,n`; a partial descriptor may
use none. Derivatives mean formal iterated derivatives, without normalization
or scaling that would change their signs. Keep index `n` even though its sign
is constant across roots: it supplies the last sign used by Thom order.
Validity is exactly

```text
Valid(d) := Domain d.p d.I ∧ wellFormed(d.J,d.τ) ∧
  ∃! α ∈ Roots(P;I), ∀ j ∈ J, sign(P⁽ʲ⁾(α)) = τ[j].
```

Here `∃! α ∈ Roots` means exactly one element of the root set satisfies the
constraints. Validity requires existence even for a full encoding: Thom
injectivity alone gives only at most one root. Validate by a complete sign
table on the selected derivatives and a matching-condition count of one.
No matching root and more than one matching root are both invalid descriptors,
with different diagnostic reasons. Constants have no valid descriptor.
Repeated/out-of-range indices or mismatched sign lengths are malformed.

`complete` computes a table on all derivatives, filters by the partial
constraints and uses validity to obtain exactly one full encoding with count
one. It returns that encoding and identity-preserving evidence. It never
fills an unknown sign with zero. `roots` uses all derivative signs to
produce one full descriptor per root, each of count one by Thom injectivity,
and sorts them by the following rule. No dyadic separation is required.

For distinct full encodings `σ,τ` of the **same** polynomial, let `k` be the
largest derivative index where they differ. The common sign at `k+1` is
nonzero and `k<n`. Thom order compares `σ[k]` with `τ[k]` in `-1<0<1` when
that common sign is positive, and reverses this comparison when it is negative.
Equal full encodings denote the same root, including across different valid
intervals. These conclusions require valid realized encodings. Complete
partial encodings before applying the rule; never apply lexicographic order
to derivative arrays.

For the same polynomial over the same exact coefficient field, completed
encodings compare directly. Decide polynomial equality with the lawful
`DensePoly K` equality; equal values may have different internal selected-root
representatives. Different polynomials use joint re-encoding. In serialized
replay, bind the declared coefficient interpretation and prove any literal
identification used by this shortcut.

Different defining polynomials require joint re-encoding. For valid
squarefree `p₁,p₂`, compute `h=p₁*p₂/gcd(p₁,p₂)` by checked exact division,
up to a certified nonzero scalar. Prove `h` squarefree with root set the union;
using the product without removing its common factors is invalid. On the
whole line, perform sign determination on `h` with its full derivatives,
the old defining polynomials, their descriptor derivatives and, for every
finite descriptor endpoint `a,b`, the polynomials `x-a,x-b`. Filtering by
`pᵢ=0`, old signs and strict endpoint signs selects exactly the original root.
The two resulting full `h` encodings can then be compared by Thom order.
Using the whole line avoids turning an endpoint of one input interval into
a forbidden root endpoint for the other polynomial. An equivalent joint
procedure needs the same root-identity and completeness theorem. Identical
raw derivative vectors from different polynomials do not establish equality.

The public API separates mathematical validity checks from ordinary total
operations. `Descriptor K` is the validated subtype of a raw descriptor;
validation is decidable by complete sign determination. `PreparedDomain K`
retains a nonzero squarefree head and ordered root-free endpoints. Its
validation predicate and descriptor count-one predicate are executable;
the companion proves their semantic meanings.

| Operation | Result |
| --- | --- |
| `determine p I Q` | `Option SignTable`, with `none` exactly for an invalid root domain. `determinePrepared` is total on a prepared domain. |
| `validate raw` | `Option (Descriptor K)`, with success exactly for a uniquely realized well-formed descriptor. |
| `complete d` | Full descriptor of the same root, total on `Descriptor K`. |
| `roots p I` | Complete strictly increasing descriptor list, or `none` for an invalid domain. Constants give an empty list; multiplicities belong downstream. |
| `signAt d q` | Total integer sign of `q` at the selected root. Joint sign determination filters to count one; the singleton-interval shortcut additionally needs one root in the interval. |
| `compare d₁ d₂` | Total `Ordering` of roots over the same coefficient field, using completion and joint re-encoding where necessary. |
| `reencode d h I'` | `Option (Descriptor K)`; succeeds exactly when the target domain is valid and the selected root belongs to it. |
| `certify` / `Replay.check` | Produce and check Tarski/BKR result certificates for tables or descriptor conclusions. Checking returns `Bool`; malformed or false certificates return `false`. |

The total computations do not require certificate production at every
arithmetic operation. Result certificates retain query replays, matrix
identities and support completeness for independent verification. A tactic
can discharge coefficient identities/signs by ordinary kernel computation or
by supplied proofs bound to those exact facts, including lower-level selected
root queries and caller-supplied real bounds. For transcendental coefficients, proof-founded refinement may depend on an
opaque accessibility proof, so direct kernel reduction of total sign is not
a supported replay assumption. The supplied-proof path must handle these
facts using finite approximation evidence and the sign correctness theorem.
The compilation of a coefficient sign search is not itself proof evidence. These are proof-boundary obligations,
not an evidence-returning field interface.

Different tower contexts must first be mapped into one compatible coefficient
field by the tower owner. Re-encoding after a dynamic split is supported here;
transporting all live tower values remains a hex-real-closure obligation.

## Validity and termination

`Option` is used only for the mathematical input conditions above, not for
resource exhaustion or ordinary coefficient arithmetic. A malformed certificate
fails `Replay.check`; that failure does not prove the requested mathematical
result false. Negative/nonintegral counts or a singular selected matrix on a
valid domain cannot occur for the specified producer. Prove these exclusions;
do not convert an internal invariant gap into `none` or a default table.

Recursion splits finite query lists strictly; empty and singleton lists are
explicit bases. Products, derivative lists, row selection and sorting have
finite bounds. Polynomial division/gcd use exact `DensePoly K` degree descent;
Tarski queries use the shared terminating ordered-field algorithm. No loop
waits for a rational separator. The retained-row-basis existence theorem and
tensor-product invertibility prove that the finite producer always completes.

Consequently prepared-domain operations and valid-descriptor operations are
total. Prove domain-exact `_isSome` theorems for raw-input `Option` APIs. This
requires lawful total coefficient decisions, including the proved sign search
of a transcendental coefficient field when used. A caller lacking its required
convergence or relative-transcendence hypotheses has not supplied such a field;
there is no generic fallback sign or global resource-budget substitute.

## Headline theorems and proof ownership

All shapes assume the computational coefficients are interpreted with
operation/sign preservation and zero reflection in a lawful exact coefficient
field, followed by its order-preserving embedding. Root statements use the ambient `R,ι` above. They are planned obligations:

| Statement | Required conclusion |
| --- | --- |
| `determine_correct` | `determine p I Q = some T` implies `Domain p I` and `∀ σ, T.count σ = count(σ)`, including omitted conditions. |
| `Replay.check_sound` | `Replay.check cert = true` implies its table/descriptor conclusion, including recursive support completeness, under sound interpretation of its coefficient facts. |
| `validate_correct` | Validation succeeds iff the raw descriptor is well formed and uniquely realized. |
| `complete_correct` | Completion preserves the unique root and supplies all derivative signs. |
| `roots_correct` | On a valid domain, descriptors are valid, strictly ordered and in bijection with `Roots(P;I)`. |
| `signAt_correct`, `compare_correct` | Values equal evaluation sign and root comparison in `R`; `compare=eq` iff the roots coincide. |
| `reencode_correct` | Success preserves the root and establishes the target domain and membership. |
| `determine_isSome`, `roots_isSome` | Success iff `Domain p I`; descriptor validation/re-encoding have their exact stated validity predicates. |
| `result_congr` | Order-preserving coefficient embeddings and root-preserving descriptor transports preserve results and their validity. |

HexSignDet proves finite matrix identities/uniqueness, literal replay checks,
structural termination, and support induction conditional on abstract moment,
query and Thom contracts. The companion discharges these contracts and proves
the headline root correspondence. Algebraic lemmas needing Mathlib structures
belong in companions, even when executable arithmetic uses HexMatrix or HexRank.

Use the [family's pinned audit and ownership table](../../SPEC/future-work.md#proof-ownership-and-public-surface),
at Mathlib `1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`:

| Foundation / missing infrastructure | Owner and statement shape |
| --- | --- |
| Exact polynomial arithmetic | Existing `DensePoly K` operations, field division/gcd/xgcd and correspondence in hex-poly/hex-poly-mathlib; positive signed pseudo-remainders belong to the shared ordered-domain query kernel. |
| Shared query algorithm and literal replay | hex-real-roots implements `ZPoly.tarskiQuery` and `IntTarskiCertificate`, including algebraic correspondence and produced-certificate acceptance. hex-sturm implements the ordered-field frontend and prepared-query reuse. Abstract root-sum/replay soundness remains a completion gate. |
| Abstract polynomial IVT, Rolle and signed-remainder/Cauchy-index identity | Tau Ceti import through hex-real-roots-mathlib, consumed via hex-sturm-mathlib's query/replay soundness. Include infinities, common gcd and zero remainder. Do not duplicate the primitive here. |
| Moment identity | Tau Ceti to hex-sign-det-mathlib: actual finite root counts satisfy `t=M*c`, including `0^0=1`, empty lists and zero roots. |
| Recursive BKR support reduction | Tau Ceti to hex-sign-det-mathlib: the family contract for abstract support-preserving reductions, with explicit complete-input-support and reduction premises. Hex proves the elementary child-restriction/Cartesian-product step locally and connects reduction premises to literal evidence. |
| Row selection and invertibility | Existing HexRank/HexRankMathlib certificates and row/column rank results. HexSignDet proves the permutation and inverse-format adapters. Square row-basis existence is linear algebra, not an additional Tau Ceti real-algebra import. |
| Reduced moments | HexSignDet extracts the checked literal identities through `ReductionStep.check_eq`. HexSignDetMathlib proves sign preservation at roots through `ReductionStep.check_sign` and `Reduction.check_sign`, then applies hex-sturm's query semantics to obtain the specified unreduced moments. |
| Thom injectivity and order | Tau Ceti to hex-sign-det-mathlib: full derivative encodings at roots are injective and satisfy the largest-differing-index rule above. Hex proves completion, count-one validity, joint re-encoding and comparison correspondence. |
| Ambient real closed field | Ordered real-closure existence requested from Tau Ceti by the family, consumed by hex-real-closure-mathlib. The pin has neither that theorem nor `IsRealClosed ℝ`; the latter is owned by hex-real-roots-mathlib. Rational-base semantics can use Hex's existing `IsRealClosed RealAlgebraicNumber`. |

These are explicit import contracts, including those requested by
[#10300](https://github.com/kim-em/hex-dev/issues/10300), not assumed existing
Lean theorem names. The computational library neither imports Tau Ceti nor
introduces axioms. The companion owns local literal-to-abstract correspondence;
it does not independently rebuild the imported real-algebra foundation.

## Production and checking bounds

Let `n=degree P`, `s=Q.length`, `D=∑ᵢ max(0,degree Qᵢ)` (zero polynomials
contribute zero), and `N=#Z≤n`. A nonempty recursion has `2s-1` nodes.
After solving, each node retains at most `N` columns and that many adapted
rows. A combination has at most `N²` candidate columns/rows; a leaf has three.
No-root evidence permits immediate empty output after input validation.
Thus `O((s+1)(n+1)²)` distinct query slots suffice without sharing, and each
unreduced moment polynomial has degree at most `2D`. For dense arithmetic,
its conservative construction bound is `O((s+1)(D+1)²)` coefficient operations.
For `n>0`, reduced moments have degree at most `min(2D,n-1)` unless zero.
Initial exact field reductions of all query polynomials cost at most
`O(n*(D+s+1))` coefficient operations. A conservative bound for dense
pseudo-division also charges `O(∑ᵢ (degree Qᵢ+1)²)` for scaling growing
quotients (zero polynomials contribute constant work). Reuse these reductions
across moments. Each moment
then needs at most `2s` reduced multiplications, costing
`O((s+1)*n²)` coefficient operations, plus the hex-sturm query bound on a
polynomial of degree `<n`. Include reduction-certificate size and actual
coefficient arithmetic/sign costs separately. Production should use reduced products when degree growth
would otherwise dominate; the unreduced method remains a reference and a
small-input alternative with proved moment agreement. Account for exact
coefficient normalization and polynomial input validation as well.

At a node with candidate dimension `r`, classical exact elimination and
inverse construction take `O(r³)` rational arithmetic operations. Selection
of rows after zero-column removal and construction of the retained inverse
fit this bound. Literal inverse checking takes `O(r³)` integer operations,
`M*c=t` takes `O(r²)`, and constructing entries costs at most `O(s*r²)` sign
operations. These are arithmetic-operation bounds, not bit-complexity claims:
report intermediate numerator/denominator bits, witness `A,d` bits, moment
coefficient sizes and allocations. For full derivative tables, `s=n`,
`D=n*(n-1)/2` and `N≤n`. Thus the
unreduced construction bound is `O(n⁵)` per moment, versus `O(n³)` for
reduced products after preprocessing, with `O(n³)` query slots. For joint
comparison let `m=n₁+n₂`; `degree h≤m`, `s=O(m)` and `D=O(m²)` including
both old derivative lists, defining polynomials and at most four endpoint
polynomials. The analogous bounds are `O(m⁵)` versus `O(m³)` per moment
and `O(m³)` query slots. These are upper bounds, not tight estimates or a
promise that matrix work is negligible. Count gcd, exact division,
derivatives and target guards separately.

Replay verifies only supplied literals and finite evidence; it does not rerun
query production, gcd search, root isolation, row search or coefficient
refinement. Reconstruct and check products, derivatives, selected rows,
transport identities, domain evidence and every recursion edge, including
parent/child list concatenation and identical domains/contexts. Reduced
moments replay their finite reduction chains rather than expanded products.
Check dimensions, indices and references before using supplied data. Supplied
rational solutions alone are not certificates; the integer identities and
support derivation remain necessary.

For nested coefficient levels, certificates form a finite DAG with references
to earlier nodes only. A coefficient-sign dependency at level `ℓ` refers to
strictly lower levels; same-level table recursion separately decreases query
list length. Context identifiers include selected roots/embeddings and bind
operands and results; stale evidence needs explicit transport. Decoding rejects
cycles, forward references and mismatched contexts. Report nodes, edges,
bytes, arithmetic calls and operand bit sizes; these are cost measurements,
not an additional operation-result protocol.

If a level-`ℓ` certificate requires at most `bℓ` lower-level subcertificates,
its unshared size and checking cost satisfy
`Sℓ ≤ Sℓ,local + bℓ*max Sℓ₋₁` and
`Tℓ ≤ Tℓ,local + bℓ*max Tℓ₋₁`, respectively (local cost includes edge checks).
Base coefficient facts are discharged by exact computation or supplied proofs.
With deduplication, charge
each distinct checked node once plus all reference validations; acceptance
caches bind exact literals and context. Without sharing, charge every replay
occurrence. State this potentially multiplicative depth dependence; a bound
only on the top matrix is insufficient. Producers obey the corresponding
child-work accounting as well. A truncated dependency graph is rejected;
no theorem may rely on a missing child fact.

## Conformance and Phase-4 evidence

Follow [testing](../../SPEC/testing.md) and [benchmarking](../../SPEC/benchmarking.md).
Fixtures record exact polynomials, coefficient contexts, endpoints, tables,
derivative signs, ordered root identities, certificates and validity results.
Pin external oracle versions and provenance. For rational cases compare exact
root/sign data from python-flint and the existing hex-real-algebraic API,
and compare reduced BKR with the full ternary solver on small lists. For
extension fixtures use pinned Z3 RCF roots and exact comparisons. Decimal
approximations never certify sign or identity. Required adversarial cases:

- `p=x²-1`, `Q=[x,x-1]` on the whole line: conditions `(-1,-1)` and `(1,0)`,
  each count one; zero and repeated query polynomials; empty lists; `p=x`
  with its root zero; nonzero constant and root-free `p=x²+1`.
- Every invalid domain, including zero/nonsquarefree `p` with an empty list,
  finite root endpoints and equal/reversed intervals. Test all infinity
  combinations allowed by hex-sturm and exact cancellation of leading coefficients.
- Omitted realized support despite matching total: for `p=x²-1`, `Q=[x]`,
  the candidate `{+1}`, row `{0}`, count `2`, moment `2`, `M=A=[1]`, `d=1`
  passes both identities and total agreement. Reject its missing support
  evidence. Also mutate child products, zero-pruning counts, selected rows,
  exponents, `0^0`, inverse witnesses, negative/nonintegral counts and empty
  supports lacking root-zero evidence. Reject repeated or wrong child sublists,
  changed domains, bad reduction identities and nonpositive reduction scales;
  compare reduced and unreduced moment values.
- A full but unrealized encoding, a partial encoding matching zero or two
  roots, and an empty partial encoding in a certified singleton interval.
  For `p=x³-x`, roots `-1,0` have derivative vectors `(+,-,+)` and `(-,0,+)`:
  lexicographic ordering gives the wrong answer. Include negative leading
  coefficients to exercise the reversed Thom rule.
- `x-1` and `x-2` have the same full derivative vector but different roots;
  `x²-2` and `(x²-2)(x-3)` share a root and need gcd removal. Compare different
  partial/full encodings, overlapping intervals for equal roots and disjoint
  intervals for distinct roots, plus intervals whose endpoint is a root only
  of the other polynomial. Include equal polynomial values represented by
  different coefficient expressions and nonzero scalar multiples; equality
  and joint re-encoding must return equal roots when the selections coincide.
- Malformed/truncated literals, cyclic references, missing coefficient-sign
  proofs, foreign or stale contexts, and nested valid/rejected result replays
  at several coefficient levels. Optional bounded oracle attempts are tested
  in hex-ordered-fn; they are not substituted for this API's total field.

Downstream integration must include the corrected
[de Moura–Passmore example](https://www.cl.cam.ac.uk/~gp351/infinitesimals.pdf)
`p=(εx²−1)(εx³−1)`. For positive infinitesimal `ε`, its ordered real roots are
`−ε^(-1/2), ε^(-1/3), ε^(-1/2)`. On `(0,+∞)`, `Q=[p''']` has conditions
`-1,+1` each with count one, and these give valid partial descriptors; the
empty constraint there is invalid. Complete and compare the descriptors
without seeking a rational separator. Multiple infinitesimal levels and
tower-generated coefficient certificates are supplied downstream, without
introducing an upward import here.

Phase 4 separates table production, Tarski queries, coefficient-sign work,
product construction, matrix solving/reduction, descriptor completion,
comparison/re-encoding and replay. Sweep `n,s,D`, realized support size,
coefficient bit size, witness size, extension depth and nested evidence size.
Include lists with many unrealized conditions, maximal realized support,
shared roots/zero signs, and expensive joint re-encoding. Record query and gcd
counts, matrix dimensions, peak coefficient/witness bits, certificate bytes,
DAG edges and allocation. Measure production and checking
against the bounds above; successful cheap cases alone are not evidence.

Reduced-versus-full solver correctness is a required check. Runtime comparison
uses identical small inputs and separately shows reduced-matrix scaling on larger
lists. Compare unreduced and modulo-`p` moment construction on derivative and
joint-encoding lists, including coefficient sizes and reduction replay costs.
Z3 and python-flint end-to-end comparisons are informational where an exact
matching operation is available; root isolation time must not be labelled
matrix-solving time. No external oracle supplies a comparable Lean proof
checker. Kernel replay uses the companion's
[fresh-module proof evidence](../../SPEC/benchmarking.md#fresh-module-proof-evidence)
track, with ordinary kernel checking and axiom inspection, separately from
Mathlib-free executable benches. Include valid and rejected nested proof
probes and one representative profile attributing arithmetic, matrices and
coefficient-sign work. The family's full `tower8` isolation and
clean-versus-eager normalization ablation remain hex-real-closure integration
obligations; this library supplies their sign-table/descriptor measurements.

Use the shared host, automatic CPU selection, fixed trial-major schedules and
adjacent alternating `AB`/`BA` comparisons. Retain every completed sample and
allow at most one unchanged rerun after an inconclusive result. The
`bench verify` fast check is not Phase-4 performance evidence. No benchmark result, proof
completion or phase advancement is claimed by this planned SPEC.
