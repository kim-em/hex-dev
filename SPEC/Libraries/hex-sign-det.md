# hex-sign-det

BKR univariate sign determination and single-polynomial Thom root descriptors,
with complete sign tables and literal replay certificates.

## Status and placement

This is a planned computational library in the
[real-closure family](../future-work.md#real-closures-of-ordered-fields).
The API names and theorem statements below are required shapes, not existing
or checked Lean declarations. This SPEC registers no target or phase. Its
companion is assigned by [#10314](https://github.com/kim-em/hex-dev/issues/10314).

`HexSignDet`, in namespace `Hex.SignDet`, depends on `HexSturm`, `HexPoly`,
`HexMatrix` and `HexRowReduce`. Matrix construction, exact rational solving,
row selection and integer identity checking reuse the Mathlib-free matrix
stack; BKR-specific support and descriptor certificates live here.
`HexSignDetMathlib` imports this library, `HexSturmMathlib`,
`HexPolyMathlib`, `HexMatrixMathlib` and `HexRowReduceMathlib`, with Tau Ceti
foundations imported only in companions. These dependencies are acyclic.

[hex-sturm](hex-sturm.md) owns ordered-field Tarski queries, domain guards and
coefficient-evidence composition over the one shared kernel in hex-real-roots.
It has consumers needing no sign matrix, and must not import this library.
Existing polynomial, rational-function, interval and real-algebraic libraries
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

Use the shared [fallible coefficient operations](../../HexPoly/SPEC/hex-poly.md#fallible-coefficient-operations)
`CoeffOps C`, `PolyOps.Limits`, `Budget`, `Result` and `CheckResult` with the
field interpretation and inversion adapter required by hex-sturm. Raw finite
coefficient arrays have checked semantic degrees. Neither structural equality
nor stored array length supplies a semantic zero or leading-coefficient test.
All calls use one threaded budget, including coefficient callbacks, polynomial
arithmetic, Tarski queries, matrices and nested evidence. Runtime arithmetic
and sign decisions are separate from the evidence establishing their claims.

The total semantic carrier adapter has exactly hex-sturm's executable
hypotheses: `[Lean.Grind.Field K] [LE K] [LT K] [Std.IsLinearOrder K]`
`[Std.LawfulOrderLT K] [Lean.Grind.OrderedRing K] [DecidableEq K]`
`[DecidableLE K] [DecidableLT K]`. The bounded adapter instead has a law package
relating successful operations on `C` to an ordered field `K`. It does not
install a field, total order or decidable semantic equality on raw syntax.

For mathematical statements, fix an ordered real closed field `R` and an
order-preserving field embedding `ι : K →+* R`. In the companion this means
`[Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]`.
Write `P,Qᵢ` for interpreted polynomials mapped to `R`. The statements are
universal in `R,ι`; existence of such an extension is a separate family
foundation, not an executable assumption or an available instance on the pin.

`Domain p I` is hex-sturm's prepared domain: `p` is semantically nonzero and
squarefree, `I=(a,b)` has `a<b`, and finite endpoints are not roots of `p`.
Endpoints are coefficient representatives or `±∞`. Let `Z` be the finite set
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
the domain and all input coefficient contexts before taking these shortcuts.

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
by a hash. Every moment uses hex-sturm's prepared-query API and its literal
replay, with exactly the same `p`, interval and coefficient context. Common
roots with `Fₑ` are allowed and contribute zero. Do not substitute derivative
root counts for general Tarski queries.

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
Another witness format needs a proved equivalent checker. Matrix dimensions,
indices, exponent ranges, distinct columns and exact count casts are checked
before use. A claimed nonsingular submatrix alone establishes no completeness.

The producer uses a balanced binary split of the query list. Each replay node
binds the exact ordered sublist, root domain and context, and carries:

1. **Leaves:** the full ternary support and three query replays. An empty-list
   root uses the one-condition system and the query of `1`.
2. **Combination:** accepted complete child tables. Every realized parent
   condition restricts to realized child conditions, hence lies in their
   Cartesian product, in concatenation order. Carry the child certificates
   and verify that the candidate columns are precisely that product.
3. **Solve:** moment rows, their query replays, `M*c=t`, nonnegative integral
   counts and the invertibility witness on this complete candidate support.
4. **Reduction:** remove columns whose counts have just been certified zero.
   Retain all positive columns. Select independent moment rows on the retained
   columns and certify the resulting square matrix's invertibility for reuse
   by a parent. Row selection does not delete any positive column.

A concrete finite construction uses the Cartesian product of the children's
retained exponent rows at combination. Its candidate matrix is the tensor
product of their invertible matrices, hence is invertible. After zero-column
removal, the remaining columns are independent, so exact row selection can
choose a square invertible minor. Query values for retained rows are reused;
removed zero columns contribute nothing to their equations. Leaf reduction
uses the same rule. This supplies a complete producer without enumerating
all `3^s` conditions. It also specifies the row-rank existence obligation.

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
or scaling that would change their signs. Validity is exactly

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

`completeWith` computes a table on all derivatives, filters by the partial
constraints and uses validity to obtain exactly one full encoding with count
one. It returns that encoding and identity-preserving evidence. It never
fills an unknown sign with zero. `rootsWith` uses all derivative signs to
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

Planned bounded operations return evidence, remaining budget and counters:

| Operation | Successful result |
| --- | --- |
| `determineWith ops limits p I Q` | Complete sparse sign table and recursive replay. |
| `validateWith ops limits d` | Opaque valid descriptor and count-one replay. |
| `completeWith ops limits d` | Valid full descriptor of the same selected root. |
| `rootsWith ops limits p I` | Complete strictly increasing list of valid full descriptors, each root once. Nonzero constants give an empty list; no multiplicity API here. |
| `signAtWith ops limits d q` | `sign(q(α))` with evidence at the selected root. Joint sign determination on descriptor derivatives and `q` filters to count one; use a singleton-interval Tarski shortcut only when the interval itself has one root. |
| `compareWith ops limits d₁ d₂` | `Ordering` matching the selected roots; equality is its `eq` case. Validate, complete and jointly re-encode as needed. |
| `reencodeWith ops limits d h I'` | Descriptor of the same root on a supplied squarefree target `h,I'`; checked joint selection must show it is a root of `h` inside `I'`. Otherwise invalid. |
| `Replay.checkWith` | Accepted, rejected or exhausted validation of supplied table/descriptor/operation evidence. Boolean `check` is true only on acceptance. |

Raw arguments to each operation are validated; opaque checked arguments may
reuse evidence only for the same context and literals. Context changes require
explicit denotation-preserving transport. The operation interface can be
instantiated by tower callbacks without importing their implementation.
Re-encoding after a dynamic split belongs to this interface; proving that the
split preserves all live tower elements belongs to hex-real-closure.

## Failure and termination contracts

Use the shared outcomes without fallback values:

| Outcome | Contract |
| --- | --- |
| `ok value evidence` | All relevant guards and evidence checks succeeded; the mathematical postcondition holds under adapter laws and companion correspondence. |
| `invalid reason` | A certified invalid coefficient context/domain, malformed descriptor, descriptor count other than one, incompatible input contexts without transport, or failed target membership in re-encoding. |
| `exhausted reason` | Arithmetic, sign/zero, matrix, allocation or evidence budget exhausted, including unresolved coefficient equality. No count, order or invalidity is asserted. |
| `rejected reason` | Malformed/false supplied certificate, or a producer invariant/check failure. Nonintegral or negative solved counts and a singular candidate matrix on already validated data are implementation errors, not mathematical absence. |

Tags are stable; reason wording and the first error chosen are diagnostic.
Invalid inputs may exhaust while their invalidity is being tested, but cannot
succeed. Missing evidence never implies a zero sign, empty root list or equal
roots. A descriptor with several matching roots is not silently narrowed.
For malformed certificates, rejection may precede semantic guard checks.

Recursion splits a finite query list into strictly smaller nonempty lists;
empty and singleton lists are explicit bases. Loops over products, row
selection, derivatives and comparisons have finite array/degree bounds.
The polynomial gcd/exact-division and Tarski work inherit hex-poly/hex-sturm's
semantic-degree descent and fueled callback contracts. No loop waits for a
rational separator. All bounded paths terminate, including malformed input,
zero budget, invalid domains and undecided coefficients. A zero remaining
budget permits success only if all required checks have already completed.

Total-coefficient forms `determine`, `validate`, `complete`, `roots`, `signAt`,
`compare` and `reencode` use computed finite work bounds and return `Option`:
`none` exactly on their respective invalid-input predicates. Their completeness
requires total lawful coefficient operations and complete evidence production
where a replay is requested. Bounded success has soundness without those
completeness assumptions. Eventual bounded success on valid input requires
proof that *every* needed child operation and certificate producer succeeds
with sufficient budgets; simply increasing a budget for an unresolved
transcendental zero test is not such a proof.

## Headline theorems and proof ownership

All shapes assume lawful interpretation of successful coefficient operations
and sound checkers for their evidence. Root statements use the ambient `R,ι`
above and interpreted, context-valid inputs. They are planned obligations:

| Statement | Required conclusion |
| --- | --- |
| `determine_correct` | `determineWith ... = ok T cert` implies `Domain p I` and `∀ σ, T.count σ = count(σ)`, including omitted conditions; hence nonnegative counts, exact total and complete support. |
| `Replay.check_sound` | Accepted replay implies the same semantic result for the bound table or descriptor operation, including recursive support completeness. |
| `validate_correct` | Successful validation iff validity for the total adapter; bounded success implies validity and bounded invalidity certifies its negation or a malformed context. |
| `complete_correct` | Completion preserves the unique root and supplies all its derivative signs. |
| `roots_correct` | Returned descriptors are valid, strictly ordered and in bijection with `Roots(P;I)`. |
| `signAt_correct`, `compare_correct` | Successful values equal evaluation sign and root comparison in `R`, respectively; `compare=eq` iff the selected roots coincide. |
| `reencode_correct` | Successful re-encoding preserves the unique root, with target domain and membership established. |
| `determine_isSome` | For total adapters, success iff `Domain p I` and all input representations are valid; analogous domain-exact theorems for the descriptor operations. |
| `result_congr` | Successful semantic results are preserved under coefficient/context embeddings and certified polynomial/descriptor transports; transferring success also requires completeness/budget hypotheses. |

The core proves finite matrix identities/uniqueness, literal replay plumbing,
structural termination, and support induction conditional on abstract moment,
query and Thom contracts. The companion discharges these contracts and proves
the headline root correspondence. Algebraic lemmas needing Mathlib structures
belong in companions, even when executable arithmetic uses the matrix stack.

Use the [family's pinned audit and ownership table](../future-work.md#proof-ownership-and-public-surface),
at Mathlib `1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`:

| Foundation / missing infrastructure | Owner and statement shape |
| --- | --- |
| Fallible coefficient/polynomial operations and semantic degree | hex-poly; not supplied by today's total `HexPoly.Field` routines on arbitrary raw coefficients. |
| Shared query algorithm and literal replay | hex-real-roots, with the hex-sturm field frontend; `ZPoly.tarskiQuery`/`TarskiReplay` remain planned declarations, not available implementations. |
| Abstract polynomial IVT, Rolle and signed-remainder/Cauchy-index identity | Tau Ceti import through hex-real-roots-mathlib, consumed via hex-sturm-mathlib's query/replay soundness. Include infinities, common gcd and zero remainder. Do not duplicate the primitive here. |
| Moment identity | Tau Ceti to hex-sign-det-mathlib: actual finite root counts satisfy `t=M*c`, including `0^0=1`, empty lists and zero roots. |
| Recursive BKR support reduction | Tau Ceti to hex-sign-det-mathlib: complete child supports cover the parent Cartesian product; certified reduction preserves every realized condition; independent columns admit a square row basis. Hex connects these abstract statements to the literal recursion, row selection and inverse witnesses. |
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
moment polynomial has degree at most `2D`. Computing powers/products and
validating stored coefficients must also be charged: for dense arithmetic a
conservative per-moment bound is `O((s+1)(D+1)²)` coefficient operations,
plus the hex-sturm bound for its query and its coefficient evidence. Use
actual stored lengths for raw arrays with semantic leading zeros.

At a node with candidate dimension `r`, classical exact elimination and
inverse construction take `O(r³)` rational arithmetic operations. Selection
of rows after zero-column removal and construction of the retained inverse
fit this bound. Literal inverse checking takes `O(r³)` integer operations,
`M*c=t` takes `O(r²)`, and constructing entries costs at most `O(s*r²)` sign
operations. These are arithmetic-operation bounds, not bit-complexity claims:
report intermediate numerator/denominator bits, witness `A,d` bits, moment
coefficient sizes and allocations. Descriptor completion uses at most `n`
derivatives; cross-polynomial comparison uses `degree h≤n₁+n₂` and the extra
old-constraint/endpoint query columns, with the same bounds. Count gcd,
exact division, derivatives and target guards separately.

Replay verifies only supplied literals and finite evidence; it does not rerun
query production, gcd search, root isolation, row search or coefficient
refinement. Reconstruct and check products, derivatives, selected rows,
transport identities, domain evidence and every recursion edge. Check shape,
size and reference bounds before allocation or multiplication. Supplied
rational solutions alone are not certificates; the integer identities and
support derivation remain necessary.

For nested coefficient levels, certificates form a finite DAG with references
to earlier nodes only. A coefficient-sign dependency at level `ℓ` refers to
strictly lower levels; same-level table recursion separately decreases query
list length. Context identifiers include selected roots/embeddings and bind
operands and results; stale evidence needs explicit transport. Decoding rejects
cycles, forward references and mismatched contexts. Budget nodes, edges,
bytes, arithmetic calls and operand bit sizes globally, not afresh per level.

If a level-`ℓ` certificate requires at most `bℓ` lower-level subcertificates,
its unshared size and checking cost satisfy
`Sℓ ≤ Sℓ,local + bℓ*max Sℓ₋₁` and
`Tℓ ≤ Tℓ,local + bℓ*max Tℓ₋₁`, respectively (local cost includes edge checks).
The base uses its certified coefficient checker. With deduplication, charge
each distinct checked node once plus all reference validations; acceptance
caches bind exact literals and context. Without sharing, charge every replay
occurrence. State this potentially multiplicative depth dependence; a bound
only on the top matrix is insufficient. Producers obey the corresponding
child-work accounting as well. A budget-limited checker can exhaust on a valid
certificate; it may never accept a truncated dependency graph.

## Conformance and Phase-4 evidence

Follow [testing](../testing.md) and [benchmarking](../benchmarking.md).
Fixtures record exact polynomials, coefficient contexts, endpoints, tables,
derivative signs, ordered root identities, certificates and outcome tags.
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
  combinations allowed by hex-sturm and unresolved semantic leading zeros.
- Omitted realized support despite matching total: for `p=x²-1`, `Q=[x]`,
  the candidate `{+1}`, row `{0}`, count `2`, moment `2`, `M=A=[1]`, `d=1`
  passes both identities and total agreement. Reject its missing support
  evidence. Also mutate child products, zero-pruning counts, selected rows,
  exponents, `0^0`, inverse witnesses, negative/nonintegral counts and empty
  supports lacking root-zero evidence.
- A full but unrealized encoding, a partial encoding matching zero or two
  roots, and an empty partial encoding in a certified singleton interval.
  For `p=x³-x`, roots `-1,0` have derivative vectors `(+,-,+)` and `(-,0,+)`:
  lexicographic ordering gives the wrong answer. Include negative leading
  coefficients to exercise the reversed Thom rule.
- `x-1` and `x-2` have the same full derivative vector but different roots;
  `x²-2` and `(x²-2)(x-3)` share a root and need gcd removal. Compare different
  partial/full encodings, overlapping intervals for equal roots and disjoint
  intervals for distinct roots, plus intervals whose endpoint is a root only
  of the other polynomial.
- Budget exhaustion in each layer, malformed or oversized literals, cyclic
  references, missing coefficient-sign evidence, foreign or stale contexts,
  and nested valid/rejected replays at several coefficient levels.

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
DAG edges, allocation and exhausted runs. Measure production and checking
against the bounds above; successful cheap cases alone are not evidence.

Reduced-versus-full solver correctness is gating; runtime comparison uses
identical small inputs and separately shows reduced scaling on larger lists.
Z3 and python-flint end-to-end comparisons are informational where an exact
matching operation is available; root isolation time must not be labelled
matrix-solving time. No external oracle supplies a comparable Lean proof
checker. Kernel replay uses the companion's
[fresh-module proof evidence](../benchmarking.md#fresh-module-proof-evidence)
track, with ordinary kernel checking and axiom inspection, separately from
Mathlib-free executable benches. Include valid and rejected nested proof
probes and one representative profile attributing arithmetic, matrices and
coefficient-sign work. The family's full `tower8` isolation and
clean-versus-eager normalization ablation remain hex-real-closure integration
obligations; this library supplies their sign-table/descriptor measurements.

Use the shared host, automatic CPU selection, fixed trial-major schedules and
adjacent alternating `AB`/`BA` comparisons. Retain every completed sample and
allow at most one unchanged rerun after an inconclusive result. CI smoke
verification is not Phase-4 performance evidence. No benchmark result, proof
completion or phase advancement is claimed by this planned SPEC.
