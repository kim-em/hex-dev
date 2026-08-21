# Further work

Sketches for libraries and algorithms the project does not yet have.
Each item is a starting point for a SPEC draft, not a specification:
enough design to know what the thing is, what it depends on, and what
its correctness statement looks like.

Two things to keep in mind while reading.

**Library names here refer to the intended graph.**
[SPEC/Libraries/README.md](Libraries/README.md) lists every library the
project plans to have; [libraries.yml](../libraries.yml) is authoritative
for what exists today. Items below name their prerequisites explicitly,
including the ones that are themselves registered but not yet built.

**What a certificate establishes.** The house style is an untrusted
search that produces a candidate, plus a small kernel-checked verifier.
The scope of that pattern is worth stating once:

> Checking a positive equality, divisibility, or decomposition
> certificate establishes minimality, maximality, irreducibility,
> uniqueness, nonexistence, or completeness only when the certificate
> carries a separate witness for that property.

A gcd that divides both inputs could be `1`; maximality needs coprime
cofactors. A polynomial that annihilates `A` and divides `χ_A` could be
any multiple of the minimal polynomial; minimality needs a lower-bound
witness. Factors whose product is the input form a decomposition;
irreducibility of each is a further obligation. Where an item needs a
second witness, it says which one.

**Hermite and Smith normal forms.** These two have graduated from this
file and are specified in [hex-hermite](Libraries/hex-hermite.md) and
[hex-smith](Libraries/hex-smith.md): Hermite normal form as a canonical
representative of an integer row lattice with lattice membership,
integer kernel bases, and integer rank on top of it, and Smith normal
form as the diagonal form with the divisibility chain `d₁ ∣ d₂ ∣ ⋯ ∣ dᵣ`,
the invariant factors, and the structure of a finitely generated abelian
group. Both are separate libraries rather than additions to hex-matrix.
Hermite uses the extended GCD from hex-arith, the echelon contracts from
hex-row-reduce, and determinant/adjugate theory from hex-determinant; Smith
builds on that library and its shared elimination step.

Two corrections to what this file said before those SPECs were written,
recorded because they are easy to make again. The `IsHNF` field list
should not carry `det transform = 1 ∨ det transform = -1`, which follows
from `IsEchelonForm.transform_inv` and `det_mul`; and it must carry the
condition that each pivot is the leading nonzero entry of its row, which
`IsEchelonForm` does not imply and without which uniqueness is false.

**Shared exact division is specified and built.** `exactDiv`, `ExactDivLaws`,
the coefficient-independent cancellation lemmas, and the `Int` and field
instances live in `HexBasic/ExactDiv.lean`, below both `hex-resultant` and
`hex-bareiss`. `HexResultant/ExactDiv.lean` holds the binary-power helpers and
the dense-polynomial operations and instances, and re-exports the contract
through a public import.

**Namespace hazard at the bottom of the graph.** A declaration `Hex.foo` in
`HexBasic` is in scope for every `Hex*Mathlib` file wherever `open Hex` is in
effect, so if Mathlib defines `_root_.foo` then a bare `foo` in that scope is
an ambiguous term. This constrains what `HexBasic` may hold: `Hex.mul_pow`,
`Hex.pow_mul`, and `Hex.pow_ne_zero` collide that way, which is why they sit
with `powNat` and `divExp` in `hex-resultant`, their only consumer.

**Generic Bareiss over integral domains (`hex-bareiss`, amendment).**
Generalize the existing `Int` implementation rather than adding a matrix
library. The executable recurrence uses the shared total exact-division
operation from `HexBasic.ExactDiv`; its correctness layer assumes a
commutative ring, decidable
equality, and `ExactDivLaws`, which supplies cancellation and rules out zero
products. Keep the current `Int` API as a specialization. The determinant
proof reuses the public Desnanot-Jacobi and Plücker API already in
hex-determinant-mathlib; that identity is not a new prerequisite library.

Note that `HexBareiss/Bareiss.lean` already defines its own
`Hex.Matrix.exactDiv`, an `Int`-specific `num / denom` that borrows both
arguments with `@&`. Generalizing the recurrence means reconciling it with
`Hex.exactDiv`, which is a total wrapper with a zero test and no borrow
annotations. The two agree on values, since `Int` division by zero is already
zero, so this is a code-generation question on the elimination hot path rather
than a semantic one, and it wants a benchmark rather than a rewrite on sight.

**Characteristic polynomial.** This one has graduated from this file and
is specified in [hex-char-poly](Libraries/hex-char-poly.md): the
Samuelson-Berkowitz algorithm, division-free over any commutative ring at
`O(n⁴)`, depending only on hex-matrix and hex-poly, with a companion that
identifies the output with Mathlib's `Matrix.charpoly` and derives
Cayley-Hamilton from it. Hessenberg reduction, Danilevsky's method,
generic Bareiss, and multi-modular recombination are recorded there as
later alternative implementations behind the same public name, each with
the measurement that would justify it, rather than as dependencies of
version one.

One correction to what this file said before that SPEC was written,
recorded because it is easy to make again. The characteristic polynomial
was described here as belonging alongside the determinant and the
adjugate in hex-determinant. Berkowitz computes no determinant, so
hex-determinant is not a computational dependency at all, and the
identification of the output with `det (x·I − A)` is a theorem of the
companion.

Isolating the roots of `χ_A` with hex-real-roots and hex-roots would give
certified eigenvalue enclosures. hex-number-field can name the resulting
exact eigenvalues.

**Minimal polynomial.** This item has graduated from this file and is
specified in [hex-min-poly](Libraries/hex-min-poly.md): the order
polynomial of a vector from the first dependency in its Krylov sequence,
the matrix minimal polynomial as the lcm of the order polynomials of the
standard basis vectors, and a certificate whose independence witness is
a right inverse of the Krylov matrix.

That SPEC also settles what this file previously left open. The
lower-bound witness is stated as a matrix identity rather than as a
degree claim, so the whole verification path is free of division and of
row reduction. The basis-wide sweep is not an implementation detail: the
accumulated-span shortcut that would make it `O(n³)` computes relative
order polynomials whose lcm is *not* the minimal polynomial, and the SPEC
carries the two-by-two counterexample. A single-vector witness always
exists and would be smaller, and the reason version one does not use it
is that producing it needs a failure branch that would have to be
specified.

`hex-char-poly` is not an algorithmic prerequisite and not a
computational dependency. The two facts that do go through it,
`m_A ∣ χ_A` and `deg m_A ≤ n`, are theorems of the companion.

**Polynomial Smith form.** This item has graduated from this file and is
specified in [hex-poly-smith](Libraries/hex-poly-smith.md): an executable
Smith form for `Matrix (DensePoly F) n m` over the Euclidean domain
`F[x]`, with monic pivot normalization folded into the elimination step,
unimodular transforms carrying their inverses as data, the divisibility
chain, and a termination measure on polynomial degree.

That SPEC also settles what this file previously left as a prediction.
It is not the integer Smith normal form of
[hex-smith](Libraries/hex-smith.md), and the inventory of what transfers
is drawn there row by row rather than in prose: the unit group, the
pivot normalisation, the exact-division primitive, the growth problem,
the product-certificate primitive, and the oracle all differ, and the
one piece that transfers verbatim is `mul_eq_one_comm`. In particular
there is no polynomial Hermite normal form underneath it, so the pairing
that holds over `ℤ` has no analogue over `F[x]`, and the
Euclidean-domain class that [hex-hermite](Libraries/hex-hermite.md)
declines to write is closed rather than deferred.

**Matrix invariant factors (`hex-invariant-factors`,
`hex-invariant-factors-mathlib`).** Apply polynomial Smith form to the
characteristic matrix `xI − A` and read the invariant factors from its
diagonal. This is the route to canonical forms: the invariant factors give the
rational canonical form directly, the largest is the minimal polynomial, and
their product is the characteristic polynomial, all certified from one
computation.

The application library depends on
[hex-poly-smith](Libraries/hex-poly-smith.md), which deliberately keeps
characteristic matrices, matrix minimal polynomials, and rational
canonical form out of its own scope. It must not be named `hex-rcf`:
that name is taken by the real-closed-field decision procedure. Its
correspondence layer
also depends on [hex-char-poly](Libraries/hex-char-poly.md) and
[hex-min-poly](Libraries/hex-min-poly.md) so those equalities compare
against the independently specified computations rather than introducing
second definitions. Factorization of `χ_A` does not determine this data:
matrices sharing a characteristic polynomial can have different invariant
factors.

**Certified eigenpair enclosures.** Run an untrusted floating-point
solver, then verify its output with interval arithmetic in the style of
Rump's method: the approximate eigenpair supplies a candidate, and a
fixed-point or contraction argument on an interval matrix places a true
eigenpair within a small ball of it.

Scope the first version to simple isolated eigenpairs of a symmetric
matrix. Multiple and defective eigenvalues, eigenvector normalisation
and phase, singular values, rectangular matrices, pivoted QR, and
interval bounds on a matrix inverse are each a distinct hard case, and
belong to a research horizon rather than to this item.

Prerequisites are hex-interval, which has no phases complete, and
hex-interval-mathlib, which is still `planned`. The interval SPEC anticipates
sparse matrix and QR consumers requesting componentwise enclosures, so
the interface it offers should be checked against what this item needs.
The remaining design question is where the untrusted solver comes from,
since the project has no floating-point linear algebra: an unverified
Lean implementation and an FFI call are equally acceptable, because the
verification step makes the choice proof-irrelevant.

**Modular techniques.** These have graduated from this file and are
specified in three libraries: [hex-modular](Libraries/hex-modular.md),
holding integer CRT, rational reconstruction, symmetric representatives,
and the modulus supply; [hex-modular-matrix](Libraries/hex-modular-matrix.md),
holding the multi-modular determinant, certified rank, and Dixon p-adic
lifting; and [hex-poly-z-gcd](Libraries/hex-poly-z-gcd.md), holding
Brown's modular gcd for `ℤ[x]` with cofactors and a coprimality witness.
The split is along the dependency seams: rational reconstruction has
consumers that want no matrices, and a matrix library and a polynomial
library should not depend on each other.

The shared shape survives. An unverified modular route produces a
candidate and an exact check accepts it, so prime selection and every
other heuristic needs no correctness proof. Four corrections to what this
file said around that shape, recorded because they are easy to make
again.

**The checker's obligations are not "primality and distinctness of the
moduli".** Reduction modulo any `m` is a ring homomorphism, so the
reconstruction argument never uses primality; what elimination needs is
that the pivots it inverts are units, which the extended gcd discovers
rather than assumes. Distinctness is not the right property either, since
distinct moduli need not be coprime. Pairwise coprimality is what the
reconstruction needs, and one extended gcd per modulus checks it.

Primality still earns its place on the producer side, and the correction
is about the checker alone. Brown's image gcd over a composite modulus is
meaningless as a degree bound (`x` and `x - 6` are coprime over `ℤ[x]`
and identical modulo `6`), so the gcd's producer and its eventual-success
argument both want primes; what the correction buys is that a spurious
image cannot produce a wrong answer, because the exact checker rejects
the candidate. Two statements do need primality outright, and both say
so: the rank of an image is a rank only over a field, and the gcd's
modular coprimality witness needs `F_p[x]` to be a domain.

**Where a checker does name a prime, the size of that prime is a cost.**
Replaying a certificate in the kernel replays the primality proof, and
trial division costs `√p`: measured on this tree, 0.04 s at 16 bits
against 6.2 s at 31 bits. Certificates name small primes for that reason,
and the multi-modular determinant may use large ones precisely because
its argument never mentions primality.

**"Reduction mod `p` can only drop rank" is the conclusion, not the
argument.** The modular rank is a lower bound because a nonvanishing
`r × r` minor modulo `p` is a nonvanishing integer minor, and that
submatrix is what the certificate carries. Phrasing it the other way
suggests the modular computation is itself the evidence.

**The Bézout witness for coprime cofactors over `ℤ[x]` does not exist.**
`ℤ[x]` is not a Bézout domain: `x` and `2` are coprime and
`u · x + v · 2 = 1` has no solution. The replacement is a modular
witness, and in one variable it is complete: reduce both cofactors at a
prime dividing neither leading coefficient, exhibit a Bézout pair over
`F_p[x]`, and check that the integer contents are coprime. The
multivariate version of the same correction is in
[hex-mv-gcd](Libraries/hex-mv-gcd.md), where the recursion on contents
makes the Gauss/common-factor development substantially larger. The
certificate checker is unconditional in both libraries; multivariate gcd
maximality is a separate Mathlib-free theorem rather than a hidden checker
premise.

Two smaller things. The condition `gcd(q, m) = 1` on a reconstructed
rational is a theorem rather than a fourth check, derivable from
`gcd(p, q) = 1` and the congruence. And the determinant is the one member
of this group with no cheap checker at all, so it is a proved algorithm
rather than a checked candidate, it carries the group's only analytic
hypothesis (a Hadamard bound, discharged in the companion), and certified
dispatch to an untrusted external implementation is unavailable for it
while remaining available for the rank and the linear solve.

**Sparse matrices.** A sparse representation alongside the dense
`Array`-backed one, with `toDense` as the specification function. The
representation needs research; the two candidates are coordinate form
(three parallel arrays `rows`, `cols`, `vals`, sorted lexicographically
with no duplicate positions and no stored zeros) and compressed sparse
row (`vals` and `colIdx` of equal length, plus `rowPtr : Array Nat` of
length `numRows + 1` where row `i` occupies
`vals[rowPtr[i] : rowPtr[i+1]]`). Coordinate form is cheapest to build
and to prove things about; CSR gives contiguous row slices, which is
what row reduction and matrix-vector products want. CSC is CSR of the
transpose, so only one of the two needs an implementation.

The choice may well be one representation per consumer rather than one
overall: CSR suits a frozen matrix being multiplied repeatedly, and
suits elimination badly, because fill-in inserts entries into rows that
have no room for them. A builder form and a frozen form with a
conversion between them is the usual resolution.

Operations: addition and scalar multiplication (a merge of two sorted
row slices), transpose (a counting sort on column indices),
sparse-times-sparse multiplication (Gustavson's algorithm: accumulate
each output row in a dense scratch array with an occupancy marker, then
compress), and sparse-times-dense products producing a dense result.
Multiplication should be available in both output flavours; the
sparse-output form needs the scratch-array compression step, the
dense-output form does not.

The theorems are the `toDense` homomorphism laws:

```lean
theorem toDense_add (a b : SparseMatrix R) : (a + b).toDense = a.toDense + b.toDense
theorem toDense_mul (a b : SparseMatrix R) : (a * b).toDense = a.toDense * b.toDense
theorem toDense_transpose (a : SparseMatrix R) : a.transpose.toDense = a.toDense.transpose
theorem get_eq (a : SparseMatrix R) (i j) : a.toDense[i]![j]! = a.get i j
```

plus extensionality on canonical form: sorted, duplicate-free,
zero-free sparse matrices with equal `toDense` are propositionally
equal. Canonicalisation has to run after every operation that can
cancel, since a sum or product can produce a structurally present entry
whose coefficient is zero. This is the same
canonical-form-plus-specification-function pattern as the polynomial
representations below, and the two should share a shape.

Sparse elimination is a separate and harder item: fill-in during row
reduction is the dominant cost, and controlling it needs a pivot
selection strategy (Markowitz) with no dense analogue. Sparse addition
and multiplication are worth having on their own first. Before either,
it is worth naming a benchmarked consumer where the dense
representation actually fails, since a second matrix ecosystem is a
large commitment; black-box methods (below) may serve the finite-field
cases more directly.

**Black-box linear algebra.** Wiedemann and block Wiedemann: solve
`A x = b` and find kernel vectors over a finite field by treating `A` as
a function rather than as stored entries, recovering the minimal
polynomial of the Krylov sequence and reading the solution off it. For
large sparse systems over `F_p` this is the method of choice, and it is
a better fit than sparse Gaussian elimination for the consumers this
project actually has, Berlekamp's kernel step among them. The
correctness statement is pleasant: the returned vector is checked by one
matrix-vector product.

**Swappable polynomial representations (deferred).** Do not introduce a
`PolyOps` / `LawfulPolyOps` abstraction merely because a second representation
exists. Dense and sparse algorithms have materially different useful
operations, complexity, and normalization behaviour, and gcd or division of
sparse inputs generally becomes dense. Build the sparse representation with
explicit conversions first; reconsider a common interface only after multiple
real consumers demonstrate which operations belong in it.

**Sparse univariate polynomials (`hex-sparse-poly`,
`hex-sparse-poly-mathlib`).** Specified in
[hex-sparse-poly](Libraries/hex-sparse-poly.md). Use a canonical sorted array of
`(exponent, coefficient)` terms with strictly increasing exponents and no zero
coefficients. Addition merges two arrays; multiplication combines all
pairwise exponent sums, which wants a heap or a map
keyed on the exponent (or a produce-sort-combine pass) rather than a
merge, with canonicalisation afterwards to drop terms whose
coefficients cancelled. Provide direct construction, evaluation, derivative,
and substitution, then `toDense` / `ofDense` with semantic and round-trip
proofs. The library depends on hex-poly at this conversion boundary rather
than making hex-poly generic over representations.

The payoff is inputs whose dense storage is linear in the *exponent*
where sparse storage is linear in the *number of terms*: `x^1000000 − 1`
is two terms against a million coefficients, and substituting `x^k`
behaves the same way. Among cyclotomics the sparse family is
`Φ_{p^k}(x) = Φ_p(x^{p^{k-1}})`. `Φ_p` has degree `p − 1` and all `p` of
its coefficients are `1`, so it is dense. Dense stays the default for
Berlekamp-Zassenhaus, where degrees are small and coefficient vectors
are full.

Gcd and division do not stay sparse: the remainder sequence of two
sparse polynomials is generically dense, so the useful implementation of
`gcd` on `SparsePoly` may be "convert to dense, call the dense
algorithm, convert back". Worth measuring before committing to a sparse
division algorithm.

**Fast polynomial arithmetic.** hex-poly multiplies schoolbook. Its SPEC
describes a Karatsuba crossover for large degree, so implementing
Karatsuba and measuring the crossover is the first step, and the
measurement is what decides whether anything further pays.

After that, in rough order of payoff for this tree:

- **Fast modular composition** (Brent-Kung), computing `g(h) mod f`.
  A better next step than faster multiplication, because it directly
  accelerates Frobenius powering, distinct-degree factorization, Rabin's
  irreducibility test, and Conway polynomial construction, all of which
  exist and are exercised today.
- **Multipoint evaluation and interpolation** via subproduct trees,
  which the reconstruction and factorization work wants.
- **Newton-iteration inversion** of a power series, giving fast division
  and remainder. Put the polynomial adapter and fast division in a later
  `hex-poly-fast` layer depending on both hex-poly and truncated series; do
  not make those two core libraries depend cyclically on each other.
- **Half-gcd** for quasi-linear gcd and extended gcd, the primitive
  under the fast form of the rational reconstruction in
  [hex-modular](Libraries/hex-modular.md), fast Padé approximation, and
  fast resultants. Its subject is the Euclidean transformation matrices, so
  the prerequisite is a verified treatment of those rather than anything
  from the series side, and its correctness proof is fiddly in a way
  plain Euclid's is not.
- **Toom-Cook and NTT** last, with a measured consumer in hand. An NTT
  over word-sized primes with CRT recombination for `ℤ[x]` reuses
  hex-mod-arith's modular arithmetic and hex-arith's Barrett/Montgomery
  reduction.

**Truncated power series (`hex-truncated-series`,
`hex-truncated-series-mathlib`).** Specified in
[hex-truncated-series](Libraries/hex-truncated-series.md). `R[[x]]`
truncated at a fixed precision, with Newton iteration for inverse,
square root, `exp`, and `log`, plus composition and reversion
(Lagrange inversion or the Brent-Kung algorithm). The consumer is fast
division above, which is Newton iteration on the reversed polynomial.

That SPEC corrects the reversion route named here: Lagrange inversion
divides by `k` at every coefficient index and so needs inverses of the
integers below the precision, which `ℤ` does not supply, while the
reversion itself is integral over `ℤ`. Newton iteration on the
composition is the route with the honest hypotheses, and Lagrange
inversion is kept as a second route where the integer inverses exist.

The core representation is a fixed-length coefficient vector and depends only
on hex-basic, not on hex-poly. State its semantics coefficientwise and put
conversion to reversed `DensePoly`, together with fast polynomial division, in
the later `hex-poly-fast` consumer. This dependency direction lets the series
library remain useful independently and prevents a release-graph cycle.

The API splits in two, because only part of it is coefficient-generic.
The ring structure and truncation are generic; each algorithm on top
carries its own hypotheses. Inversion needs the constant term to be a
unit, square root needs a chosen root of the constant term and generally
`2` invertible, `exp` and `log` need division by the integers up to the
precision, and composition and reversion need conditions on the constant
and linear terms. A generic truncated series ring plus separately
constrained algorithms states all of that honestly; one bundled
interface does not.

The theorems are the precision contract: an operation on inputs correct
to precision `n` returns a result correct to precision `n`, with the
Newton iterations doubling precision per step so that the fuel bound is
logarithmic.

**Cyclotomic polynomials (`hex-cyclotomic`,
`hex-cyclotomic-mathlib`).** Specified in
[hex-cyclotomic](Libraries/hex-cyclotomic.md). `Φₙ` for positive `n`,
constructed by the recursive division
`Φₙ = (xⁿ − 1) / ∏_{d | n, d < n} Φ_d`, or faster from the squarefree
kernel of `n` and the identity `Φₙ(x) = Φ_rad(n)(x^(n/rad n))`.

Worth building because cyclotomics currently appear across the tree as
hard-coded fixtures and benchmark inputs rather than as something a
library constructs. The API is `Φₙ` as a `ZPoly`, the factorization
`xⁿ − 1 = ∏_{d | n} Φ_d`, irreducibility over `ℚ`, and the degree
identity `deg Φₙ = φ(n)`.

The computational library depends on hex-poly-z and
[hex-int-factor](Libraries/hex-int-factor.md). Its primary constructor
accepts a `CheckedFactorization` of the index, making divisor
enumeration, `radical`, and `totient` total and avoiding hidden
refactorization; a convenience search API factors the index first.
That SPEC corrects the positivity requirement named here: the
certificate already requires `0 < subject`, so `CheckedFactorization 0`
is uninhabited and neither a `0 < n` argument nor `[NeZero n]` is
needed. Sparse output is an adapter at a consumer through
hex-sparse-poly rather than a dependency of the dense constructor,
because Lake has no conditional dependencies.

[hex-int-factor](Libraries/hex-int-factor.md) needs the *values*
`Φ_d(b)` at an integer `b`, to split `b^n ± 1` before factoring it, and
computes them in `Nat` by its own recursion rather than through a
polynomial. The two agree where they overlap, which is a conformance
boundary owned by the cyclotomic library, since it is the one that can
import both.

**Multivariate gcd and squarefree decomposition.** Required by rational
expression simplification, by the recursive view, and by multivariate
factorization, so it gets its own entry rather than being assumed. The
standard routes are modular and sparse-interpolation algorithms (Brown
for the dense case, Zippel for the sparse), reducing to univariate gcds
at evaluation points and interpolating back. Content and primitive part
in a distinguished variable belong to this library. Their coefficient
hypotheses are stated on the individual operations rather than folded
into the generic polynomial interface.

The certificate is cofactors plus a coprimality witness, and the witness
is not a Bézout identity: `ℤ[x]` and
`R[x₁, …, xₙ]` are not Bézout domains, so the replacement is a modular
witness together with a recursion on contents. That recursion rests on
the universal property of the content, which is gcd maximality one
variable down. The SPEC separates certificate replay from maximality and
schedules the fraction-field embedding, primitive descent, and Gauss
common-factor law needed to prove the latter Mathlib-free.

Over `ℤ` the word "squarefree" needs care: `12x` is not squarefree in
`ℤ[x]` because `4 ∣ 12`, so the ring-theoretic predicate is partly a
question about the integer content. Deciding it does not need
[hex-int-factor](Libraries/hex-int-factor.md) -- Mathlib already
decides squarefreeness on `Nat` -- but producing the square divisor and
the squarefree part does. The library uses the ordinary computer-algebra convention
instead, pulling the content out as an unfactored scalar.

Specified in [hex-mv-gcd](Libraries/hex-mv-gcd.md). Squarefree
decomposition in positive characteristic is explicitly outside that
library version: the Yun recursion runs over a coefficient ring that is
not perfect, so a later amendment must specify the multi-derivative
algorithm rather than reserving an unimplementable milestone.

**Gröbner bases.** Buchberger's algorithm with the Gebauer-Möller pair
criteria, then F4 if benchmarks call for it. Applications are ideal
membership, ideal intersection and quotient, elimination and
triangularization, and radical membership by the Rabinowitsch trick.
Elimination produces elimination ideals and implicitization; solving a
system, in the sense of reconstructing its solutions, is a further
algorithm on top (zero-dimensional solving, then root reconstruction).

Ideal membership is certified by exhibiting the cofactors in
`p = Σ hᵢ gᵢ`, so the checker is a single polynomial identity and the
whole Buchberger search, every pair selection and reduction order
heuristic included, runs untrusted. That gives a `polyrith`-shaped
tactic with no external CAS in the loop. The certificate is directly
checkable rather than small: cofactors can be enormous even where the
checker is trivial.

Non-membership costs more. A nonzero remainder means something only once
the divisor set is certified to be a Gröbner basis, which requires
connecting every basis element back to the original generators and
discharging the S-pair criterion. Treat it as a separate decision with
its own budget.

Elimination also reaches some of the problems the cylindrical algebraic
decomposition item below attacks, over algebraically closed fields
rather than real closed ones. The two are complementary: Gröbner bases
answer questions about complex solutions, CAD about real ones.

**Multivariate Hensel lifting (`hex-mv-hensel`,
`hex-mv-hensel-mathlib`).** The lifting engine, specified before
factorization. Unlike hex-hensel, it lifts a factorization in several
variables against an evaluation ideal and carries the coprimality,
leading-coefficient, modulus/precision, and reconstruction conditions used
by Wang's EEZ algorithm. Hex-hensel is a design model, not an
implementation the new library can call unchanged.

Specified in [hex-mv-hensel](Libraries/hex-mv-hensel.md), over
`MvPoly (n+1) Int cmp` and on top of hex-mv-poly and hex-mv-gcd's exact
division and gcd contract.

Four corrections to what this file said before that SPEC was written,
recorded because they are easy to make again. The sharpest reason
hex-hensel does not apply is not the number of variables: it is that its
prime is simultaneously the residue field and the lifting direction,
whereas multivariately the lifting direction is the evaluation ideal and
the prime only makes the univariate coefficient arithmetic invertible.
The working modulus is therefore fixed for the whole lift, and the
coprimality witness computed at the start stays valid at every step,
where hex-hensel must update its Bézout data. The leading-coefficient
distribution is an *input contract* rather than something the lifting
engine searches for, since finding it is itself recursive multivariate
factorization; what the lifting engine gets from that contract is the
degree drop `deg_{x_i}(f - ∏ F_j) < deg_{x_i} f` that makes every
correction equation solvable. And the ideal-adic direction needs no
coefficient bound at all, because the per-variable degrees of `f` bound
the precision exactly; only the reconstruction of integer coefficients
needs a bound, and Gel'fond's inequality is the one worth proving, with
Kronecker substitution into hex-poly-z's Mignotte bound as the valid but
very weak alternative.

**Multivariate factorization (`hex-mv-factor`,
`hex-mv-factor-mathlib`).** Scope the first version to
`ℤ[x₁, …, xₙ]`: squarefree-decompose, split off content in the main variable,
evaluate the remaining variables at a well-chosen point, factor the resulting
univariate polynomial with Berlekamp-Zassenhaus, then lift with hex-mv-hensel,
including leading-coefficient correction and retry on a bad evaluation point.

The hard prerequisites are hex-mv-poly, [hex-mv-gcd](Libraries/hex-mv-gcd.md),
univariate Berlekamp-Zassenhaus, and
[hex-mv-hensel](Libraries/hex-mv-hensel.md). General factorization over
arbitrary coefficient domains is not the first library: finite fields,
number fields, and `ℤ` require materially different algorithms and
certificates.

The evaluation-point search, the leading-coefficient distribution, the
retry policy, and the recombination of coarser groupings all live here
rather than in the lifting engine; that boundary is drawn in
[hex-mv-hensel §What stays in the downstream consumer](Libraries/hex-mv-hensel.md).

Specified in [hex-mv-factor](Libraries/hex-mv-factor.md), over
`MvPoly n Int cmp` and on top of the four prerequisites above.

The product check certifies a decomposition, not irreducibility, and
that SPEC keeps the two claims in separate types with separate
checkers: `checkDecomp` for the product and `checkIrred` for
irreducibility, the latter reducing to a named list of univariate
irreducibility obligations that the Mathlib companion discharges. Two
corrections to what this file said before it was written. The
`irreducible_of_image_irreducible` route does *not* apply verbatim,
because Wang's leading-coefficient correction rescales each univariate
image by an integer and that theorem's hypothesis is irreducibility of
the image as the lift received it; the factorizer proves the scaled
form itself, one Gauss step longer. And a failed lift is not a
refutation at any modulus the search reaches, so the unconditional
completeness route is a Kronecker substitution into univariate
factorization rather than an exhausted recombination search.

**Generic finite fields, and equal-degree splitting.** Specified in
[hex-finite-field](Libraries/hex-finite-field.md): the Mathlib-free
`F_q` interface and its instances as a new library, and the
equal-degree stage with both Cantor-Zassenhaus arms as amendments to
hex-berlekamp, where the distinct-degree stage and the tactic drivers
already are.

Three corrections to what this file said before that SPEC was written,
recorded because they are easy to make again. The interface does not
need to cover the linear algebra: `Matrix.nullspace` is already stated
for `[Lean.Grind.Field R] [DecidableEq R]`, and `DensePoly`'s division,
gcd, and extended gcd for a bare operation list. `GFq p n` is not the
type to generalise over, since it takes a `Conway.SupportedEntry` and so
exists only for committed table entries; the type that admits an
arbitrary finite field is `GFqField.FiniteField f hf hp hirr`. And there
is no existing pattern of separating a random draw from a deterministic
function -- no production library consumes randomness, only bench and
conformance fixture generators -- so this item introduces the
convention, and the generator with it. That SPEC also records five
prerequisites the sketch did not anticipate, the largest being that
`GFqField.FiniteField` wraps a different quotient representation from
the one hex-poly-fp's `pow_card_eq_self_of_irreducible` is proved for.

**Tactics for rational expressions.** Analogues of Mathematica's
`Together` and `Apart`, in three pieces. Combining an expression built
from ring operations and division into a single quotient `p / q` needs a
common denominator and no gcd. Reducing that quotient to lowest terms is
a separate `cancel`, and that is the piece that needs multivariate gcd.
`Apart` is partial fraction decomposition: factor the denominator, then
solve for the numerators over each factor power. In one variable over
`ℚ` it needs only univariate factorization and the extended gcd on
polynomials, both of which exist, so univariate `Apart` is reachable
well before the multivariate machinery lands.

Denominator nonvanishing surfaces in all three. It is not provable for
free indeterminates without hypotheses, so the side condition has to go
somewhere: either emitted as a side goal (`q ≠ 0`), as `field_simp`
does, or required up front. Matching `field_simp` is probably right.
`Together` also wants a term-level form producing `a = p / q` together
with the nonvanishing proof, for use inside larger computations rather
than as a goal-closing tactic.

**Better primality.** Specified in
[hex-primality](Libraries/hex-primality.md). The diagnosis this file
made -- the mechanism is in place in `HexArith/Nat/Prime.lean` and in
hex-berlekamp-zassenhaus's 94 stored candidate primes, and what it
lacks is scale -- is what that SPEC starts from. Mathlib's baseline is
still the `norm_num` extension in
`Mathlib/Tactic/NormNum/Prime.lean`.

Three corrections to what this file said before that SPEC was written,
all found by reading https://github.com/b-mehta/PrimeCert (Bhavik Mehta
and Kenny Lau) at commit `924f63d9` rather than its description. "Depending on it beats
reimplementing Pocklington" is not available as stated: PrimeCert
requires Mathlib, so only a `-mathlib` companion may depend on it, and
the Mathlib-free layer -- which is where `ZMod64.PrimeModulus`, BZ prime
selection, and `GFq` construction all live -- has to prove Pocklington
itself. Its toolchain is `v4.33.0` against this tree's `v4.32.0-rc1`, so
even the companion cannot depend on it today. And initial-segment sieves
do not "remain open": `PrimeCert/Sieve.lean` is a kernel-reducible
bitset Sieve of Eratosthenes with no imports at all, exercised at
`10^8`, which is a strictly better technique than the
bootstrap-by-trial-division this file proposed. Adopting rather than
duplicating still applies; it means contributing upstream and
reimplementing the Mathlib-free executable core with attribution, not
taking a dependency.

**Integer factorization.** Specified in
[hex-int-factor](Libraries/hex-int-factor.md), which keeps this file's
certificate design unchanged -- the prime-exponent list plus the product
equality, complete because any further prime factor would have to
divide a product of known primes -- and its scoping of discrete
logarithms out of the item.

One sharpening. The consumer that actually exists in this tree is
hex-conway Tier 2, whose group order is `p^n − 1` rather than `p − 1`,
and that is a materially harder family: it is the Cunningham problem.
The structure that makes it tractable is `p^n − 1 = ∏_{d | n} Φ_d(p)`,
which splits one number of `n log p` bits into several of at most
`φ(d) log p` bits, and the values `Φ_d(p)` can be computed in `Nat` by
Möbius inversion without the cyclotomic polynomials of the item above.
For the currently committed Conway table the largest such number is
`13^6 − 1`, which trial division finishes instantly, so Tier 2 is
cheap today and the table's growth policy is what the factorization
cost constrains.

**Ring of integers.** hex-number-field and hex-number-field-tower implement
towers, Trager factorization, and splitting fields; their computational and
Mathlib libraries remain registered with no phases complete. The maximal order
`O_K` is the next object: the Round 2 (Pohst-Zassenhaus) algorithm gives an
integral basis and the field discriminant.

The dependency is [hex-int-factor](Libraries/hex-int-factor.md), for
the squarefree part of the polynomial discriminant, and it is where
such computations turn conditional in practice. The design records what
was assumed when factorization ran out of budget, so a
possibly-non-maximal order announces itself as one; that SPEC's
`PartialFactorization`, which carries an unfactored `residual` and
makes no completeness claim, is the object to record it with.

**Unit and class groups.** The unit group (Dirichlet rank plus
fundamental units) and the class group, by the Minkowski-bound-plus-
relations approach, on top of the maximal order. Both are large
projects and both need their statements chosen with care, because the
standard relation-collection algorithms rest on GRH for factor-base
sufficiency. An individual ideal class relation is checkable, so the
certificate model applies to each relation; completeness of the relation
lattice is the part that is conditional, and a checked set of relations
is not by itself the class group. Either commit to unconditional
Minkowski-bound enumeration with a completeness certificate, or state
conditional theorems that name their hypothesis. Regulator certification
and unit completeness are separate problems again.

**Permutation groups.** Finite permutation groups with orbit and
stabilizer algorithms, subgroup containment, cosets, and the transitive
group data that resolvent methods index against. Independently useful,
and a prerequisite for the next item.

**Galois groups.** The Galois group of an irreducible `p ∈ ℚ[x]` as a
permutation group on its roots, by the resolvent method (Stauduhar):
descend the lattice of transitive subgroups of `Sₙ`, testing at each
step whether a resolvent polynomial has a rational root, using numerical
root approximations to decide which coset to test. hex-roots supplies
the approximations, hex-resultant the resolvents, hex-number-field-tower
the splitting fields, and the permutation group item above the group
theory.

Containment in a subgroup `H` is witnessed by an `H`-invariant
polynomial in the roots taking a rational value, which makes it the
cheap direction. Turning that into a certified group identification
takes more: exact stabilizer data, a fixed labelling of the roots, and
a guarantee that distinct cosets give distinct resolvent values, since
a collision would let a rational value witness the wrong subgroup.
Non-containment is a factorization question about the resolvent.

**Lattice applications beyond recombination.** hex-lll exists to serve
Berlekamp-Zassenhaus recombination, and the same primitive answers
several further questions. `HexManual` already demonstrates the first of
these heuristically; what these items add is a certified API with stated
hypotheses.

- **Minimal polynomial recovery.** Given an algebraic number, find the
  integer polynomial it is a root of, by reducing the lattice spanned by
  the powers of an approximation. The statement needs an exact target to
  refer to: a real number supplied only as a decimal has no mathematical
  referent, and an enclosure that contains a candidate root proves
  nothing on its own. The usable form takes an exact expression together
  with a certified approximation error, plus degree and height bounds,
  and concludes from a separation bound that no other polynomial within
  those bounds can vanish. The Mahler separation bound is the natural
  ingredient; it is specified for hex-roots-mathlib, which has no
  phases complete.
- **Integer relation detection.** The same computation on a vector of
  approximations rather than powers: the PSLQ / LLL question "is there a
  small integer combination of these reals that vanishes". Same
  certificate shape and the same requirement of exact referents and
  error bounds.
- **Stronger reduction.** BKZ, or LLL with deep insertions, if
  recombination benchmarks ever show reduction quality rather than
  reduction time to be the constraint.

**Cylindrical algebraic decomposition.** hex-rcf decides the
one-variable fragment of the theory of real closed fields, where the
cell decomposition of `ℝ` by the roots of a single polynomial does the
work; CAD lifts that to several variables, and
[hex-rcf](Libraries/hex-rcf.md) puts it out of scope.

The implemented base layer is in place. hex-real-roots isolates the real roots
of a squarefree `p ∈ ℤ[x]` with exact Sturm-count witnesses, and hex-roots
does the complex case with Newton-Kantorovich and Pellet witnesses on dyadic
squares. hex-resultant holds univariate subresultants, while hex-number-field
and hex-number-field-tower implement exact arithmetic on algebraic numbers with
certified isolations maintained throughout. Their phase attestations remain
pending. Together these provide the exact sample-point arithmetic a CAD builds
on; sign determination at those points is part of the lifting work below.

The lifting structure on top is entirely to come: multivariate
polynomials, a projection operator (Collins, with the McCallum and Hong
refinements to keep the projection set small), subresultant chains of
multivariate polynomials in the main variable, and sign determination
for a polynomial with algebraic-number coefficients at a sample point in
a cell. That last is where one-variable isolation stops sufficing, since
the polynomial whose roots are wanted has coefficients that are
themselves algebraic numbers from the level below, which is tower
arithmetic.

Two things make this the least certain item on the list, and put it last
in the dependency chain that runs from multivariate polynomials through
factorization to here. CAD is doubly exponential in the number of
variables in the worst case, so the realistic target is quantifier
elimination in two or three variables rather than a general decision
procedure. And the certificate story is weaker than in the univariate
case: a checkable object for a CAD run seems to require the whole cell
decomposition with sign-invariance witnesses, which is the expensive
part. Prototype the projection phase before committing to a proof
architecture.

For comparison, Bhavik Mehta and Arend Mellendijk certify complex root
isolation via the Newton-Kantorovich theorem, a generalisation of the
Krawczyk method Macaulay2 uses, in `CertifyingLmfdbData/Polynomial` at
https://github.com/xgenereux/certifying-lmfdb-data, over Mathlib and a
third-party interval arithmetic library. hex-roots reaches the same
Newton-Kantorovich witness through exact Gaussian-dyadic arithmetic,
with Pellet witnesses as a second certificate form and cluster handling
for non-simple roots. Their treatment of the contraction bound is the
part worth comparing against ours.

**Symbolic summation.** Graduated to
[hex-summation](Libraries/hex-summation.md): Gosper's algorithm for
indefinite hypergeometric summation, Zeilberger's creative telescoping
for the definite case, and Petkovšek's Hyper for hypergeometric
solutions of recurrences, as untrusted searches emitting certificates
whose checkers verify cross-multiplied polynomial identities in
`MvPoly`, with the `gosper`, `zeilberger`, and `hyper` tactics in the
companion.

Two corrections to what this file said before that SPEC was written.
Neither gcd nor rational function normalisation is a prerequisite of
the verified layer: the checkers cross-multiply and never reduce a
fraction, so both live only in the untrusted search. And the identity
`y(k+1) t(k+1) − y(k) t(k) = t(k)` presumes the term ratio exists,
which fails exactly at the support boundary where the telescoping
boundary terms live; every ratio hypothesis in the SPEC is stated in
the multiplied form `q(k) t(k+1) = p(k) t(k)`, which holds at every
natural argument.

The natural extension remains future work here: holonomic function
machinery, closure properties for sequences and functions satisfying
linear recurrences or differential equations with polynomial
coefficients, of which Zeilberger is one instance. A larger project,
worth deferring until the certificate checkers have proved themselves
on the hypergeometric case.

**Fixed-precision p-adic approximations (`hex-padics`,
`hex-padics-mathlib`).** Specified in
[hex-padics](Libraries/hex-padics.md). hex-hensel implements lifting as
an algorithm. First-class `ZpApprox` and `QpApprox` values would be
shared by consumers that each roll their own modular tower:
Berlekamp-Zassenhaus's lifting phase, the Dixon lifting in
[hex-modular-matrix](Libraries/hex-modular-matrix.md), and the p-adic
route to `ℤ[x]` factoring.

That SPEC qualifies the sharing claim. The Dixon solve and hex-hensel
work on integer vectors and coefficient arrays with one shared modulus,
so replacing an entry by a boxed approximation costs more than the
shared bookkeeping saves. What those consumers should take is the
modulus record, the exact division, the valuation, and the
exactification, and the element type is for consumers that hold single
p-adic scalars.

`ZpApprox p N` is a residue modulo `p^N` together with reduction maps and a
valuation lower bound. `QpApprox p` carries a normalized centre, valuation,
and absolute precision rather than pretending that finite data is an exact
p-adic number: finite data cannot distinguish zero from a value of very high
valuation, so inversion and division are partial and lose precision by the
valuation of the divisor. Approximation equality is not mathematical equality
in `ℚ_p`.

The library depends on hex-arith and hex-modular, and uses a checked
hex-primality witness for `p`. Keep the approximation core below hex-hensel,
Berlekamp-Zassenhaus, and hex-modular-matrix; adapters in those consumers can
then replace their private modular towers without creating cycles. An actual
inverse-limit or lazy exact `ℤ_p` / `ℚ_p` type is separate future work. The
precision contract resembles truncated series, but a shared valued-approximation
typeclass should wait until both concrete APIs have been exercised.

**Certificate serialization and caching.** hex-interval-mathlib's SPEC
specifies certificate replay with a stable rule name and a versioned
certificate schema. Factorization, primality, root isolation, and every
other item here that separates an untrusted search from a cheap check
wants the same treatment. A shared format would let expensive searches
run once rather than on every build, and would let downstream users
consume a Hex result without rerunning the search behind it.

The shared part should be an envelope rather than a payload format: a
checker and schema version, a toolchain and ABI identifier, a hash of
the certified input, and a payload type tag. Each library then owns its
own payload, since a common representation across primality certificates
and interval propagation traces would be an abstraction over things with
nothing in common. Validation always replays: a cache hit supplies data,
never trust.

The design questions worth settling early are whether certificates are
content-addressed by the input they certify, how version skew is handled
when a checker changes, and whether stored artefacts live in the
repository or in a cache directory. hex-conway's stored polynomial
database is the closest existing thing and the natural first case study.
This is cross-cutting infrastructure rather than any one library's job,
which is the reason to write it down: otherwise each library invents its
own format and the fifth to do so pays for the first four.
