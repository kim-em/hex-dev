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
group. Both are separate libraries rather than additions to hex-matrix,
because both need the extended GCD from hex-arith and the echelon
contracts from hex-row-reduce, and Hermite normal form needs a
determinant from hex-bareiss for its modular algorithm.

Two corrections to what this file said before those SPECs were written,
recorded because they are easy to make again. The `IsHNF` field list
should not carry `det transform = 1 ∨ det transform = -1`, which follows
from `IsEchelonForm.transform_inv` and `det_mul`; and it must carry the
condition that each pivot is the leading nonzero entry of its row, which
`IsEchelonForm` does not imply and without which uniqueness is false.

**Sylvester's identity (hex-matrix).** The Desnanot-Jacobi identity
relating minors of a matrix. Now the primary proof strategy for
`bareiss_eq_det` (see hex-matrix section above). Listed here as
further work only in the sense that it's a useful standalone result
beyond the Bareiss application.

**Generic Bareiss over integral domains (hex-matrix).** Generalize
Bareiss from `Int` to any integral domain with a data-carrying exact
division operation (`ediv : α → α → α` with `b ∣ a → ediv a b * b = a`);
for `Int` this is `Int.divExact`
and no zero divisors (`a * b = 0 → a = 0 ∨ b = 0`).

**Characteristic polynomial.** The matrix family holds dense operations
in hex-matrix, rank and nullspace in hex-row-reduce, and the determinant
and adjugate in hex-determinant. A characteristic polynomial belongs
alongside them. The algorithms divide along the line this project cares
about, namely whether they divide at all:

- **Berkowitz (Samuelson-Berkowitz)** is division-free, works over any
  commutative ring with no invertibility side conditions, and costs
  `O(n⁴)`. For a library whose base ring is `Int` this is the natural
  default and the easiest to state correctly.
- **Hessenberg reduction** followed by the recurrence on leading
  principal minors, and **Danilevsky's method** (reduction to Frobenius
  companion form by similarity), are faster and divide by pivot entries.
  Over `ℤ` each wants a fraction-free reformulation in the style of
  hex-bareiss, or a detour through `ℚ` and the coefficient growth that
  brings.
- **Multi-modular**, computing `χ_A` modulo several primes and
  recombining, using [hex-modular](Libraries/hex-modular.md) with a
  coefficient bound from the matrix norm. The determinant in
  [hex-modular-matrix](Libraries/hex-modular-matrix.md) is the same
  shape one degree down, and its handling of the bound is the model to
  follow.

Isolating the roots of `χ_A` with hex-real-roots and hex-roots would give
certified eigenvalue enclosures; hex-number-field can name the resulting exact
eigenvalues.

**Minimal polynomial.** A separate computation from the characteristic
polynomial. The Krylov sequence `v, Av, A²v, …` yields the minimal
polynomial of the vector `v`, which divides the matrix minimal
polynomial and coincides with it for generic `v`; the lcm over a basis
removes the genericity assumption.

Certifying minimality takes a lower-bound witness, since annihilation
plus division into `χ_A` is satisfied by every multiple of the true
minimal polynomial that divides `χ_A`. A vector whose Krylov iterates
are independent through degree `deg m − 1` and annihilated at degree
`deg m` supplies the missing half. Certified invariant factors supply
it too, and give more.

**Polynomial matrices and invariant factors.** Matrices over `F[x]`,
the Smith normal form of the characteristic matrix `xI − A`, and the
invariant factors read off its diagonal. This is the route to canonical
forms: the invariant factors give the rational canonical form directly,
the largest of them is the minimal polynomial, and their product is the
characteristic polynomial, all certified from one computation.

Two distinctions are worth holding onto. The factorization of `χ_A` does
not determine the canonical form, because matrices sharing a
characteristic polynomial can have different invariant factors. And this
is not the integer Smith normal form of [hex-smith](Libraries/hex-smith.md):
the base ring is `F[x]`, the units are the nonzero constants, and the two
items share an algorithm shape rather than a theorem. The
[hex-hermite](Libraries/hex-hermite.md) SPEC records, under "Why `Int`
and not a Euclidean domain class", exactly which parts transfer (the 2x2
elimination step) and which do not (pivot normalisation, the reduction of
entries above a pivot, the termination measure, and the growth problem
the algorithm choice is designed around).

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
makes the soundness theorem conditional; in one variable the
corresponding fact is `Int.dvd_gcd` and the theorem is unconditional.

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

**Swappable polynomial representations.** Abstract over the polynomial
representation via typeclasses, allowing sparse and hash-backed
representations alongside `DensePoly`. For now, all libraries use
`DensePoly` directly.

The same abstraction problem is now concrete for multivariate polynomials.
The release-quality HexMvPoly kernel sweep at clean commit
`91adf91b04cd9aa676e7bb08fed176f2038fd0a2` did not meet its predeclared
gate. After round-matched import and construction subtraction, the
canonical sorted-list proxy's terminal point ratios were 5.216× for addition,
2.379× for cancellation, 2.890× for SOS, and 1.586× for structural
collisions. The first three conservative intervals began at 1.287×, 1.265×,
and 1.477× respectively; addition and structural collisions were
noise-limited. Collision-heavy multiplication had a 0.930× point estimate
with an unresolved [0.359×, 2.329×] interval. No family had a lower bound
above 2×, let alone two families. The exact record is
`reports/bench-results/hex-mv-poly-kernel-91adf91b-chungus2.json`.

The current evidence therefore does not demonstrate the gate.
`Hex.MvPoly` remains the single `ExtTreeMap` representation by default. The
proof-probe sorted adapter is comparison evidence only and must not be exposed
as production API. All five terminal comparisons are unresolved, and the
measured rungs finish well below the per-module budget rather than
establishing the largest budget-fitting cases required for a positive
decision. A future decision needs a preregistered larger ladder, more samples,
and preferably a quiescent host. In particular, the SOS-scale null has a
1.199 s conservative envelope, a 3.252% IQR/build ratio, and yields a 2.890×
SOS point estimate with only a 1.477× conservative lower bound.

Typeclass interface:
```lean
class PolyOps (P : Type*) (R : outParam Type*) extends
    Add P, Mul P, Neg P, Zero P, One P, BEq P where
  X : P
  C : R → P
  degree : P → Nat
  coeff : P → Nat → R
  leadingCoeff : P → R
  dropZeros : P → P
  divMod : P → P → P × P
  eval : P → R → R
  ofCoeffs : Array R → P
  toCoeffs : P → Array R

class LawfulPolyOps (P : Type*) (R : outParam Type*) [PolyOps P R] where
  -- Ring axioms
  add_comm : ∀ a b : P, a + b = b + a
  add_assoc : ∀ a b c : P, a + b + c = a + (b + c)
  mul_comm : ∀ a b : P, a * b = b * a
  mul_assoc : ∀ a b c : P, a * b * c = a * (b * c)
  add_zero : ∀ a : P, a + 0 = a
  mul_one : ∀ a : P, a * 1 = a
  left_distrib : ∀ a b c : P, a * (b + c) = a * b + a * c
  -- Coefficient semantics
  coeff_add : ∀ (a b : P) (i : Nat), coeff (a + b) i = coeff a i + coeff b i
  coeff_mul : ...  -- convolution formula
  -- BEq correctness: == agrees with coefficient equality
  beq_iff : ∀ a b : P, (a == b) = true ↔ ∀ i, coeff a i = coeff b i
  -- dropZeros: normalization to canonical form
  dropZeros_idem : ∀ p, dropZeros (dropZeros p) = dropZeros p
  dropZeros_coeff : ∀ p i, coeff (dropZeros p) i = coeff p i
  dropZeros_ext : ∀ p q, dropZeros p = p → dropZeros q = q →
      (∀ i, coeff p i = coeff q i) → p = q
  -- Division
  divMod_spec : ∀ a b : P, let (q, r) := divMod a b; q * b + r = a
  -- Evaluation is a ring homomorphism
  eval_C : ∀ r x, eval (C r) x = r
  eval_X : ∀ x, eval X x = x
  eval_add : ∀ p q x, eval (p + q) x = eval p x + eval q x
  eval_mul : ∀ p q x, eval (p * q) x = eval p x * eval q x
```

`dropZeros` is the canonical form function. For dense representations,
it strips trailing zeros. For sparse representations, it removes entries
with zero coefficients. `dropZeros_ext` gives extensionality on the
subtype `{ p : P // dropZeros p = p }` — two canonical-form polynomials
with the same coefficients are propositionally equal.

The subtype `CanonicalPoly P := { p : P // dropZeros p = p }` is where
the `≃+*` lives. The `-mathlib` companion would prove:

```lean
def CanonicalPoly (P : Type*) [PolyOps P R] := { p : P // dropZeros p = p }

def equiv [LawfulPolyOps P R] : CanonicalPoly P ≃+* Polynomial R
```

Eagerly-normalizing implementations (like `DensePoly`) satisfy
`dropZeros = id`, so `CanonicalPoly (DensePoly R) ≃ DensePoly R` and
the subtype wrapper is trivial. Lazy implementations pay the cost of
normalization only when they need propositional equality.

Alternative representations:

Sparse sorted array:
```lean
structure SparsePoly (R : Type*) [Zero R] [DecidableEq R] where
  terms : Array (Nat × R)
  sorted : ∀ i j, i < j → i < terms.size → j < terms.size →
           (terms[i]).1 < (terms[j]).1
  nonzero : ∀ i, i < terms.size → (terms[i]).2 ≠ 0
```

Sparse `ExtHashMap`-backed (with extensional equality):
```lean
structure ExtHashPoly (R : Type*) [Zero R] [BEq R] [Hashable Nat]
    [EquivBEq Nat] [LawfulHashable Nat] where
  map : ExtHashMap Nat R
  nonzero : ∀ k v, map.find? k = some v → v ≠ 0
```

Using `ExtHashMap` (not `HashMap`) gives extensionality lemmas — two
`ExtHashPoly` values are equal iff they have the same key-value pairs.

**Sparse univariate polynomials.** The `SparsePoly` sketch above,
implemented: addition by merging two sorted term lists; multiplication
by combining all pairwise exponent sums, which wants a heap or a map
keyed on the exponent (or a produce-sort-combine pass) rather than a
merge, with canonicalisation afterwards to drop terms whose
coefficients cancelled. Then `toDense` / `ofDense` with a round-trip
proof, and the `PolyOps` / `LawfulPolyOps` instances so it drops into
the abstraction.

The payoff is inputs whose dense storage is linear in the *exponent*
where sparse storage is linear in the *number of terms*: `x^1000000 − 1`
is two terms against a million coefficients, and substituting `x^k`
behaves the same way. Among cyclotomics the sparse family is
`Φ_{p^k}(x) = Φ_p(x^{p^{k-1}})`; `Φ_p` itself has `p − 1` nonzero
coefficients and is dense. Dense stays the default for
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
  and remainder. Depends on truncated power series, below.
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

**Truncated power series.** `R[[x]]` truncated at a fixed precision,
with Newton iteration for inverse, square root, `exp`, and `log`, plus
composition and reversion (Lagrange inversion or the Brent-Kung
algorithm). The consumer is fast division above, which is Newton
iteration on the reversed polynomial.

The API splits in two, because only part of it is coefficient-generic.
The ring structure and truncation are generic; each algorithm on top
carries its own hypotheses. Inversion needs the constant term to be a
unit, square root needs a chosen root of the constant term and generally
`2` invertible, `exp` and `log` need division by the integers up to the
precision, and composition and reversion need conditions on the constant
and linear terms. A generic truncated series ring plus separately
constrained algorithms states all of that honestly; one bundled
interface does not.

The specification function is truncation from the polynomial type, and
the theorems are the precision contract: an operation on inputs correct
to precision `n` returns a result correct to precision `n`, with the
Newton iterations doubling precision per step so that the fuel bound is
logarithmic.

**Cyclotomic polynomials.** `Φₙ` for positive `n`, constructed by the
recursive division `Φₙ = (xⁿ − 1) / ∏_{d | n, d < n} Φ_d`, or faster
from the squarefree kernel of `n` and the identity
`Φₙ(x) = Φ_rad(n)(x^(n/rad n))`. The index is positive throughout, so
the API takes `0 < n` or `[NeZero n]` rather than a bare `Nat`; the
identity and the degree formula both need it.

Small enough to build rather than plan, and worth recording because
cyclotomics currently appear across the tree as hard-coded fixtures and
benchmark inputs rather than as something a library constructs. The
natural API is `Φₙ` as a `ZPoly`, the factorization
`xⁿ − 1 = ∏_{d | n} Φ_d`, irreducibility over `ℚ`, and the degree
identity `deg Φₙ = φ(n)`.

[hex-int-factor](Libraries/hex-int-factor.md) needs the *values*
`Φ_d(b)` at an integer `b`, to split `b^n ± 1` before factoring it, and
computes them in `Nat` by Möbius inversion rather than through a
polynomial. The two should agree where they overlap, which is one
conformance case in that SPEC.

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
variable down, so the Mathlib-free soundness theorem is conditional and
the companion discharges the hypothesis.

Over `ℤ` the word "squarefree" needs care: `12x` is not squarefree in
`ℤ[x]` because `4 ∣ 12`, so the ring-theoretic predicate is partly a
question about the integer content. Deciding it does not need
[hex-int-factor](Libraries/hex-int-factor.md) -- Mathlib already
decides squarefreeness on `Nat` -- but producing the square divisor and
the squarefree part does. The library uses the ordinary computer-algebra convention
instead, pulling the content out as an unfactored scalar.

Specified in [hex-mv-gcd](Libraries/hex-mv-gcd.md). Squarefree
decomposition in positive characteristic is scheduled there but not
solved: the Yun recursion runs over a coefficient ring that is not
perfect, so the univariate fix does not apply level by level.

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

**Multivariate factorization.** Multivariate squarefree decomposition,
split off the content in the main variable, evaluate the remaining
variables at a well-chosen point to reduce to a univariate problem over
`ℤ`, factor that with Berlekamp-Zassenhaus, then lift the factorization
back by multivariate Hensel lifting (Wang's EEZ algorithm), with
leading-coefficient correction and retry on a bad evaluation point.

Prerequisites are the multivariate gcd, content, and squarefree
decomposition above, and univariate Berlekamp-Zassenhaus. Multivariate
Hensel lifting is its own algorithm rather than a call into hex-hensel:
it lifts in several variables against an evaluation ideal, so hex-hensel
is the model to follow.

The product check certifies a decomposition. Irreducibility of each
returned factor is the further obligation, hard in the same way as the
univariate case, so the API either carries irreducibility certificates
per factor or advertises itself as returning a decomposition and lets
the caller ask for more.

**Generic finite fields, and equal-degree splitting.** Three related
items in dependency order. This group is the best-aligned on the list,
since distinct-degree factorization, prime-field factoring, Conway
polynomials, and `GFq` all exist.

First, **genericity**. hex-berlekamp is written against `FpPoly` and
`ZMod64`. A finite-field interface covering cardinality, inverse,
Frobenius, and the linear algebra Berlekamp's kernel step uses, with
both the prime-field and extension cases implementing it, is what lets
the factoring algorithms run over `GFq p n`. Everything else here
depends on it.

Second, **an explicit equal-degree stage**. hex-berlekamp exports
distinct-degree factorization, while the factorizer reaches its result
through Berlekamp-kernel splitting and a sweep over constants `c` in
`gcd(f, h − c)`, linear in `p` per witness in the worst case.
Introducing a DDF-to-EDF pipeline is a restructuring of the factorizer,
not a single new function.

Third, **Cantor-Zassenhaus**, which is two algorithms. For odd `q`, pick
a random `h` and split by `gcd(f, h^((q^d − 1)/2) − 1)`, with the
powering done in `F_q[x]/(f)`. For even `q` that exponent is not an
integer and the split uses the trace map
`h + h² + h⁴ + ⋯ + h^(2^(d·m−1))`. Both are Las Vegas, so randomness
costs retries and never correctness, and the random input is an explicit
argument rather than a monad, following the tree's existing pattern of
separating the random draw from the deterministic function.

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

**Symbolic summation.** Gosper's algorithm for indefinite hypergeometric
summation, and Zeilberger's creative telescoping for the definite case.
This has the best ratio of user-visible payoff to proof burden on the
list. Gosper's output is a rational `y` with
`y(k+1) t(k+1) − y(k) t(k) = t(k)`, where `y(k) t(k)` is the
antidifference; Zeilberger's is a recurrence together with a rational
certificate function `R(n, k)`. In both cases the identity to check is
between rational functions, and clearing denominators turns it into a
polynomial identity, so the verified core is small and the search that
found the certificate runs untrusted.

Two obligations sit outside that core, and the SPEC should separate
them. Clearing denominators introduces poles and exceptional indices, so
the polynomial identity carries nonvanishing side conditions back to the
rational statement. And a verified summand identity is not yet the
definite-sum recurrence: the telescoping has to be summed over the
range, which brings in boundary terms, the support of the summand, and
the semantics of the binomial and factorial notation the identity is
stated in. Splitting "replay a supplied certificate" from "search for a
certificate and conclude the definite sum" makes the first shippable
long before the second.

What this buys is a tactic proving binomial coefficient identities
(Vandermonde, Dixon, the sums that appear constantly in combinatorics)
rather than requiring them to exist in Mathlib. Prerequisites are
multivariate polynomial arithmetic, gcd, and rational function
normalisation. The checker is small enough to write first and test
against hand-supplied certificates.

The natural extension is holonomic function machinery: closure
properties for sequences and functions satisfying linear recurrences or
differential equations with polynomial coefficients, of which Zeilberger
is one instance. A larger project, worth deferring until the certificate
checker has proved itself on the hypergeometric case.

**p-adic numbers as a type.** hex-hensel implements lifting as an
algorithm. A first-class `Zp` and `Qp` at fixed precision would be
shared by consumers that each roll their own modular tower:
Berlekamp-Zassenhaus's lifting phase, the Dixon lifting in
[hex-modular-matrix](Libraries/hex-modular-matrix.md), and the p-adic
route to `ℤ[x]` factoring.

`Zp` at precision `N` is `ℤ/p^N ℤ` with a valuation, and is the easy
half. `Qp` needs elements to carry precision explicitly, as a centre
with a valuation and a precision bound rather than as a residue: finite
data cannot distinguish zero from a value of very high valuation, so
inversion and division are partial and lose precision by the valuation
of the divisor. The theorems are that precision contract, in the same
spirit as the truncated power series item though over a different
valuation; a shared abstraction may emerge once both exist.

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
