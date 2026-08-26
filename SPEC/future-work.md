# Further work

Sketches for libraries and algorithms that do not yet have a SPEC. Each item
records enough scope, dependencies, and correctness obligations to start a
SPEC; it is not itself a specification.

[Libraries/README.md](Libraries/README.md) indexes work that has a SPEC, and
[libraries.yml](../libraries.yml) records the libraries currently registered in
the monorepo. Once an item below gains a SPEC, remove it from this file.

The usual certificate discipline applies: checking an equality, divisibility,
or decomposition establishes only that positive claim. Minimality,
maximality, irreducibility, uniqueness, nonexistence, and completeness each
need their own witness or theorem.

## Matrix and linear algebra

### Certified eigenpair enclosures

Run an untrusted numerical eigensolver and verify an approximate eigenpair
with interval arithmetic, using a fixed-point or contraction argument to
enclose a true eigenpair.

Scope the first version to simple isolated eigenpairs of symmetric matrices.
Multiple or defective eigenvalues, singular values, rectangular matrices,
phase conventions, pivoted QR, and interval inverse bounds should remain
separate extensions. The verified layer depends on `hex-interval-mathlib` and
the matrix correspondence API; `hex-char-poly`, `hex-roots`, and
`hex-number-field` provide independent spectral cross-checks and exact names
for algebraic eigenvalues.

The SPEC must choose an enclosure theorem whose hypotheses are executable to
check and decide how an untrusted solver supplies candidates. An in-Lean
floating-point implementation and an FFI solver are equivalent from the
trusted layer's point of view.

### Sparse matrices

Add a canonical sparse representation alongside the dense matrix type, with
`toDense` as its specification function. The first SPEC should choose among a
coordinate builder, compressed sparse row storage, or a builder/frozen pair.
The representation invariant must exclude duplicate positions and stored
zeros and must support extensionality through `toDense`.

The initial operation set should include construction, lookup, addition,
scalar multiplication, transpose, sparse-by-sparse multiplication, and
sparse-by-dense products. Correctness is expressed by `toDense` commuting
with each operation. Benchmarks need a named consumer and input family where
dense storage is genuinely the constraint before the project commits to a
second matrix ecosystem.

Sparse elimination is a separate project. Fill-in makes a frozen CSR layout a
poor update structure and introduces pivot-order questions such as Markowitz
selection. It should follow the representation library and be compared with
black-box methods on the finite-field workloads that motivate it.

### Black-box linear algebra

Specify Wiedemann and block Wiedemann algorithms over finite fields, treating
a matrix as a linear map rather than stored entries. Intended operations are
solving `A x = b`, producing kernel vectors, and recovering Krylov minimal
polynomials for large sparse systems.

The trusted result checks a proposed solution or kernel vector with a single
matrix-vector product. Claims about rank, nullity, minimality, or exhaustive
kernel bases need additional certificates. The library should depend on the
generic finite-field interface and the minimal-polynomial vocabulary without
requiring the sparse-matrix representation.

## Polynomial computation

### Swappable polynomial representations (deferred)

Do not introduce a `PolyOps` or `LawfulPolyOps` abstraction solely because
dense and sparse polynomials both exist. Their useful operations, complexity,
and normalization behaviour differ, and gcd or division of sparse inputs
usually becomes dense. Keep explicit conversions until several real consumers
show which operations a common interface must support.

### Positive-characteristic multivariate squarefree decomposition

Amend `hex-mv-gcd` with squarefree decomposition over perfect fields of
positive characteristic. The characteristic-zero Yun recursion is
insufficient because every formal derivative may vanish. The replacement
needs multi-derivative splitting, detection of `p`-th powers, coefficient
`p`-th roots supplied by the finite-field interface, and a recursion whose
measure accounts for the degree drop after extracting a `p`-th root.

The SPEC must state whether it supports arbitrary perfect fields or only the
project's finite-field instances and must distinguish squarefree factor
decomposition from irreducible factorization.

### Gröbner bases

Start with Buchberger's algorithm and the Gebauer-Möller pair criteria; add F4
only if benchmarks justify it. Applications include ideal membership,
intersection, quotient, elimination, implicitization, and radical membership
through the Rabinowitsch trick.

Ideal membership has a compact trusted boundary: return cofactors witnessing
`p = sum_i h_i * g_i`. Non-membership requires more. A nonzero remainder is
conclusive only after the divisor set is certified to be a Gröbner basis and
connected to the original generators, including the required S-pair
criterion. Treat positive and negative decisions as separate certificate
types with separate budgets.

The computational layer depends on `hex-mv-poly`; coefficient-domain
hypotheses and monomial order must be explicit. Zero-dimensional solving and
root reconstruction are downstream work rather than part of the first basis
library.

### Rational-expression tactics

Specify three related but separable operations:

- `Together`: combine ring operations and division into one quotient. This
  needs common-denominator arithmetic but no gcd.
- `cancel`: reduce a quotient to lowest terms. The multivariate form depends
  on `hex-mv-gcd`.
- `Apart`: partial fractions. The univariate rational form can use existing
  factorization and polynomial extended gcd; multivariate variants require
  substantially more machinery.

Denominator nonvanishing cannot be inferred for free indeterminates. Tactics
should emit explicit side goals, following `field_simp`, and term-level APIs
should return both the normalized expression and the hypotheses under which
it equals the input.

### Holonomic functions

Extend [hex-summation](Libraries/hex-summation.md) with closure operations for
sequences and functions satisfying linear recurrences or differential
equations with polynomial coefficients. Candidate operations include sum,
product, specialization, definite summation, differentiation, and integration,
with executable recurrence certificates for each closure step.

The first SPEC should choose either the recurrence or differential-equation
side and define normalization, initial-value obligations, singular indices,
and equality from a shared operator. It should reuse summation's certificate
checker rather than enlarge the trusted surface of its search algorithms.

## Number fields and groups

### Exact p-adic numbers

Add an inverse-limit or lazy exact `Z_p` and `Q_p` type above
[hex-padics](Libraries/hex-padics.md). Exact equality cannot be decided from a
finite approximation, so the API must distinguish observation at a requested
precision from mathematical equality. Arithmetic should refine precision on
demand and expose nontermination or undecidability honestly where zero-testing
is required.

Do not introduce a shared valued-approximation typeclass until both the
fixed-precision p-adic and truncated-series APIs have enough consumers to
identify a useful common contract.

### Ring of integers

Build the maximal order `O_K` of a number field, with an integral basis and
field discriminant, using a Round 2/Pohst-Zassenhaus-style algorithm. The
library depends on `hex-number-field`, `hex-number-field-tower`, and
`hex-int-factor` for the discriminant's squarefree part.

Factorization may run out of budget. The result type must distinguish a proved
maximal order from an order conditional on an incomplete factorization and
must retain the residual factorization data rather than silently asserting
maximality.

### Unit and class groups

Build the unit group, regulator, and ideal class group on top of the maximal
order. Relation collection produces checkable individual relations, but a set
of relations is not by itself a completeness proof for the relation lattice.

The SPEC must choose between unconditional enumeration bounded by Minkowski
with an explicit completeness certificate and conditional algorithms whose
hypotheses, including any GRH assumption used for factor-base sufficiency, are
present in the theorem statements. Unit completeness, regulator
certification, and class-group completeness are distinct obligations.

### Permutation groups

Provide finite permutation groups with orbits, stabilizers, subgroup
containment, cosets, and the transitive-group data required by resolvent
methods. Executable certificates should cover membership and subgroup
relations; classification tables and their trust boundary need an explicit
data policy.

This library is independently useful and is a prerequisite for certified
Galois-group computation.

### Galois groups

Compute the Galois group of an irreducible polynomial over `Q` as a
permutation group on its roots, using Stauduhar-style resolvent descent.
Dependencies include permutation groups, `hex-roots`, `hex-resultant`,
univariate factorization, and `hex-number-field-tower`.

Subgroup containment can be witnessed by an invariant polynomial in the roots
taking a rational value. Full group identification additionally needs exact
stabilizer data, a fixed root labelling, separation of distinct coset
resolvent values, and certified non-containment at rejected branches.

## Lattices and real algebra

### Lattice applications beyond factor recombination

Build certified APIs on top of `hex-lll` for:

- Minimal-polynomial recovery from an exact algebraic target, a certified
  approximation error, and degree and height bounds.
- Integer-relation detection for exact real targets with certified
  approximations and coefficient bounds.
- Stronger reduction such as deep-insertion LLL or BKZ, once benchmarks show
  that reduction quality rather than reduction time is the limiting factor.

An enclosure around a candidate root or relation is not sufficient. Recovery
needs a separation theorem ruling out every competing polynomial or relation
within the stated bounds.

### Cylindrical algebraic decomposition

Extend the univariate real-closed-field decision procedure to quantifier
elimination in a small number of variables. The intended stack includes a
projection operator, multivariate subresultant chains in a distinguished
variable, exact algebraic sample points, and sign determination for
polynomials with algebraic coefficients.

Dependencies include `hex-mv-poly`, `hex-mv-factor`, `hex-resultant`,
`hex-real-roots`, `hex-number-field`, and `hex-number-field-tower`. Scope the
first version to two or three variables. Before fixing a public API, prototype
the projection phase and a certificate that carries a complete cell
decomposition with the sign-invariance evidence needed for a negative as well
as a positive decision.

## Cross-cutting infrastructure

### Certificate serialization and caching

Define a shared envelope for expensive certificates while leaving each
library's payload format under its own versioning. The envelope should include
the checker and schema versions, toolchain and ABI identifiers, a hash of the
certified input, and a payload type tag.

A cache hit supplies untrusted data and validation always replays the checker.
The SPEC must decide content addressing, version skew, storage location, and
resource limits for decoding and replay. `hex-conway`'s stored database and
the interval certificate schema are useful first consumers, but neither
should become a universal payload representation.
