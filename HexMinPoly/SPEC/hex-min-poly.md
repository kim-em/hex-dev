# hex-min-poly

`hex-min-poly` provides executable minimal polynomials for dense square
matrices over fields. It is Mathlib-free. Its dependencies are `hex-matrix`,
`hex-row-reduce`, and `hex-poly`; correspondence with Mathlib belongs in
`hex-min-poly-mathlib`.

## Convention

For a square matrix `A : Matrix F n n`, `minPoly A` is the unique monic dense
polynomial that annihilates every vector and divides every other polynomial
with that property. Polynomial coefficients are stored in ascending order.
For a vector `v`, `vecMinPoly A v` is its monic order polynomial: it
annihilates `v` and divides every other polynomial that annihilates `v`.

The empty matrix has minimal polynomial `1`. In positive dimension, the zero
matrix has minimal polynomial `x` and the identity has minimal polynomial
`x - 1`. The zero vector has order polynomial `1`.

## Algorithm

`krylovRows A v r` materializes

```text
v, A v, A^2 v, ..., A^(r-1) v
```

in one forward recurrence. Each row after the first is computed from the
preceding row, so no matrix-vector product is repeated within the array.
`krylovMat` presents those vectors as matrix rows.

`krylovDeg` is the rank of the full `(n + 1) × n` Krylov matrix. The first
`d = krylovDeg A v` rows are independent and the next lies in their span.
`krylovCoeffs?` constructs the full Krylov row workspace once, slices its
prefix, and solves for that first dependency by row reduction. If the
ascending dependency coefficients are `c_0, ..., c_(d-1)`, then
`dependencyPoly` returns

```text
x^d - c_(d-1) x^(d-1) - ... - c_1 x - c_0.
```

`minPoly` computes the least common multiple of the order polynomials of all
standard basis vectors. This deterministic basis sweep is complete because a
polynomial annihilates the matrix exactly when it annihilates every basis
vector.

## Public API

```lean
namespace Hex.Matrix

def evalVec (p : DensePoly F) (A : Matrix F n n)
    (v : Vector F n) : Vector F n
def basisVec (n : Nat) (i : Fin n) : Vector F n
def krylovVec (A : Matrix F n n) (v : Vector F n) :
    Nat → Vector F n
def krylovRows (A : Matrix F n n) (v : Vector F n) :
    (r : Nat) → Vector (Vector F n) r
def krylovMat (A : Matrix F n n) (v : Vector F n)
    (r : Nat) : Matrix F r n
def krylovDeg (A : Matrix F n n) (v : Vector F n) : Nat
def krylovCoeffs? (A : Matrix F n n) (v : Vector F n) :
    Option (Vector F (krylovDeg A v))
def dependencyPoly {d : Nat} (c : Vector F d) : DensePoly F
def vecMinPoly (A : Matrix F n n) (v : Vector F n) : DensePoly F
def minPoly (A : Matrix F n n) : DensePoly F

end Hex.Matrix
```

The proof-facing universal properties are:

```lean
theorem vecMinPoly_dvd (A : Matrix F n n) (v : Vector F n)
    (p : DensePoly F) (h : evalVec p A v = 0) :
    vecMinPoly A v ∣ p

theorem minPoly_dvd_iff (A : Matrix F n n) (p : DensePoly F) :
    minPoly A ∣ p ↔ ∀ v : Vector F n, evalVec p A v = 0
```

Both computed polynomials are monic and satisfy their annihilation property.

## Certificates

`minPolyCert A` returns a `MinPolyCert F n`. For every standard basis vector,
the certificate records its order polynomial and a right inverse of the
independent Krylov prefix. Every LCM step records common-factor,
cofactor, and Bézout identities. These witnesses establish both directions
of minimality without division inside the checker.

`MinPolyCert.check A c` checks:

- the stated order degree and polynomial;
- annihilation by every order polynomial;
- the right-inverse identities that exclude lower-degree annihilators;
- all LCM divisibility and Bézout identities;
- the final polynomial, monicity, and basis-wide annihilation claim.

`MinPolyCert.check_sound` proves that a successful check makes the claimed
polynomial monic, makes it annihilate every vector, and makes it divide every
other polynomial with that property. `minPolyCert_check` proves that the
bundled producer succeeds.

## Complexity

For dense `n × n` matrices, one Krylov row extension is a dense
matrix-vector product and costs `O(n²)` field operations. Constructing up to
`n + 1` rows costs `O(n³)`. Row reduction of the resulting dense Krylov matrix
also costs `O(n³)`. The complete standard-basis sweep therefore has a
conservative `O(n⁴)` field-operation bound. Polynomial LCM work does not
increase that bound.

The benchmark surface separates direct evaluation, Krylov construction,
vector order, matrix minimal polynomial, certificate production, and
certificate checking. It also includes dense rational, fixed-width prime
field, derogatory, and companion-matrix families. FLINT and PARI are
informational external comparators because they use different algorithms.

## Conformance

Required CI conformance checks direct operation examples, valid certificates,
and corrupted inverse, order, Bézout, and monicity witnesses. Fixture families
cover empty and scalar matrices, zero and identity matrices, nilpotent chains,
repeated eigenvalues, triangular and block matrices, transpose and similarity
pairs, companion matrices, dense random matrices, and large integer entries.
The fixture output is checked coefficient-for-coefficient against
python-flint for integer and rational matrices.

## Mathlib correspondence

`hex-min-poly-mathlib` proves that conversion to Mathlib polynomials sends
`Hex.Matrix.minPoly A` to `minpoly F (matrixEquiv A)`. It transports vector
orders to an `aeval` divisibility characterization, identifies executable LCM
with Mathlib's normalized LCM, proves divisibility into `charPoly`, and proves
transpose and similarity invariance.
