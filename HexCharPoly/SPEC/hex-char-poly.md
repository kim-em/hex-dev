# hex-char-poly (depends on hex-matrix and hex-poly)

`hex-char-poly` computes the characteristic polynomial
`det (x·I − A)` of a dense square matrix with the division-free
Samuelson--Berkowitz algorithm.  It is Mathlib-free and works over every
commutative ring with decidable equality.

## Representation and convention

`Hex.Matrix.berkowitz A` returns the `n + 1` coefficients in descending
degree order.  `Hex.Matrix.charPoly A` reverses that vector once and stores it
as a normalized `Hex.DensePoly`, whose coefficient order is ascending.  The
result is monic, is `1` for the empty matrix, and has the `x^(n-1)` coefficient
`-trace A`.  Over a nontrivial ring its stored size is exactly `n + 1`.

The algorithm grows trailing principal blocks.  At step `k`, its Toeplitz
column is

```text
1, -a, -(R·C), -(R·B·C), ..., -(R·B^(k-1)·C),
```

where the new block is bordered as `[[a,R],[C,B]]`.  Successive `B^j C`
vectors are computed iteratively, so the complete recursion takes `O(n^4)`
ring operations and performs no division, pivoting, or failure-producing
operation.

## Public API

```lean
namespace Hex.Matrix

def toeplitzMulVec {k : Nat} (t : Vector R (k + 2))
    (v : Vector R (k + 1)) : Vector R (k + 2)
def berkowitzColumn (A : Matrix R n n) (k : Nat) (hk : k + 1 ≤ n) :
    Vector R (k + 2)
def berkowitzStep (A : Matrix R n n) (k : Nat) (hk : k + 1 ≤ n)
    (v : Vector R (k + 1)) : Vector R (k + 2)
def berkowitzAux (A : Matrix R n n) : (k : Nat) → k ≤ n → Vector R (k + 1)
def berkowitz (A : Matrix R n n) : Vector R (n + 1)
def charPoly (A : Matrix R n n) : DensePoly R
def trace (A : Matrix R n n) : R
noncomputable def evalMatrix (p : DensePoly R) (A : Matrix R n n) : Matrix R n n

end Hex.Matrix
```

The library proves the entry formula for Toeplitz multiplication, the leading
coefficient invariant, coefficient reversal, size, degree, monicity, the trace
coefficient, and the closed forms in dimensions zero, one, and two.  The
determinant correspondence and Cayley--Hamilton live in
`hex-char-poly-mathlib`; the computational package deliberately has no
determinant dependency.

## Verification and performance

Integer conformance fixtures cover dimensions zero and one, zero and diagonal
matrices, nilpotent and repeated-eigenvalue Jordan blocks, both triangular
directions, block triangularity, transpose and similarity pairs, dense random
matrices, and entries near `2^63`.  JSONL output is checked coefficient-for-
coefficient against python-flint's `fmpz_mat.charpoly()` without normalizing or
reversing either list.  Lean guards check Cayley--Hamilton on every fixture and
retain the explicit counterexample showing that a monic degree-`n` annihilator
need not be the characteristic polynomial.

Benchmarks cover dense random dimension and bit-width ladders, small-entry
tridiagonal matrices, and self-checking companion/Jordan families.  Random
runs report the peak bit size among Toeplitz columns and intermediate
coefficient vectors.  FLINT's selected characteristic-polynomial routine and
PARI's flag-3 Berkowitz routine are informational external comparators.
