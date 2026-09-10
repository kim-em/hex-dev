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

For closed integer matrices, importing the umbrella also provides the
`char_poly` elaborator and tactic:

```lean
def A : Hex.Matrix Int 2 2 := #m[1, 2; 3, 4]

#check char_poly A
-- (char_poly A).poly : Hex.DensePoly Int
-- (char_poly A).charPoly_eq : Hex.Matrix.charPoly A = (char_poly A).poly

example : Hex.Matrix.charPoly A = #p[-2, -5, 1] := by
  char_poly

example : True := by
  char_poly A
  -- poly : Hex.DensePoly Int
  -- charPoly_eq : Hex.Matrix.charPoly A = poly
  trivial
```

`char_poly A` computes with compiled code and emits a fine-grained certificate
that the kernel rechecks.  Bare `char_poly` closes a direct characteristic-
polynomial equality in either orientation, while the tactic form with an
argument introduces a `poly` let and `charPoly_eq` hypothesis.  The input,
dimension, and any polynomial in a direct equality must be closed and
definitionally transparent.  This interface currently supports only
`Hex.Matrix Int n n`; the underlying characteristic-polynomial API remains
generic over commutative rings.

The library proves the entry formula for Toeplitz multiplication, the leading
coefficient invariant, coefficient reversal, size, degree, monicity, the trace
coefficient, and the closed forms in dimensions zero, one, and two.  The
determinant correspondence and Cayley--Hamilton live in
`hex-char-poly-mathlib`; the computational package deliberately has no
determinant dependency.

## Supported coefficient carriers

`charPoly` is division-free and directly instantiates at every
`[Lean.Grind.CommRing R] [DecidableEq R]`. The generic definition remains the
only public entry point; support is pinned by the following conformance and
benchmark matrix rather than by carrier-specific aliases:

| carrier `R` | instance provider imported by the integration module | required fixture family | exact oracle |
|---|---|---|---|
| `DensePoly Int` | `HexPoly.Instances` | univariate integer-polynomial matrices with nonconstant trace, determinant and intermediate coefficients | SymPy over `ZZ[x,t]` |
| `DensePoly Rat` | `HexPoly.Instances` | the same shapes with nonintegral coefficients | SymPy over `QQ[x,t]` |
| `DensePoly (ZMod64 p)` | `HexPoly.Instances` and `HexModArith`, with `[ZMod64.Bounds p]` | the same shapes at a fixed word-sized prime, including characteristic reduction | SymPy over `GF(p)[x,t]` |
| `MvPoly n Int cmp` | `HexMvPoly.Ring` | sparse two- and three-variable integer-polynomial matrices with mixed monomials | SymPy over `ZZ[x0, ..., t]` |
| `MvPoly n Rat cmp` | `HexMvPoly.Ring` | the same shapes with rational coefficients | SymPy over `QQ[x0, ..., t]` |
| `RationalFn Rat` | `HexRationalFn.Field` | matrices whose entries and output coefficients require nonconstant reduced denominators | SymPy over `QQ(x)[t]` |

Here `t` is a fresh characteristic-polynomial indeterminate, distinct from all
entry variables. For `MvPoly`, conformance fixes the standard graded reverse
lexicographic comparator and supplies its `Std.TransCmp` and
`Std.LawfulEqCmp` instances.

The direct calls live in `conformance/HexCharPoly/Carriers.lean` and
`bench/HexCharPoly/Carriers.lean`. Those are build-only integration roots and
may import `HexMvPoly`, `HexModArith`, and `HexRationalFn` alongside
`HexCharPoly`; they do not change the published library's
`deps: [HexMatrix, HexPoly]`. A reusable source declaration involving one of
these carriers must instead live above both libraries. This placement is the
one accepted by `scripts/check_dag.py`: no carrier package is imported upward
from a production `HexCharPoly/*` module.

## Conformance

Integer conformance fixtures cover dimensions zero and one, zero and diagonal
matrices, nilpotent and repeated-eigenvalue Jordan blocks, both triangular
directions, block triangularity, transpose and similarity pairs, dense random
matrices, and entries near `2^63`.  JSONL output is checked coefficient-for-
coefficient against python-flint's `fmpz_mat.charpoly()` without normalizing or
reversing either list.  Lean guards check Cayley--Hamilton on every fixture and
retain the explicit counterexample showing that a monic degree-`n` annihilator
need not be the characteristic polynomial.

The six carrier families above append canonically encoded records to
`conformance-fixtures/HexCharPoly/charpoly.jsonl`: ascending arrays for nested
`DensePoly`, ordered exponent-vector terms for `MvPoly`, and reduced
numerator/monic-denominator pairs for `RationalFn`. Each family includes `n = 0`
and `n = 1`, diagonal and triangular cases, a singular dense case, and a dense
case with genuinely nonconstant output coefficients.

The symbolic oracle does **not** call SymPy's characteristic-polynomial
routine. It constructs `tI - A` over the exact polynomial or fraction-field
domain and computes `det(tI - A)`, then compares every coefficient in canonical
ascending order. This is an independent route from Hex's Berkowitz recursion;
no point sampling or expression simplifier decides equality. SymPy is already
installed and preflighted by the existing single oracle job, so the
`HexCharPoly` tuple in `scripts/ci/run_oracles.sh` is extended without a new
dependency or job.

This is an independent division-free arm: its emit target and oracle records do
not import or wait for the `bareissWith` carrier integration. Exact-division
availability can therefore neither enable nor suppress characteristic-
polynomial coverage.

## Performance

Benchmarks cover dense random dimension and bit-width ladders, small-entry
tridiagonal matrices, and self-checking companion/Jordan families.  Random
runs observe the peak bit size among Toeplitz columns and intermediate
coefficient vectors.  `lake exe hexcharpoly_bench growth` emits a JSONL row for
every dimension and bit-width rung with elapsed nanoseconds and the observed
peak side by side.  FLINT's selected characteristic-polynomial routine and
PARI's flag-3 Berkowitz routine are informational external comparators.

Each added carrier also has a required Mathlib-free lean-bench family. Dense
univariate carriers sweep matrix dimension and entry degree; multivariate
carriers sweep dimension and term count at fixed arity and total degree;
rational functions sweep dimension and numerator/denominator degree. Every run
observes the maximum canonical coefficient size or term count among the
Toeplitz columns and coefficient vectors, using the carrier's structural size
measure rather than an evaluation.

| target family | external comparator | class |
|---|---|---|
| `runCharDenseInt`, `runCharDenseRat`, `runCharDenseMod` | SymPy exact `det(tI-A)` on the identical matrix | informational |
| `runCharMvInt`, `runCharMvRat` | SymPy exact `det(tI-A)` on the identical matrix | informational |
| `runCharRatFn` | SymPy fraction-field `det(tI-A)` on the identical matrix | informational |

These external comparisons are scheduled-capable process-call targets and are
informational, never Phase-4 gates: SymPy uses a different implementation
language and may select different determinant algorithms. They extend the
existing single bench script, and all result hashes cover the full canonical
polynomial.
