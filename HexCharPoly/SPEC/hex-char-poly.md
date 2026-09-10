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
| `DensePoly (ZMod64 p)` | `HexPoly.Instances` and `HexModArith`, with `[ZMod64.Bounds p]` | the same shapes at a fixed prime below `2^31`, including characteristic reduction | SymPy over `GF(p, symmetric=False)[x,t]` |
| `MvPoly n Int cmp` | `HexMvPoly.Ring` | sparse two- and three-variable integer-polynomial matrices with mixed monomials | SymPy over `ZZ[x0, ..., t]` |
| `MvPoly n Rat cmp` | `HexMvPoly.Ring` | the same shapes with rational coefficients | SymPy over `QQ[x0, ..., t]` |
| `RationalFn Rat` | `HexRationalFn.Field` | matrices whose entries and output coefficients require nonconstant reduced denominators | SymPy over `QQ(x)[t]` |

Here `t` is a fresh characteristic-polynomial indeterminate, distinct from all
entry variables. For `MvPoly`, the ring instance additionally requires
`[BEq R]` and `[LawfulBEq R]`. Conformance fixes `Hex.Mono.grevlex`; its
existing `Std.TransCmp` and `Std.LawfulEqCmp` instances determine the term
order.

Direct typechecking and guards live in the existing build-only
`conformance/HexCharPoly/Conformance.lean`; a separate
`EmitCarrierFixtures.lean` is an explicit emitter root; and carrier benchmarks
are registered by the existing `bench/HexCharPoly/Bench.lean` executable root.
Those modules may import `HexMvPoly`, `HexModArith`, and `HexRationalFn`
alongside `HexCharPoly`; they do not change the published library's
`deps: [HexMatrix, HexPoly]`. A reusable source declaration involving one of
these carriers must instead live above both libraries. `scripts/check_dag.py`
enforces the production graph from `libraries.yml`; the integration paths have
no production owner, though its sealed-import check still scans them.

## Conformance

Integer conformance fixtures cover dimensions zero and one, zero and diagonal
matrices, nilpotent and repeated-eigenvalue Jordan blocks, both triangular
directions, block triangularity, transpose and similarity pairs, dense random
matrices, and entries near `2^63`.  JSONL output is checked coefficient-for-
coefficient against python-flint's `fmpz_mat.charpoly()` without normalizing or
reversing either list.  Lean guards check Cayley--Hamilton on every fixture and
retain the explicit counterexample showing that a monic degree-`n` annihilator
need not be the characteristic polynomial.

`hexcharpoly_emit_carrier_fixtures` writes the six added families to the
separate `conformance-fixtures/HexCharPoly/carriers.jsonl`: ascending arrays for
nested `DensePoly`, ordered exponent-vector terms for `MvPoly`, and reduced
numerator/monic-denominator pairs for `RationalFn`. Finite-field residues are
normalized to `[0, p)`. Each family includes `n = 0` and `n = 1`, diagonal and
triangular cases, a singular dense case, and a dense case with genuinely
nonconstant output coefficients. The existing integer emitter and
`matrix_flint.py` stream stay unchanged.

The new `scripts/oracle/matrix_carriers.py` tuple does **not** call SymPy's
characteristic-polynomial routine. It constructs a `DomainMatrix` for `tI - A`
over the exact polynomial or fraction-field domain and calls
`DomainMatrix.det()` (Bareiss), then compares every coefficient in canonical
ascending order. Finite fields use `GF(p, symmetric=False)`. This is an
independent route from Hex's Berkowitz recursion; no point sampling or
expression simplifier decides equality. SymPy is already installed and
preflighted by the existing single oracle job, so the extra
emitter/fixture/oracle tuple introduces no dependency, workflow, job, or
matrix.

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
| `runCharDenseInt`, `runCharDenseRat`, `runCharDenseMod` | SymPy `DomainMatrix.det()` (Bareiss) on the identical exact-domain `tI-A` | informational |
| `runCharMvInt`, `runCharMvRat` | SymPy `DomainMatrix.det()` (Bareiss) on the identical exact-domain `tI-A` | informational |
| `runCharRatFn` | SymPy `DomainMatrix.det()` (Bareiss) on the identical fraction-field `tI-A` | informational |

These external comparisons are informational, never Phase-4 gates. They use the
carrier driver's persistent-subprocess mode and are scheduled-only. Because the
body is `IO`, each point of a dimension/degree or dimension/term-count sweep is
a separate `setup_fixed_benchmark`; the SymPy `DomainMatrix.det()` method is
pinned to Bareiss. The implementation PR records trivial-request overhead and
overhead-adjusted ratios in
`reports/hex-char-poly-performance.md §Comparator ratios`, updates
`libraries.yml phase4.comparators` and `input_families`, and extends the
existing single bench script. All result hashes cover the full canonical
polynomial.
