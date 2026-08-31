# hex-poly-smith

`hex-poly-smith` computes Smith normal forms of dense polynomial matrices over
a field. It is Mathlib-free and depends on `hex-poly`, `hex-matrix`, and
`hex-determinant`.

For `A : Matrix (DensePoly F) n m`, the library produces a diagonal matrix
`S = U * A * V` whose nonzero diagonal entries are monic and form a
divisibility chain. The explicit-data API also returns inverses for `U` and
`V`. The coefficient assumptions are

```lean
{F : Type u} [Lean.Grind.Field F] [DecidableEq F]
```

The matrix representation remains `Hex.Matrix`; this library introduces no
second polynomial or matrix carrier.

## Public computational API

The user-facing namespace is `Hex.PolyMatrix`.

```lean
structure SmithData (F : Type u) [Zero F] [DecidableEq F] (n m : Nat) where
  rank : Nat
  diag : Vector (DensePoly F) rank
  left : Matrix (DensePoly F) n n
  leftInv : Matrix (DensePoly F) n n
  right : Matrix (DensePoly F) m m
  rightInv : Matrix (DensePoly F) m m

structure IsSNF (A : Matrix (DensePoly F) n m) (S : SmithData F n m) : Prop where
  left_inv : S.left * S.leftInv = Matrix.identity n
  right_inv : S.right * S.rightInv = Matrix.identity m
  mul_eq : S.left * A * S.right = Matrix.diagMatrix S.diag n m
  rank_le_n : S.rank ≤ n
  rank_le_m : S.rank ≤ m
  diag_monic : ∀ i : Fin S.rank, S.diag[i].Monic
  chain : ∀ i (h : i + 1 < S.rank), S.diag[i]'(by omega) ∣ S.diag[i + 1]

def snf (A : Matrix (DensePoly F) n m) : Matrix (DensePoly F) n m
def snfRank (A : Matrix (DensePoly F) n m) : Nat
def snfData (A : Matrix (DensePoly F) n m) : SmithData F n m

def invariantFactors (A : Matrix (DensePoly F) n m) :
    Vector (DensePoly F) (snfRank A)
def moduleStructure (A : Matrix (DensePoly F) n m) :
    Nat × Array (DensePoly F)
def quotientOrder (A : Matrix (DensePoly F) n m) : DensePoly F
def solve (A : Matrix (DensePoly F) n m) (b : Vector (DensePoly F) m) :
    Option (Vector (DensePoly F) n)

def snfDiagonal (d : Vector (DensePoly F) r) :
    Matrix (DensePoly F) r r
def snfDiagonalData (d : Vector (DensePoly F) r) : SmithData F r r

def isSNFShape (S : SmithData F n m) : Bool
def snfCert (A : Matrix (DensePoly F) n m) (S : SmithData F n m)
    (T : Matrix (DensePoly F) n m) : Bool
def evalMatrix (A : Matrix (DensePoly F) n m) (x : F) : Matrix F n m
def mulEqCertAt (pts : Vector F k) (U : Matrix (DensePoly F) n n)
    (A C : Matrix (DensePoly F) n m) : Bool
```

`snf`, `snfRank`, `invariantFactors`, `moduleStructure`, and `quotientOrder`
run the transform-free path. `snfData` and `solve` accumulate both transforms
and both inverses. `snfDiagonal` and `snfDiagonalData` are convenience entry
points that construct the diagonal matrix and use the same certified general
reduction. They do not claim a separate asymptotic or constant-factor fast
path.

`moduleStructure A` returns `(m - snfRank A, torsion)`, with unit invariant
factors removed from `torsion`. `quotientOrder A` is the monic product of the
invariant factors when `snfRank A = m` and zero otherwise. `solve A b` solves
the row-vector equation `Matrix.vecMul x A = b`.

The direct certificate deliberately accepts the intermediate product
`T = S.left * A`, avoiding recomputation between its first two checks.
`mulEqCertAt` is a separate product checker: its soundness theorem requires a
point set that separates every result polynomial through a supplied degree
bound. Small fields may not contain enough distinct points, so the direct
certificate remains the unconditional route.

## Specification functions and theorems

`minors A k` enumerates all `k × k` selected minors. `detDivisor A k` is the
monic gcd of their determinants, with `detDivisor A 0 = 1` and zero when all
such minors vanish. Both are noncomputable specification functions and are not
runtime entry points.

The headline executable correctness results are:

```lean
theorem snfData_isSNF (A : Matrix (DensePoly F) n m) :
    IsSNF A (snfData A)
theorem snf_eq (A : Matrix (DensePoly F) n m) :
    snf A = Matrix.diagMatrix (snfData A).diag n m
theorem snfRank_eq (A : Matrix (DensePoly F) n m) :
    snfRank A = (snfData A).rank
theorem invariantFactors_eq (A : Matrix (DensePoly F) n m) :
    HEq (invariantFactors A) (snfData A).diag
theorem snfDiagonalData_isSNF (d : Vector (DensePoly F) r) :
    IsSNF (Matrix.diagMatrix d r r) (snfDiagonalData d)
theorem solve_sound (h : solve A b = some x) : Matrix.vecMul x A = b
theorem solve_complete (h : ∃ x, Matrix.vecMul x A = b) :
    (solve A b).isSome
```

The diagonal solvability theorem is stated using the canonical
`S := snfData A`; callers cannot override the transform with unrelated data:

```lean
theorem solve_iff_diagonal {A : Matrix (DensePoly F) n m} {b} :
    let S := snfData A
    (∃ x, Matrix.vecMul x A = b) ↔
      ∃ z, Matrix.vecMul z (Matrix.diagMatrix S.diag n m) =
        Matrix.vecMul b S.right
```

`IsSNF.detDivisor_eq` characterizes every determinantal divisor, including the
zero tail. It yields `IsSNF.rank_eq` and `IsSNF.diag_eq`, so the rank and monic
diagonal are canonical even though the transforms are not. For square
full-rank input, `prod_invariantFactors` identifies the product with the monic
associate of `Matrix.det A`; `degree_prod_invariantFactors` gives the
corresponding degree equality.

`snfCert_sound` proves that every accepted direct certificate satisfies
`IsSNF`. `mulEqCertAt_sound` proves a checked evaluated product identity once
the separation and degree hypotheses are supplied. The core
`EvaluationSeparatesUpTo` premise is intentionally semantic and Mathlib-free;
the companion theorem
`HexPolySmithMathlib.evaluationSeparatesUpTo_of_nodup` discharges it from a
distinct-point hypothesis when Mathlib is available. The product-degree bound
is explicit because callers may use tighter bounds derived from their input
families rather than paying to recompute a generic bound inside the checker.

## Totality and degenerate cases

All executable entry points are total. The required behavior includes:

- zero rows or columns: rank zero, empty diagonal, and identity transforms;
- the zero matrix: rank zero and no pivot search past the empty trailing block;
- `1 × 1`: zero stays zero and a nonzero polynomial is made monic;
- constant units: normalized to one and retained by `invariantFactors`;
- rank-deficient tall and wide matrices: zero diagonal tail;
- diagonal input containing zero or nonmonic entries: zeros move to the tail
  and nonzero entries become a monic divisibility chain;
- insufficient evaluation points: `mulEqCertAt` remains a Boolean check, but
  no soundness claim is available without `EvaluationSeparatesUpTo`.

## Conformance

The core profile is `conformance/HexPolySmith/Conformance.lean`. It covers all
advertised computational entry points on typical, edge, and adversarial
inputs. Its property checks include transformation and inverse identities,
Smith shape, diagonal agreement, rank and structure projections, determinant
degree, direct and evaluation certificates, and sound/complete solving on
concrete inputs.

The CI-profile oracle is SymPy's `smith_normal_form` over `QQ[x]` and
`GF(p)[x]`, in `required` mode for release verification. Fixtures contain the
input and Lean diagonal; the oracle independently recomputes the canonical
diagonal. Transform matrices are checked in Lean because they are not unique.

## Performance contract

The benchmark suite is Mathlib-free. It controls matrix dimension and
polynomial degree independently and covers these families:

- `dense-polysmith`: controlled dimension chains and consecutive-remainder
  degree ladders in dense rational presentations;
- `chain-conjugate-poly`: known invariant-factor chains conjugated by
  unimodular matrices;
- `rational-polysmith`: fixed-denominator dimension chains and rational
  consecutive-remainder degree ladders;
- `diagonal-polysmith`: unordered diagonal presentations that require block
  repair;
- `small-field-degree`: consecutive-remainder degree ladders over `ZMod64 2`,
  where evaluation-point supply is constrained.

The Smith loop performs polynomial gcd/division plus dense row and column
updates. The degree registrations use consecutive continuants, so they force a
linear Euclidean remainder chain instead of short-circuiting on divisibility.
Their maximum transform degree, rational denominator width, and coefficient
width follow from the recurrence and appear in the mode-1 wall models. The
supplemental dimension chains isolate dense matrix traversal at fixed degree.
The original generic dense inputs remain fixed comparator stress cases; they do
not make a parametric complexity claim.

The general worst-case contract remains broader than those family-specific
models. For a concrete `n × m` run, let `e` be the total number of nontrivial
pair and block reductions, `D` the maximum intermediate polynomial degree, and
`L` the maximum rational coefficient width in 64-bit limbs. The schoolbook
kernel performs at most
`O((e * (n + m) + min(n,m) * n * m) * D^2 * L^2 * (1 + log L))`
word operations: reductions
update one full row or column, every stage scans its trailing block, and dense
polynomial multiplication/division is quadratic in degree, while rational
normalization adds the standard logarithmic factor to schoolbook limb work.
Rank, invariant-factor, module-structure, quotient-order, and solving
postprocessing do not increase that bound. A dense direct certificate is
`O(n^3 * D^2 * L^2 * (1 + log L))`; evaluation at `k` points is
`O(k * (n^2 * D + n^3) * L^2 * (1 + log L))`. These are worst-case
operational bounds, not the two-sided declarations for a particular benchmark
family.

The continuant degree families specialize the Smith bound more tightly:
dimension is fixed, every Euclidean quotient is linear, and the remainder
degrees decrease by one, so their coefficient scans sum quadratically rather
than paying the general maximum-degree bound at every reduction. The dimension
families instead fix `D` and keep `L` within the derived limb count, leaving the
cubic trailing-matrix work dominant. Thus the mode-1 models are specializations
of, not replacements for, the worst-case contract.

The required within-Lean comparisons are:

- `snf` against `snfData` on the same dimension and degree ladders;
- `snfCert` against `mulEqCertAt` at fixed degree across the dimension ladder.

External square-input comparisons are informational:

- SymPy `smith_normal_form` over `QQ[x]`;
- PARI/GP `matsnf` on matrices of polynomial entries.

Both use persistent subprocesses and fixed-rung registrations. Their process
framing overhead and every shared-rung ratio are recorded in
`reports/hex-poly-smith-performance.md`. PARI is square-only and neither tool
exposes the transform, solving, structure, or certificate surfaces; those
operations therefore have `no-comparable-surface-in-named-comparator`.

## Files

- `Contracts.lean`: `SmithData`, `IsSNF`, and shape reflection.
- `Step.lean`: the normalized two-entry Bézout step.
- `Smith.lean`: general transform-free and full-data elimination.
- `Correctness.lean`: loop invariants, soundness, uniqueness, and consumers.
- `Diagonal.lean`: convenience entry points for diagonal input.
- `Divisor.lean`: selected minors and determinantal divisors.
- `Structure.lean`: invariant factors, module structure, order, and solving.
- `Cert.lean`: direct and evaluation-based certificate checkers.

The Mathlib correspondence is specified separately in the
[hex-poly-smith-mathlib SPEC](../../HexPolySmithMathlib/SPEC/hex-poly-smith-mathlib.md).
