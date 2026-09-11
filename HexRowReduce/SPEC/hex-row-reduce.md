# hex-row-reduce (depends on hex-matrix)

Executable row reduction (RREF over fields), span/nullspace machinery, field
inverse, and exact linear solve.

In this computational SPEC, `Field` and `Ring` abbreviate `Lean.Grind.Field`
and `Lean.Grind.Ring`; matrices and operations live in `Hex.Matrix`.
The inverse and solve APIs below are required extensions, not existing
implementation. They add no Mathlib or determinant dependency.

**Row-echelon data and contracts:**

```lean
/-- Pure data: the result of row-reducing a matrix. -/
structure RowEchelonData (R : Type) (n m : Nat) where
  rank : Nat
  echelon : Matrix R n m
  transform : Matrix R n n
  pivotCols : Vector (Fin m) rank

/-- Shared conditions for any echelon form (RREF or HNF). -/
structure IsEchelonForm (M : Matrix R n m) (D : RowEchelonData R n m) : Prop where
  transform_mul : D.transform * M = D.echelon
  transform_inv : ∃ Tinv : Matrix R n n, Tinv * D.transform = 1
  transform_right_inv : ∃ Tinv : Matrix R n n, D.transform * Tinv = 1
  rank_le_n : D.rank ≤ n
  rank_le_m : D.rank ≤ m
  pivotCols_sorted : ∀ i j, i < j → D.pivotCols[i] < D.pivotCols[j]
  below_pivot_zero : ∀ (i : Fin D.rank) (j : Fin n),
      i.val < j.val → D.echelon[j][D.pivotCols[i]] = 0
  zero_row : ∀ (i : Fin n), D.rank ≤ i.val → D.echelon[i] = 0

/-- RREF-specific: pivots are 1, everything above is 0. -/
structure IsRowReduced (M : Matrix R n m) (D : RowEchelonData R n m)
    extends IsEchelonForm M D : Prop where
  pivot_one : ∀ (i : Fin D.rank), D.echelon[i][D.pivotCols[i]] = 1
  above_pivot_zero : ∀ (i : Fin D.rank) (j : Fin n),
      j.val < i.val → D.echelon[j][D.pivotCols[i]] = 0

def rowReduce [Field R] [DecidableEq R] (M : Matrix R n m) : RowEchelonData R n m
theorem rowReduce_isRowReduced [Field R] [DecidableEq R] (M : Matrix R n m) : IsRowReduced M (rowReduce M)
```

**Column partition.** The sorted complement of `pivotCols` in `Fin m`. Together
with `pivotCols` they partition all column indices; this decomposition is used
by both span and nullspace.

```lean
def IsEchelonForm.freeCols (E : IsEchelonForm M D) : Vector (Fin m) (m - D.rank)
theorem IsEchelonForm.freeCols_sorted (E : IsEchelonForm M D) :
    ∀ i j, i < j → E.freeCols[i] < E.freeCols[j]
theorem IsEchelonForm.colPartition (E : IsEchelonForm M D) (j : Fin m) :
    (∃ i : Fin D.rank, D.pivotCols[i] = j) ∨
    (∃ k : Fin (m - D.rank), E.freeCols[k] = j)
theorem IsEchelonForm.colPartition_exclusive (E : IsEchelonForm M D) (j : Fin m) :
    ¬((∃ i : Fin D.rank, D.pivotCols[i] = j) ∧
      (∃ k : Fin (m - D.rank), E.freeCols[k] = j))
```

**Span via echelon form.** Given an `IsEchelonForm`, solve for coefficients or
test membership. Works for both RREF and HNF.

```lean
def IsEchelonForm.spanCoeffs [Field R] [DecidableEq R] (F : IsEchelonForm M D)
    (v : Vector R m) : Option (Vector R n)
def IsEchelonForm.spanContains [Field R] [DecidableEq R] (F : IsEchelonForm M D)
    (v : Vector R m) : Bool
def Matrix.spanCoeffs [Field R] [DecidableEq R] (M : Matrix R n m) (v : Vector R m) :
    Option (Vector R n)
def Matrix.spanContains [Field R] [DecidableEq R] (M : Matrix R n m) (v : Vector R m) : Bool
```

**Nullspace** via RREF. Each free variable gives one basis vector. The
basis-vector formula uses negation (`[Ring R]`); the proof of completeness
requires RREF (`[Field R]`).

```lean
def IsRowReduced.nullspaceMatrix [Ring R] (E : IsRowReduced M D) : Matrix R m (m - D.rank)
def IsRowReduced.nullspace [Ring R] (E : IsRowReduced M D) : Vector (Vector R m) (m - D.rank)
def Matrix.nullspace [Field R] [DecidableEq R] (M : Matrix R n m) :
    Vector (Vector R m) (m - Matrix.rowReduce_rank M)
```

**Key properties:**
- `IsEchelonForm.spanCoeffs_sound : E.spanCoeffs v = some c → vecMul c M = v`
- `IsRowReduced.spanCoeffs_complete : (∃ c, vecMul c M = v) → (E.toIsEchelonForm.spanCoeffs v).isSome`
- `IsRowReduced.spanContains_iff : E.toIsEchelonForm.spanContains v = true ↔ ∃ c, vecMul c M = v`
- `transform_mul_inv : ∃ Tinv, D.transform * Tinv = 1`
- `freeCols_sorted`, `colPartition`, `colPartition_exclusive`
- `pivotCols_injective`, `freeCols_injective` (from `_sorted`)
- `pivotCols_disjoint_freeCols` (from `colPartition_exclusive`)

**Nullspace correctness:**

```lean
theorem nullspace_sound [Ring R] (E : IsRowReduced M D) (k : Fin (m - D.rank)) :
    M * E.nullspace[k] = 0
theorem nullspace_complete [Field R] (E : IsRowReduced M D) (v : Vector R m) :
    M * v = 0 → ∃ c : Vector R (m - D.rank), E.nullspaceMatrix * c = v
```

(`nullspace_rank` is definitional: `E.nullspace` has type `Vector _ (m - D.rank)`.)

Proof strategy for `nullspace_sound`: verify `D.echelon * bₖ = 0` directly from
the basis-vector formula and RREF properties, then use `transform_inv` to obtain
`Tinv` with `Tinv * D.transform = 1`, so `M = Tinv * D.echelon` and
`M * bₖ = Tinv * (D.echelon * bₖ) = 0`.

Proof strategy for `nullspace_complete`: push `M * v = 0` through `transform_mul`
to `D.echelon * v = 0`; define `cₖ := v[E.freeCols[k]]`; verify entry by entry
with `colPartition` (free columns telescope to `v[freeCols[l]]`; pivot columns
follow from `pivot_one` / `above_pivot_zero` / `below_pivot_zero` / `zero_row`);
package into `E.nullspaceMatrix * c = v`.

## Field inverse and complete linear solve

All new executable APIs and their computational contracts take
`[Lean.Grind.Field F] [DecidableEq F]`, with `F : Type u` and dimensions
`n m : Nat`. The following signatures specify new declarations in
`Hex.Matrix`; theorem bodies are implementation obligations.

### Inverse

```lean
def inverse? (A : Matrix F n n) : Option (Matrix F n n)

theorem inverse?_spec (A B : Matrix F n n) :
    inverse? A = some B →
      A * B = Matrix.identity n ∧ B * A = Matrix.identity n

theorem inverse?_isSome (A : Matrix F n n) :
    (inverse? A).isSome ↔ rowReduce_rank A = n

/-- Convenience corollary of `inverse?_isSome`. -/
theorem inverse?_eq_none (A : Matrix F n n) :
    inverse? A = none ↔ rowReduce_rank A ≠ n
```

Reduce the augmented system `[A | I]`, choosing pivots only in the `A`
block. The existing `D := rowReduce A` already performs precisely these
operations: `D.echelon = D.transform * A`, and `D.transform` is the
transformed identity block. Return `some D.transform` exactly when
`D.rank = n`; then `D.echelon = I`. The invertibility of the transform
establishes both product identities. Do not test the rank of an unrestricted
reduction of `[A | I]`: that augmented matrix has rank `n` even when `A`
is singular.

`rowReduce_rank A` is the definition `(rowReduce A).rank` in
`HexRowReduce/Api.lean`, not a theorem identifying rank with a determinant.
The determinant form of completeness, `inverse? A = none ↔ det A = 0`,
belongs to the companion, using `rank_eq` on `rowReduce_isRowReduced A`.
The computational code decides only the rank test and does not evaluate a
determinant. There is no fuel, search limit, or resource-failure return.
This API exposes singularity through its completeness theorem. A separate
witness-producing inverse operation is outside this extension's scope.

### Solve and inconsistency witness

A solution stores a particular vector and a matrix whose columns are the
existing canonical nullspace basis. Its type fixes the basis size from
`A`, so a caller never supplies a rank witness.

```lean
abbrev SolveData (A : Matrix F n m) :=
  Vector F m × Matrix F m (m - rowReduce_rank A)

def solve (A : Matrix F n m) (b : Vector F n) :
    Except (Vector F n) (SolveData A)

def solve? (A : Matrix F n m) (b : Vector F n) : Option (SolveData A) :=
  (solve A b).toOption

theorem solve?_spec (A : Matrix F n m) (b : Vector F n) (s : SolveData A) :
    solve? A b = some s →
      A * s.1 = b ∧ s.2 = nullspaceBasisMatrix A ∧
      ∀ x : Vector F m, A * x = b ↔
        ∃ c : Vector F (m - rowReduce_rank A), x = s.1 + s.2 * c

theorem solve?_isSome (A : Matrix F n m) (b : Vector F n) :
    (solve? A b).isSome ↔ ∃ x : Vector F m, A * x = b

/-- Convenience corollary of `solve?_isSome`. -/
theorem solve?_eq_none (A : Matrix F n m) (b : Vector F n) :
    solve? A b = none ↔ ¬ ∃ x : Vector F m, A * x = b

theorem solve_error (A : Matrix F n m) (b y : Vector F n) :
    solve A b = .error y → vecMul y A = 0 ∧ Vector.dotProduct y b ≠ 0

theorem solve?_none_witness (A : Matrix F n m) (b : Vector F n) :
    solve? A b = none ↔
      ∃ y : Vector F n, vecMul y A = 0 ∧ Vector.dotProduct y b ≠ 0

/-- Uniqueness of the nullspace coefficients in a successful answer. -/
theorem solve?_unique (A : Matrix F n m) (b : Vector F n) (s : SolveData A)
    (c₁ c₂ : Vector F (m - rowReduce_rank A)) :
    solve? A b = some s → s.2 * c₁ = s.2 * c₂ → c₁ = c₂
```

`solve` is the witness-producing entry point; its `.error` means a proved
mathematical inconsistency. `solve?` only forgets that witness. Both are
total over a field. A consumer needing a negative certificate calls `solve`
once, rather than calling `solve?` and recomputing an elimination.

Compute `D := rowReduce A`, `E := rowReduce_isRowReduced A`, and
`c := D.transform * b`, sharing this reduction with basis construction.
This is reduction of `[A | b]` with pivots restricted to the coefficient
columns. If there is a row `i ≥ D.rank` with `c[i] ≠ 0`, return `.error y`
where `i` is the first such row and `y` is row `i` of `D.transform`.
`transform_mul` and `zero_row` give `yᵀ A = 0`; the same row of the
transformed right-hand side gives `yᵀ b = c[i] ≠ 0`. Consequently no
solution exists, since any `A * x = b` would imply `yᵀ b = 0`.

Otherwise set every free coordinate of `x₀` to zero and set
`x₀[D.pivotCols[j]] := c[j]` for each pivot row `j`. Return
`.ok (x₀, E.nullspaceMatrix)`. Require that `x₀` has zero free coordinates
and that the returned columns equal `Matrix.nullspace A` in its existing
increasing free-column order. The zero-row test is necessary and sufficient:
the RREF pivot equations give `D.echelon * x₀ = c`, and `transform_inv`
transports this equality back to `A * x₀ = b`.

For all solutions, apply the existing `nullspace_complete` to `x - x₀`;
the converse uses `nullspace_sound` and linearity. The coefficient vector
is unique: its coordinates are the free coordinates of `x - x₀`, since
the free rows of the basis matrix form an identity. Thus the answer describes
the entire affine solution set, including systems with nonzero nullity.
The rank and basis always come from `A`, not from an augmented matrix with
an extra pivot in the right-hand side.

### Boundary cases

These equations hold over every field, including characteristic two.

| Input | Required answer and completeness check |
| --- | --- |
| `A : Matrix F 0 0` | `inverse? A = some (Matrix.identity 0)`. Rank is `0`; the empty determinant is `1`, so the `none` condition is false. Both inverse identities are equalities of empty matrices. |
| `A : Matrix F 0 m`, empty `b` | Solve succeeds with `x₀ = 0` and basis `Iₘ`; there are no equations, and every vector is a solution. For `m = 0` this is the unique empty solution with an empty basis. |
| `A : Matrix F n 0` | Solve succeeds with the empty vector and empty basis iff `b = 0`. Otherwise a coordinate vector at a nonzero entry of `b` is the inconsistency witness. |
| `A = [[1, 0], [0, 0]]` | Inverse returns `none` (rank `1`, determinant `0`). For `b = [a, 0]`, solve returns `x₀ = [a, 0]` and basis column `[0, 1]`; singularity alone does not imply inconsistency. For `b = [a, 1]`, solve fails with witness `[0, 1]`. |
| `A = [[1, 0, 0], [1, 0, 0]]`, `b = [0, 1]` | This inconsistent rectangular system reduces to a zero second coefficient row with transformed RHS `1`. Witness `y = [-1, 1]` satisfies `yᵀ A = 0`, `yᵀ b = 1`; `solve?` returns `none`. |
| `A = [[0, 1, 1]]`, `b = [a]` | Solve returns `x₀ = [0, a, 0]` with basis columns `[1, 0, 0]`, `[0, -1, 1]`. Solutions are `[u, a - v, v]`; the leading free column is not mistaken for a pivot. |

### Relationship to the domain rank certificate

[hex-rank](../../SPEC/Libraries/hex-rank.md) specifies fraction-free
elimination over domains with a checked numerator `adj` and nonzero
`denom` for the inverse of a selected nonsingular minor. Division by
`denom` takes place in a fraction field, or in the domain only when that
denominator is a unit. A nonsingular integer matrix need not have an
integer inverse.

For a checked full-rank square certificate, write its selected submatrix
as `B = P * A * Q`, where `P` and `Q` are the row and column permutation
matrices determined by the selections. In the fraction field,
`A⁻¹ = Q * (denom⁻¹ • adj) * P`. Dividing `adj` alone gives the inverse
of `B`, so the selections must be undone; `adj` and `denom` need not be
the literal adjugate and determinant for an arbitrary passing certificate.
The field RREF route returns the inverse in the original indexing directly.
The two routes agree by uniqueness of a two-sided inverse when interpreted
over the same field. Neither library acquires a dependency on the other;
tactic selection and domain-certificate adapters belong to their consumers.

## Inverse and solve conformance

Extend `conformance/HexRowReduce/{Conformance,EmitFixtures}.lean` and
`scripts/oracle/matrix_flint.py`. Add carrier-tagged dispatch there, importing
SymPy only for rational-function records. Preserve the existing rational and
integer handlers used by the other matrix libraries. Add SymPy to the existing
CI dependency step when implementing this extension. Fixtures record dimensions explicitly (including
empty shapes), the carrier, `A`, `b`, and the returned inverse, particular
solution and basis, or inconsistency witness. Exercise `Rat`, `ZMod64 p`
with `[ZMod64.Bounds p] [ZMod64.PrimeModulus p]` and the field instance from
`HexPolyFp.PrimeField`, and `RationalFn Rat` (more generally the executable
API accepts `RationalFn K` for any `Lean.Grind.Field K` with decidable
equality). Carrier imports belong in conformance and bench drivers, not
in the generic library.

Include every boundary case above, invertible matrices requiring row swaps,
tall and wide consistent systems, rank-deficient systems with non-leading
pivots, inconsistent systems, and nonintegral rational coefficients. Modular
fixtures include characteristic two and an odd prime. Rational-function
fixtures include nonconstant denominators and pivots; check identities in
`Rat(t)` exactly, without relying on evaluations at sample points.

For `Rat`, compare inverse entries with python-flint `fmpq_mat.inv()` and
unique square solutions with `fmpq_mat.solve()` (one-column RHS).
[python-flint's solve contract](https://python-flint.readthedocs.io/en/latest/fmpq_mat.html#flint.fmpq_mat.solve)
requires a square invertible coefficient matrix; its exception on a singular
matrix does not certify that a particular RHS is inconsistent. For general
systems use independent ranks of `A` and `[A | b]`, check `A * x₀ = b`,
`A * N = 0`, and `rank N = m - rank A`, or check both witness identities.
Use exact modular arithmetic for the analogous `ZMod64` checks. For rational
functions use [SymPy DomainMatrix](https://docs.sympy.org/latest/modules/polys/domainmatrix.html)
over `QQ.frac_field(t)` for inverse and RREF/rank checks of general systems.
Do not compare arbitrary basis entries or particular solutions from different
pivot conventions; compare the affine solution sets via these invariants.

## Inverse and solve benchmarks

Extend `bench/HexRowReduce/Bench.lean` with direct end-to-end coverage of
`inverse?`, `solve`, and `solve?`, forcing all returned entries (including
failure witnesses). Sweep square dimension `n = 4, 8, 16, 32, 64` at each
fixed rational coefficient height `h = 8, 32, 128` bits, and sweep
`h = 8, 16, 32, 64, 128, 256` at fixed dimensions `8` and `16`. Record
actual numerator/denominator heights and use seeded dense inputs with
nontrivial elimination. Separate full-rank, rank-`n - 1`, and rank-`n / 2`
families, with both consistent and inconsistent RHSs for deficient inputs;
add tall `2n × n` and wide `n × 2n` solve families. Construct and verify
input ranks and consistency outside timing.

The field-operation bound for inverse is `O(n³)`. For solve of rank `r`,
reduction plus RHS multiplication and basis materialization costs
`O(rn(n + m) + n² + m(m - r))` field operations/output work; do not rerun
RREF to compute the dependent result size or the basis. The dimension model
is cubic for dense fixed-aspect inputs with rank proportional to dimension.
The height sweep measures bit cost, including coefficient growth; it makes
no cubic bit-complexity claim. Add modular dimension sweeps at a fixed prime
and smaller rational-function dimensions `2, 4, 8` at fixed degree and
coefficient height, recording those parameters separately.

Represent each dimension sweep as a separate one-parameter registration per
fixed carrier, height, and rank/consistency family, using a custom parameter
schedule for the stated ladder. Represent each height sweep as a separate
registration per fixed dimension and family. Use the harness's fixed,
trial-major schedule for scientific measurements. The large dimensions and
heights are scientific settings for manual shared-host runs, not CI inputs.
For dimension registrations, configure the `verify` parameter to dimension
`2` (`2n × n` or `n × 2n` for rectangular families), retaining the fixed
coefficient height and rank/consistency family. For height registrations,
use height `8` while retaining the fixed dimension and family. Use degree
`1` and coefficient height `8` as the fixed rational-function family for both
scientific runs and verification. Give verification minimal tuning budgets
and repeat counts. Measure total `verify` time across registrations against
the existing per-library warning and repository cap. Adjust only verification
budgets if needed, retaining the scientific ladders and input families.

Informational external comparisons use `fmpq_mat.inv()` and, for nonsingular
square inputs with empty nullspace, `fmpq_mat.solve()`. Compare complete
outputs on the same inputs, with construction outside timing. The general
affine solution/witness surface has no matching python-flint callable;
correctness still has the conformance checks above. Follow the shared-host
schedule and retention rules in `SPEC/benchmarking.md`; extend the existing
single CI job's `Bench verify` checks when implementing these targets.

## Complexity and benchmark contract

For an `n × m` matrix of rank `r`, Gauss--Jordan reduction performs at most
`r` pivot stages and visits `O(n(n + m))` entries per stage across the echelon
and transform matrices.  The arithmetic-operation bound is therefore
`O(rn(n + m))`, cubic on the fixed-aspect square benchmark families.  Exact
rational bit cost additionally depends on numerator and denominator growth.

The compiled implementation uses a proved linear sorted merge for the
free-column complement.  Prepared nullspace construction materializes the
column-to-pivot-row lookup once and then writes `m(m - r)` output entries with
constant-time lookup per entry; its fixed-aspect bound is quadratic.

`bench/HexRowReduce/Bench.lean` gives the 12 existing executable operations
direct mode-1 coverage:

| Operations | Prepared state | Model |
| --- | --- | --- |
| `Matrix.rowReduce`, `Matrix.rowReduce_rank` | dense input | `n³` |
| `Matrix.spanCoeffs`, `Matrix.spanContains` | dense input | `n³` |
| `IsEchelonForm.spanCoeffs`, `IsEchelonForm.spanContains` | proved RREF | `n²` |
| `IsEchelonForm.echelonCoeffs`, `IsEchelonForm.freeCols` | proved RREF | `n` |
| `Matrix.nullspaceBasisMatrix`, `Matrix.nullspace` | deficient input | `n³` |
| `IsRowReduced.nullspaceMatrix`, `IsRowReduced.nullspace` | proved RREF | `n²` |

The dense family is `I + J`, so every pivot fires while coefficient heights
remain controlled.  The deficient family has rank and nullity `n / 2`.
Preparation is outside the timed region and result forcing is inside it.

## External comparators

The identical constant-size rank result is compared informationally with
python-flint's `fmpq_mat.rref()` through the shared persistent driver.  Both
arms use the same dense `I + J` family; construction is cached during warmup,
and each timed request returns only the integer rank.

The remaining existing operations declare
`no-comparable-surface-in-named-comparator`: Hex `rowReduce` returns the row
transform that `fmpq_mat.rref()` omits; python-flint 0.9.0's `fmpq_mat` has no
native nullspace callable; and span coefficients are transform-dependent
witnesses.  A comparator-specific derived algorithm would not be the same
callable surface.  Full RREF and nullspace correctness remain cross-checked by
`scripts/oracle/matrix_flint.py`, driven by `hexrowreduce_emit_fixtures`.
