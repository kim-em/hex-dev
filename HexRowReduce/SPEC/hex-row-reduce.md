# hex-row-reduce (depends on hex-matrix)

Executable row reduction (RREF over fields) plus span/nullspace machinery.

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
structure IsRREF (M : Matrix R n m) (D : RowEchelonData R n m)
    extends IsEchelonForm M D : Prop where
  pivot_one : ∀ (i : Fin D.rank), D.echelon[i][D.pivotCols[i]] = 1
  above_pivot_zero : ∀ (i : Fin D.rank) (j : Fin n),
      j.val < i.val → D.echelon[j][D.pivotCols[i]] = 0

def rref [Field R] [DecidableEq R] (M : Matrix R n m) : RowEchelonData R n m
theorem rref_isRREF [Field R] [DecidableEq R] (M : Matrix R n m) : IsRREF M (rref M)
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
def IsRREF.nullspaceMatrix [Ring R] (E : IsRREF M D) : Matrix R m (m - D.rank)
def IsRREF.nullspace [Ring R] (E : IsRREF M D) : Vector (Vector R m) (m - D.rank)
def Matrix.nullspace [Field R] [DecidableEq R] (M : Matrix R n m) :
    Vector (Vector R m) (m - rref_rank)
```

**Key properties:**
- `spanCoeffs_sound : E.spanCoeffs v = some c → rowCombination M c = v`
- `spanCoeffs_complete : (∃ c, rowCombination M c = v) → (E.spanCoeffs v).isSome`
- `spanContains_iff : E.spanContains v = true ↔ ∃ c, rowCombination M c = v`
- `transform_mul_inv : ∃ Tinv, D.transform * Tinv = 1`
- `freeCols_sorted`, `colPartition`, `colPartition_exclusive`
- `pivotCols_injective`, `freeCols_injective` (from `_sorted`)
- `pivotCols_disjoint_freeCols` (from `colPartition_exclusive`)

**Nullspace correctness:**

```lean
theorem nullspace_sound [Ring R] (E : IsRREF M D) (k : Fin (m - D.rank)) :
    M * E.nullspace[k] = 0
theorem nullspace_complete [Field R] (E : IsRREF M D) (v : Vector R m) :
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

## External comparators

The `rank`, `rref`, and `nullspace` operations are cross-checked for correctness
against python-flint's `fmpz_mat` / `fmpq_mat` through the conformance oracle
(`scripts/oracle/matrix_flint.py`, driven by `hexrowreduce_emit_fixtures`).
There is no Phase-4 performance comparator: row reduction is an exact rational
computation validated for correctness, not timed against an external tool. See
`reports/hex-row-reduce-performance.md`.
