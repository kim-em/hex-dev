/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Basic

public section

/-!
Principal submatrices and row prefixes.
-/

namespace Hex

universe u

namespace Matrix

/-- Leading principal `k × k` submatrix of a square matrix: the top-left block
indexed by `{0, …, k-1}` along both axes. Includes the empty submatrix
(`k = 0`) and is convenient for Bareiss pivot/minor statements. -/
@[expose]
def principalSubmatrix (M : Matrix R n n) (k : Nat) (hk : k ≤ n) : Matrix R k k :=
  ofFn fun i j =>
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
    M[(ii, jj)]

/-- The first `k` rows of a matrix, retaining all source columns. -/
@[expose]
def takeRows (M : Matrix R n m) (k : Nat) (hk : k ≤ n) : Matrix R k m :=
  ofFn fun i j =>
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    M[(ii, j)]

/-- Entry formula for the `k × k` principal submatrix. -/
@[grind =] theorem getElem_principalSubmatrix (M : Matrix R n n) (k : Nat) (hk : k ≤ n)
    (i j : Fin k) :
    (principalSubmatrix M k hk)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
       M[ii][jj]) := by
  unfold principalSubmatrix
  rw [getElem_ofFn, getElem_pair_eq_nested]

/-- Row `i` of the `k × k` principal submatrix is row `i` of `M`, restricted to
the first `k` columns. -/
@[simp, grind =] theorem row_principalSubmatrix (M : Matrix R n n) (k : Nat) (hk : k ≤ n)
    (i : Fin k) :
    row (principalSubmatrix M k hk) i =
      Vector.ofFn fun j : Fin k =>
        (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
         let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
         M[ii][jj]) := by
  ext j hj
  show (row (principalSubmatrix M k hk) i)[(⟨j, hj⟩ : Fin k)] =
    (Vector.ofFn fun j : Fin k =>
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
       M[ii][jj]))[(⟨j, hj⟩ : Fin k)]
  rw [getElem_row, getElem_principalSubmatrix]
  simp

/-- Column `j` of the `k × k` principal submatrix is column `j` of `M`,
restricted to the first `k` rows. -/
@[simp, grind =] theorem col_principalSubmatrix (M : Matrix R n n) (k : Nat) (hk : k ≤ n)
    (j : Fin k) :
    col (principalSubmatrix M k hk) j =
      Vector.ofFn fun i : Fin k =>
        (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
         let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
         M[ii][jj]) := by
  ext i hi
  show (col (principalSubmatrix M k hk) j)[(⟨i, hi⟩ : Fin k)] =
    (Vector.ofFn fun i : Fin k =>
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
       M[ii][jj]))[(⟨i, hi⟩ : Fin k)]
  rw [getElem_col, getElem_principalSubmatrix]
  simp

/-- The first `k` columns of a matrix, retaining all source rows. -/
@[expose]
def takeCols (M : Matrix R n m) (k : Nat) (hk : k ≤ m) : Matrix R n k :=
  ofFn fun i j =>
    let jj : Fin m := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
    M[(i, jj)]

/-- Entry formula for the first-`k`-rows slice. -/
@[grind =] theorem getElem_takeRows (M : Matrix R n m) (k : Nat) (hk : k ≤ n)
    (i : Fin k) (j : Fin m) :
    (takeRows M k hk)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       M[ii][j]) := by
  unfold takeRows
  rw [getElem_ofFn, getElem_pair_eq_nested]

/-- Entry formula for the first-`k`-columns slice. -/
@[grind =] theorem getElem_takeCols (M : Matrix R n m) (k : Nat) (hk : k ≤ m)
    (i : Fin n) (j : Fin k) :
    (takeCols M k hk)[i][j] =
      (let jj : Fin m := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
       M[i][jj]) := by
  unfold takeCols
  rw [getElem_ofFn, getElem_pair_eq_nested]

/-- The leading principal `k × k` submatrix of the identity is the identity. -/
@[simp, grind =] theorem principalSubmatrix_identity {R : Type u} [OfNat R 0] [OfNat R 1] {n : Nat}
    (k : Nat) (hk : k ≤ n) :
    principalSubmatrix (Matrix.identity (R := R) n) k hk = (Matrix.identity (R := R) k) := by
  apply ext_getElem
  intro i j
  rw [getElem_principalSubmatrix,
    getElem_identity (i := (⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ : Fin n)),
    getElem_identity (i := i)]
  by_cases hij : i = j
  · simp [hij]
  · have hijn :
        (⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ : Fin n) ≠ ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ := by
      intro heq
      exact hij (Fin.ext (by simpa using congrArg Fin.val heq))
    simp [hij, hijn]

end Matrix

/-! ### Copy-free submatrix views

A `Submatrix R rows cols` is a **view** into a backing `Matrix R N M`: a row/column
offset plus the real-data extent, with the logical `rows × cols` shape carried as
type indices. Reading entry `(i, j)` is pure offset arithmetic into the shared flat
buffer (`base[(r0 + i, c0 + j)]`) when that position holds real data, and `0`
otherwise — the zero-fill lets a view stand for a matrix logically padded past its
data without copying. The backing dims `N, M` never change through a recursion, so
`r0 + i < rhi` (the real-row bound, a prefix of the logical rows) is the exact
real-vs-pad test at every nesting depth. Quadrant-of-a-view is a view (offset
arithmetic, no copy); this is the recursion surface `mulStrassen` runs over
(`HexMatrix/Strassen.lean`). See `HexMatrix/SPEC/hex-matrix.md` § "Avoiding
sub-block copies". -/

/-- A copy-free view of a `rows × cols` block, possibly zero-padded past its
real-data extent, into a shared backing `Matrix R N M`. Reading `(i, j)` returns
`base[(r0 + i, c0 + j)]` when `r0 + i < rhi ∧ c0 + j < chi` (real data) and `0`
otherwise (pad). The invariants pin `[r0, rhi) × [c0, chi)` inside the backing and
inside the logical block, so the real data is a prefix of each axis. -/
structure Submatrix (R : Type u) (rows cols : Nat) where
  /-- Backing row count. -/ N : Nat
  /-- Backing column count. -/ M : Nat
  /-- Shared backing buffer; sub-views alias it, never copy it. -/ base : Hex.Matrix R N M
  /-- Row offset into the backing. -/ r0 : Nat
  /-- Column offset into the backing. -/ c0 : Nat
  /-- One past the last real-data row (backing coordinate). -/ rhi : Nat
  /-- One past the last real-data column (backing coordinate). -/ chi : Nat
  /-- Real rows stay inside the backing. -/ hrN : rhi ≤ N
  /-- Real columns stay inside the backing. -/ hcM : chi ≤ M
  /-- Real rows are a prefix of the logical rows. -/ hrR : rhi ≤ r0 + rows
  /-- Real columns are a prefix of the logical columns. -/ hcC : chi ≤ c0 + cols

namespace Submatrix

variable {R : Type u} {rows cols : Nat}

/-- Read entry `(i, j)` of a view: the flat backing read at `(r0 + i, c0 + j)`
inside the real-data window, `0` in the zero-pad fringe. -/
@[expose]
def entry [OfNat R 0] (A : Submatrix R rows cols) (i : Fin rows) (j : Fin cols) : R :=
  if h : A.r0 + i.val < A.rhi ∧ A.c0 + j.val < A.chi then
    A.base[(A.r0 + i.val, A.c0 + j.val)]'(by
      obtain ⟨h1, h2⟩ := h; exact ⟨by have := A.hrN; omega, by have := A.hcM; omega⟩)
  else 0

/-- Materialize a view into a genuine `Matrix` (a copy of the block, with the
zero-pad fringe filled in). This is the leaf/operand allocation the recursion
pays; interior quadrants stay views. -/
@[expose]
def toMatrix [OfNat R 0] (A : Submatrix R rows cols) : Matrix R rows cols :=
  Matrix.ofFn fun i j => A.entry i j

/-- Entry access of a materialized view is the view read. -/
@[simp, grind =] theorem getElem_toMatrix [OfNat R 0] (A : Submatrix R rows cols)
    (i : Fin rows) (j : Fin cols) : (A.toMatrix)[i][j] = A.entry i j := by
  rw [toMatrix, Matrix.getElem_ofFn]

/-- The full-matrix view of a `Matrix`: offset `0`, real extent the whole matrix. -/
@[expose]
def ofMatrix (Mx : Matrix R n m) : Submatrix R n m where
  N := n; M := m; base := Mx; r0 := 0; c0 := 0; rhi := n; chi := m
  hrN := Nat.le_refl _
  hcM := Nat.le_refl _
  hrR := by omega
  hcC := by omega

/-- Reading the full-matrix view is reading the matrix. -/
@[simp, grind =] theorem entry_ofMatrix [OfNat R 0] (Mx : Matrix R n m) (i : Fin n) (j : Fin m) :
    (ofMatrix Mx).entry i j = Mx[i][j] := by
  rw [entry, ofMatrix]
  rw [dif_pos (⟨by omega, by omega⟩ : (0 : Nat) + i.val < n ∧ (0 : Nat) + j.val < m)]
  simp [Matrix.getElem_pair_nat]

/-- Materializing the full-matrix view returns the matrix. -/
@[simp, grind =] theorem toMatrix_ofMatrix [OfNat R 0] (Mx : Matrix R n m) :
    (ofMatrix Mx).toMatrix = Mx := by
  apply Matrix.ext_getElem
  intro i j
  rw [getElem_toMatrix, entry_ofMatrix]

/-- Widen a view's logical shape to `n' × m'` (`n ≤ n'`, `m ≤ m'`) without copying:
the real-data window is unchanged, so the new fringe reads `0`. This is the
zero-padding the Strassen recursion applies before splitting. -/
@[expose]
def pad (A : Submatrix R n m) (n' m' : Nat) (hn : n ≤ n') (hm : m ≤ m') : Submatrix R n' m' where
  N := A.N; M := A.M; base := A.base; r0 := A.r0; c0 := A.c0; rhi := A.rhi; chi := A.chi
  hrN := A.hrN; hcM := A.hcM
  hrR := by have := A.hrR; omega
  hcC := by have := A.hcC; omega

/-- Reading a widened view agrees with the source view inside the source shape. -/
@[grind =] theorem entry_pad [OfNat R 0] (A : Submatrix R n m) (n' m' : Nat)
    (hn : n ≤ n') (hm : m ≤ m') (i : Fin n') (j : Fin m') :
    (A.pad n' m' hn hm).entry i j =
      if h : i.val < n ∧ j.val < m then A.entry ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else 0 := by
  by_cases hin : i.val < n ∧ j.val < m
  · rw [dif_pos hin]; rfl
  · rw [dif_neg hin, entry]
    apply dif_neg
    simp only [pad]
    intro hd
    have h1 := A.hrR
    have h2 := A.hcC
    omega

/-- Top-left `h × w` quadrant of an `(h+h) × (w+w)` view: same offset, real extent
capped at the block boundary. No copy. -/
@[expose]
def toBlocks₁₁ (A : Submatrix R (h + h) (w + w)) : Submatrix R h w where
  N := A.N; M := A.M; base := A.base; r0 := A.r0; c0 := A.c0
  rhi := min A.rhi (A.r0 + h); chi := min A.chi (A.c0 + w)
  hrN := by have := A.hrN; omega
  hcM := by have := A.hcM; omega
  hrR := by omega
  hcC := by omega

/-- Top-right `h × w` quadrant of an `(h+h) × (w+w)` view. No copy. -/
@[expose]
def toBlocks₁₂ (A : Submatrix R (h + h) (w + w)) : Submatrix R h w where
  N := A.N; M := A.M; base := A.base; r0 := A.r0; c0 := A.c0 + w
  rhi := min A.rhi (A.r0 + h); chi := A.chi
  hrN := by have := A.hrN; omega
  hcM := A.hcM
  hrR := by omega
  hcC := by have := A.hcC; omega

/-- Bottom-left `h × w` quadrant of an `(h+h) × (w+w)` view. No copy. -/
@[expose]
def toBlocks₂₁ (A : Submatrix R (h + h) (w + w)) : Submatrix R h w where
  N := A.N; M := A.M; base := A.base; r0 := A.r0 + h; c0 := A.c0
  rhi := A.rhi; chi := min A.chi (A.c0 + w)
  hrN := A.hrN
  hcM := by have := A.hcM; omega
  hrR := by have := A.hrR; omega
  hcC := by omega

/-- Bottom-right `h × w` quadrant of an `(h+h) × (w+w)` view. No copy. -/
@[expose]
def toBlocks₂₂ (A : Submatrix R (h + h) (w + w)) : Submatrix R h w where
  N := A.N; M := A.M; base := A.base; r0 := A.r0 + h; c0 := A.c0 + w
  rhi := A.rhi; chi := A.chi
  hrN := A.hrN
  hcM := A.hcM
  hrR := by have := A.hrR; omega
  hcC := by have := A.hcC; omega

/-- Entrywise sum of two views, materialized into a fresh matrix (an operand-sum
allocation). -/
@[expose]
def add [Add R] [OfNat R 0] (A B : Submatrix R rows cols) : Submatrix R rows cols :=
  ofMatrix (Matrix.ofFn fun i j => A.entry i j + B.entry i j)

/-- Entrywise difference of two views, materialized into a fresh matrix. -/
@[expose]
def sub [Sub R] [OfNat R 0] (A B : Submatrix R rows cols) : Submatrix R rows cols :=
  ofMatrix (Matrix.ofFn fun i j => A.entry i j - B.entry i j)

/-- Materializing a view sum is the matrix sum of the materializations. -/
@[simp, grind =] theorem toMatrix_add [Add R] [OfNat R 0] (A B : Submatrix R rows cols) :
    (A.add B).toMatrix = A.toMatrix + B.toMatrix := by
  apply Matrix.ext_getElem
  intro i j
  rw [add, toMatrix_ofMatrix, Matrix.getElem_add, Matrix.getElem_ofFn, getElem_toMatrix,
    getElem_toMatrix]

/-- Materializing a view difference is the matrix difference of the materializations. -/
@[simp, grind =] theorem toMatrix_sub [Sub R] [OfNat R 0] (A B : Submatrix R rows cols) :
    (A.sub B).toMatrix = A.toMatrix - B.toMatrix := by
  apply Matrix.ext_getElem
  intro i j
  rw [sub, toMatrix_ofMatrix, Matrix.getElem_sub, Matrix.getElem_ofFn, getElem_toMatrix,
    getElem_toMatrix]

end Submatrix

end Hex
