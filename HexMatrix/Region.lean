/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Submatrix
public import HexMatrix.Block

public section

/-!
Backing-free output regions for storage-scheduled matrix algorithms.

Unlike `Submatrix`, a `Region` deliberately carries no matrix.  It is only an
offset and bounds proof into an output matrix that is passed separately and
linearly through every write.  Consequently four quadrant descriptors do not
create four aliases of the output backing buffer.
-/

namespace Hex

universe u

namespace Matrix

/-- A backing-free descriptor for a `rows × cols` rectangle inside an
`N × M` matrix. -/
structure Region (N M rows cols : Nat) where
  /-- Row offset in the destination matrix. -/
  r0 : Nat
  /-- Column offset in the destination matrix. -/
  c0 : Nat
  /-- The described rows lie in the destination. -/
  rows_le : r0 + rows ≤ N
  /-- The described columns lie in the destination. -/
  cols_le : c0 + cols ≤ M

namespace Region

variable {R : Type u} {N M rows cols : Nat}

/-- Destination row corresponding to a local region row. -/
@[inline]
def row (D : Region N M rows cols) (i : Fin rows) : Fin N :=
  ⟨D.r0 + i.val, by have := D.rows_le; omega⟩

/-- Destination column corresponding to a local region column. -/
@[inline]
def col (D : Region N M rows cols) (j : Fin cols) : Fin M :=
  ⟨D.c0 + j.val, by have := D.cols_le; omega⟩

/-- First flat destination index in a local region row. -/
@[inline]
def rowStart (D : Region N M rows cols) (i : Fin rows) : Nat :=
  (D.r0 + i.val) * M + D.c0

/-- Flat destination index corresponding to local region coordinates.  The
row-invariant multiplication is kept in `rowStart`, outside column loops. -/
@[inline]
def index (D : Region N M rows cols) (i : Fin rows) (j : Fin cols) : Fin (N * M) :=
  ⟨rowStart D i + j.val, by
    have h := flatIdx_lt (row D i).isLt (col D j).isLt
    simpa only [rowStart, row, col, Nat.add_assoc] using h⟩

/-- Read a matrix entry through a region descriptor. -/
@[inline]
def get (D : Region N M rows cols) (A : Matrix R N M) (i : Fin rows) (j : Fin cols) : R :=
  A[(row D i, col D j)]

/-- A region read is a read at its flat `index`. -/
theorem get_eq_data (D : Region N M rows cols) (A : Matrix R N M)
    (i : Fin rows) (j : Fin cols) :
    get D A i j = A.data[(index D i j).val]'(index D i j).isLt := by
  change A.data.get ⟨(D.r0 + i.val) * M + (D.c0 + j.val), _⟩ =
    A.data.get (index D i j)
  congr 1
  apply Fin.ext
  simp only [index, rowStart, Nat.add_assoc]

/-- Materialize the entries described by a region.  This is a proof-facing
operation; the storage-scheduled implementation writes through descriptors
without calling it. -/
@[expose]
def toMatrix (D : Region N M rows cols) (A : Matrix R N M) : Matrix R rows cols :=
  Matrix.ofFn fun i j => get D A i j

/-- Entry formula for a materialized region. -/
@[simp, grind =] theorem getElem_toMatrix (D : Region N M rows cols) (A : Matrix R N M)
    (i : Fin rows) (j : Fin cols) : (toMatrix D A)[i][j] = get D A i j := by
  rw [toMatrix, Matrix.getElem_ofFn]

/-- Extract an entry equality from equality of a materialized region and a matrix. -/
theorem get_of_toMatrix_eq (D : Region N M rows cols) (A : Matrix R N M)
    (B : Matrix R rows cols) (h : toMatrix D A = B) (i : Fin rows) (j : Fin cols) :
    get D A i j = B[(i, j)] := by
  have e := congrArg (fun X => X[i][j]) h
  simpa only [getElem_toMatrix, getElem_pair_eq_nested] using e

/-- Equal materialized regions have equal entries. -/
theorem get_eq_of_toMatrix_eq (D : Region N M rows cols) (A B : Matrix R N M)
    (h : toMatrix D A = toMatrix D B) (i : Fin rows) (j : Fin cols) :
    get D A i j = get D B i j := by
  have e := congrArg (fun X => X[i][j]) h
  simpa only [getElem_toMatrix] using e

/-- The descriptor for a whole matrix. -/
@[inline]
def full (N M : Nat) : Region N M N M where
  r0 := 0
  c0 := 0
  rows_le := by omega
  cols_le := by omega

/-- Reading through a whole-matrix descriptor is ordinary matrix access. -/
@[simp, grind =] theorem get_full (A : Matrix R N M) (i : Fin N) (j : Fin M) :
    get (full N M) A i j = A[(i, j)] := by
  simp only [get, full, row, col, Nat.zero_add, getElem_pair_eq_nested]

/-- Materializing a whole-matrix descriptor returns the matrix. -/
@[simp] theorem toMatrix_full (A : Matrix R N M) :
    toMatrix (full N M) A = A := by
  apply Matrix.ext_getElem
  intro i j
  rw [getElem_toMatrix, get_full, getElem_pair_eq_nested]

/-- Top-left quadrant of an evenly split region. -/
@[inline]
def toBlocks₁₁ (D : Region N M (h + h) (w + w)) : Region N M h w where
  r0 := D.r0
  c0 := D.c0
  rows_le := by have := D.rows_le; omega
  cols_le := by have := D.cols_le; omega

/-- Top-right quadrant of an evenly split region. -/
@[inline]
def toBlocks₁₂ (D : Region N M (h + h) (w + w)) : Region N M h w where
  r0 := D.r0
  c0 := D.c0 + w
  rows_le := by have := D.rows_le; omega
  cols_le := by have := D.cols_le; omega

/-- Bottom-left quadrant of an evenly split region. -/
@[inline]
def toBlocks₂₁ (D : Region N M (h + h) (w + w)) : Region N M h w where
  r0 := D.r0 + h
  c0 := D.c0
  rows_le := by have := D.rows_le; omega
  cols_le := by have := D.cols_le; omega

/-- Bottom-right quadrant of an evenly split region. -/
@[inline]
def toBlocks₂₂ (D : Region N M (h + h) (w + w)) : Region N M h w where
  r0 := D.r0 + h
  c0 := D.c0 + w
  rows_le := by have := D.rows_le; omega
  cols_le := by have := D.cols_le; omega

/-- Two region descriptors have disjoint rectangles. -/
@[expose]
def Disjoint (D : Region N M rows cols) (E : Region N M rows' cols') : Prop :=
  D.r0 + rows ≤ E.r0 ∨ E.r0 + rows' ≤ D.r0 ∨
  D.c0 + cols ≤ E.c0 ∨ E.c0 + cols' ≤ D.c0

/-- The left and right quadrants in the top row are disjoint. -/
theorem disjoint₁₁₁₂ (D : Region N M (h + h) (w + w)) :
    Disjoint D.toBlocks₁₁ D.toBlocks₁₂ := by
  simp only [Disjoint, toBlocks₁₁, toBlocks₁₂]
  omega

/-- The top-left and bottom-left quadrants are disjoint. -/
theorem disjoint₁₁₂₁ (D : Region N M (h + h) (w + w)) :
    Disjoint D.toBlocks₁₁ D.toBlocks₂₁ := by
  simp only [Disjoint, toBlocks₁₁, toBlocks₂₁]
  omega

/-- The top-left and bottom-right quadrants are disjoint. -/
theorem disjoint₁₁₂₂ (D : Region N M (h + h) (w + w)) :
    Disjoint D.toBlocks₁₁ D.toBlocks₂₂ := by
  simp only [Disjoint, toBlocks₁₁, toBlocks₂₂]
  omega

/-- The top-right and bottom-left quadrants are disjoint. -/
theorem disjoint₁₂₂₁ (D : Region N M (h + h) (w + w)) :
    Disjoint D.toBlocks₁₂ D.toBlocks₂₁ := by
  simp only [Disjoint, toBlocks₁₂, toBlocks₂₁]
  omega

/-- The top-right and bottom-right quadrants are disjoint. -/
theorem disjoint₁₂₂₂ (D : Region N M (h + h) (w + w)) :
    Disjoint D.toBlocks₁₂ D.toBlocks₂₂ := by
  simp only [Disjoint, toBlocks₁₂, toBlocks₂₂]
  omega

/-- The left and right quadrants in the bottom row are disjoint. -/
theorem disjoint₂₁₂₂ (D : Region N M (h + h) (w + w)) :
    Disjoint D.toBlocks₂₁ D.toBlocks₂₂ := by
  simp only [Disjoint, toBlocks₂₁, toBlocks₂₂]
  omega

/-- A region disjoint from a parent is disjoint from its top-left quadrant. -/
theorem disjoint_toBlocks₁₁ (D : Region N M (h + h) (w + w))
    (E : Region N M rows cols) (hDE : Disjoint D E) : Disjoint D.toBlocks₁₁ E := by
  simp only [Disjoint, toBlocks₁₁] at hDE ⊢
  omega

/-- A region disjoint from a parent is disjoint from its top-right quadrant. -/
theorem disjoint_toBlocks₁₂ (D : Region N M (h + h) (w + w))
    (E : Region N M rows cols) (hDE : Disjoint D E) : Disjoint D.toBlocks₁₂ E := by
  simp only [Disjoint, toBlocks₁₂] at hDE ⊢
  omega

/-- A region disjoint from a parent is disjoint from its bottom-left quadrant. -/
theorem disjoint_toBlocks₂₁ (D : Region N M (h + h) (w + w))
    (E : Region N M rows cols) (hDE : Disjoint D E) : Disjoint D.toBlocks₂₁ E := by
  simp only [Disjoint, toBlocks₂₁] at hDE ⊢
  omega

/-- A region disjoint from a parent is disjoint from its bottom-right quadrant. -/
theorem disjoint_toBlocks₂₂ (D : Region N M (h + h) (w + w))
    (E : Region N M rows cols) (hDE : Disjoint D E) : Disjoint D.toBlocks₂₂ E := by
  simp only [Disjoint, toBlocks₂₂] at hDE ⊢
  omega

/-- Materializing a descriptor's top-left quadrant is matrix block extraction. -/
theorem toMatrix_toBlocks₁₁ (D : Region N M (h + h) (w + w)) (A : Matrix R N M) :
    toMatrix D.toBlocks₁₁ A = Matrix.toBlocks₁₁ (toMatrix D A) := by
  apply Matrix.ext_getElem
  intro i j
  simp only [getElem_toMatrix, Matrix.getElem_toBlocks₁₁, get, row, col, toBlocks₁₁,
    Fin.val_castAdd]

/-- Materializing a descriptor's top-right quadrant is matrix block extraction. -/
theorem toMatrix_toBlocks₁₂ (D : Region N M (h + h) (w + w)) (A : Matrix R N M) :
    toMatrix D.toBlocks₁₂ A = Matrix.toBlocks₁₂ (toMatrix D A) := by
  apply Matrix.ext_getElem
  intro i j
  simp only [getElem_toMatrix, Matrix.getElem_toBlocks₁₂, get, row, col, toBlocks₁₂,
    Fin.val_castAdd, Fin.val_natAdd, Nat.add_assoc]

/-- Materializing a descriptor's bottom-left quadrant is matrix block extraction. -/
theorem toMatrix_toBlocks₂₁ (D : Region N M (h + h) (w + w)) (A : Matrix R N M) :
    toMatrix D.toBlocks₂₁ A = Matrix.toBlocks₂₁ (toMatrix D A) := by
  apply Matrix.ext_getElem
  intro i j
  simp only [getElem_toMatrix, Matrix.getElem_toBlocks₂₁, get, row, col, toBlocks₂₁,
    Fin.val_castAdd, Fin.val_natAdd, Nat.add_assoc]

/-- Materializing a descriptor's bottom-right quadrant is matrix block extraction. -/
theorem toMatrix_toBlocks₂₂ (D : Region N M (h + h) (w + w)) (A : Matrix R N M) :
    toMatrix D.toBlocks₂₂ A = Matrix.toBlocks₂₂ (toMatrix D A) := by
  apply Matrix.ext_getElem
  intro i j
  simp only [getElem_toMatrix, Matrix.getElem_toBlocks₂₂, get, row, col, toBlocks₂₂,
    Fin.val_natAdd, Nat.add_assoc]

/-- Disjointness of region descriptors is symmetric. -/
theorem disjoint_comm {D : Region N M rows cols} {E : Region N M rows' cols'} :
    Disjoint D E ↔ Disjoint E D := by
  simp only [Disjoint]
  omega

/-- Disjoint rectangles have distinct flat indices. -/
private theorem index_ne_of_disjoint (D : Region N M rows cols)
    (E : Region N M rows' cols') (h : Disjoint D E)
    (i : Fin rows) (j : Fin cols) (i' : Fin rows') (j' : Fin cols') :
    (index D i j).val ≠ (index E i' j').val := by
  intro heq
  have hd : (row D i).val * M + (col D j).val =
      (row E i').val * M + (col E j').val := by
    simpa only [index, rowStart, row, col, Nat.add_assoc] using heq
  have hrowD : ((row D i).val * M + (col D j).val) / M = (row D i).val :=
    flatIdx_div (col D j).isLt
  have hrowE : ((row E i').val * M + (col E j').val) / M = (row E i').val :=
    flatIdx_div (col E j').isLt
  have hcolD : ((row D i).val * M + (col D j).val) % M = (col D j).val :=
    flatIdx_mod (col D j).isLt
  have hcolE : ((row E i').val * M + (col E j').val) % M = (col E j').val :=
    flatIdx_mod (col E j').isLt
  have hr : (row D i).val = (row E i').val := by
    rw [← hrowD, hd, hrowE]
  have hc : (col D j).val = (col E j').val := by
    rw [← hcolD, hd, hcolE]
  simp only [row, col] at hr hc
  unfold Disjoint at h
  rcases h with h | h | h | h <;> omega

/-- Overwrite one row segment directly from an entry function.  `rowStart` is
computed once, and the consumed array is not retained by a temporary row. -/
@[inline]
private def setRowWith (D : Region N M rows cols) (d : Vector R (N * M))
    (i : Fin rows) (f : Fin cols → R) : Vector R (N * M) :=
  let base := rowStart D i
  Fin.foldl cols (fun d j => d.set (base + j.val) (f j) (index D i j).isLt) d

/-- Update one row segment entrywise.  Each old value is read before
`Vector.set` consumes the array, avoiding both a temporary row and
`Vector.modify`'s clear-then-set implementation. -/
@[inline]
private def modifyRowWith (D : Region N M rows cols) (d : Vector R (N * M))
    (i : Fin rows) (g : Fin cols → R → R) : Vector R (N * M) :=
  let base := rowStart D i
  Fin.foldl cols (fun d j =>
    let p := base + j.val
    let x := d[p]'(index D i j).isLt
    d.set p (g j x) (index D i j).isLt) d

/-- Flat indices inside a region are injective in their local coordinates. -/
private theorem index_inj (D : Region N M rows cols) (i i' : Fin rows) (j j' : Fin cols)
    (h : (index D i j).val = (index D i' j').val) : i = i' ∧ j = j' := by
  have hd : (row D i).val * M + (col D j).val =
      (row D i').val * M + (col D j').val := by
    simpa only [index, rowStart, row, col, Nat.add_assoc] using h
  have hr : (row D i).val = (row D i').val := by
    have hi : ((row D i).val * M + (col D j).val) / M = (row D i).val :=
      flatIdx_div (col D j).isLt
    have hi' : ((row D i').val * M + (col D j').val) / M = (row D i').val :=
      flatIdx_div (col D j').isLt
    have hdiv := congrArg (fun x => x / M) hd
    omega
  have hc : (col D j).val = (col D j').val := by
    have hj : ((row D i).val * M + (col D j).val) % M = (col D j).val :=
      flatIdx_mod (col D j).isLt
    have hj' : ((row D i').val * M + (col D j').val) % M = (col D j').val :=
      flatIdx_mod (col D j').isLt
    have hmod := congrArg (fun x => x % M) hd
    omega
  constructor
  · apply Fin.ext
    simp only [row] at hr
    omega
  · apply Fin.ext
    simp only [col] at hc
    omega

/-- Reading the row segment just written returns the supplied value. -/
private theorem get_setRowWith (D : Region N M rows cols) (d : Vector R (N * M))
    (i : Fin rows) (f : Fin cols → R) (j : Fin cols) :
    (setRowWith D d i f)[(index D i j).val]'(index D i j).isLt = f j := by
  unfold setRowWith
  rw [Fin.foldl_eq_finRange_foldl]
  exact Matrix.foldl_set_mem (fun t : Fin cols => (index D i t).val) f
    (fun t => (index D i t).isLt)
    (fun a b h => (index_inj D i i a b h).2)
    (List.finRange cols) (Matrix.nodup_finRange cols) d j (List.mem_finRange _)

/-- Writing a row segment preserves every flat index outside that segment. -/
private theorem get_setRowWith_ne (D : Region N M rows cols) (d : Vector R (N * M))
    (i : Fin rows) (f : Fin cols → R) (p : Nat) (hp : p < N * M)
    (hne : ∀ j : Fin cols, (index D i j).val ≠ p) :
    (setRowWith D d i f)[p]'hp = d[p]'hp := by
  unfold setRowWith
  rw [Fin.foldl_eq_finRange_foldl]
  exact Matrix.foldl_set_ne (fun j : Fin cols => (index D i j).val) f
    (fun j => (index D i j).isLt) hp (List.finRange cols) d
    (fun j _ => hne j)

/-- A fold of row transforms preserves a flat index when every row transform
preserves it. -/
private theorem foldl_rows_ne {count size : Nat}
    (step : Vector R size → Fin count → Vector R size) (p : Nat) (hp : p < size)
    (xs : List (Fin count))
    (hstep : ∀ d i, i ∈ xs → (step d i)[p]'hp = d[p]'hp) :
    ∀ (d : Vector R size),
      (xs.foldl step d)[p]'hp = d[p]'hp := by
  induction xs with
  | nil => intro d; rfl
  | cons x xs ih =>
    intro d
    rw [List.foldl_cons, ih (fun d i hi => hstep d i (List.mem_cons_of_mem _ hi)),
      hstep d x List.mem_cons_self]

/-- A fold of distinct row transforms stores the requested row's value when
each transform writes its own row and preserves every other row. -/
private theorem foldl_rows_mem {count size : Nat}
    (step : Vector R size → Fin count → Vector R size)
    (idx : Fin count → Nat) (bd : ∀ i, idx i < size) (val : Fin count → R)
    (hself : ∀ d i, (step d i)[idx i]'(bd i) = val i)
    (hne : ∀ d i r, i ≠ r → (step d i)[idx r]'(bd r) = d[idx r]'(bd r)) :
    ∀ (xs : List (Fin count)), xs.Nodup → ∀ (d : Vector R size) (r : Fin count), r ∈ xs →
      (xs.foldl step d)[idx r]'(bd r) = val r := by
  intro xs
  induction xs with
  | nil => intro _ _ r hr; simp at hr
  | cons x xs ih =>
    intro hnd d r hr
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · rw [foldl_rows_ne step (idx r) (bd r) xs (fun d t ht => hne d t r (fun h =>
          (List.nodup_cons.mp hnd).1 (h ▸ ht))), hself]
    · rw [ih (List.nodup_cons.mp hnd).2 _ r hr']

/-- Fill a destination region from an entry function, threading the destination
array directly through its writes. -/
@[inline]
def overwrite (D : Region N M rows cols) (A : Matrix R N M)
    (f : Fin rows → Fin cols → R) : Matrix R N M :=
  match A with
  | ⟨d⟩ =>
    ⟨Fin.foldl rows (fun d i => setRowWith D d i (f i)) d⟩

/-- Reading inside an overwritten region returns the supplied entry. -/
@[grind =] theorem get_overwrite (D : Region N M rows cols) (A : Matrix R N M)
    (f : Fin rows → Fin cols → R) (i : Fin rows) (j : Fin cols) :
    get D (overwrite D A f) i j = f i j := by
  obtain ⟨d⟩ := A
  rw [get_eq_data]
  change ((overwrite D ⟨d⟩ f).data[(index D i j).val]'(index D i j).isLt) = f i j
  simp only [overwrite]
  have hfold :
      Fin.foldl rows (fun d i => setRowWith D d i (f i)) d =
        (List.finRange rows).foldl
          (fun d i => setRowWith D d i (f i)) d :=
    Fin.foldl_eq_finRange_foldl (fun d i => setRowWith D d i (f i)) d
  have hmem := foldl_rows_mem
    (fun d i => setRowWith D d i (f i))
    (fun i => (index D i j).val) (fun i => (index D i j).isLt) (fun i => f i j)
    (fun d i => by
      rw [get_setRowWith])
    (fun d a i hai => get_setRowWith_ne D d a (f a)
      (index D i j).val (index D i j).isLt (fun t heq =>
        hai (index_inj D a i t j heq).1))
    (List.finRange rows) (Matrix.nodup_finRange rows) d i (List.mem_finRange _)
  exact (congrArg (fun v : Vector R (N * M) => v.get (index D i j)) hfold).trans hmem

/-- Overwriting one region preserves every disjoint region. -/
theorem get_overwrite_disjoint (D : Region N M rows cols)
    (E : Region N M rows' cols') (h : Disjoint D E) (A : Matrix R N M)
    (f : Fin rows → Fin cols → R) (i : Fin rows') (j : Fin cols') :
    get E (overwrite D A f) i j = get E A i j := by
  obtain ⟨d⟩ := A
  rw [get_eq_data, get_eq_data]
  change ((overwrite D ⟨d⟩ f).data[(index E i j).val]'(index E i j).isLt) =
    d[(index E i j).val]'(index E i j).isLt
  simp only [overwrite]
  have hfold :
      Fin.foldl rows (fun d i => setRowWith D d i (f i)) d =
        (List.finRange rows).foldl
          (fun d i => setRowWith D d i (f i)) d :=
    Fin.foldl_eq_finRange_foldl (fun d i => setRowWith D d i (f i)) d
  have hpres := foldl_rows_ne
    (fun d i => setRowWith D d i (f i))
    (index E i j).val (index E i j).isLt (List.finRange rows)
    (fun d a _ => get_setRowWith_ne D d a (f a)
      (index E i j).val (index E i j).isLt
      (fun b => index_ne_of_disjoint D E h a b i j)) d
  exact (congrArg (fun v : Vector R (N * M) => v.get (index E i j)) hfold).trans hpres

/-- Combine a destination region with entries supplied by a read-only function,
modifying each destination entry directly. -/
@[inline]
def accumulateWith (D : Region N M rows cols) (A : Matrix R N M)
    (f : Fin rows → Fin cols → R) (op : R → R → R) : Matrix R N M :=
  match A with
  | ⟨d⟩ =>
    ⟨Fin.foldl rows (fun d i =>
      modifyRowWith D d i (fun j x => op x (f i j))) d⟩

/-- Combine a destination region entrywise with a separate matrix, modifying
each destination entry directly. -/
@[inline]
def accumulateExternal (D : Region N M rows cols) (A : Matrix R N M)
    (B : Matrix R rows cols) (op : R → R → R) : Matrix R N M :=
  match A with
  | ⟨d⟩ =>
    ⟨Fin.foldl rows (fun d i =>
      modifyRowWith D d i (fun j x => op x B[(i, j)])) d⟩

/-- A row fold whose own row update depends on the previous value stores the
requested row's transformed value. -/
private theorem foldl_rows_modify {count size : Nat}
    (step : Vector R size → Fin count → Vector R size)
    (idx : Fin count → Nat) (bd : ∀ i, idx i < size) (g : Fin count → R → R)
    (hself : ∀ d i, (step d i)[idx i]'(bd i) = g i (d[idx i]'(bd i)))
    (hne : ∀ d i r, i ≠ r → (step d i)[idx r]'(bd r) = d[idx r]'(bd r)) :
    ∀ (xs : List (Fin count)), xs.Nodup → ∀ (d : Vector R size) (r : Fin count), r ∈ xs →
      (xs.foldl step d)[idx r]'(bd r) = g r (d[idx r]'(bd r)) := by
  intro xs
  induction xs with
  | nil => intro _ _ r hr; simp at hr
  | cons x xs ih =>
    intro hnd d r hr
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · rw [foldl_rows_ne step (idx r) (bd r) xs (fun d t ht => hne d t r (fun h =>
          (List.nodup_cons.mp hnd).1 (h ▸ ht))), hself]
    · rw [ih (List.nodup_cons.mp hnd).2 _ r hr', hne d x r (fun h =>
        (List.nodup_cons.mp hnd).1 (h ▸ hr'))]

/-- Reading an updated row returns the entrywise transformation. -/
private theorem get_modifyRowWith (D : Region N M rows cols) (d : Vector R (N * M))
    (i : Fin rows) (g : Fin cols → R → R) (j : Fin cols) :
    (modifyRowWith D d i g)[(index D i j).val]'(index D i j).isLt =
      g j (d[(index D i j).val]'(index D i j).isLt) := by
  unfold modifyRowWith
  rw [Fin.foldl_eq_finRange_foldl]
  let step := fun (d : Vector R (N * M)) (j : Fin cols) =>
    let p := (index D i j).val
    let x := d[p]'(index D i j).isLt
    d.set p (g j x) (index D i j).isLt
  exact foldl_rows_modify step (fun j => (index D i j).val)
    (fun j => (index D i j).isLt) g
    (fun d j => by
      dsimp only [step]
      rw [Vector.getElem_set_self])
    (fun d a j haj => by
      dsimp only [step]
      exact Vector.getElem_set_ne (index D i a).isLt (index D i j).isLt
        (fun heq => haj (index_inj D i i a j heq).2))
    (List.finRange cols) (Matrix.nodup_finRange cols) d j (List.mem_finRange _)

/-- Updating a row preserves every flat index outside that row segment. -/
private theorem get_modifyRowWith_ne (D : Region N M rows cols) (d : Vector R (N * M))
    (i : Fin rows) (g : Fin cols → R → R) (p : Nat) (hp : p < N * M)
    (hne : ∀ j : Fin cols, (index D i j).val ≠ p) :
    (modifyRowWith D d i g)[p]'hp = d[p]'hp := by
  unfold modifyRowWith
  rw [Fin.foldl_eq_finRange_foldl]
  let step := fun (d : Vector R (N * M)) (j : Fin cols) =>
    let q := (index D i j).val
    let x := d[q]'(index D i j).isLt
    d.set q (g j x) (index D i j).isLt
  exact foldl_rows_ne step p hp (List.finRange cols) (fun d j _ => by
    dsimp only [step]
    exact Vector.getElem_set_ne (index D i j).isLt hp (hne j)) d

/-- Reading a region after accumulation with a function returns the entrywise
combination. -/
@[grind =] theorem get_accumulateWith (D : Region N M rows cols) (A : Matrix R N M)
    (f : Fin rows → Fin cols → R) (op : R → R → R)
    (i : Fin rows) (j : Fin cols) :
    get D (accumulateWith D A f op) i j = op (get D A i j) (f i j) := by
  obtain ⟨d⟩ := A
  rw [get_eq_data, get_eq_data]
  change ((accumulateWith D ⟨d⟩ f op).data[(index D i j).val]'
    (index D i j).isLt) = op (d[(index D i j).val]'(index D i j).isLt) (f i j)
  simp only [accumulateWith]
  let step := fun d (i : Fin rows) =>
    modifyRowWith D d i (fun j x => op x (f i j))
  have hfold : Fin.foldl rows step d = (List.finRange rows).foldl step d :=
    Fin.foldl_eq_finRange_foldl step d
  have hmem := foldl_rows_modify step
    (fun i => (index D i j).val) (fun i => (index D i j).isLt)
    (fun i x => op x (f i j))
    (fun d i => by
      dsimp only [step]
      rw [get_modifyRowWith])
    (fun d a i hai => by
      dsimp only [step]
      exact get_modifyRowWith_ne D d a _ (index D i j).val (index D i j).isLt
        (fun t heq => hai (index_inj D a i t j heq).1))
    (List.finRange rows) (Matrix.nodup_finRange rows) d i (List.mem_finRange _)
  exact (congrArg (fun v : Vector R (N * M) => v.get (index D i j)) hfold).trans hmem

/-- Accumulation with a read-only function preserves every disjoint region. -/
theorem get_accumulateWith_disjoint (D : Region N M rows cols)
    (E : Region N M rows' cols') (h : Disjoint D E) (A : Matrix R N M)
    (f : Fin rows → Fin cols → R) (op : R → R → R)
    (i : Fin rows') (j : Fin cols') :
    get E (accumulateWith D A f op) i j = get E A i j := by
  obtain ⟨d⟩ := A
  rw [get_eq_data, get_eq_data]
  change ((accumulateWith D ⟨d⟩ f op).data[(index E i j).val]'
    (index E i j).isLt) = d[(index E i j).val]'(index E i j).isLt
  simp only [accumulateWith]
  let step := fun d (a : Fin rows) =>
    modifyRowWith D d a (fun b x => op x (f a b))
  have hfold : Fin.foldl rows step d = (List.finRange rows).foldl step d :=
    Fin.foldl_eq_finRange_foldl step d
  have hpres := foldl_rows_ne step (index E i j).val (index E i j).isLt
    (List.finRange rows) (fun d a _ => by
      dsimp only [step]
      exact get_modifyRowWith_ne D d a _ (index E i j).val (index E i j).isLt
        (fun b => index_ne_of_disjoint D E h a b i j)) d
  exact (congrArg (fun v : Vector R (N * M) => v.get (index E i j)) hfold).trans hpres

/-- Reading a region after an external accumulation returns the entrywise
combination. -/
@[grind =] theorem get_accumulateExternal (D : Region N M rows cols)
    (A : Matrix R N M) (B : Matrix R rows cols) (op : R → R → R)
    (i : Fin rows) (j : Fin cols) :
    get D (accumulateExternal D A B op) i j = op (get D A i j) B[(i, j)] := by
  obtain ⟨d⟩ := A
  rw [get_eq_data, get_eq_data]
  change ((accumulateExternal D ⟨d⟩ B op).data[(index D i j).val]'
    (index D i j).isLt) =
      op (d[(index D i j).val]'(index D i j).isLt) B[(i, j)]
  simp only [accumulateExternal]
  let step := fun d (i : Fin rows) =>
    modifyRowWith D d i (fun j x => op x B[(i, j)])
  have hfold : Fin.foldl rows step d = (List.finRange rows).foldl step d :=
    Fin.foldl_eq_finRange_foldl step d
  have hmem := foldl_rows_modify step
    (fun i => (index D i j).val) (fun i => (index D i j).isLt)
    (fun i x => op x B[(i, j)])
    (fun d i => by
      dsimp only [step]
      rw [get_modifyRowWith])
    (fun d a i hai => by
      dsimp only [step]
      exact get_modifyRowWith_ne D d a _ (index D i j).val (index D i j).isLt
        (fun t heq => hai (index_inj D a i t j heq).1))
    (List.finRange rows) (Matrix.nodup_finRange rows) d i (List.mem_finRange _)
  exact (congrArg (fun v : Vector R (N * M) => v.get (index D i j)) hfold).trans hmem

/-- Accumulating into one region preserves every disjoint region. -/
theorem get_accumulateExternal_disjoint (D : Region N M rows cols)
    (E : Region N M rows' cols') (h : Disjoint D E) (A : Matrix R N M)
    (B : Matrix R rows cols) (op : R → R → R) (i : Fin rows') (j : Fin cols') :
    get E (accumulateExternal D A B op) i j = get E A i j := by
  obtain ⟨d⟩ := A
  rw [get_eq_data, get_eq_data]
  change ((accumulateExternal D ⟨d⟩ B op).data[(index E i j).val]'
    (index E i j).isLt) = d[(index E i j).val]'(index E i j).isLt
  simp only [accumulateExternal]
  let step := fun d (a : Fin rows) =>
    modifyRowWith D d a (fun b x => op x B[(a, b)])
  have hfold : Fin.foldl rows step d = (List.finRange rows).foldl step d :=
    Fin.foldl_eq_finRange_foldl step d
  have hpres := foldl_rows_ne step (index E i j).val (index E i j).isLt
    (List.finRange rows) (fun d a _ => by
      dsimp only [step]
      exact get_modifyRowWith_ne D d a _ (index E i j).val (index E i j).isLt
        (fun b => index_ne_of_disjoint D E h a b i j)) d
  exact (congrArg (fun v : Vector R (N * M) => v.get (index E i j)) hfold).trans hpres

/-- Combine one row of two disjoint regions directly into the destination.  The
two entries are read before `Vector.set` consumes the array, so the array is not
retained by a temporary or modifying closure. -/
@[inline]
private def combineRowWith (D S : Region N M rows cols) (d : Vector R (N * M))
    (i : Fin rows) (op : R → R → R) : Vector R (N * M) :=
  let base := rowStart D i
  Fin.foldl cols (fun d j =>
    let p := base + j.val
    let x := d[p]'(index D i j).isLt
    let y := d.get (index S i j)
    d.set p (op x y) (index D i j).isLt) d

/-- Combine two disjoint regions of the owned output matrix, writing the first
and threading the backing array directly through every entry update. -/
@[inline]
def accumulate (D S : Region N M rows cols) (_h : Disjoint D S)
    (A : Matrix R N M) (op : R → R → R) : Matrix R N M :=
  match A with
  | ⟨d⟩ => ⟨Fin.foldl rows (fun d i => combineRowWith D S d i op) d⟩

/-- A row fold can transform one index from both its old value and an invariant
source index. -/
private theorem foldl_modify₂ {count size : Nat}
    (step : Vector R size → Fin count → Vector R size)
    (dst src : Fin count → Nat) (bdDst : ∀ i, dst i < size) (bdSrc : ∀ i, src i < size)
    (g : Fin count → R → R → R)
    (hself : ∀ d i,
      (step d i)[dst i]'(bdDst i) = g i (d[dst i]'(bdDst i)) (d[src i]'(bdSrc i)))
    (hneDst : ∀ d i r, i ≠ r →
      (step d i)[dst r]'(bdDst r) = d[dst r]'(bdDst r))
    (hneSrc : ∀ d i r, (step d i)[src r]'(bdSrc r) = d[src r]'(bdSrc r)) :
    ∀ (xs : List (Fin count)), xs.Nodup → ∀ (d : Vector R size) (r : Fin count), r ∈ xs →
      (xs.foldl step d)[dst r]'(bdDst r) =
        g r (d[dst r]'(bdDst r)) (d[src r]'(bdSrc r)) := by
  intro xs
  induction xs with
  | nil => intro _ _ r hr; simp at hr
  | cons x xs ih =>
    intro hnd d r hr
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · rw [foldl_rows_ne step (dst r) (bdDst r) xs (fun d t ht =>
          hneDst d t r (fun h => (List.nodup_cons.mp hnd).1 (h ▸ ht))), hself]
    · rw [ih (List.nodup_cons.mp hnd).2 _ r hr',
        hneDst d x r (fun h => (List.nodup_cons.mp hnd).1 (h ▸ hr')), hneSrc d x r]

/-- Reading a directly combined row returns the entrywise combination. -/
private theorem get_combineRowWith (D S : Region N M rows cols) (h : Disjoint D S)
    (d : Vector R (N * M)) (i : Fin rows) (op : R → R → R) (j : Fin cols) :
    (combineRowWith D S d i op)[(index D i j).val]'(index D i j).isLt =
      op (d[(index D i j).val]'(index D i j).isLt)
        (d[(index S i j).val]'(index S i j).isLt) := by
  unfold combineRowWith
  rw [Fin.foldl_eq_finRange_foldl]
  let step := fun (d : Vector R (N * M)) (j : Fin cols) =>
    let p := (index D i j).val
    let x := d[p]'(index D i j).isLt
    let y := d.get (index S i j)
    d.set p (op x y) (index D i j).isLt
  exact foldl_modify₂ step (fun j => (index D i j).val) (fun j => (index S i j).val)
    (fun j => (index D i j).isLt) (fun j => (index S i j).isLt) (fun _ x y => op x y)
    (fun d j => by
      dsimp only [step]
      rw [Vector.getElem_set_self]
      rfl)
    (fun d a j haj => by
      dsimp only [step]
      exact Vector.getElem_set_ne (index D i a).isLt (index D i j).isLt
        (fun heq => haj (index_inj D i i a j heq).2))
    (fun d a j => by
      dsimp only [step]
      exact Vector.getElem_set_ne (index D i a).isLt (index S i j).isLt
        (index_ne_of_disjoint D S h i a i j))
    (List.finRange cols) (Matrix.nodup_finRange cols) d j (List.mem_finRange _)

/-- Combining one row preserves every flat index outside its destination. -/
private theorem get_combineRowWith_ne (D S : Region N M rows cols)
    (d : Vector R (N * M)) (i : Fin rows) (op : R → R → R)
    (p : Nat) (hp : p < N * M) (hne : ∀ j : Fin cols, (index D i j).val ≠ p) :
    (combineRowWith D S d i op)[p]'hp = d[p]'hp := by
  unfold combineRowWith
  rw [Fin.foldl_eq_finRange_foldl]
  let step := fun (d : Vector R (N * M)) (j : Fin cols) =>
    let q := (index D i j).val
    let x := d[q]'(index D i j).isLt
    let y := d.get (index S i j)
    d.set q (op x y) (index D i j).isLt
  exact foldl_rows_ne step p hp (List.finRange cols) (fun d j _ => by
    dsimp only [step]
    exact Vector.getElem_set_ne (index D i j).isLt hp (hne j)) d

/-- Reading the destination of an in-buffer accumulation returns the requested
entrywise combination. -/
@[grind =] theorem get_accumulate (D S : Region N M rows cols) (h : Disjoint D S)
    (A : Matrix R N M) (op : R → R → R) (i : Fin rows) (j : Fin cols) :
    get D (accumulate D S h A op) i j = op (get D A i j) (get S A i j) := by
  obtain ⟨d⟩ := A
  rw [get_eq_data, get_eq_data, get_eq_data]
  change ((accumulate D S h ⟨d⟩ op).data[(index D i j).val]'
    (index D i j).isLt) = op (d[(index D i j).val]'(index D i j).isLt)
      (d[(index S i j).val]'(index S i j).isLt)
  simp only [accumulate]
  let step := fun d (i : Fin rows) => combineRowWith D S d i op
  have hfold : Fin.foldl rows step d = (List.finRange rows).foldl step d :=
    Fin.foldl_eq_finRange_foldl step d
  have hmem := foldl_modify₂ step
    (fun i => (index D i j).val) (fun i => (index S i j).val)
    (fun i => (index D i j).isLt) (fun i => (index S i j).isLt)
    (fun _ x y => op x y)
    (fun d i => by
      dsimp only [step]
      exact get_combineRowWith D S h d i op j)
    (fun d a i hai => by
      dsimp only [step]
      exact get_combineRowWith_ne D S d a op (index D i j).val (index D i j).isLt
        (fun t heq => hai (index_inj D a i t j heq).1))
    (fun d a i => by
      dsimp only [step]
      exact get_combineRowWith_ne D S d a op (index S i j).val (index S i j).isLt
        (fun t => index_ne_of_disjoint D S h a t i j))
    (List.finRange rows) (Matrix.nodup_finRange rows) d i (List.mem_finRange _)
  exact (congrArg (fun v : Vector R (N * M) => v.get (index D i j)) hfold).trans hmem

/-- In-buffer accumulation writes only its destination region. -/
theorem get_accumulate_disjoint (D S : Region N M rows cols) (hDS : Disjoint D S)
    (E : Region N M rows' cols') (hDE : Disjoint D E) (A : Matrix R N M)
    (op : R → R → R) (i : Fin rows') (j : Fin cols') :
    get E (accumulate D S hDS A op) i j = get E A i j := by
  obtain ⟨d⟩ := A
  rw [get_eq_data, get_eq_data]
  change ((accumulate D S hDS ⟨d⟩ op).data[(index E i j).val]'
    (index E i j).isLt) = d[(index E i j).val]'(index E i j).isLt
  simp only [accumulate]
  let step := fun d (a : Fin rows) => combineRowWith D S d a op
  have hfold : Fin.foldl rows step d = (List.finRange rows).foldl step d :=
    Fin.foldl_eq_finRange_foldl step d
  have hpres := foldl_rows_ne step (index E i j).val (index E i j).isLt
    (List.finRange rows) (fun d a _ => by
      dsimp only [step]
      exact get_combineRowWith_ne D S d a op (index E i j).val (index E i j).isLt
        (fun b => index_ne_of_disjoint D E hDE a b i j)) d
  exact (congrArg (fun v : Vector R (N * M) => v.get (index E i j)) hfold).trans hpres

/-- Matrix-level form of `get_overwrite_disjoint`. -/
theorem toMatrix_overwrite_disjoint (D : Region N M rows cols)
    (E : Region N M rows' cols') (h : Disjoint D E) (A : Matrix R N M)
    (f : Fin rows → Fin cols → R) :
    toMatrix E (overwrite D A f) = toMatrix E A := by
  apply Matrix.ext_getElem
  intro i j
  rw [getElem_toMatrix, getElem_toMatrix, get_overwrite_disjoint D E h]

/-- Matrix-level form of `get_accumulateWith_disjoint`. -/
theorem toMatrix_accumulateWith_disjoint (D : Region N M rows cols)
    (E : Region N M rows' cols') (h : Disjoint D E) (A : Matrix R N M)
    (f : Fin rows → Fin cols → R) (op : R → R → R) :
    toMatrix E (accumulateWith D A f op) = toMatrix E A := by
  apply Matrix.ext_getElem
  intro i j
  rw [getElem_toMatrix, getElem_toMatrix, get_accumulateWith_disjoint D E h]

/-- Matrix-level form of `get_accumulateExternal_disjoint`. -/
theorem toMatrix_accumulateExternal_disjoint (D : Region N M rows cols)
    (E : Region N M rows' cols') (h : Disjoint D E) (A : Matrix R N M)
    (B : Matrix R rows cols) (op : R → R → R) :
    toMatrix E (accumulateExternal D A B op) = toMatrix E A := by
  apply Matrix.ext_getElem
  intro i j
  rw [getElem_toMatrix, getElem_toMatrix, get_accumulateExternal_disjoint D E h]

/-- Matrix-level form of `get_accumulate_disjoint`. -/
theorem toMatrix_accumulate_disjoint (D S : Region N M rows cols)
    (hDS : Disjoint D S) (E : Region N M rows' cols') (hDE : Disjoint D E)
    (A : Matrix R N M) (op : R → R → R) :
    toMatrix E (accumulate D S hDS A op) = toMatrix E A := by
  apply Matrix.ext_getElem
  intro i j
  rw [getElem_toMatrix, getElem_toMatrix, get_accumulate_disjoint D S hDS E hDE]

end Region

end Matrix

end Hex
