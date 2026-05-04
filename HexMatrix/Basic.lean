import Batteries.Data.List.Lemmas

/-!
Core dense matrix definitions for `hex-matrix`.

This module models matrices as `Vector (Vector R m) n` and provides the
basic executable operations needed by later linear-algebra algorithms:
row/column accessors, zero and identity matrices, dot products,
matrix-vector multiplication, matrix-matrix multiplication, and norm-squared
helpers.
-/
namespace Hex

universe u

/-- Dense `n × m` matrices over `R`, represented as vectors of rows. -/
abbrev Matrix (R : Type u) (n m : Nat) := Vector (Vector R m) n

namespace Vector

/-- Dot product of two vectors. -/
def dotProduct [Mul R] [Add R] [OfNat R 0] (u v : Vector R n) : R :=
  (List.finRange n).foldl (fun acc i => acc + u[i] * v[i]) 0

private theorem foldl_dotProduct_sub_smul_rat
    (xs : List (Fin n)) (u v w : Vector Rat n) (c accU accV : Rat) :
    xs.foldl (fun acc i => acc + (u - c • v)[i] * w[i]) (accU - c * accV) =
      xs.foldl (fun acc i => acc + u[i] * w[i]) accU -
        c * xs.foldl (fun acc i => acc + v[i] * w[i]) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp
  | cons i xs ih =>
      have hstart :
          accU - c * accV + (u - c • v)[i] * w[i] =
            (accU + u[i] * w[i]) - c * (accV + v[i] * w[i]) := by
        have hentry : (u - c • v)[i] = u[i] - c * v[i] := by
          change (u - c • v)[i.val] = u[i.val] - c * v[i.val]
          rw [Vector.getElem_sub, Vector.getElem_smul]
          rfl
        rw [hentry]
        grind
      simp only [List.foldl_cons]
      rw [hstart]
      exact ih (accU := accU + u[i] * w[i]) (accV := accV + v[i] * w[i])

/-- Dot product distributes over subtracting a scalar multiple in the left argument. -/
theorem dotProduct_sub_smul_rat (u v w : Vector Rat n) (c : Rat) :
    dotProduct (u - c • v) w = dotProduct u w - c * dotProduct v w := by
  have hzero : (0 : Rat) - 0 = 0 := by
    grind
  simpa [dotProduct, hzero] using
    foldl_dotProduct_sub_smul_rat (xs := List.finRange n) (u := u) (v := v) (w := w)
      (c := c) (accU := 0) (accV := 0)

/-- Zero specialization of `dotProduct_sub_smul`. -/
theorem dotProduct_sub_smul_eq_zero_rat (u v w : Vector Rat n) (c : Rat)
    (h : dotProduct u w = c * dotProduct v w) :
    dotProduct (u - c • v) w = 0 := by
  rw [dotProduct_sub_smul_rat, h]
  grind

/-- Squared Euclidean norm of a vector. -/
def normSq [Mul R] [Add R] [OfNat R 0] (v : Vector R n) : R :=
  dotProduct v v

/-- Squared Euclidean norm specialized to integer vectors. -/
def intNormSq (v : Vector Int n) : Int :=
  normSq v

/-- Squared Euclidean norm specialized to rational vectors. -/
def ratNormSq (v : Vector Rat n) : Rat :=
  normSq v

end Vector

namespace Matrix

/-- Build a matrix from an entry function. -/
def ofFn (f : Fin n → Fin m → R) : Matrix R n m :=
  Vector.ofFn fun i => Vector.ofFn fun j => f i j

/-- The `i`-th row of a matrix. -/
def row (M : Matrix R n m) (i : Fin n) : Vector R m :=
  M[i]

/-- The `j`-th column of a matrix. -/
def col (M : Matrix R n m) (j : Fin m) : Vector R n :=
  Vector.ofFn fun i => M[i][j]

/-- The transpose of a dense matrix. -/
def transpose (M : Matrix R n m) : Matrix R m n :=
  Vector.ofFn fun j => col M j

/-- The all-zero matrix. -/
protected def zero [OfNat R 0] : Matrix R n m :=
  ofFn fun _ _ => 0

instance [OfNat R 0] : Zero (Matrix R n m) where
  zero := Matrix.zero

/-- The identity matrix. -/
protected def identity [OfNat R 0] [OfNat R 1] : Matrix R n n :=
  ofFn fun i j => if i = j then 1 else 0

instance [OfNat R 0] [OfNat R 1] : One (Matrix R n n) where
  one := Matrix.identity

/-- Dot product of two vectors. -/
def dot [Mul R] [Add R] [OfNat R 0] (u v : Vector R n) : R :=
  Hex.Vector.dotProduct u v

/-- Dot product distributes over subtracting a scalar multiple in the left argument. -/
theorem dot_sub_smul_rat (u v w : Vector Rat n) (c : Rat) :
    dot (u - c • v) w = dot u w - c * dot v w := by
  simpa [dot] using Hex.Vector.dotProduct_sub_smul_rat (u := u) (v := v) (w := w) (c := c)

/-- Zero specialization of `dot_sub_smul`. -/
theorem dot_sub_smul_eq_zero_rat (u v w : Vector Rat n) (c : Rat)
    (h : dot u w = c * dot v w) :
    dot (u - c • v) w = 0 := by
  rw [dot_sub_smul_rat, h]
  grind

/-- Multiply a matrix by a column vector. -/
def mulVec [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (v : Vector R m) :
    Vector R n :=
  Vector.ofFn fun i => dot (row M i) v

/-- Multiply two matrices. -/
def mul [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (N : Matrix R m k) :
    Matrix R n k :=
  ofFn fun i j => dot (row M i) (col N j)

instance [Mul R] [Add R] [OfNat R 0] : HMul (Matrix R n m) (Vector R m) (Vector R n) where
  hMul := mulVec

instance [Mul R] [Add R] [OfNat R 0] : HMul (Matrix R n m) (Matrix R m k) (Matrix R n k) where
  hMul := mul

/-- Squared Euclidean norm of a vector. -/
def normSq [Mul R] [Add R] [OfNat R 0] (v : Vector R n) : R :=
  Hex.Vector.normSq v

/-- Squared Euclidean norm specialized to integer vectors. -/
def intNormSq (v : Vector Int n) : Int :=
  Hex.Vector.intNormSq v

/-- Squared Euclidean norm specialized to rational vectors. -/
def ratNormSq (v : Vector Rat n) : Rat :=
  Hex.Vector.ratNormSq v

/-- Gram matrix of the rows of a dense matrix. -/
def gramMatrix [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) : Matrix R n n :=
  ofFn fun i j => Hex.Vector.dotProduct (row M i) (row M j)

/-- Leading principal `(k + 1) × (k + 1)` submatrix of a square matrix. -/
def submatrix (M : Matrix R n n) (k : Fin n) : Matrix R (k.val + 1) (k.val + 1) :=
  ofFn fun i j =>
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt k.isLt)⟩
    let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
    M[ii][jj]

/-- Leading principal `k × k` prefix of a square matrix. This variant includes
the empty prefix and is convenient for Bareiss pivot/minor statements. -/
def leadingPrefix (M : Matrix R n n) (k : Nat) (hk : k ≤ n) : Matrix R k k :=
  ofFn fun i j =>
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
    M[ii][jj]

@[simp] theorem leadingPrefix_entry (M : Matrix R n n) (k : Nat) (hk : k ≤ n)
    (i j : Fin k) :
    (leadingPrefix M k hk)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
       M[ii][jj]) := by
  simp [leadingPrefix, ofFn]

@[simp] theorem submatrix_entry (M : Matrix R n n) (k : Fin n)
    (i j : Fin (k.val + 1)) :
    (submatrix M k)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt k.isLt)⟩
       let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
       M[ii][jj]) := by
  simp [submatrix, ofFn]

/-- The existing `submatrix` API is the `(k + 1)` leading-prefix API at the
same boundary. -/
theorem submatrix_eq_leadingPrefix (M : Matrix R n n) (k : Fin n) :
    submatrix M k = leadingPrefix M (k.val + 1) (Nat.succ_le_of_lt k.isLt) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [submatrix, leadingPrefix, ofFn]

/-- Bordered Bareiss minor with the first `k` rows/columns and one extra
border row `i` and column `j`. For Bareiss applications `i` and `j` are in the
trailing part, but the constructor is total and leaves that side condition to
the invariant using it. -/
def borderedMinor (M : Matrix R n n) (k : Nat) (hk : k < n) (i j : Fin n) :
    Matrix R (k + 1) (k + 1) :=
  ofFn fun r c =>
    let rr : Fin n :=
      if hr : r.val < k then
        ⟨r.val, Nat.lt_trans hr hk⟩
      else
        i
    let cc : Fin n :=
      if hc : c.val < k then
        ⟨c.val, Nat.lt_trans hc hk⟩
      else
        j
    M[rr][cc]

@[simp] theorem borderedMinor_entry_lt_lt (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) (r c : Fin (k + 1)) (hr : r.val < k) (hc : c.val < k) :
    (borderedMinor M k hk i j)[r][c] =
      (let rr : Fin n := ⟨r.val, Nat.lt_trans hr hk⟩
       let cc : Fin n := ⟨c.val, Nat.lt_trans hc hk⟩
       M[rr][cc]) := by
  simp [borderedMinor, ofFn, hr, hc]

@[simp] theorem borderedMinor_entry_lt_last (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) (r : Fin (k + 1)) (hr : r.val < k) :
    (borderedMinor M k hk i j)[r][Fin.last k] =
      (let rr : Fin n := ⟨r.val, Nat.lt_trans hr hk⟩
       M[rr][j]) := by
  simp [borderedMinor, ofFn, hr]

@[simp] theorem borderedMinor_entry_last_lt (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) (c : Fin (k + 1)) (hc : c.val < k) :
    (borderedMinor M k hk i j)[Fin.last k][c] =
      (let cc : Fin n := ⟨c.val, Nat.lt_trans hc hk⟩
       M[i][cc]) := by
  simp [borderedMinor, ofFn, hc]

@[simp] theorem borderedMinor_entry_last_last (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) :
    (borderedMinor M k hk i j)[Fin.last k][Fin.last k] = M[i][j] := by
  simp [borderedMinor, ofFn]

/-- The top-left `k × k` block of a bordered minor is the leading prefix of the
source matrix. This is the reindexing fact used when a determinant expansion
isolates the final border row/column. -/
theorem leadingPrefix_borderedMinor_eq_leadingPrefix (M : Matrix R n n) (k : Nat)
    (hk : k < n) (i j : Fin n) :
    leadingPrefix (borderedMinor M k hk i j) k (Nat.le_succ k) =
      leadingPrefix M k (Nat.le_of_lt hk) := by
  apply Vector.ext
  intro r _hr
  apply Vector.ext
  intro c _hc
  simp [leadingPrefix, borderedMinor, ofFn]

/-- The top-left `(k + 1) × (k + 1)` block of the next bordered minor is the
current bordered minor whose extra row/column are the `k`-th source row/column. -/
theorem leadingPrefix_borderedMinor_succ_eq_borderedMinor (M : Matrix R n n)
    (k : Nat) (hk : k < n) (hnext : k + 1 < n) (i j : Fin n) :
    leadingPrefix (borderedMinor M (k + 1) hnext i j) (k + 1)
        (Nat.le_succ (k + 1)) =
      borderedMinor M k hk ⟨k, hk⟩ ⟨k, hk⟩ := by
  apply Vector.ext
  intro r _hr
  apply Vector.ext
  intro c _hc
  by_cases hrk : r < k <;> by_cases hck : c < k
  · simp [leadingPrefix, borderedMinor, ofFn, hrk, hck]
  · have hc_eq : c = k := by omega
    simp [leadingPrefix, borderedMinor, ofFn, hrk, hc_eq]
  · have hr_eq : r = k := by omega
    simp [leadingPrefix, borderedMinor, ofFn, hck, hr_eq]
  · have hr_eq : r = k := by omega
    have hc_eq : c = k := by omega
    simp [leadingPrefix, borderedMinor, ofFn, hr_eq, hc_eq]

/-- The identity matrix entry function: `1[i][j] = 1` if `i = j`, else `0`. -/
@[simp] theorem getElem_one [OfNat R 0] [OfNat R 1] {n : Nat} (i j : Fin n) :
    (1 : Matrix R n n)[i][j] = if i = j then (1 : R) else 0 := by
  simp [show (1 : Matrix R n n) = Matrix.identity from rfl, Matrix.identity, ofFn]

/-- A foldl whose every step adds `0` reduces to the initial accumulator. -/
private theorem foldl_add_eq_acc {R : Type u} [Lean.Grind.CommRing R]
    {α : Type v} (xs : List α) (f : α → R) (acc : R)
    (hf : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) acc = acc := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.foldl_nil]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = 0 := hf x (by simp)
      have hxs : ∀ y ∈ xs, f y = 0 := fun y hy => hf y (List.mem_cons_of_mem _ hy)
      rw [hx]
      have hac : acc + (0 : R) = acc := by grind
      rw [hac]
      exact ih acc hxs

/-- A foldl summing an indicator function picks out the unique matching index. -/
private theorem foldl_indicator_unique {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (xs : List (Fin n)) (i : Fin n)
    (hi : i ∈ xs) (hnodup : xs.Nodup) (acc : R) :
    xs.foldl (fun acc l => acc + (if i = l then (1 : R) else 0)) acc = acc + 1 := by
  induction xs generalizing acc with
  | nil => exact absurd hi (List.not_mem_nil)
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hi with hieq | hitail
      · have hx_eq : (if i = x then (1 : R) else 0) = 1 := by
          rw [hieq]; simp
        rw [hx_eq]
        have hxs_zero : ∀ y ∈ xs, (if i = y then (1 : R) else 0) = 0 := by
          intro y hy
          have hyx : y ≠ x := fun heq => by
            rw [heq] at hy
            exact (List.nodup_cons.mp hnodup).1 hy
          have hiy : i ≠ y := by
            rw [hieq]; exact fun h => hyx h.symm
          simp [hiy]
        rw [foldl_add_eq_acc xs _ _ hxs_zero]
      · have hxi : i ≠ x := by
          intro heq
          rw [← heq] at hnodup
          exact (List.nodup_cons.mp hnodup).1 hitail
        have hx_eq : (if i = x then (1 : R) else 0) = 0 := by simp [hxi]
        rw [hx_eq]
        have hac : acc + (0 : R) = acc := by grind
        rw [hac]
        exact ih hitail (List.nodup_cons.mp hnodup).2 acc

/-- Squaring an indicator gives the same indicator. -/
private theorem foldl_indicator_square_eq {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (xs : List (Fin n)) (i : Fin n) (acc : R) :
    xs.foldl (fun acc l =>
        acc + (if i = l then (1 : R) else 0) * (if i = l then (1 : R) else 0)) acc =
      xs.foldl (fun acc l => acc + (if i = l then (1 : R) else 0)) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hsq :
          (if i = x then (1 : R) else 0) * (if i = x then (1 : R) else 0) =
            if i = x then (1 : R) else 0 := by
        by_cases h : i = x
        · rw [if_pos h]; grind
        · rw [if_neg h]; grind
      rw [hsq]
      exact ih _

/-- Strip `Vector.ofFn` lookups inside a dotProduct-style foldl body. -/
private theorem foldl_dotProduct_basis_body {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (xs : List (Fin n)) (i j : Fin n) (acc : R) :
    xs.foldl
        (fun acc l =>
          acc +
            (Vector.ofFn fun b : Fin n => (if i = b then (1 : R) else 0))[l] *
              (Vector.ofFn fun b : Fin n => (if j = b then (1 : R) else 0))[l]) acc =
      xs.foldl
        (fun acc l =>
          acc + (if i = l then (1 : R) else 0) * (if j = l then (1 : R) else 0)) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hxi : (Vector.ofFn fun b : Fin n => (if i = b then (1 : R) else 0))[x] =
          if i = x then (1 : R) else 0 := by simp
      have hxj : (Vector.ofFn fun b : Fin n => (if j = b then (1 : R) else 0))[x] =
          if j = x then (1 : R) else 0 := by simp
      rw [hxi, hxj]
      exact ih (acc + (if i = x then 1 else 0) * (if j = x then 1 else 0))

/-- Dot product of the `i`-th and `j`-th identity rows. -/
theorem dotProduct_basis_basis {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (i j : Fin n) :
    Hex.Vector.dotProduct
        (Vector.ofFn fun b : Fin n => (if i = b then (1 : R) else 0))
        (Vector.ofFn fun b : Fin n => (if j = b then (1 : R) else 0)) =
      if i = j then 1 else 0 := by
  unfold Hex.Vector.dotProduct
  rw [foldl_dotProduct_basis_body]
  by_cases hij : i = j
  · subst hij
    rw [foldl_indicator_square_eq]
    rw [foldl_indicator_unique (List.finRange n) i (List.mem_finRange i)
      (List.nodup_finRange n) (0 : R)]
    rw [if_pos rfl]; grind
  · have hzero : ∀ l ∈ List.finRange n,
        (if i = l then (1 : R) else 0) * (if j = l then (1 : R) else 0) = 0 := by
      intro l _
      by_cases hil : i = l
      · have hjl : j ≠ l := fun heq => hij (hil.trans heq.symm)
        rw [if_pos hil, if_neg hjl]; grind
      · rw [if_neg hil]; grind
    rw [foldl_add_eq_acc (List.finRange n) _ _ hzero]
    rw [if_neg hij]

/-- The Gram matrix of the identity is the identity. -/
theorem gramMatrix_one {R : Type u} [Lean.Grind.CommRing R] {n : Nat} :
    gramMatrix (1 : Matrix R n n) = (1 : Matrix R n n) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have hrow_i : (1 : Matrix R n n).row ⟨i, hi⟩ =
      Vector.ofFn fun b : Fin n => (if (⟨i, hi⟩ : Fin n) = b then (1 : R) else 0) := by
    apply Vector.ext
    intro a ha
    show ((1 : Matrix R n n).row ⟨i, hi⟩)[(⟨a, ha⟩ : Fin n)] =
      (Vector.ofFn fun b : Fin n => if (⟨i, hi⟩ : Fin n) = b then (1 : R) else 0)[
        (⟨a, ha⟩ : Fin n)]
    rw [Matrix.row, getElem_one]
    simp
  have hrow_j : (1 : Matrix R n n).row ⟨j, hj⟩ =
      Vector.ofFn fun b : Fin n => (if (⟨j, hj⟩ : Fin n) = b then (1 : R) else 0) := by
    apply Vector.ext
    intro a ha
    show ((1 : Matrix R n n).row ⟨j, hj⟩)[(⟨a, ha⟩ : Fin n)] =
      (Vector.ofFn fun b : Fin n => if (⟨j, hj⟩ : Fin n) = b then (1 : R) else 0)[
        (⟨a, ha⟩ : Fin n)]
    rw [Matrix.row, getElem_one]
    simp
  show (gramMatrix (1 : Matrix R n n))[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin n)] =
    (1 : Matrix R n n)[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin n)]
  have hgram :
      (gramMatrix (1 : Matrix R n n))[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin n)] =
        Hex.Vector.dotProduct ((1 : Matrix R n n).row ⟨i, hi⟩)
          ((1 : Matrix R n n).row ⟨j, hj⟩) := by
    unfold gramMatrix ofFn
    simp
  rw [hgram, hrow_i, hrow_j, dotProduct_basis_basis, getElem_one]

/-- The leading principal `(k + 1) × (k + 1)` submatrix of the identity is the
identity. -/
theorem submatrix_one {R : Type u} [OfNat R 0] [OfNat R 1] {n : Nat} (k : Fin n) :
    submatrix (1 : Matrix R n n) k = (1 : Matrix R (k.val + 1) (k.val + 1)) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  show (submatrix (1 : Matrix R n n) k)[(⟨i, hi⟩ : Fin (k.val + 1))][
      (⟨j, hj⟩ : Fin (k.val + 1))] =
    (1 : Matrix R (k.val + 1) (k.val + 1))[(⟨i, hi⟩ : Fin (k.val + 1))][
      (⟨j, hj⟩ : Fin (k.val + 1))]
  rw [submatrix_entry]
  rw [getElem_one (i := (⟨i, Nat.lt_of_lt_of_le hi (Nat.succ_le_of_lt k.isLt)⟩ : Fin n))]
  rw [getElem_one (i := (⟨i, hi⟩ : Fin (k.val + 1)))]
  by_cases hij : (⟨i, hi⟩ : Fin (k.val + 1)) = ⟨j, hj⟩
  · have hval : i = j := Fin.val_eq_of_eq hij
    have hijn :
        (⟨i, Nat.lt_of_lt_of_le hi (Nat.succ_le_of_lt k.isLt)⟩ : Fin n) =
          ⟨j, Nat.lt_of_lt_of_le hj (Nat.succ_le_of_lt k.isLt)⟩ := by
      apply Fin.eq_of_val_eq; exact hval
    simp [hij, hijn]
  · have hval : i ≠ j := fun heq => hij (by apply Fin.eq_of_val_eq; exact heq)
    have hijn :
        (⟨i, Nat.lt_of_lt_of_le hi (Nat.succ_le_of_lt k.isLt)⟩ : Fin n) ≠
          ⟨j, Nat.lt_of_lt_of_le hj (Nat.succ_le_of_lt k.isLt)⟩ := fun heq =>
      hval (Fin.val_eq_of_eq heq)
    simp [hij, hijn]

end Matrix
end Hex
