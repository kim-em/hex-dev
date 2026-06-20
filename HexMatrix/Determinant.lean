import Std
import Init.Grind.Ring.Field
import Batteries.Data.Fin.Fold
import Batteries.Data.List.Lemmas
import Batteries.Data.Vector.Lemmas
import HexMatrix.RowEchelon

/-!
Determinant routines for `hex-matrix`.

This module adds the generic Leibniz-formula determinant for dense square
matrices together with the determinant behavior of the elementary row
operations used by row reduction and Bareiss pivot tracking.
-/

namespace Hex

universe u

namespace Matrix

variable {α : Type u}

/-- Insert an element into a vector at a given position. -/
def insertAt (x : α) (v : Vector α n) (i : Fin (n + 1)) : Vector α (n + 1) :=
  ⟨(v.toList.insertIdx i.val x).toArray, by
    have hi : i.val ≤ v.toList.length := by
      simpa using Nat.lt_succ_iff.mp i.isLt
    simpa using List.length_insertIdx_of_le_length (a := x) (as := v.toList) hi⟩

/-- The unique empty vector. -/
def emptyVec : Vector α 0 :=
  ⟨#[], rfl⟩

/-- Enumerate the permutations of `Fin n` as length-`n` vectors. -/
def permutationVectors : (n : Nat) → List (Vector (Fin n) n)
  | 0 => [emptyVec]
  | n + 1 =>
      List.flatMap
        (fun v =>
          (List.finRange (n + 1)).map fun i =>
            insertAt (Fin.last n) (v.map Fin.castSucc) i)
        (permutationVectors n)

/-- Count inversions in a permutation written as a list. -/
def inversionCount : List (Fin n) → Nat
  | [] => 0
  | x :: xs =>
      xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 + inversionCount xs

/-- Count the cross-inversions between two lists: pairs `(x, y)` with `x` drawn
from the first list, `y` from the second, and `y < x`. -/
private def crossInversionCount {n : Nat} : List (Fin n) → List (Fin n) → Nat
  | [], _ => 0
  | x :: xs, ys =>
      ys.foldl (fun acc y => acc + if y < x then 1 else 0) 0 +
        crossInversionCount xs ys

/-- A predicate-counting left fold splits its starting accumulator off
additively. -/
private theorem foldCount_start {α : Type u} (xs : List α) (p : α → Prop)
    [DecidablePred p] (acc : Nat) :
    xs.foldl (fun acc y => acc + if p y then 1 else 0) acc =
      acc + xs.foldl (fun acc y => acc + if p y then 1 else 0) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + if p y then 1 else 0), ih (0 + if p y then 1 else 0)]
      omega

/-- The inversion-counting left fold splits its starting accumulator off
additively. -/
private theorem inversionFold_start {n : Nat} (xs : List (Fin n)) (x : Fin n)
    (acc : Nat) :
    xs.foldl (fun acc y => acc + if y < x then 1 else 0) acc =
      acc + xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + if y < x then 1 else 0), ih (0 + if y < x then 1 else 0)]
      omega

/-- The inversion-counting fold over an appended list is the sum of the folds
over each part. -/
private theorem inversionFold_append {n : Nat} (xs ys : List (Fin n)) (x : Fin n) :
    (xs ++ ys).foldl (fun acc y => acc + if y < x then 1 else 0) 0 =
      xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 +
        ys.foldl (fun acc y => acc + if y < x then 1 else 0) 0 := by
  rw [List.foldl_append, inversionFold_start]

/-- Inversions of a concatenation split into the inversions within each part
plus the cross-inversions between them. -/
private theorem inversionCount_append {n : Nat} (xs ys : List (Fin n)) :
    inversionCount (xs ++ ys) =
      inversionCount xs + inversionCount ys + crossInversionCount xs ys := by
  induction xs with
  | nil =>
      change inversionCount ys =
        inversionCount ([] : List (Fin n)) + inversionCount ys +
          crossInversionCount ([] : List (Fin n)) ys
      simp [inversionCount, crossInversionCount]
  | cons x xs ih =>
      simp only [List.cons_append, inversionCount, crossInversionCount]
      rw [inversionFold_append, ih]
      omega

/-- Cross-inversion count is additive in its right argument under
concatenation. -/
private theorem crossInversionCount_append_right {n : Nat}
    (xs ys zs : List (Fin n)) :
    crossInversionCount xs (ys ++ zs) =
      crossInversionCount xs ys + crossInversionCount xs zs := by
  induction xs with
  | nil =>
      simp [crossInversionCount]
  | cons x xs ih =>
      simp only [crossInversionCount]
      rw [inversionFold_append, ih]
      omega

/-- Cross-inversions into a singleton right list count the left-list entries
above that element. -/
private theorem crossInversionCount_singleton_right {n : Nat}
    (xs : List (Fin n)) (y : Fin n) :
    crossInversionCount xs [y] =
      xs.foldl (fun acc x => acc + if y < x then 1 else 0) 0 := by
  induction xs with
  | nil =>
      simp [crossInversionCount]
  | cons x xs ih =>
      simp only [crossInversionCount, List.foldl_cons, List.foldl_nil]
      rw [ih]
      exact (foldCount_start xs (fun x => y < x) (0 + if y < x then 1 else 0)).symm

/-- Swapping the two elements of a right-hand pair leaves the cross-inversion
count unchanged. -/
private theorem crossInversionCount_pair_swap_right {n : Nat}
    (xs : List (Fin n)) (a b : Fin n) :
    crossInversionCount xs [a, b] =
      crossInversionCount xs [b, a] := by
  induction xs with
  | nil =>
      simp [crossInversionCount]
  | cons x xs ih =>
      simp [crossInversionCount]
      rw [ih]
      omega

/-- Swapping the two elements of a left-hand pair leaves the cross-inversion
count unchanged. -/
private theorem crossInversionCount_pair_swap_left {n : Nat}
    (xs : List (Fin n)) (a b : Fin n) :
    crossInversionCount [a, b] xs =
      crossInversionCount [b, a] xs := by
  simp [crossInversionCount]
  omega

/-- A two-element list has exactly one inversion precisely when its entries are
out of order. -/
private theorem inversionCount_pair {n : Nat} (a b : Fin n) :
    inversionCount [a, b] = if b < a then 1 else 0 := by
  simp [inversionCount]

/-- Swapping two distinct adjacent entries flips the parity of the inversion
count. -/
private theorem inversionCount_adjacent_swap_parity {n : Nat}
    (pre post : List (Fin n)) (a b : Fin n) (h : a ≠ b) :
    inversionCount (pre ++ a :: b :: post) % 2 =
      (inversionCount (pre ++ b :: a :: post) + 1) % 2 := by
  have horder : a < b ∨ b < a := by
    have hval : a.val ≠ b.val := by
      intro hv
      exact h (Fin.ext hv)
    cases Nat.lt_or_gt_of_ne hval with
    | inl hab => exact Or.inl hab
    | inr hba => exact Or.inr hba
  rw [show pre ++ a :: b :: post = pre ++ ([a, b] ++ post) by simp]
  rw [show pre ++ b :: a :: post = pre ++ ([b, a] ++ post) by simp]
  have hcross :
      crossInversionCount pre ([a, b] ++ post) =
        crossInversionCount pre ([b, a] ++ post) := by
    repeat rw [crossInversionCount_append_right]
    rw [crossInversionCount_pair_swap_right]
  have htail :
      crossInversionCount [a, b] post =
        crossInversionCount [b, a] post := by
    exact crossInversionCount_pair_swap_left post a b
  rw [inversionCount_append pre ([a, b] ++ post)]
  rw [inversionCount_append pre ([b, a] ++ post)]
  rw [hcross]
  rw [inversionCount_append [a, b] post]
  rw [inversionCount_append [b, a] post]
  rw [htail]
  rw [inversionCount_pair a b]
  rw [inversionCount_pair b a]
  cases horder with
  | inl hab =>
      have hba : ¬ b < a := by omega
      simp [hab, hba]
      omega
  | inr hba =>
      have hab : ¬ a < b := by omega
      simp [hab, hba]
      omega

/-- Swapping two entries separated by an arbitrary duplicate-free middle segment
flips the parity of the inversion count. -/
private theorem inversionCount_swap_separated_parity {n : Nat}
    (pre mid post : List (Fin n)) (a b : Fin n)
    (hnodup : (pre ++ a :: mid ++ b :: post).Nodup) :
    inversionCount (pre ++ b :: mid ++ a :: post) % 2 =
      (inversionCount (pre ++ a :: mid ++ b :: post) + 1) % 2 := by
  induction mid generalizing pre with
  | nil =>
      have hne : b ≠ a := by
        intro hba
        subst b
        have hsplit : ((pre ++ [a]) ++ a :: post).Nodup := by
          simpa [List.append_assoc] using hnodup
        exact ((List.nodup_append (l₁ := pre ++ [a]) (l₂ := a :: post)).mp hsplit).2.2
          a (by simp) a (by simp) rfl
      simpa [Nat.add_comm] using
        (inversionCount_adjacent_swap_parity pre post b a hne)
  | cons x xs ih =>
      have hswap₁ :
          inversionCount (pre ++ b :: x :: xs ++ a :: post) % 2 =
            (inversionCount (pre ++ x :: b :: xs ++ a :: post) + 1) % 2 := by
        simpa [List.append_assoc] using
          inversionCount_adjacent_swap_parity pre (xs ++ a :: post) b x (by
            intro hbx
            subst b
            have hsplit : ((pre ++ a :: x :: xs) ++ x :: post).Nodup := by
              simpa [List.append_assoc] using hnodup
            exact ((List.nodup_append (l₁ := pre ++ a :: x :: xs) (l₂ := x :: post)).mp hsplit).2.2
              x (by simp) x (by simp) rfl)
      have hnodup_tail : ((pre ++ [x]) ++ a :: xs ++ b :: post).Nodup := by
        have hp :
            ((pre ++ [x]) ++ a :: xs ++ b :: post).Perm
              (pre ++ a :: x :: xs ++ b :: post) := by
          simpa [List.append_assoc] using
            List.Perm.append_left pre (List.Perm.swap a x (xs ++ b :: post))
        exact hp.nodup_iff.mpr hnodup
      have hmid :
          inversionCount (pre ++ x :: b :: xs ++ a :: post) % 2 =
            (inversionCount (pre ++ x :: a :: xs ++ b :: post) + 1) % 2 := by
        simpa only [List.cons_append, List.append_assoc] using
          (ih (pre ++ [x]) hnodup_tail)
      have hswap₂ :
          inversionCount (pre ++ x :: a :: xs ++ b :: post) % 2 =
            (inversionCount (pre ++ a :: x :: xs ++ b :: post) + 1) % 2 := by
        simpa [List.append_assoc] using
          inversionCount_adjacent_swap_parity pre (xs ++ b :: post) x a (by
            intro hxa
            subst x
            have hsplit : (pre ++ [a] ++ (a :: xs ++ b :: post)).Nodup := by
              simpa [List.append_assoc] using hnodup
            exact ((List.nodup_append (l₁ := pre ++ [a]) (l₂ := a :: xs ++ b :: post)).mp hsplit).2.2
              a (by simp) a (by simp) rfl)
      omega

/-- The sign of a permutation vector, computed from inversion parity. -/
def detSign {R : Type u} [Lean.Grind.Ring R] {n : Nat} (perm : Vector (Fin n) n) : R :=
  if inversionCount perm.toList % 2 = 0 then 1 else -1

/-- The unsigned product associated to a permutation vector. -/
def detProduct {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) : R :=
  (List.finRange n).foldl (fun acc i => acc * M[i][perm[i]]) 1

/-- The Leibniz summand associated to a permutation vector. -/
def detTerm {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) : R :=
  detSign perm * detProduct M perm

/-- The determinant of a dense square matrix, defined by the Leibniz formula. -/
def det {R : Type u} [Lean.Grind.Ring R] {n : Nat} (M : Matrix R n n) : R :=
  (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0

/-- Embed `Fin n` into `Fin (n + 1)` while skipping one deleted index. -/
def skipIndex {n : Nat} (skip : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if h : i.val < skip.val then
    ⟨i.val, by omega⟩
  else
    ⟨i.val + 1, by omega⟩

/-- The skipped-index embedding leaves entries below the deleted index unchanged.
This is the low-side `simp` branch for row and column deletion. -/
@[simp, grind =] theorem skipIndex_val_of_lt {n : Nat} (skip : Fin (n + 1)) (i : Fin n)
    (h : i.val < skip.val) :
    (skipIndex skip i).val = i.val := by
  simp [skipIndex, h]

/-- The skipped-index embedding shifts entries at or above the deleted index by
one. This is the high-side `simp` branch for row and column deletion. -/
@[simp, grind =] theorem skipIndex_val_of_not_lt {n : Nat} (skip : Fin (n + 1)) (i : Fin n)
    (h : ¬ i.val < skip.val) :
    (skipIndex skip i).val = i.val + 1 := by
  simp [skipIndex, h]

/-- The index produced by `skipIndex skip` is never the deleted index `skip`.
This is the basic side condition for minors that remove a row or column. -/
theorem skipIndex_ne {n : Nat} (skip : Fin (n + 1)) (i : Fin n) :
    skipIndex skip i ≠ skip := by
  intro hsame
  have hval : (skipIndex skip i).val = skip.val := congrArg Fin.val hsame
  by_cases hlt : i.val < skip.val
  · rw [skipIndex_val_of_lt skip i hlt] at hval
    omega
  · rw [skipIndex_val_of_not_lt skip i hlt] at hval
    omega

/-- The deleted-index embedding `skipIndex skip` is injective. -/
private theorem skipIndex_injective {n : Nat} (skip : Fin (n + 1)) :
    Function.Injective (skipIndex skip) := by
  intro i j h
  apply Fin.ext
  have hval : (skipIndex skip i).val = (skipIndex skip j).val := congrArg Fin.val h
  by_cases hi : i.val < skip.val
  · rw [skipIndex_val_of_lt skip i hi] at hval
    by_cases hj : j.val < skip.val
    · rw [skipIndex_val_of_lt skip j hj] at hval
      exact hval
    · rw [skipIndex_val_of_not_lt skip j hj] at hval
      omega
  · rw [skipIndex_val_of_not_lt skip i hi] at hval
    by_cases hj : j.val < skip.val
    · rw [skipIndex_val_of_lt skip j hj] at hval
      omega
    · rw [skipIndex_val_of_not_lt skip j hj] at hval
      omega

/-- Skipping the final index embeds `Fin n` by `castSucc`.
This normalizes bottom-right minors to leading prefixes. -/
@[simp, grind =] theorem skipIndex_last {n : Nat} (i : Fin n) :
    skipIndex (Fin.last n) i = i.castSucc := by
  apply Fin.ext
  simp [skipIndex, Fin.last, i.isLt]

/-- Delete one row and one column from an `(n + 1) × (n + 1)` matrix. -/
def deleteRowCol {R : Type u} {n : Nat} (M : Matrix R (n + 1) (n + 1))
    (row col : Fin (n + 1)) : Matrix R n n :=
  ofFn fun i j => M[skipIndex row i][skipIndex col j]

/-- Entries of a deleted-row/deleted-column minor are the corresponding source
entries at the skipped row and column indices. -/
@[grind =] theorem deleteRowCol_entry {R : Type u} {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row col : Fin (n + 1)) (i j : Fin n) :
    (deleteRowCol M row col)[i][j] = M[skipIndex row i][skipIndex col j] := by
  simp [deleteRowCol, ofFn]

/-- Deleting the final row and final column gives the leading prefix.
This is the minor normalization used by bottom-right cofactor expansion. -/
@[simp, grind =] theorem deleteRowCol_last_last {R : Type u} {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) :
    deleteRowCol M (Fin.last n) (Fin.last n) =
      leadingPrefix M n (Nat.le_succ n) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin n := ⟨j, hj⟩
  change (deleteRowCol M (Fin.last n) (Fin.last n))[ii][jj] =
    (leadingPrefix M n (Nat.le_succ n))[ii][jj]
  rw [deleteRowCol_entry]
  simp [leadingPrefix, ofFn]

/-- Deleting row `row` and column `col` after transposing is the transpose of
the minor obtained by deleting row `col` and column `row` before transposing. -/
theorem deleteRowCol_transpose {R : Type u} {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row col : Fin (n + 1)) :
    deleteRowCol M.transpose row col = (deleteRowCol M col row).transpose := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin n := ⟨j, hj⟩
  change (deleteRowCol M.transpose row col)[ii][jj] =
    (deleteRowCol M col row).transpose[ii][jj]
  simp [deleteRowCol, ofFn, Matrix.transpose, Matrix.col]

/-- The alternating sign used in signed cofactors. -/
def cofactorSign {R : Type u} [OfNat R 1] [Neg R] {n : Nat}
    (row col : Fin (n + 1)) : R :=
  if (row.val + col.val) % 2 = 0 then 1 else -1

/-- An even row-plus-column parity gives cofactor sign `1`.
This is the positive `simp` branch for signed cofactors. -/
@[simp, grind =] theorem cofactorSign_of_even {R : Type u} [OfNat R 1] [Neg R] {n : Nat}
    (row col : Fin (n + 1)) (h : (row.val + col.val) % 2 = 0) :
    cofactorSign (R := R) row col = 1 := by
  simp [cofactorSign, h]

/-- An odd row-plus-column parity gives cofactor sign `-1`.
This is the negative `simp` branch for signed cofactors. -/
@[simp, grind =] theorem cofactorSign_of_odd {R : Type u} [OfNat R 1] [Neg R] {n : Nat}
    (row col : Fin (n + 1)) (h : (row.val + col.val) % 2 ≠ 0) :
    cofactorSign (R := R) row col = -1 := by
  simp [cofactorSign, h]

/-- The signed cofactor for the local Leibniz determinant. -/
def cofactor {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row col : Fin (n + 1)) : R :=
  cofactorSign row col * det (deleteRowCol M row col)

/-- At even parity, a signed cofactor is just the determinant of its minor.
This removes the sign in cofactor-expansion normalization. -/
@[simp, grind =] theorem cofactor_of_even {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row col : Fin (n + 1))
    (h : (row.val + col.val) % 2 = 0) :
    cofactor M row col = det (deleteRowCol M row col) := by
  simp [cofactor, h]
  grind

/-- At odd parity, a signed cofactor is the negated determinant of its minor.
This supplies the alternating sign in cofactor-expansion normalization. -/
@[simp, grind =] theorem cofactor_of_odd {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row col : Fin (n + 1))
    (h : (row.val + col.val) % 2 ≠ 0) :
    cofactor M row col = -det (deleteRowCol M row col) := by
  simp [cofactor, h]
  grind

/-- The bottom-right cofactor reduces to the determinant of the leading prefix.
This combines the final-index minor with its even sign. -/
@[simp, grind =] theorem cofactor_last_last {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) :
    cofactor M (Fin.last n) (Fin.last n) =
      det (leadingPrefix M n (Nat.le_succ n)) := by
  rw [cofactor_of_even]
  · simp
  · omega

/-- The determinant of the empty leading prefix is the Bareiss previous-pivot
convention `1`. -/
@[simp, grind =] theorem det_leadingPrefix_zero {R : Type u} [Lean.Grind.Ring R]
    (M : Matrix R n n) :
    det (leadingPrefix M 0 (Nat.zero_le n)) = (1 : R) := by
  simp [det, detTerm, detSign, detProduct, permutationVectors, emptyVec, inversionCount]
  grind

/-- The determinant of a `1 × 1` matrix is its only entry.
This is the smallest non-empty determinant base case. -/
@[simp, grind =] theorem det_one_by_one {R : Type u} [Lean.Grind.Ring R]
    (M : Matrix R 1 1) :
    det M = M[0][0] := by
  simp [det, detTerm, detSign, detProduct, permutationVectors, emptyVec, insertAt,
    inversionCount, List.finRange]
  grind

/-- The determinant of a `2 × 2` matrix has the usual diagonal-minus-off-diagonal
closed form used by small cofactor expansions. -/
@[simp, grind =] theorem det_two_by_two {R : Type u} [Lean.Grind.CommRing R]
    (M : Matrix R 2 2) :
    det M = M[0][0] * M[1][1] - M[1][0] * M[0][1] := by
  simp [det, detTerm, detSign, detProduct, permutationVectors, emptyVec, insertAt,
    inversionCount, List.finRange]
  grind

/-- Congruence for the determinant-style left fold over a finite list. -/
private theorem foldl_det_sum_congr {R : Type u} [Add R] {β : Type v}
    (xs : List β) (f g : β → R) (z : R)
    (h : ∀ x, x ∈ xs → f x = g x) :
    xs.foldl (fun acc x => acc + f x) z =
      xs.foldl (fun acc x => acc + g x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h x (by simp)]
      apply ih
      intro y hy
      exact h y (List.mem_cons_of_mem x hy)

/-- Two left folds agree when their step functions agree on every list
element. -/
private theorem foldl_acc_congr {α : Type u} {β : Type v}
    (xs : List β) (f g : α → β → α) (z : α)
    (h : ∀ acc x, x ∈ xs → f acc x = g acc x) :
    xs.foldl f z = xs.foldl g z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h z x (by simp)]
      exact ih (g z x) (fun acc y hy => h acc y (List.mem_cons_of_mem x hy))

/-- A summing left fold is invariant under permuting the list. -/
private theorem foldl_det_sum_perm {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (f : β → R) {xs ys : List β} (hperm : xs.Perm ys) (z : R) :
    xs.foldl (fun acc x => acc + f x) z =
      ys.foldl (fun acc x => acc + f x) z := by
  induction hperm generalizing z with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.foldl_cons]
      exact ih (z + _)
  | swap x y xs =>
      simp only [List.foldl_cons]
      congr 1
      grind
  | trans _ _ ih₁ ih₂ =>
      exact (ih₁ z).trans (ih₂ z)

/-- A product left fold is unchanged when its factor function is replaced by one
agreeing on every list element. -/
private theorem foldl_det_product_congr {R : Type u} [Mul R] {β : Type v}
    (xs : List β) (f g : β → R) (z : R)
    (h : ∀ x, x ∈ xs → f x = g x) :
    xs.foldl (fun acc x => acc * f x) z =
      xs.foldl (fun acc x => acc * g x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h x (by simp)]
      apply ih
      intro y hy
      exact h y (List.mem_cons_of_mem x hy)

/-- A product left fold is invariant under permuting the list. -/
private theorem foldl_det_product_perm {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (f : β → R) {xs ys : List β} (hperm : xs.Perm ys) (z : R) :
    xs.foldl (fun acc x => acc * f x) z =
      ys.foldl (fun acc x => acc * f x) z := by
  induction hperm generalizing z with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.foldl_cons]
      exact ih (z * _)
  | swap x y xs =>
      simp only [List.foldl_cons]
      congr 1
      grind
  | trans _ _ ih₁ ih₂ =>
      exact (ih₁ z).trans (ih₂ z)

/-- Mapping a duplicate-free list by an injective function preserves
duplicate-freeness. -/
private theorem list_nodup_map_of_injective {α : Type u} {β : Type v}
    [DecidableEq β] {f : α → β} (hinj : Function.Injective f) :
    ∀ {xs : List α}, xs.Nodup → (xs.map f).Nodup
  | [], _ => by simp
  | x :: xs, hnodup => by
      simp only [List.map_cons, List.nodup_cons] at hnodup ⊢
      constructor
      · intro hmem
        simp only [List.mem_map] at hmem
        rcases hmem with ⟨y, hy, hfy⟩
        exact hnodup.1 (hinj hfy.symm ▸ hy)
      · exact list_nodup_map_of_injective hinj hnodup.2

/-- Mapping a duplicate-free list preserves duplicate-freeness when the function
is injective on that list's elements. -/
private theorem list_nodup_map_on {α : Type u} {β : Type v}
    [DecidableEq β] {f : α → β} :
    ∀ {xs : List α}, xs.Nodup →
      (∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b) →
      (xs.map f).Nodup
  | [], _hnodup, _hinj => by simp
  | x :: xs, hnodup, hinj => by
      simp only [List.nodup_cons] at hnodup
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨y, hy, hfy⟩
        have hxy := hinj x (by simp) y (List.mem_cons_of_mem x hy) hfy.symm
        subst y
        exact hnodup.1 hy
      · exact list_nodup_map_on hnodup.2 (by
          intro a ha b hb hab
          exact hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb) hab)

/-- Factor a scalar out of a determinant-style finite left fold. -/
private theorem foldl_det_sum_mul_left {R : Type u} [Lean.Grind.CommRing R] {β : Type v}
    (xs : List β) (c : R) (f : β → R) (z : R) :
    xs.foldl (fun acc x => acc + c * f x) (c * z) =
      c * xs.foldl (fun acc x => acc + f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [← show c * (z + f x) = c * z + c * f x by grind]
      exact ih (z + f x)

/-- Factor a scalar out of a determinant-style finite left fold from zero. -/
private theorem foldl_det_sum_mul_left_zero {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (c : R) (f : β → R) :
    xs.foldl (fun acc x => acc + c * f x) 0 =
      c * xs.foldl (fun acc x => acc + f x) 0 := by
  have hzero : c * 0 = 0 := by grind
  simpa [hzero] using (foldl_det_sum_mul_left (R := R) xs c f 0)

/-- Factor a right multiplier out of a summing left fold started from zero. -/
private theorem foldl_det_sum_mul_right_zero {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (f : β → R) (c : R) :
    xs.foldl (fun acc x => acc + f x * c) 0 =
      xs.foldl (fun acc x => acc + f x) 0 * c := by
  calc
    xs.foldl (fun acc x => acc + f x * c) 0 =
        xs.foldl (fun acc x => acc + c * f x) 0 := by
          apply foldl_det_sum_congr
          intro x _hmem
          grind
    _ = c * xs.foldl (fun acc x => acc + f x) 0 := by
          exact foldl_det_sum_mul_left_zero xs c f
    _ = xs.foldl (fun acc x => acc + f x) 0 * c := by
          grind

/-- A summing left fold of a sum of two functions splits into the two folds,
distributing the starting accumulator. -/
private theorem foldl_det_sum_add_start {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (f g : β → R) (a b : R) :
    xs.foldl (fun acc x => acc + (f x + g x)) (a + b) =
      xs.foldl (fun acc x => acc + f x) a +
        xs.foldl (fun acc x => acc + g x) b := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      calc
        xs.foldl (fun acc x => acc + (f x + g x)) (a + b + (f x + g x)) =
          xs.foldl (fun acc x => acc + (f x + g x)) ((a + f x) + (b + g x)) := by
            congr 1
            grind
        _ =
          xs.foldl (fun acc x => acc + f x) (a + f x) +
            xs.foldl (fun acc x => acc + g x) (b + g x) := by
            exact ih (a + f x) (b + g x)

/-- A summing left fold of the pointwise sum `f x + g x` from `0` splits into the
sum of the separate folds of `f` and of `g`, each from `0`. -/
private theorem foldl_det_sum_add_zero {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (f g : β → R) :
    xs.foldl (fun acc x => acc + (f x + g x)) 0 =
      xs.foldl (fun acc x => acc + f x) 0 +
        xs.foldl (fun acc x => acc + g x) 0 := by
  calc
    xs.foldl (fun acc x => acc + (f x + g x)) 0 =
      xs.foldl (fun acc x => acc + (f x + g x)) ((0 : R) + 0) := by
        congr 1
        grind
    _ =
      xs.foldl (fun acc x => acc + f x) 0 +
        xs.foldl (fun acc x => acc + g x) 0 := by
        exact foldl_det_sum_add_start xs f g 0 0

/-- A summing left fold from a starting accumulator `z` equals `z` plus the same
fold from `0`. -/
private theorem foldl_det_sum_start {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (f : β → R) (z : R) :
    xs.foldl (fun acc x => acc + f x) z =
      z + xs.foldl (fun acc x => acc + f x) 0 := by
  induction xs generalizing z with
  | nil =>
      have hzero : z + (0 : R) = z := by grind
      exact hzero.symm
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (z + f x), ih (0 + f x)]
      grind

/-- A summing left fold over `xs.flatMap f` equals the fold over `xs` whose body
folds each sublist `f x` into the accumulator. -/
private theorem foldl_det_sum_flatMap {R : Type u} [Add R] {β γ : Type v}
    (xs : List β) (f : β → List γ) (g : γ → R) (z : R) :
    (xs.flatMap f).foldl (fun acc x => acc + g x) z =
      xs.foldl (fun acc x => (f x).foldl (fun acc y => acc + g y) acc) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons]
      exact ih ((f x).foldl (fun acc y => acc + g y) z)

/-- A summing left fold whose body adds `0` returns the starting accumulator `z`
unchanged. -/
private theorem foldl_det_sum_zero {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (z : R) :
    xs.foldl (fun acc _ => acc + 0) z = z := by
  induction xs generalizing z with
  | nil => rfl
  | cons _ xs ih =>
      simp only [List.foldl_cons]
      have hzero : z + (0 : R) = z := by grind
      simpa [hzero] using ih z

/-- If `a - b + c = 0` and `f x - g x + h x = 0` for every `x ∈ xs`, then the same
combination of the three summing folds from `a`, `b`, `c` is `0`. -/
private theorem foldl_det_sum_sub_add_zero_of_body_zero
    {R : Type u} [Lean.Grind.CommRing R] {β : Type v}
    (xs : List β) (f g h : β → R) (a b c : R)
    (hacc : a - b + c = 0)
    (hall : ∀ x, x ∈ xs → f x - g x + h x = 0) :
    xs.foldl (fun acc x => acc + f x) a -
      xs.foldl (fun acc x => acc + g x) b +
      xs.foldl (fun acc x => acc + h x) c = 0 := by
  induction xs generalizing a b c with
  | nil => exact hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · have hx : f x - g x + h x = 0 := hall x List.mem_cons_self
        grind
      · intro y hy
        exact hall y (List.mem_cons_of_mem x hy)

/-- A multiplying left fold from `c * z` equals `c` times the same fold from `z`,
factoring the scalar out to the left. -/
private theorem foldl_det_product_mul_left {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (c : R) (f : β → R) (z : R) :
    xs.foldl (fun acc x => acc * f x) (c * z) =
      c * xs.foldl (fun acc x => acc * f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [← show c * (z * f x) = (c * z) * f x by grind]
      exact ih (z * f x)

/-- When `i ∉ xs`, scaling the factor at index `i` by `c` leaves the multiplying
fold unchanged, since no element of `xs` equals `i`. -/
private theorem foldl_det_product_no_scale_of_not_mem {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (c : R) (f : β → R) (z : R) (hnot : i ∉ xs) :
    xs.foldl (fun acc x => acc * if x = i then c * f x else f x) z =
      xs.foldl (fun acc x => acc * f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mem_cons, not_or] at hnot
      simp only [List.foldl_cons]
      have hx : x ≠ i := by
        intro hxi
        exact hnot.1 hxi.symm
      rw [if_neg hx]
      exact ih (z * f x) hnot.2

/-- For a `Nodup` list `xs` containing `i`, scaling only the factor at `i` by `c`
multiplies the entire multiplying fold by `c`. -/
private theorem foldl_det_product_single_scale {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (c : R) (f : β → R) (z : R)
    (hmem : i ∈ xs) (hnodup : xs.Nodup) :
    xs.foldl (fun acc x => acc * if x = i then c * f x else f x) z =
      c * xs.foldl (fun acc x => acc * f x) z := by
  induction xs generalizing z with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.nodup_cons] at hnodup
      simp only [List.foldl_cons]
      by_cases hx : x = i
      · subst x
        rw [if_pos rfl]
        calc
          xs.foldl (fun acc x => acc * if x = i then c * f x else f x) (z * (c * f i)) =
              xs.foldl (fun acc x => acc * f x) (z * (c * f i)) := by
                exact foldl_det_product_no_scale_of_not_mem xs i c f (z * (c * f i)) hnodup.1
          _ = xs.foldl (fun acc x => acc * f x) (c * (z * f i)) := by
                congr 1
                grind
          _ = c * xs.foldl (fun acc x => acc * f x) (z * f i) := by
                exact foldl_det_product_mul_left xs c f (z * f i)
      · rw [if_neg hx]
        have hmemTail : i ∈ xs := by
          cases hmem with
          | inl hxi => exact False.elim (hx hxi.symm)
          | inr htail => exact htail
        exact ih (z * f x) hmemTail hnodup.2

/-- A multiplying left fold from a sum `a + b` of starting accumulators equals the
sum of the folds from `a` and from `b`. -/
private theorem foldl_det_product_add_start {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (f : β → R) (a b : R) :
    xs.foldl (fun acc x => acc * f x) (a + b) =
      xs.foldl (fun acc x => acc * f x) a +
        xs.foldl (fun acc x => acc * f x) b := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      calc
        xs.foldl (fun acc x => acc * f x) ((a + b) * f x) =
          xs.foldl (fun acc x => acc * f x) (a * f x + b * f x) := by
            congr 1
            grind
        _ =
          xs.foldl (fun acc x => acc * f x) (a * f x) +
            xs.foldl (fun acc x => acc * f x) (b * f x) := by
            exact ih (a * f x) (b * f x)

/-- For a `Nodup` list containing `i` with `g` agreeing with `f` away from `i`,
replacing the factor at `i` by `f i + c * g i` splits the fold into the `f`-product
plus `c` times the `g`-product. -/
private theorem foldl_det_product_single_add {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (c : R) (f g : β → R) (z : R)
    (hmem : i ∈ xs) (hnodup : xs.Nodup)
    (hagree : ∀ x, x ∈ xs → x ≠ i → g x = f x) :
    xs.foldl (fun acc x => acc * if x = i then f x + c * g x else f x) z =
      xs.foldl (fun acc x => acc * f x) z +
        c * xs.foldl (fun acc x => acc * g x) z := by
  induction xs generalizing z with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.nodup_cons] at hnodup
      simp only [List.foldl_cons]
      by_cases hx : x = i
      · subst x
        rw [if_pos rfl]
        have hnot : i ∉ xs := hnodup.1
        calc
          xs.foldl (fun acc x => acc * if x = i then f x + c * g x else f x)
              (z * (f i + c * g i)) =
            xs.foldl (fun acc x => acc * f x) (z * (f i + c * g i)) := by
              apply foldl_det_product_congr
              intro y hy
              have hyi : y ≠ i := by
                intro h
                exact hnot (h ▸ hy)
              rw [if_neg hyi]
          _ = xs.foldl (fun acc x => acc * f x) (z * f i + c * (z * g i)) := by
              congr 1
              grind
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f i) +
              xs.foldl (fun acc x => acc * f x) (c * (z * g i)) := by
              exact foldl_det_product_add_start xs f (z * f i) (c * (z * g i))
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f i) +
              c * xs.foldl (fun acc x => acc * f x) (z * g i) := by
              rw [show
                xs.foldl (fun acc x => acc * f x) (c * (z * g i)) =
                  c * xs.foldl (fun acc x => acc * f x) (z * g i) from
                    foldl_det_product_mul_left xs c f (z * g i)]
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f i) +
              c * xs.foldl (fun acc x => acc * g x) (z * g i) := by
              congr 2
              apply foldl_det_product_congr
              intro y hy
              exact (hagree y (List.mem_cons.mpr (Or.inr hy)) (by
                intro h
                exact hnot (h ▸ hy))).symm
      · rw [if_neg hx]
        have hmemTail : i ∈ xs := by
          cases hmem with
          | inl hxi => exact False.elim (hx hxi.symm)
          | inr htail => exact htail
        have hgx : g x = f x := hagree x (List.mem_cons.mpr (Or.inl rfl)) hx
        calc
          xs.foldl (fun acc x => acc * if x = i then f x + c * g x else f x)
              (z * f x) =
            xs.foldl (fun acc x => acc * f x) (z * f x) +
              c * xs.foldl (fun acc x => acc * g x) (z * f x) := by
              exact ih (z * f x) hmemTail hnodup.2
                (fun y hy hyi => hagree y (List.mem_cons.mpr (Or.inr hy)) hyi)
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f x) +
              c * xs.foldl (fun acc x => acc * g x) (z * g x) := by
              rw [hgx]

/-- A multiplying left fold from starting accumulator `0` is `0`. -/
private theorem foldl_det_product_zero_start {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} (xs : List β) (f : β → R) :
    xs.foldl (fun acc x => acc * f x) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hzero : (0 : R) * f x = 0 := by grind
      simpa [hzero] using ih

/-- A multiplying left fold is `0` whenever some factor vanishes, that is `i ∈ xs`
and `f i = 0`. -/
private theorem foldl_det_product_zero_of_mem {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (f : β → R) (z : R)
    (hmem : i ∈ xs) (hzero : f i = 0) :
    xs.foldl (fun acc x => acc * f x) z = 0 := by
  induction xs generalizing z with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldl_cons]
      by_cases hx : x = i
      · subst x
        rw [hzero]
        have hz : z * (0 : R) = 0 := by grind
        simpa [hz] using foldl_det_product_zero_start xs f
      · have htail : i ∈ xs := by
          cases hmem with
          | inl hxi => exact False.elim (hx hxi.symm)
          | inr htail => exact htail
        exact ih (z * f x) htail

/-- Entry `(i, j)` of the identity matrix `(1 : Matrix R n n)` is `1` when `i = j`
and `0` otherwise. -/
private theorem identity_get {R : Type u} [OfNat R 0] [OfNat R 1] {n : Nat}
    (i j : Fin n) :
    (1 : Matrix R n n)[i][j] = if i = j then 1 else 0 := by
  change Matrix.identity[i][j] = if i = j then 1 else 0
  simp [Matrix.identity, Matrix.ofFn]

/-- `detProduct` of the identity matrix along `perm` is `0` whenever `perm` moves
some index, that is `perm[i] ≠ i`. -/
private theorem detProduct_identity_zero_of_mismatch {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (perm : Vector (Fin n) n)
    (i : Fin n) (h : perm[i] ≠ i) :
    detProduct (1 : Matrix R n n) perm = 0 := by
  unfold detProduct
  have hsymm : i ≠ perm[i] := by
    intro hi
    exact h hi.symm
  exact foldl_det_product_zero_of_mem
    (List.finRange n) i (fun r => (1 : Matrix R n n)[r][perm[r]]) 1
    (List.mem_finRange i) (by
      change (1 : Matrix R n n)[i][perm[i]] = 0
      rw [identity_get]
      rw [if_neg hsymm])

/-- Reading `insertAt x v i` at the insertion position `i` returns the inserted
element `x`. -/
private theorem insertAt_get_self {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin (n + 1)) :
    (insertAt x v i)[i] = x := by
  unfold insertAt
  simp [List.getElem_insertIdx_self]

/-- After inserting `x` at `Fin.last n`, reading the result at `i.castSucc` returns
the original entry `v[i]`. -/
private theorem insertAt_last_get_castSucc {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin n) :
    (insertAt x v (Fin.last n))[i.castSucc] = v[i] := by
  unfold insertAt
  simp [List.getElem_insertIdx_of_lt]

/-- For `i ≤ r < xs.length`, element `r + 1` of `xs.insertIdx i x` is the original
`xs[r]`, since the insertion shifts later entries up by one. -/
private theorem list_getElem_insertIdx_succ_of_le {α : Type u}
    (xs : List α) (x : α) {i r : Nat} (h : i ≤ r) (hr : r < xs.length) :
    (xs.insertIdx i x)[r + 1]'(by
      have hi : i ≤ xs.length := Nat.le_trans h (Nat.le_of_lt hr)
      rw [List.length_insertIdx_of_le_length hi]
      omega) = xs[r] := by
  induction xs generalizing i r with
  | nil =>
      cases hr
  | cons y ys ih =>
      cases i with
      | zero =>
          cases r with
          | zero =>
              simp
          | succ r =>
              simp
      | succ i =>
          cases r with
          | zero =>
              omega
          | succ r =>
              simp only [List.insertIdx, List.getElem_cons_succ]
              exact ih (Nat.succ_le_succ_iff.mp h) (Nat.succ_lt_succ_iff.mp hr)

/-- `detProduct` of the identity matrix along `insertAt (Fin.last n) (v.map
Fin.castSucc) i` is `0` when `i ≠ Fin.last n`, since the inserted index is then
moved. -/
private theorem detProduct_identity_insertAt_not_last_zero {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n)
    (i : Fin (n + 1)) (h : i ≠ Fin.last n) :
    detProduct (1 : Matrix R (n + 1) (n + 1))
      (insertAt (Fin.last n) (v.map Fin.castSucc) i) = 0 := by
  apply detProduct_identity_zero_of_mismatch
  exact by
    rw [insertAt_get_self]
    exact h.symm

/-- Inserting `Fin.last n` at the last position equates `detProduct` of the
`(n + 1)`-identity along the extended permutation with `detProduct` of the
`n`-identity along `v`. -/
private theorem detProduct_identity_insertAt_last {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n) :
    detProduct (1 : Matrix R (n + 1) (n + 1))
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
    detProduct (1 : Matrix R n n) v := by
  unfold detProduct
  rw [← Fin.foldl_eq_foldl_finRange, ← Fin.foldl_eq_foldl_finRange]
  rw [Fin.foldl_succ_last]
  have hfold :
      Fin.foldl n
          (fun acc i =>
            acc *
              (1 : Matrix R (n + 1) (n + 1))[i.castSucc][
                (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc]]) 1 =
      Fin.foldl n (fun acc i => acc * (1 : Matrix R n n)[i][v[i]]) 1 := by
    congr
    funext acc i
    rw [identity_get, identity_get]
    have hget :
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc] =
          (v[i]).castSucc := by
      simpa using insertAt_last_get_castSucc (Fin.last n) (v.map Fin.castSucc) i
    rw [hget]
    simp [Fin.ext_iff]
  have hlast :
      (1 : Matrix R (n + 1) (n + 1))[Fin.last n][
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[Fin.last n]] = 1 := by
    rw [identity_get]
    have hself :
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[Fin.last n] =
          Fin.last n := by
      exact insertAt_get_self (Fin.last n) (v.map Fin.castSucc) (Fin.last n)
    simp [hself]
  rw [hfold, hlast]
  have hmul_one : ∀ x : R, x * (1 : R) = x := by
    intro x
    exact Lean.Grind.Semiring.mul_one x
  exact hmul_one _

/-- Folding the inversion count against a pivot is unchanged when both the list
`xs` and the pivot `x` are mapped through `Fin.castSucc`. -/
private theorem inversionFold_map_castSucc {n : Nat} (xs : List (Fin n)) (x : Fin n)
    (acc : Nat) :
    (xs.map Fin.castSucc).foldl
        (fun acc y => acc + if y < x.castSucc then 1 else 0) acc =
    xs.foldl (fun acc y => acc + if y < x then 1 else 0) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hhead :
          (if y.castSucc < x.castSucc then 1 else 0) =
            (if y < x then 1 else 0) := by
        simp [Fin.lt_def]
      rw [hhead]
      exact ih _

/-- `inversionCount` is invariant under mapping the permutation list through
`Fin.castSucc`. -/
private theorem inversionCount_map_castSucc {n : Nat} (xs : List (Fin n)) :
    inversionCount (xs.map Fin.castSucc) = inversionCount xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [inversionCount, ih, inversionFold_map_castSucc]

/-- Appending `Fin.last n` after the `castSucc`-embedded list adds no inversions,
so the count equals `inversionCount xs`. -/
private theorem inversionCount_insert_last_castSucc {n : Nat} (xs : List (Fin n)) :
    inversionCount ((xs.map Fin.castSucc) ++ [Fin.last n]) = inversionCount xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.cons_append, inversionCount]
      rw [ih]
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [inversionFold_map_castSucc]
      simp [Fin.lt_def]

/-- Inserting `Fin.last n` at any position into the `castSucc`-embedded list leaves
the inversion fold against `x.castSucc` unchanged, since the new last element is
never below `x.castSucc`. -/
private theorem foldl_insertIdx_last_castSucc_not_lt {n : Nat} (xs : List (Fin n))
    (x : Fin n) (p acc : Nat) :
    ((xs.map Fin.castSucc).insertIdx p (Fin.last n)).foldl
        (fun acc y => acc + if y < x.castSucc then 1 else 0) acc =
      (xs.map Fin.castSucc).foldl
        (fun acc y => acc + if y < x.castSucc then 1 else 0) acc := by
  induction xs generalizing p acc with
  | nil =>
      cases p <;> simp [List.insertIdx, Fin.lt_def]
  | cons y ys ih =>
      cases p with
      | zero =>
          have hnlt : ¬ n < x.val := by omega
          simp [List.insertIdx, Fin.lt_def, hnlt]
      | succ p =>
          simp only [List.map_cons]
          rw [List.insertIdx, List.modifyTailIdx_succ_cons]
          simp only [List.foldl_cons]
          change
            ((ys.map Fin.castSucc).insertIdx p (Fin.last n)).foldl
                (fun acc y => acc + if y < x.castSucc then 1 else 0)
                (acc + if y.castSucc < x.castSucc then 1 else 0) =
              (ys.map Fin.castSucc).foldl
                (fun acc y => acc + if y < x.castSucc then 1 else 0)
                (acc + if y.castSucc < x.castSucc then 1 else 0)
          rw [ih p (acc + if y.castSucc < x.castSucc then 1 else 0)]

/-- Every `castSucc`-embedded element is below `Fin.last n`, so folding the
`< Fin.last n` count over the embedded list adds exactly its length. -/
private theorem foldl_all_lt_last_castSucc {n : Nat} (xs : List (Fin n)) (acc : Nat) :
    (xs.map Fin.castSucc).foldl
        (fun acc y => acc + if y < Fin.last n then 1 else 0) acc =
      acc + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons, List.length_cons]
      rw [ih (acc + if x.castSucc < Fin.last n then 1 else 0)]
      simp [Fin.lt_def]
      omega

/-- Inserting `Fin.last n` at position `p ≤ xs.length` into the `castSucc`-embedded
list raises the inversion count by the `xs.length - p` elements it jumps over. -/
private theorem inversionCount_insertIdx_castSucc_last_eq {n : Nat}
    (xs : List (Fin n)) (p : Nat) (hp : p ≤ xs.length) :
    inversionCount ((xs.map Fin.castSucc).insertIdx p (Fin.last n)) =
      inversionCount xs + (xs.length - p) := by
  induction xs generalizing p with
  | nil =>
      cases p with
      | zero => rfl
      | succ p => cases hp
  | cons x xs ih =>
      cases p with
      | zero =>
          simp only [List.map_cons]
          rw [List.insertIdx, List.modifyTailIdx_zero]
          simp only [inversionCount, List.foldl_cons]
          rw [foldl_all_lt_last_castSucc xs
            (0 + if x.castSucc < Fin.last n then 1 else 0)]
          rw [inversionFold_map_castSucc]
          rw [inversionCount_map_castSucc]
          simp [Fin.lt_def]
          omega
      | succ p =>
          have hp' : p ≤ xs.length := Nat.succ_le_succ_iff.mp hp
          have hlen : (x :: xs).length - (p + 1) = xs.length - p := by
            simp
          simp only [List.map_cons]
          rw [List.insertIdx, List.modifyTailIdx_succ_cons]
          simp only [inversionCount]
          change
            ((xs.map Fin.castSucc).insertIdx p (Fin.last n)).foldl
                (fun acc y => acc + if y < x.castSucc then 1 else 0) 0 +
                inversionCount ((xs.map Fin.castSucc).insertIdx p (Fin.last n)) =
              xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 +
                inversionCount xs + ((x :: xs).length - (p + 1))
          rw [foldl_insertIdx_last_castSucc_not_lt xs x p]
          rw [inversionFold_map_castSucc]
          rw [ih p hp']
          rw [hlen]
          grind

/-- Inserting an element at index `xs.length` is the same as appending it. -/
private theorem list_insertIdx_length {α : Type u} (xs : List α) (x : α) :
    xs.insertIdx xs.length x = xs ++ [x] := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      simp [ih]

/-- `Vector.map` commutes with `Vector.toList`. -/
private theorem vector_toList_map {α β : Type u} {n : Nat} (v : Vector α n)
    (f : α → β) :
    (v.map f).toList = v.toList.map f := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp

/-- `insertAt x v (Fin.last n)` appends `x` to the end of `v.toList`. -/
private theorem insertAt_last_toList {α : Type u} {n : Nat} (x : α) (v : Vector α n) :
    (insertAt x v (Fin.last n)).toList = v.toList ++ [x] := by
  unfold insertAt
  simp only [Vector.toList]
  have hidx : (Fin.last n).val = v.toArray.toList.length := by
    simp
  simpa [hidx] using list_insertIdx_length v.toArray.toList x

/-- `insertAt x v i` corresponds to `List.insertIdx` at position `i` on the
underlying list. -/
private theorem insertAt_toList {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin (n + 1)) :
    (insertAt x v i).toList = v.toList.insertIdx i.val x := by
  unfold insertAt
  simp [Vector.toList]

/-- Mapping a `Nodup` list through the injective `Fin.castSucc` keeps it `Nodup`. -/
private theorem list_nodup_map_castSucc {n : Nat} (xs : List (Fin n)) :
    xs.Nodup → (xs.map Fin.castSucc).Nodup := by
  induction xs with
  | nil =>
      intro _h
      simp
  | cons x xs ih =>
      intro hnodup
      rw [List.nodup_cons] at hnodup
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨y, hy, hxy⟩
        have hval : x.val = y.val := by
          simpa using (congrArg Fin.val hxy).symm
        exact hnodup.1 (Fin.ext hval ▸ hy)
      · exact ih hnodup.2

/-- `Fin.last n` never lies in the image of a list under `Fin.castSucc`. -/
private theorem finLast_not_mem_map_castSucc {n : Nat} (xs : List (Fin n)) :
    Fin.last n ∉ xs.map Fin.castSucc := by
  intro hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨x, _hxmem, hxlast⟩
  have hval : x.val = n := by
    simpa using congrArg Fin.val hxlast
  exact Nat.ne_of_lt x.isLt hval

/-- Inserting `Fin.last n` at any position into the `castSucc`-embedded nodup vector
keeps the resulting list `Nodup`, since `Fin.last n` is new and the embedding
stays injective. -/
private theorem insertAt_last_castSucc_nodup {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1))
    (hnodup : v.toList.Nodup) :
    (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.Nodup := by
  rw [insertAt_toList]
  have hmap : (v.map Fin.castSucc).toList.Nodup := by
    rw [vector_toList_map]
    exact list_nodup_map_castSucc v.toList hnodup
  have hlast : Fin.last n ∉ (v.map Fin.castSucc).toList := by
    rw [vector_toList_map]
    exact finLast_not_mem_map_castSucc v.toList
  have hcons : (Fin.last n :: (v.map Fin.castSucc).toList).Nodup := by
    rw [List.nodup_cons]
    exact ⟨hlast, hmap⟩
  have hidx : i.val ≤ (v.map Fin.castSucc).toList.length := by
    simpa using Nat.lt_succ_iff.mp i.isLt
  exact (List.perm_insertIdx (Fin.last n) (v.map Fin.castSucc).toList hidx).symm.nodup hcons

/-- A `Nodup` list of `Fin (n + 1)` with full length `n + 1` must contain
`Fin.last n`. -/
private theorem finLast_mem_of_full_nodup {n : Nat} {xs : List (Fin (n + 1))}
    (hlen : xs.length = n + 1) (hnodup : xs.Nodup) :
    Fin.last n ∈ xs := by
  by_cases hmem : Fin.last n ∈ xs
  · exact hmem
  · exfalso
    have hsub : List.Subperm xs ((List.finRange (n + 1)).erase (Fin.last n)) := by
      apply List.subperm_of_subset hnodup
      intro x hx
      exact (List.mem_erase_of_ne (by
        intro hxlast
        exact hmem (hxlast ▸ hx))).2 (List.mem_finRange x)
    have hle : xs.length ≤ ((List.finRange (n + 1)).erase (Fin.last n)).length :=
      List.Subperm.length_le hsub
    have herase :
        ((List.finRange (n + 1)).erase (Fin.last n)).length = n := by
      rw [List.length_erase]
      simp [List.mem_finRange, List.length_finRange]
    omega

/-- `lowerFinLast x h` reinterprets an `x : Fin (n + 1)` that is not `Fin.last n`
as an element of `Fin n` carrying the same underlying value. -/
private def lowerFinLast {n : Nat} (x : Fin (n + 1)) (h : x ≠ Fin.last n) :
    Fin n :=
  ⟨x.val, by
    have hxlt : x.val < n + 1 := x.isLt
    have hxne : x.val ≠ n := by
      intro hx
      exact h (Fin.ext hx)
    omega⟩

/-- `raiseFinAbove i r` embeds `r : Fin n` into `Fin (n + 1)` while skipping the
position `i`: values below `i` are kept, values at or above `i` are shifted up by
one. -/
private def raiseFinAbove {n : Nat} (i : Fin (n + 1)) (r : Fin n) :
    Fin (n + 1) :=
  if h : r.val < i.val then
    ⟨r.val, by omega⟩
  else
    ⟨r.val + 1, by omega⟩

/-- Indexing `insertAt x v i` at the raised position `raiseFinAbove i r` recovers
the original entry `v[r]`. -/
private theorem insertAt_get_raiseFinAbove {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin (n + 1)) (r : Fin n) :
    (insertAt x v i)[raiseFinAbove i r] = v[r] := by
  unfold insertAt raiseFinAbove
  split
  · simpa [Vector.getElem_toList] using
      List.getElem_insertIdx_of_lt (l := v.toList) (x := x) (i := i.val)
        (j := r.val) ‹r.val < i.val› (by
          have hi : i.val ≤ v.toList.length := by
            simpa [Vector.length_toList] using Nat.lt_succ_iff.mp i.isLt
          rw [List.length_insertIdx_of_le_length hi]
          simpa [Vector.length_toList] using Nat.lt_succ_of_lt r.isLt)
  · simpa using
      list_getElem_insertIdx_succ_of_le v.toList x (Nat.le_of_not_gt ‹¬r.val < i.val›)
        (by simp [Vector.length_toList])

/-- `raiseFinAbove i` is strictly monotone: `raiseFinAbove i a < raiseFinAbove i b`
holds exactly when `a < b`. -/
private theorem raiseFinAbove_lt_iff {n : Nat} (i : Fin (n + 1)) (a b : Fin n) :
    raiseFinAbove i a < raiseFinAbove i b ↔ a < b := by
  by_cases hai : a.val < i.val
  · by_cases hbi : b.val < i.val
    · simp [raiseFinAbove, hai, hbi, Fin.lt_def]
    · simp [raiseFinAbove, hai, hbi, Fin.lt_def]
      omega
  · by_cases hbi : b.val < i.val
    · simp [raiseFinAbove, hai, hbi, Fin.lt_def]
      omega
    · simp [raiseFinAbove, hai, hbi, Fin.lt_def]

/-- The inversion fold against a pivot `x` is unchanged when both the list `xs` and
the pivot are mapped through `raiseFinAbove i`. -/
private theorem inversionFold_map_raiseFinAbove {n : Nat} (i : Fin (n + 1))
    (xs : List (Fin n)) (x : Fin n) (acc : Nat) :
    (xs.map (raiseFinAbove i)).foldl
        (fun acc y => acc + if y < raiseFinAbove i x then 1 else 0) acc =
    xs.foldl (fun acc y => acc + if y < x then 1 else 0) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hhead :
          (if raiseFinAbove i y < raiseFinAbove i x then 1 else 0) =
            (if y < x then 1 else 0) := by
        by_cases hyx : y < x
        · have hraise : raiseFinAbove i y < raiseFinAbove i x :=
            (raiseFinAbove_lt_iff i y x).2 hyx
          simp [hyx, hraise]
        · have hraise : ¬ raiseFinAbove i y < raiseFinAbove i x := by
            intro h
            exact hyx ((raiseFinAbove_lt_iff i y x).1 h)
          simp [hyx, hraise]
      rw [hhead]
      exact ih _

/-- `inversionCount` is invariant under mapping the permutation list through
`raiseFinAbove i`. -/
private theorem inversionCount_map_raiseFinAbove {n : Nat}
    (i : Fin (n + 1)) (xs : List (Fin n)) :
    inversionCount (xs.map (raiseFinAbove i)) = inversionCount xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [inversionCount, ih, inversionFold_map_raiseFinAbove]

/-- Folding `i < y` over the `raiseFinAbove i`-mapped list counts the original
entries `x` satisfying `i ≤ x`, added onto the starting accumulator. -/
private theorem inversionFold_map_raiseFinAbove_self {n : Nat} (i : Fin (n + 1))
    (xs : List (Fin n)) (acc : Nat) :
    (xs.map (raiseFinAbove i)).foldl
        (fun acc y => acc + if i < y then 1 else 0) acc =
    acc + xs.foldl (fun acc y => acc + if i.val ≤ y.val then 1 else 0) 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hhead :
          (if i < raiseFinAbove i x then 1 else 0) =
            (if i.val ≤ x.val then 1 else 0) := by
        by_cases hxi : x.val < i.val
        · have hnle : ¬ i.val ≤ x.val := by omega
          have hnlt : ¬ i < raiseFinAbove i x := by
            simp [raiseFinAbove, hxi, Fin.lt_def]
            omega
          simp [hnle, hnlt]
        · have hle : i.val ≤ x.val := Nat.le_of_not_gt hxi
          have hlt : i < raiseFinAbove i x := by
            change i.val < (raiseFinAbove i x).val
            simp [raiseFinAbove, hxi]
            omega
          simp [hle, hlt]
      rw [hhead]
      rw [ih (acc + if i.val ≤ x.val then 1 else 0)]
      rw [foldCount_start xs (fun y : Fin n => i.val ≤ y.val)
        (0 + if i.val ≤ x.val then 1 else 0)]
      omega

/-- Appending `i` after the `raiseFinAbove i`-mapped list yields `inversionCount xs`
plus the number of entries at or above `i`. -/
private theorem inversionCount_map_raiseFinAbove_append_self {n : Nat}
    (i : Fin (n + 1)) (xs : List (Fin n)) :
    inversionCount ((xs.map (raiseFinAbove i)) ++ [i]) =
      inversionCount xs +
        xs.foldl (fun acc y => acc + if i.val ≤ y.val then 1 else 0) 0 := by
  rw [inversionCount_append]
  rw [inversionCount_map_raiseFinAbove]
  have hsingle : inversionCount ([i] : List (Fin (n + 1))) = 0 := by
    simp [inversionCount]
  rw [hsingle]
  rw [crossInversionCount_singleton_right]
  rw [inversionFold_map_raiseFinAbove_self i xs 0]
  omega

/-- The `i ≤ y` count fold is unchanged when the list is mapped through
`Fin.castSucc`. -/
private theorem foldCount_map_castSucc_ge {n : Nat} (i : Fin (n + 1))
    (xs : List (Fin n)) (acc : Nat) :
    (xs.map Fin.castSucc).foldl
        (fun acc y => acc + if i.val ≤ y.val then 1 else 0) acc =
      xs.foldl (fun acc y => acc + if i.val ≤ y.val then 1 else 0) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact ih _

/-- Folding a step that discards each element and returns the accumulator leaves
the accumulator unchanged. -/
private theorem foldl_ignore {α : Type u} (xs : List α) (acc : Nat) :
    xs.foldl (fun acc _x => acc) acc = acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons _ xs ih =>
      simp only [List.foldl_cons]
      exact ih acc

/-- Counting the entries `y` of `List.finRange n` with `i ≤ y` gives `n - i`. -/
private theorem foldCount_finRange_ge {n : Nat} (i : Fin (n + 1)) :
    (List.finRange n).foldl
        (fun acc y => acc + if i.val ≤ y.val then 1 else 0) 0 =
      n - i.val := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      by_cases htop : i.val = n + 1
      · have hfalse :
            ∀ acc y, y ∈ List.finRange (n + 1) →
              (fun (acc : Nat) (y : Fin (n + 1)) =>
                acc + if i.val ≤ y.val then 1 else 0) acc y =
                (fun (acc : Nat) (_y : Fin (n + 1)) => acc) acc y := by
          intro acc y _hy
          have hnle : ¬ i.val ≤ y.val := by omega
          simp [hnle]
        calc
          (List.finRange (n + 1)).foldl
              (fun acc y => acc + if i.val ≤ y.val then 1 else 0) 0 =
              (List.finRange (n + 1)).foldl
                (fun (acc : Nat) (_y : Fin (n + 1)) => acc) 0 := by
                exact foldl_acc_congr (List.finRange (n + 1))
                  (fun (acc : Nat) (y : Fin (n + 1)) =>
                    acc + if i.val ≤ y.val then 1 else 0)
                  (fun (acc : Nat) (_y : Fin (n + 1)) => acc) 0 hfalse
          _ = 0 := foldl_ignore (List.finRange (n + 1)) 0
          _ = n + 1 - i.val := by omega
      · have hiLt : i.val < n + 1 := by omega
        let i' : Fin (n + 1) := ⟨i.val, hiLt⟩
        rw [List.finRange_succ_last]
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [foldCount_map_castSucc_ge i' (List.finRange n) 0]
        rw [ih i']
        have hleLast : i.val ≤ n := by omega
        simp [i', hleLast]
        omega

/-- The `foldl` count of elements satisfying `p` is invariant under permutation of
the list. -/
private theorem foldCount_perm {α : Type u} (p : α → Prop) [DecidablePred p]
    {xs ys : List α} (hperm : xs.Perm ys) :
    xs.foldl (fun acc y => acc + if p y then 1 else 0) 0 =
      ys.foldl (fun acc y => acc + if p y then 1 else 0) 0 := by
  induction hperm with
  | nil => rfl
  | cons x hperm ih =>
      rename_i l₁ l₂
      simp only [List.foldl_cons]
      let a := 0 + if p x then 1 else 0
      calc
        l₁.foldl (fun acc y => acc + if p y then 1 else 0) a =
            a + l₁.foldl (fun acc y => acc + if p y then 1 else 0) 0 := by
              exact foldCount_start l₁ p a
        _ = a + l₂.foldl (fun acc y => acc + if p y then 1 else 0) 0 := by
              rw [ih]
        _ = l₂.foldl (fun acc y => acc + if p y then 1 else 0) a := by
              exact (foldCount_start l₂ p a).symm
  | swap x y xs =>
      simp only [List.foldl_cons]
      rw [foldCount_start xs p ((0 + if p y then 1 else 0) + if p x then 1 else 0)]
      rw [foldCount_start xs p ((0 + if p x then 1 else 0) + if p y then 1 else 0)]
      omega
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Every `x : Fin n` is a member of a nodup list of `Fin n` whose length is `n`. -/
private theorem fin_mem_of_full_nodup_for_count {n : Nat} {xs : List (Fin n)}
    (x : Fin n) (hlen : xs.length = n) (hnodup : xs.Nodup) :
    x ∈ xs := by
  by_cases hmem : x ∈ xs
  · exact hmem
  · exfalso
    have hsub : List.Subperm xs ((List.finRange n).erase x) := by
      apply List.subperm_of_subset hnodup
      intro y hy
      exact (List.mem_erase_of_ne (by
        intro hyx
        exact hmem (hyx ▸ hy))).2 (List.mem_finRange y)
    have hle : xs.length ≤ ((List.finRange n).erase x).length :=
      List.Subperm.length_le hsub
    have herase : ((List.finRange n).erase x).length = n - 1 := by
      rw [List.length_erase]
      simp [List.mem_finRange, List.length_finRange]
    rw [hlen, herase] at hle
    cases n with
    | zero => exact Fin.elim0 x
    | succ n => omega

/-- A nodup list of `Fin n` of length `n` is a permutation of `List.finRange n`. -/
private theorem list_perm_finRange_of_full_nodup {n : Nat} {xs : List (Fin n)}
    (hlen : xs.length = n) (hnodup : xs.Nodup) :
    xs.Perm (List.finRange n) := by
  rw [List.perm_ext_iff_of_nodup hnodup (List.nodup_finRange n)]
  intro x
  constructor
  · intro _hx
    exact List.mem_finRange x
  · intro _hx
    exact fin_mem_of_full_nodup_for_count x hlen hnodup

/-- Counting the entries `y` with `i ≤ y` in a length-`n` nodup list of `Fin n`
gives `n - i`. -/
private theorem foldCount_full_nodup_ge {n : Nat} (i : Fin (n + 1))
    {xs : List (Fin n)} (hlen : xs.length = n) (hnodup : xs.Nodup) :
    xs.foldl (fun acc y => acc + if i.val ≤ y.val then 1 else 0) 0 =
      n - i.val := by
  rw [foldCount_perm (fun y : Fin n => i.val ≤ y.val)
    (list_perm_finRange_of_full_nodup hlen hnodup)]
  exact foldCount_finRange_ge i

/-- `Fin.castSucc` undoes `lowerFinLast`: `(lowerFinLast x h).castSucc = x`. -/
private theorem lowerFinLast_castSucc {n : Nat} (x : Fin (n + 1))
    (h : x ≠ Fin.last n) :
    (lowerFinLast x h).castSucc = x := by
  exact Fin.ext rfl

/-- In a length-`(n + 1)` nodup list the index of `Fin.last n` is within bounds. -/
private theorem finLast_idxOf_lt_of_full_nodup {n : Nat} {xs : List (Fin (n + 1))}
    (hlen : xs.length = n + 1) (hnodup : xs.Nodup) :
    xs.idxOf (Fin.last n) < xs.length := by
  exact List.idxOf_lt_length_of_mem (finLast_mem_of_full_nodup hlen hnodup)

/-- `peelLastVector perm k …` removes the entry `Fin.last n` (located at position
`k`) from a nodup permutation vector, lowering each remaining entry back to
`Fin n`. -/
private def peelLastVector {n : Nat} (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (_hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) : Vector (Fin n) n :=
  Vector.ofFn fun r =>
    let j := if r.val < k then r.val else r.val + 1
    have hj : j < n + 1 := by
      dsimp [j]
      split
      · omega
      · have hr : r.val < n := r.isLt
        omega
    let y := perm[(⟨j, hj⟩ : Fin (n + 1))]
    lowerFinLast y (by
      intro hy
      have hjlen : j < perm.toList.length := by
        simpa [Vector.length_toList] using hj
      have hjidx :
          perm.toList.idxOf (perm.toList[j]'hjlen) = j := by
        exact hnodup.idxOf_getElem j hjlen
      have hylist : perm.toList[j]'hjlen = Fin.last n := by
        simpa [Vector.getElem_toList] using hy
      have hkj : k = j := by
        rw [← hidx, ← hylist, hjidx]
      dsimp [j] at hkj
      split at hkj
      · omega
      · omega)

/-- Re-embedding `peelLastVector` through `Fin.castSucc` yields the original
permutation list with position `k` erased. -/
private theorem peelLastVector_castSucc_toList {n : Nat}
    (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) :
    ((peelLastVector perm k hk hidx hnodup).map Fin.castSucc).toList =
      perm.toList.eraseIdx k := by
  apply List.ext_getElem
  · have hklist : k < perm.toList.length := by
      simpa [Vector.length_toList] using hk
    rw [List.length_eraseIdx_of_lt hklist]
    simp [Vector.length_toList]
  · intro i hi₁ hi₂
    by_cases hik : i < k
    · simp [peelLastVector, hik, lowerFinLast_castSucc, List.getElem_eraseIdx]
    · have hikle : k ≤ i := Nat.le_of_not_gt hik
      have hklist : k < perm.toList.length := by
        simpa [Vector.length_toList] using hk
      have heraseLen : (perm.toList.eraseIdx k).length = n := by
        rw [List.length_eraseIdx_of_lt hklist]
        simp [Vector.length_toList]
      have hi : i < n := by
        simpa [heraseLen] using hi₂
      simp [peelLastVector, hik, lowerFinLast_castSucc, List.getElem_eraseIdx]

/-- If `xs.map f` is nodup and `f` is injective, then `xs` is nodup. -/
private theorem list_nodup_of_map_injective {α β : Type u} {f : α → β}
    (hinj : Function.Injective f) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup
  | [], _ => by simp
  | x :: xs, hnodup => by
      simp only [List.map_cons, List.nodup_cons] at hnodup ⊢
      constructor
      · intro hxmem
        exact hnodup.1 (List.mem_map.mpr ⟨x, hxmem, rfl⟩)
      · exact list_nodup_of_map_injective hinj hnodup.2

/-- `peelLastVector` produces a nodup vector. -/
private theorem peelLastVector_nodup {n : Nat}
    (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) :
    (peelLastVector perm k hk hidx hnodup).toList.Nodup := by
  apply list_nodup_of_map_injective (f := Fin.castSucc)
  · intro x y hxy
    exact Fin.ext (by simpa using congrArg Fin.val hxy)
  · rw [← vector_toList_map]
    rw [peelLastVector_castSucc_toList perm k hk hidx hnodup]
    exact hnodup.eraseIdx k

/-- Inserting the erased element `xs[i]` back at position `i` of `xs.eraseIdx i`
reconstructs the original list `xs`. -/
private theorem list_insertIdx_eraseIdx_getElem {α : Type u} {xs : List α} {i : Nat}
    (hi : i < xs.length) :
    (xs.eraseIdx i).insertIdx i (xs[i]'hi) = xs := by
  induction xs generalizing i with
  | nil =>
      cases hi
  | cons x xs ih =>
      cases i with
      | zero =>
          simp
      | succ i =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
          simp [ih hi]

/-- Inserting `Fin.last n` at position `k` into the `castSucc`-embedded
`peelLastVector` reconstructs the original permutation vector `perm`. -/
private theorem insertAt_peelLastVector {n : Nat}
    (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) :
    insertAt (Fin.last n)
        ((peelLastVector perm k hk hidx hnodup).map Fin.castSucc) ⟨k, hk⟩ =
      perm := by
  apply Vector.toArray_inj.mp
  apply Array.toList_inj.mp
  change (insertAt (Fin.last n)
        ((peelLastVector perm k hk hidx hnodup).map Fin.castSucc) ⟨k, hk⟩).toList =
      perm.toList
  rw [insertAt_toList]
  rw [peelLastVector_castSucc_toList perm k hk hidx hnodup]
  have hklist : k < perm.toList.length := by
    simpa [Vector.length_toList] using hk
  have hget : perm.toList[k]'hklist = Fin.last n := by
    have hidxLt : perm.toList.idxOf (Fin.last n) < perm.toList.length := by
      simpa [hidx] using hklist
    simpa [hidx] using
      (List.getElem_idxOf (x := Fin.last n) (xs := perm.toList) hidxLt)
  simpa [hget] using
    (list_insertIdx_eraseIdx_getElem (xs := perm.toList) (i := k) hklist)

/-- Every duplicate-free length-`n` vector of `Fin n` appears in
`permutationVectors n`. This gives the completeness half of the local
permutation enumeration used by the Leibniz determinant. -/
theorem permutationVectors_complete {n : Nat} {perm : Vector (Fin n) n}
    (hnodup : perm.toList.Nodup) :
    perm ∈ permutationVectors n := by
  induction n with
  | zero =>
      have hnil : perm.toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      have hperm : perm = emptyVec := by
        apply Vector.ext
        intro i hi
        omega
      simp [permutationVectors, hperm]
  | succ n ih =>
      let k := perm.toList.idxOf (Fin.last n)
      have hk : k < n + 1 := by
        simpa [k, Vector.length_toList] using
          finLast_idxOf_lt_of_full_nodup (by simp [Vector.length_toList]) hnodup
      have hidx : perm.toList.idxOf (Fin.last n) = k := rfl
      let peeled := peelLastVector perm k hk hidx hnodup
      have hpeeled : peeled ∈ permutationVectors n := by
        exact ih (peelLastVector_nodup perm k hk hidx hnodup)
      change perm ∈
        List.flatMap
          (fun v =>
            (List.finRange (n + 1)).map fun i =>
              insertAt (Fin.last n) (v.map Fin.castSucc) i)
          (permutationVectors n)
      rw [List.mem_flatMap]
      refine ⟨peeled, hpeeled, ?_⟩
      rw [List.mem_map]
      refine ⟨(⟨k, hk⟩ : Fin (n + 1)), List.mem_finRange (⟨k, hk⟩ : Fin (n + 1)), ?_⟩
      exact insertAt_peelLastVector perm k hk hidx hnodup

/-- Every vector enumerated by `permutationVectors n` is duplicate-free, so
each listed vector really represents a permutation of `Fin n`. -/
theorem permutationVectors_nodup {n : Nat} {perm : Vector (Fin n) n}
    (hmem : perm ∈ permutationVectors n) :
    perm.toList.Nodup := by
  induction n with
  | zero =>
      have hnil : perm.toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      rw [hnil]
      simp
  | succ n ih =>
      simp [permutationVectors, List.mem_flatMap, List.mem_map] at hmem
      rcases hmem with ⟨v, hv, i, _hi, rfl⟩
      exact insertAt_last_castSucc_nodup v i (ih hv)

private theorem insertAt_last_castSucc_idxOf {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1)) (hnodup : v.toList.Nodup) :
    (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.idxOf (Fin.last n) =
      i.val := by
  have hins :
      (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.Nodup :=
    insertAt_last_castSucc_nodup v i hnodup
  have hlen :
      i.val < (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.length := by
    simp [Vector.length_toList]
  have hget :
      (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList[i.val] =
        Fin.last n := by
    change (insertAt (Fin.last n) (v.map Fin.castSucc) i)[i] = Fin.last n
    exact insertAt_get_self (Fin.last n) (v.map Fin.castSucc) i
  simpa [hget] using hins.idxOf_getElem i.val hlen

/-- `insertAt_last_castSucc_injective` states that inserting `Fin.last n` into the
`castSucc`-lifted nodup vectors `v` and `w` at positions `i` and `j` yields equal
results only when `i = j` and `v = w`, the injectivity that keeps the inserted
permutation vectors distinct in the recursive enumeration. -/
private theorem insertAt_last_castSucc_injective {n : Nat}
    {v w : Vector (Fin n) n} {i j : Fin (n + 1)}
    (hv : v.toList.Nodup) (hw : w.toList.Nodup)
    (h :
      insertAt (Fin.last n) (v.map Fin.castSucc) i =
        insertAt (Fin.last n) (w.map Fin.castSucc) j) :
    i = j ∧ v = w := by
  have hidx :
      i.val = j.val := by
    rw [← insertAt_last_castSucc_idxOf v i hv]
    rw [h]
    exact insertAt_last_castSucc_idxOf w j hw
  have hij : i = j := Fin.ext hidx
  subst j
  have hlist := congrArg
    (fun x : Vector (Fin (n + 1)) (n + 1) => x.toList.eraseIdx i.val) h
  change
    (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.eraseIdx i.val =
      (insertAt (Fin.last n) (w.map Fin.castSucc) i).toList.eraseIdx i.val at hlist
  rw [insertAt_toList, insertAt_toList] at hlist
  repeat rw [List.eraseIdx_insertIdx_self] at hlist
  have hmap : v.toList.map Fin.castSucc = w.toList.map Fin.castSucc := by
    simpa [vector_toList_map] using hlist
  have hvwList : v.toList = w.toList := by
    exact (List.map_inj_right
      (fun x y hxy => Fin.ext (by simpa using congrArg Fin.val hxy))).mp hmap
  refine ⟨rfl, ?_⟩
  apply Vector.toArray_inj.mp
  apply Array.toList_inj.mp
  simpa [Vector.toList] using hvwList

/-- `permutationVectorInsertions_nodup` states that, for a fixed nodup vector `v`,
the list of insertions of `Fin.last n` at each position has no duplicates, so the
size-`n+1` vectors built from a single size-`n` permutation stay distinct. -/
private theorem permutationVectorInsertions_nodup {n : Nat}
    (v : Vector (Fin n) n) (hnodup : v.toList.Nodup) :
    ((List.finRange (n + 1)).map fun i =>
        insertAt (Fin.last n) (v.map Fin.castSucc) i).Nodup := by
  exact list_nodup_map_of_injective
    (fun i j h => (insertAt_last_castSucc_injective hnodup hnodup h).1)
    (List.nodup_finRange (n + 1))

/-- `permutationVectorInsertions_disjoint` states that distinct nodup vectors `v`
and `w` produce insertion lists sharing no element, the cross-vector disjointness
that prevents collisions when the per-vector insertions are concatenated. -/
private theorem permutationVectorInsertions_disjoint {n : Nat}
    {v w : Vector (Fin n) n}
    (hv : v.toList.Nodup) (hw : w.toList.Nodup) (hvw : v ≠ w) :
    ∀ a, a ∈ ((List.finRange (n + 1)).map fun i =>
        insertAt (Fin.last n) (v.map Fin.castSucc) i) →
      ∀ b, b ∈ ((List.finRange (n + 1)).map fun i =>
        insertAt (Fin.last n) (w.map Fin.castSucc) i) →
        a ≠ b := by
  intro a ha b hb hab
  simp only [List.mem_map] at ha hb
  rcases ha with ⟨i, _hi, rfl⟩
  rcases hb with ⟨j, _hj, hb⟩
  exact hvw (insertAt_last_castSucc_injective hv hw (hab.trans hb.symm)).2

/-- `permutationVectors_flatMap_nodup` states that flat-mapping the per-vector
insertion lists over a nodup list `vs` of nodup vectors yields a nodup list,
combining the per-vector and cross-vector facts into the no-duplicates property of
the size-`n+1` permutation enumeration. -/
private theorem permutationVectors_flatMap_nodup {n : Nat}
    (vs : List (Vector (Fin n) n))
    (hvs : vs.Nodup) (hperm : ∀ v, v ∈ vs → v.toList.Nodup) :
    (vs.flatMap fun v =>
        (List.finRange (n + 1)).map fun i =>
          insertAt (Fin.last n) (v.map Fin.castSucc) i).Nodup := by
  induction vs with
  | nil =>
      simp
  | cons v vs ih =>
      simp only [List.flatMap_cons]
      rw [List.nodup_append]
      simp only [List.nodup_cons] at hvs
      refine ⟨?_, ?_, ?_⟩
      · exact permutationVectorInsertions_nodup v (hperm v (by simp))
      · exact ih hvs.2 (fun w hw => hperm w (List.mem_cons_of_mem v hw))
      · intro a ha b hb hab
        simp only [List.mem_flatMap, List.mem_map] at hb
        rcases hb with ⟨w, hw, j, _hj, rfl⟩
        exact permutationVectorInsertions_disjoint
          (hperm v (by simp)) (hperm w (List.mem_cons_of_mem v hw))
          (by
            intro hvw
            exact hvs.1 (hvw ▸ hw))
          a ha _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩) hab

/-- The permutation enumeration itself has no duplicate vectors. This lets
determinant proofs compare sums over `permutationVectors` by list
permutation rather than by quotienting repeated terms. -/
theorem permutationVectors_nodup_list {n : Nat} :
    (permutationVectors n).Nodup := by
  induction n with
  | zero =>
      simp [permutationVectors]
  | succ n ih =>
      simp only [permutationVectors]
      exact permutationVectors_flatMap_nodup
        (permutationVectors n) ih
        (fun v hv => permutationVectors_nodup hv)

/-- Appending the new largest value in the last position does not change
the determinant sign, because it adds no inversions. -/
theorem detSign_insertAt_last {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (v : Vector (Fin n) n) :
    detSign (R := R)
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
    detSign (R := R) v := by
  unfold detSign
  rw [insertAt_last_toList, vector_toList_map, inversionCount_insert_last_castSucc]

private theorem detSignParity_add {R : Type u} [Lean.Grind.Ring R] (a m : Nat) :
    (if (a + m) % 2 = 0 then (1 : R) else -1) =
      (-1 : R) ^ m * if a % 2 = 0 then (1 : R) else -1 := by
  induction m with
  | zero =>
      simp [Nat.add_zero]
      grind
  | succ m ih =>
      rw [Nat.add_succ]
      rw [Lean.Grind.Semiring.pow_succ]
      rw [show (-1 : R) ^ m * -1 * (if a % 2 = 0 then (1 : R) else -1) =
          -1 * ((-1 : R) ^ m * if a % 2 = 0 then (1 : R) else -1) by
        grind]
      rw [← ih]
      have hsucc : (a + m).succ = a + (m + 1) := by omega
      rw [hsucc]
      by_cases hm : (a + m) % 2 = 0
      · have hmnot' : ¬(a + (m + 1)) % 2 = 0 := by omega
        rw [if_pos hm, if_neg hmnot']
        grind
      · have hmnext' : (a + (m + 1)) % 2 = 0 := by omega
        rw [if_neg hm, if_pos hmnext']
        grind

private theorem detSign_of_inversionCount_add {R : Type u} [Lean.Grind.Ring R]
    {n n' : Nat} (perm : Vector (Fin n) n) (perm' : Vector (Fin n') n') (m : Nat)
    (h :
      inversionCount perm'.toList =
        inversionCount perm.toList + m) :
    detSign (R := R) perm' = (-1 : R) ^ m * detSign (R := R) perm := by
  unfold detSign
  rw [h]
  exact detSignParity_add (R := R) (inversionCount perm.toList) m

private theorem detSign_insertAt_prefix {R : Type u} [Lean.Grind.Ring R] {k : Nat}
    (v : Vector (Fin (k + 1)) (k + 1)) (r : Fin k) :
    detSign (R := R)
      (insertAt (Fin.last (k + 1)) (v.map Fin.castSucc) r.castSucc.castSucc) =
      (-1 : R) ^ (k + 1 - r.val) * detSign (R := R) v := by
  apply detSign_of_inversionCount_add
  rw [insertAt_toList, vector_toList_map]
  change inversionCount ((v.toList.map Fin.castSucc).insertIdx r.val (Fin.last (k + 1))) =
    inversionCount v.toList + (k + 1 - r.val)
  simpa [Vector.length_toList] using
    inversionCount_insertIdx_castSucc_last_eq v.toList r.val (by
      simp [Vector.length_toList]
      omega)

/-- The identity permutation has positive determinant sign. -/
theorem detSign_identity {R : Type u} [Lean.Grind.Ring R] (n : Nat) :
    detSign (R := R) (Vector.ofFn fun i : Fin n => i) = 1 := by
  induction n with
  | zero =>
      have hvec : (Vector.ofFn fun i : Fin 0 => i) = emptyVec := by
        apply Vector.ext
        intro i hi
        omega
      simp [hvec, detSign, emptyVec, inversionCount]
  | succ n ih =>
      have hvec :
          (Vector.ofFn fun i : Fin (n + 1) => i) =
            insertAt (Fin.last n)
              ((Vector.ofFn fun i : Fin n => i).map Fin.castSucc) (Fin.last n) := by
        apply Vector.ext
        intro k hk
        by_cases hlast : k = n
        · subst k
          simp [insertAt, List.getElem_insertIdx_self]
          exact Fin.ext rfl
        · have hklt : k < n := by omega
          simp [insertAt, List.getElem_insertIdx_of_lt, hklt]
      rw [hvec, detSign_insertAt_last]
      exact ih

/-- Product reindexing for a permutation that fixes the final column. The
Leibniz product splits into the product on the leading prefix times the final
row/column entry. -/
theorem detProduct_insertAt_last {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) :
    detProduct M (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
      detProduct (leadingPrefix M n (Nat.le_succ n)) v * M[Fin.last n][Fin.last n] := by
  unfold detProduct
  rw [← Fin.foldl_eq_foldl_finRange, ← Fin.foldl_eq_foldl_finRange]
  rw [Fin.foldl_succ_last]
  have hfold :
      Fin.foldl n
          (fun acc i =>
            acc *
              M[i.castSucc][
                (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc]]) 1 =
        Fin.foldl n
          (fun acc i => acc * (leadingPrefix M n (Nat.le_succ n))[i][v[i]]) 1 := by
    congr
    funext acc i
    have hget :
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc] =
          (v[i]).castSucc := by
      simpa using insertAt_last_get_castSucc (Fin.last n) (v.map Fin.castSucc) i
    simp [leadingPrefix, ofFn, hget]
  have hlast :
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[Fin.last n] =
        Fin.last n := by
    exact insertAt_get_self (Fin.last n) (v.map Fin.castSucc) (Fin.last n)
  rw [hfold]
  simp [hlast]

/-- Leibniz-term reindexing for a permutation that fixes the final column. This
packages the sign and product split used by last-row/last-column expansions. -/
theorem detTerm_insertAt_last {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) :
    detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
      detSign (R := R) v *
        (detProduct (leadingPrefix M n (Nat.le_succ n)) v * M[Fin.last n][Fin.last n]) := by
  unfold detTerm
  rw [detSign_insertAt_last, detProduct_insertAt_last]

/-- Insertion-position generalization of `detSign_insertAt_last`/`detSign_insertAt_prefix`:
inserting `Fin.last n` at any position `i` adds `n - i.val` inversions. -/
private theorem detSign_insertAt_general {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1)) :
    detSign (R := R) (insertAt (Fin.last n) (v.map Fin.castSucc) i) =
      (-1 : R) ^ (n - i.val) * detSign (R := R) v := by
  apply detSign_of_inversionCount_add
  rw [insertAt_toList, vector_toList_map]
  have hlen : i.val ≤ v.toList.length := by
    rw [Vector.length_toList]; exact Nat.le_of_lt_succ i.isLt
  simpa [Vector.length_toList] using
    inversionCount_insertIdx_castSucc_last_eq v.toList i.val hlen

/-- The cofactor sign for the last column equals `(-1)^(n - i.val)`. -/
private theorem cofactorSign_last_eq_pow {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (i : Fin (n + 1)) :
    cofactorSign (R := R) i (Fin.last n) = (-1 : R) ^ (n - i.val) := by
  unfold cofactorSign
  simp only [Fin.val_last]
  have hle : i.val ≤ n := Nat.le_of_lt_succ i.isLt
  have h := detSignParity_add (R := R) (2 * i.val) (n - i.val)
  have heven : (2 * i.val) % 2 = 0 := by omega
  rw [if_pos heven] at h
  have hsum : 2 * i.val + (n - i.val) = i.val + n := by omega
  rw [hsum] at h
  -- h : (if (i.val + n) % 2 = 0 then 1 else -1) = (-1) ^ (n - i.val) * 1
  calc (if (i.val + n) % 2 = 0 then (1 : R) else -1)
      = (-1 : R) ^ (n - i.val) * 1 := h
    _ = (-1 : R) ^ (n - i.val) := by grind

/-- Reading `insertAt x v i` at `skipIndex i r'` recovers `v[r']`: the inserted
element occupies position `i`, leaving the other positions in bijection with the
original via `skipIndex i`. -/
private theorem insertAt_get_skipIndex {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin (n + 1)) (r' : Fin n) :
    (insertAt x v i)[skipIndex i r'] = v[r'] := by
  unfold insertAt
  by_cases hlt : r'.val < i.val
  · simp [List.getElem_insertIdx_of_lt, hlt]
  · have hge : i.val ≤ r'.val := by omega
    have hgt : i.val < r'.val + 1 := by omega
    simp [List.getElem_insertIdx_of_gt, hlt, hgt]

/-- `List.finRange (n + 1)` decomposes as the `Fin n` enumeration mapped through
`skipIndex i` with `i` inserted at position `i.val`. -/
private theorem list_finRange_succ_eq_insertIdx_skipIndex {n : Nat} (i : Fin (n + 1)) :
    List.finRange (n + 1) =
      ((List.finRange n).map (skipIndex i)).insertIdx i.val i := by
  have hilen : i.val ≤ ((List.finRange n).map (skipIndex i)).length := by
    simp [List.length_finRange]; exact Nat.le_of_lt_succ i.isLt
  apply List.ext_getElem
  · rw [List.length_finRange, List.length_insertIdx_of_le_length hilen,
        List.length_map, List.length_finRange]
  · intro k hk hk'
    rw [List.getElem_finRange]
    by_cases hki : k < i.val
    · rw [List.getElem_insertIdx_of_lt hki]
      have hkn : k < n := by
        have : k < ((List.finRange n).map (skipIndex i)).length := by
          simp [List.length_finRange]; omega
        simpa [List.length_map, List.length_finRange] using this
      rw [List.getElem_map, List.getElem_finRange]
      apply Fin.ext
      simp [skipIndex_val_of_lt, hki]
    · by_cases hkeq : k = i.val
      · subst hkeq
        rw [List.getElem_insertIdx_self]
        apply Fin.ext; rfl
      · have hkgt : i.val < k := by omega
        rw [List.getElem_insertIdx_of_gt hkgt]
        have hk1n : k - 1 < n := by
          have hklt : k < n + 1 := by simp [List.length_finRange] at hk; exact hk
          omega
        rw [List.getElem_map, List.getElem_finRange]
        apply Fin.ext
        have hgt' : ¬ (k - 1 < i.val) := by omega
        simp [skipIndex_val_of_not_lt, hgt']
        omega

/-- `List.finRange (n + 1)` is a permutation of `i :: ((List.finRange n).map (skipIndex i))`. -/
private theorem list_finRange_succ_perm_skipIndex {n : Nat} (i : Fin (n + 1)) :
    (List.finRange (n + 1)).Perm (i :: (List.finRange n).map (skipIndex i)) := by
  rw [list_finRange_succ_eq_insertIdx_skipIndex i]
  have hilen : i.val ≤ ((List.finRange n).map (skipIndex i)).length := by
    simp [List.length_finRange]; exact Nat.le_of_lt_succ i.isLt
  exact List.perm_insertIdx i ((List.finRange n).map (skipIndex i)) hilen

/-- Factorize a multiplicative `foldl` over `List.finRange (n + 1)` at index `i`,
yielding `f i` times the foldl over `List.finRange n` reindexed via `skipIndex i`. -/
private theorem foldl_finRange_succ_factor_skipIndex {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (i : Fin (n + 1)) (f : Fin (n + 1) → R) :
    (List.finRange (n + 1)).foldl (fun acc r => acc * f r) 1 =
      f i * (List.finRange n).foldl (fun acc r' => acc * f (skipIndex i r')) 1 := by
  rw [foldl_det_product_perm f (list_finRange_succ_perm_skipIndex i) 1]
  show (i :: (List.finRange n).map (skipIndex i)).foldl (fun acc r => acc * f r) 1 = _
  simp only [List.foldl_cons]
  rw [show (1 : R) * f i = f i * 1 from by grind]
  rw [foldl_det_product_mul_left ((List.finRange n).map (skipIndex i)) (f i) f 1]
  rw [List.foldl_map]

/-- Permutation-product equation generalizing `detProduct_insertAt_last` to any
insertion position: factor the Leibniz product into the `(i, last)` entry times
the product over the `deleteRowCol` minor. -/
private theorem detProduct_insertAt_general {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) (i : Fin (n + 1)) :
    detProduct M (insertAt (Fin.last n) (v.map Fin.castSucc) i) =
      M[i][Fin.last n] * detProduct (deleteRowCol M i (Fin.last n)) v := by
  unfold detProduct
  rw [foldl_finRange_succ_factor_skipIndex i
    (fun r => M[r][(insertAt (Fin.last n) (v.map Fin.castSucc) i)[r]])]
  congr 1
  · -- M[i][(insertAt ... i)[i]] = M[i][Fin.last n]
    congr 1
    exact insertAt_get_self _ _ _
  · apply foldl_det_product_congr
    intro r' _hmem
    -- Identify the column index of each side with `(v[r']).castSucc`.
    have hLHS_col :
        (insertAt (Fin.last n) (v.map Fin.castSucc) i)[skipIndex i r'] =
          (v[r']).castSucc := by
      rw [insertAt_get_skipIndex]
      simp [Vector.getElem_map]
    have hRHS_col :
        skipIndex (Fin.last n) v[r'] = (v[r']).castSucc := skipIndex_last v[r']
    simp only [deleteRowCol_entry, hLHS_col, hRHS_col]

/-- Leibniz-term equation for an arbitrary insertion position. -/
private theorem detTerm_insertAt_general {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) (i : Fin (n + 1)) :
    detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i) =
      cofactorSign (R := R) i (Fin.last n) *
        (M[i][Fin.last n] * detTerm (deleteRowCol M i (Fin.last n)) v) := by
  unfold detTerm
  rw [detSign_insertAt_general, detProduct_insertAt_general]
  rw [cofactorSign_last_eq_pow]
  grind

private theorem detProduct_insertAt_not_last_zero_of_last_row_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n)
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n)
    (hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0) :
    detProduct M (insertAt (Fin.last n) (v.map Fin.castSucc) i) = 0 := by
  unfold detProduct
  apply foldl_det_product_zero_of_mem
    (List.finRange (n + 1)) (Fin.last n)
    (fun r => M[r][(insertAt (Fin.last n) (v.map Fin.castSucc) i)[r]]) 1
    (List.mem_finRange (Fin.last n))
  have hiVal : i.val < n := by
    have hne : i.val ≠ n := by
      intro hval
      exact hi (Fin.ext hval)
    omega
  have hcolVal :
      ((insertAt (Fin.last n) (v.map Fin.castSucc) i)[Fin.last n]).val < n := by
    unfold insertAt
    simp [List.getElem_insertIdx_of_gt, hiVal, Vector.toList]
  exact hrow ((insertAt (Fin.last n) (v.map Fin.castSucc) i)[Fin.last n]) hcolVal

private theorem detTerm_insertAt_not_last_zero_of_last_row_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n)
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n)
    (hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0) :
    detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i) = 0 := by
  unfold detTerm
  rw [detProduct_insertAt_not_last_zero_of_last_row_zero M v i hi hrow]
  grind

private theorem foldl_detTerm_last_row_insertions
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) (z : R)
    (hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0) :
    (List.finRange (n + 1)).foldl
        (fun acc i =>
          acc + detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i)) z =
      z + detSign (R := R) v *
        (detProduct (leadingPrefix M n (Nat.le_succ n)) v * M[Fin.last n][Fin.last n]) := by
  rw [← Fin.foldl_eq_foldl_finRange]
  rw [Fin.foldl_succ_last]
  have hprefix :
      Fin.foldl n
          (fun acc i =>
            acc + detTerm M
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z = z := by
    rw [Fin.foldl_eq_foldl_finRange]
    calc
      (List.finRange n).foldl
          (fun acc i =>
            acc + detTerm M
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z =
        (List.finRange n).foldl (fun acc (_i : Fin n) => acc + (0 : R)) z := by
          apply foldl_det_sum_congr
          intro i _hmem
          rw [detTerm_insertAt_not_last_zero_of_last_row_zero M v i.castSucc
            (by
              intro hlast
              have hval := congrArg Fin.val hlast
              simp at hval
              exact (Nat.ne_of_lt i.isLt) hval)
            hrow]
      _ = z := by
          exact foldl_det_sum_zero (List.finRange n) z
  rw [hprefix]
  rw [detTerm_insertAt_last]

/-- If the last row is zero before the diagonal entry, the determinant
factors as the leading principal determinant times the bottom-right entry.
This is the triangular-recursion step used by positivity and diagonal-product
lemmas. -/
theorem det_eq_det_leadingPrefix_mul_last_of_last_row_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1))
    (hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0) :
    det M = det (leadingPrefix M n (Nat.le_succ n)) * M[Fin.last n][Fin.last n] := by
  unfold det
  rw [show permutationVectors (n + 1) =
      List.flatMap
        (fun v =>
          (List.finRange (n + 1)).map fun i =>
            insertAt (Fin.last n) (v.map Fin.castSucc) i)
        (permutationVectors n) by rfl]
  rw [foldl_det_sum_flatMap]
  calc
    (permutationVectors n).foldl
        (fun acc v =>
          (List.map (fun i => insertAt (Fin.last n) (Vector.map Fin.castSucc v) i)
              (List.finRange (n + 1))).foldl
            (fun acc perm => acc + detTerm M perm) acc) 0 =
      (permutationVectors n).foldl
        (fun acc v =>
          (List.finRange (n + 1)).foldl
            (fun acc i =>
              acc + detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i)) acc) 0 := by
        apply foldl_acc_congr
        intro acc v _hmem
        simp only [List.foldl_map]
    _ =
      (permutationVectors n).foldl
        (fun acc v =>
          acc + detSign (R := R) v *
            (detProduct (leadingPrefix M n (Nat.le_succ n)) v *
              M[Fin.last n][Fin.last n])) 0 := by
        apply foldl_acc_congr
        intro acc v _hmem
        exact foldl_detTerm_last_row_insertions M v acc hrow
    _ =
      (permutationVectors n).foldl
          (fun acc v => acc + detTerm (leadingPrefix M n (Nat.le_succ n)) v) 0 *
        M[Fin.last n][Fin.last n] := by
        unfold detTerm
        calc
          (permutationVectors n).foldl
              (fun acc v =>
                acc + detSign (R := R) v *
                  (detProduct (leadingPrefix M n (Nat.le_succ n)) v *
                    M[Fin.last n][Fin.last n])) 0 =
            (permutationVectors n).foldl
              (fun acc v =>
                acc + (detSign (R := R) v *
                  detProduct (leadingPrefix M n (Nat.le_succ n)) v) *
                    M[Fin.last n][Fin.last n]) 0 := by
              apply foldl_det_sum_congr
              intro v _hmem
              grind
          _ =
            (permutationVectors n).foldl
                (fun acc v =>
                  acc + detSign (R := R) v *
                    detProduct (leadingPrefix M n (Nat.le_succ n)) v) 0 *
              M[Fin.last n][Fin.last n] := by
              exact foldl_det_sum_mul_right_zero
                (permutationVectors n)
                (fun v => detSign (R := R) v *
                  detProduct (leadingPrefix M n (Nat.le_succ n)) v)
                M[Fin.last n][Fin.last n]
    _ = det (leadingPrefix M n (Nat.le_succ n)) * M[Fin.last n][Fin.last n] := by
        rfl

/-- An integer upper-triangular matrix with strictly positive diagonal has
strictly positive determinant. -/
theorem det_upperTriangular_pos_diag
    {n : Nat} (M : Matrix Int n n)
    (hzero : ∀ i j : Fin n, j.val < i.val → M[i][j] = 0)
    (hdiag : ∀ i : Fin n, 0 < M[i][i]) :
    0 < det M := by
  induction n with
  | zero =>
      simp [det, permutationVectors, detTerm, detSign, detProduct, emptyVec, inversionCount]
  | succ n ih =>
      have hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0 := by
        intro j hj
        exact hzero (Fin.last n) j hj
      rw [det_eq_det_leadingPrefix_mul_last_of_last_row_zero M hrow]
      have hprefixZero :
          ∀ i j : Fin n, j.val < i.val →
            (leadingPrefix M n (Nat.le_succ n))[i][j] = 0 := by
        intro i j hij
        let ii : Fin (n + 1) := ⟨i.val, by omega⟩
        let jj : Fin (n + 1) := ⟨j.val, by omega⟩
        have hentry : (leadingPrefix M n (Nat.le_succ n))[i][j] = M[ii][jj] := by
          simp [leadingPrefix, ofFn, ii, jj]
        rw [hentry]
        exact hzero ii jj hij
      have hprefixDiag :
          ∀ i : Fin n, 0 < (leadingPrefix M n (Nat.le_succ n))[i][i] := by
        intro i
        let ii : Fin (n + 1) := ⟨i.val, by omega⟩
        have hentry : (leadingPrefix M n (Nat.le_succ n))[i][i] = M[ii][ii] := by
          simp [leadingPrefix, ofFn, ii]
        rw [hentry]
        exact hdiag ii
      exact Int.mul_pos (ih (leadingPrefix M n (Nat.le_succ n)) hprefixZero hprefixDiag)
        (hdiag (Fin.last n))

/-- The determinant of an upper-triangular square matrix (entries below the
diagonal are zero) over a commutative ring is the product of its diagonal
entries, expressed via a `Fin.foldl` over the diagonal indices. -/
theorem det_upperTriangular_eq_finFoldl_diag
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat} (M : Matrix R n n)
    (hzero : ∀ i j : Fin n, j.val < i.val → M[i][j] = 0) :
    det M = Fin.foldl n (fun acc i => acc * M[i][i]) 1 := by
  induction n with
  | zero =>
      simp only [Fin.foldl_zero]
      simp [det, permutationVectors, detTerm, detSign, detProduct, emptyVec,
        inversionCount]
      grind
  | succ n ih =>
      have hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0 := by
        intro j hj
        exact hzero (Fin.last n) j hj
      rw [det_eq_det_leadingPrefix_mul_last_of_last_row_zero M hrow]
      have hprefixZero :
          ∀ i j : Fin n, j.val < i.val →
            (leadingPrefix M n (Nat.le_succ n))[i][j] = 0 := by
        intro i j hij
        let ii : Fin (n + 1) := ⟨i.val, by omega⟩
        let jj : Fin (n + 1) := ⟨j.val, by omega⟩
        have hentry : (leadingPrefix M n (Nat.le_succ n))[i][j] = M[ii][jj] := by
          simp [leadingPrefix, ofFn, ii, jj]
        rw [hentry]
        exact hzero ii jj hij
      rw [ih (leadingPrefix M n (Nat.le_succ n)) hprefixZero]
      -- The (n+1)-length Fin.foldl over diagonals splits as the n-length foldl
      -- times the last diagonal entry.
      rw [Fin.foldl_succ_last]
      -- Rewrite the leading prefix diagonal entries as M[i.castSucc][i.castSucc].
      have hcongr :
          Fin.foldl n
              (fun acc i => acc * (leadingPrefix M n (Nat.le_succ n))[i][i]) 1 =
            Fin.foldl n (fun acc i => acc * M[i.castSucc][i.castSucc]) 1 := by
        rw [Fin.foldl_eq_foldl_finRange, Fin.foldl_eq_foldl_finRange]
        apply foldl_acc_congr
        intro acc i _hmem
        have hentry : (leadingPrefix M n (Nat.le_succ n))[i][i] = M[i.castSucc][i.castSucc] :=
          by simp [leadingPrefix, ofFn, Fin.castSucc]
        rw [hentry]
      rw [hcongr]

/-- The determinant of an upper-triangular square matrix as a `List.foldl`
product over the diagonal indices in `Fin.finRange`. -/
theorem det_upperTriangular_eq_foldl_diag
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat} (M : Matrix R n n)
    (hzero : ∀ i j : Fin n, j.val < i.val → M[i][j] = 0) :
    det M = (List.finRange n).foldl (fun acc i => acc * M[i][i]) 1 := by
  rw [det_upperTriangular_eq_finFoldl_diag M hzero]
  rw [Fin.foldl_eq_foldl_finRange]

private theorem detTerm_identity_insertAt_last {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n) :
    detTerm (1 : Matrix R (n + 1) (n + 1))
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
    detTerm (1 : Matrix R n n) v := by
  unfold detTerm
  rw [detSign_insertAt_last, detProduct_identity_insertAt_last]

private theorem foldl_detTerm_identity_insertions {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n) (z : R) :
    (List.finRange (n + 1)).foldl
        (fun acc i =>
          acc + detTerm (1 : Matrix R (n + 1) (n + 1))
            (insertAt (Fin.last n) (v.map Fin.castSucc) i)) z =
      z + detTerm (1 : Matrix R n n) v := by
  rw [← Fin.foldl_eq_foldl_finRange]
  rw [Fin.foldl_succ_last]
  have hprefix :
      Fin.foldl n
          (fun acc i =>
            acc + detTerm (1 : Matrix R (n + 1) (n + 1))
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z = z := by
    rw [Fin.foldl_eq_foldl_finRange]
    calc
      (List.finRange n).foldl
          (fun acc i =>
            acc + detTerm (1 : Matrix R (n + 1) (n + 1))
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z =
        (List.finRange n).foldl (fun acc (_i : Fin n) => acc + (0 : R)) z := by
          apply foldl_det_sum_congr
          intro i _hmem
          unfold detTerm
          rw [detProduct_identity_insertAt_not_last_zero (R := R) v i.castSucc (by
            intro hlast
            have hval := congrArg Fin.val hlast
            simp at hval
            exact (Nat.ne_of_lt i.isLt) hval)]
          grind
      _ = z := by
          exact foldl_det_sum_zero (List.finRange n) z
  rw [hprefix]
  rw [detTerm_identity_insertAt_last]

private theorem rowScale_get {R : Type u} [Mul R] {n m : Nat}
    (M : Matrix R n m) (i r : Fin n) (c : R) (k : Fin m) :
    (rowScale M i c)[r][k] = if r = i then c * M[i][k] else M[r][k] := by
  by_cases h : r = i
  · subst r
    simp [rowScale]
  · simp [rowScale, h]
    have hval : i.val ≠ r.val := by
      intro hval
      exact h (Fin.ext hval.symm)
    have hrow :
        (M.set i (Vector.ofFn fun k => c * M[i][k]))[r] = M[r] := by
      exact
        (Vector.getElem_set_ne (xs := M) (x := Vector.ofFn fun k => c * M[i][k])
          i.isLt r.isLt hval)
    simpa [rowScale] using congrArg (fun row => row[k]) hrow

private theorem detProduct_rowScale {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detProduct (rowScale M i c) perm = c * detProduct M perm := by
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc r => acc * (rowScale M i c)[r][perm[r]]) 1 =
      (List.finRange n).foldl
        (fun acc r => acc * if r = i then c * M[r][perm[r]] else M[r][perm[r]]) 1 := by
        apply foldl_det_product_congr
        intro r _hmem
        by_cases h : r = i
        · subst r
          simpa using (rowScale_get M i i c perm[i])
        · simpa [h] using (rowScale_get M i r c perm[r])
    _ = c * (List.finRange n).foldl (fun acc r => acc * M[r][perm[r]]) 1 := by
        exact foldl_det_product_single_scale
          (List.finRange n) i c (fun r => M[r][perm[r]]) 1
          (List.mem_finRange i) (List.nodup_finRange n)

/-- The transposition of `Fin n` swapping `i` and `j`, sending `r` to `j` if
`r = i`, to `i` if `r = j`, and to itself otherwise. -/
private def finTranspose {n : Nat} (i j : Fin n) (r : Fin n) : Fin n :=
  if r = i then j else if r = j then i else r

/-- `finTranspose i j` sends `i` to `j`. -/
private theorem finTranspose_left {n : Nat} (i j : Fin n) :
    finTranspose i j i = j := by
  simp [finTranspose]

/-- `finTranspose i j` sends `j` to `i`. -/
private theorem finTranspose_right {n : Nat} (i j : Fin n) :
    finTranspose i j j = i := by
  by_cases h : j = i
  · subst j
    simp [finTranspose]
  · simp [finTranspose, h]

/-- `finTranspose i j` fixes every `r` distinct from both `i` and `j`. -/
private theorem finTranspose_of_ne {n : Nat} (i j r : Fin n)
    (hi : r ≠ i) (hj : r ≠ j) :
    finTranspose i j r = r := by
  simp [finTranspose, hi, hj]

/-- `finTranspose i j` is an involution: applying it twice returns `r`. -/
private theorem finTranspose_involutive {n : Nat} (i j r : Fin n) :
    finTranspose i j (finTranspose i j r) = r := by
  by_cases hi : r = i
  · subst r
    rw [finTranspose_left, finTranspose_right]
  · by_cases hj : r = j
    · subst r
      rw [finTranspose_right, finTranspose_left]
    · rw [finTranspose_of_ne i j r hi hj]
      exact finTranspose_of_ne i j r hi hj

/-- `finTranspose i j` is injective, since it is its own inverse. -/
private theorem finTranspose_injective {n : Nat} (i j : Fin n) :
    Function.Injective (finTranspose i j) := by
  intro a b h
  have h' := congrArg (finTranspose i j) h
  simpa [finTranspose_involutive] using h'

/-- Mapping `finTranspose i j` over `List.finRange n` permutes it, since the
transposition is a bijection of `Fin n`. -/
private theorem finRange_map_finTranspose_perm {n : Nat} (i j : Fin n) :
    ((List.finRange n).map (finTranspose i j)).Perm (List.finRange n) := by
  apply (List.perm_ext_iff_of_nodup
    (list_nodup_map_of_injective (finTranspose_injective i j) (List.nodup_finRange n))
    (List.nodup_finRange n)).mpr
  intro r
  constructor
  · intro _h
    exact List.mem_finRange r
  · intro _h
    simp only [List.mem_map]
    exact ⟨finTranspose i j r, List.mem_finRange _, by
      rw [finTranspose_involutive]⟩

/-- Precompose a permutation vector `perm` with the transposition swapping rows
`i` and `j`, yielding the vector whose `r`-th entry is `perm[finTranspose i j r]`. -/
private def transposePermutationValues {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) : Vector (Fin n) n :=
  Vector.ofFn fun r => perm[finTranspose i j r]

/-- Entrywise read of a row swap: `(rowSwap M i j)[r][k]` reads from row `i`
when `r = j`, from row `j` when `r = i`, and from row `r` otherwise. -/
private theorem rowSwap_get {R : Type u} {n m : Nat}
    (M : Matrix R n m) (i j r : Fin n) (k : Fin m) :
    (rowSwap M i j)[r][k] =
      if r = j then M[i][k] else if r = i then M[j][k] else M[r][k] := by
  by_cases hrj : r = j
  · subst r
    simp [rowSwap]
  · by_cases hri : r = i
    · subst r
      simp [rowSwap, hrj]
      have hval : j.val ≠ i.val := by
        intro hval
        exact hrj (Fin.ext hval.symm)
      have hrow : ((M.set i M[j]).set j M[i])[i] = (M.set i M[j])[i] := by
        exact Vector.getElem_set_ne (xs := M.set i M[j]) (x := M[i]) j.isLt i.isLt hval
      simpa using congrArg (fun row => row[k]) hrow
    · simp [rowSwap, hrj, hri]
      have hir : i.val ≠ r.val := by
        intro hval
        exact hri (Fin.ext hval.symm)
      have hjr : j.val ≠ r.val := by
        intro hval
        exact hrj (Fin.ext hval.symm)
      have hrow₁ : (M.set i M[j])[r] = M[r] := by
        exact Vector.getElem_set_ne (xs := M) (x := M[j]) i.isLt r.isLt hir
      have hrow₂ : ((M.set i M[j]).set j M[i])[r] = (M.set i M[j])[r] := by
        exact Vector.getElem_set_ne (xs := M.set i M[j]) (x := M[i]) j.isLt r.isLt hjr
      exact (congrArg (fun row => row[k]) hrow₂).trans (congrArg (fun row => row[k]) hrow₁)

/-- For distinct `i, j`, reading row `r` of `rowSwap M i j` is the same as
reading row `finTranspose i j r` of `M`, identifying the swap with the
transposition. -/
private theorem rowSwap_get_finTranspose {R : Type u} {n m : Nat}
    (M : Matrix R n m) (i j r : Fin n) (h : i ≠ j) (k : Fin m) :
    (rowSwap M i j)[r][k] = M[finTranspose i j r][k] := by
  rw [rowSwap_get]
  by_cases hrj : r = j
  · subst r
    simp [finTranspose, h.symm]
  · by_cases hri : r = i
    · subst r
      simp [finTranspose, hrj]
    · rw [if_neg hrj, if_neg hri]
      exact congrArg (fun row => M[row][k]) (finTranspose_of_ne i j r hri hrj).symm

/-- The `r`-th entry of `transposePermutationValues perm i j` is
`perm[finTranspose i j r]`, unfolding the definition. -/
private theorem transposePermutationValues_get {n : Nat}
    (perm : Vector (Fin n) n) (i j r : Fin n) :
    (transposePermutationValues perm i j)[r] = perm[finTranspose i j r] := by
  simp [transposePermutationValues]

/-- `vector_toList_eq_finRange_map_get` rewrites a vector's list view as the finite range of indices mapped through its getter. -/
private theorem vector_toList_eq_finRange_map_get {α : Type u} {n : Nat}
    (v : Vector α n) :
    v.toList = (List.finRange n).map fun i => v[i] := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp

/-- `transposePermutationValues_toList_perm` shows that transposing two positions in a permutation vector only permutes its list of values. -/
private theorem transposePermutationValues_toList_perm {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) :
    (transposePermutationValues perm i j).toList.Perm perm.toList := by
  rw [vector_toList_eq_finRange_map_get (transposePermutationValues perm i j)]
  rw [vector_toList_eq_finRange_map_get perm]
  have hleft :
      (List.finRange n).map (fun r => (transposePermutationValues perm i j)[r]) =
        (List.finRange n).map ((fun r => perm[r]) ∘ finTranspose i j) := by
    apply List.map_congr_left
    intro r _hr
    exact transposePermutationValues_get perm i j r
  rw [hleft]
  simpa [List.map_map] using
    (finRange_map_finTranspose_perm i j).map fun r => perm[r]

/-- `transposePermutationValues_mem_permutationVectors` preserves membership in `permutationVectors n` after transposing two positions. -/
private theorem transposePermutationValues_mem_permutationVectors {n : Nat}
    {perm : Vector (Fin n) n} (i j : Fin n)
    (hmem : perm ∈ permutationVectors n) :
    transposePermutationValues perm i j ∈ permutationVectors n := by
  apply permutationVectors_complete
  exact (transposePermutationValues_toList_perm perm i j).symm.nodup
    (permutationVectors_nodup hmem)

/-- `vector_get_fin_congr` transports a vector lookup across an equality of finite indices. -/
private theorem vector_get_fin_congr {α : Type u} {n : Nat} (v : Vector α n)
    {a b : Fin n} (h : a = b) : v[a] = v[b] := by
  subst b
  rfl

/-- `vector_toList_split_two` splits a vector's list view around two strictly ordered finite indices. -/
private theorem vector_toList_split_two {α : Type u} {n : Nat}
    (v : Vector α n) {i j : Fin n} (hij : i.val < j.val) :
    v.toList =
      v.toList.take i.val ++ v[i] ::
        (v.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          v[j] :: v.toList.drop (j.val + 1) := by
  have hi : i.val < v.toList.length := by
    simp [Vector.length_toList]
  have hjdrop : j.val - i.val - 1 < (v.toList.drop (i.val + 1)).length := by
    simp only [List.length_drop, Vector.length_toList]
    omega
  calc
    v.toList = v.toList.take i.val ++ v.toList.drop i.val := by
      exact (List.take_append_drop i.val v.toList).symm
    _ = v.toList.take i.val ++ v[i] :: v.toList.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hi]
      simp [Vector.getElem_toList]
    _ =
      v.toList.take i.val ++ v[i] ::
        (v.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          (v.toList.drop (i.val + 1)).drop (j.val - i.val - 1) := by
      rw [List.append_assoc]
      congr 1
      congr 1
      exact (List.take_append_drop (j.val - i.val - 1)
        (v.toList.drop (i.val + 1))).symm
    _ =
      v.toList.take i.val ++ v[i] ::
        (v.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          v[j] :: v.toList.drop (j.val + 1) := by
      have hmid : i.val + 1 + (j.val - i.val - 1) = j.val := by
        omega
      have hdrop : i.val + 1 + ((j.val - i.val - 1) + 1) = j.val + 1 := by
        omega
      rw [List.drop_eq_getElem_cons hjdrop]
      simp [List.drop_drop, Vector.getElem_toList, List.getElem_drop, hmid, hdrop]

/-- `transposePermutationValues_take_of_lt` identifies the unchanged prefix before the first transposed index. -/
private theorem transposePermutationValues_take_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    (transposePermutationValues perm i j).toList.take i.val =
      perm.toList.take i.val := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp [Vector.length_toList] at hk₁ hk₂
    have hk : k < n := by omega
    have hki : (⟨k, hk⟩ : Fin n) ≠ i := by
      intro h
      have : k = i.val := by simpa using congrArg Fin.val h
      omega
    have hkj : (⟨k, hk⟩ : Fin n) ≠ j := by
      intro h
      have : k = j.val := by simpa using congrArg Fin.val h
      omega
    calc
      (List.take i.val (transposePermutationValues perm i j).toList)[k] =
          (transposePermutationValues perm i j)[k]'hk := by
        simp [Vector.getElem_toList]
      _ = perm[k]'hk := by
        change (transposePermutationValues perm i j)[(⟨k, hk⟩ : Fin n)] =
          perm[(⟨k, hk⟩ : Fin n)]
        rw [transposePermutationValues_get]
        exact vector_get_fin_congr perm (finTranspose_of_ne i j ⟨k, hk⟩ hki hkj)
      _ = (List.take i.val perm.toList)[k] := by
        simp [Vector.getElem_toList]

/-- `transposePermutationValues_middle_of_lt` identifies the unchanged middle segment between two transposed indices. -/
private theorem transposePermutationValues_middle_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    ((transposePermutationValues perm i j).toList.drop (i.val + 1)).take
        (j.val - i.val - 1) =
      (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp [Vector.length_toList] at hk₁ hk₂
    have hrlt : i.val + 1 + k < n := by
      omega
    have hri : (⟨i.val + 1 + k, hrlt⟩ : Fin n) ≠ i := by
      intro h
      have : i.val + 1 + k = i.val := by simpa using congrArg Fin.val h
      omega
    have hrj : (⟨i.val + 1 + k, hrlt⟩ : Fin n) ≠ j := by
      intro h
      have : i.val + 1 + k = j.val := by simpa using congrArg Fin.val h
      omega
    calc
      (List.take (j.val - i.val - 1)
          (List.drop (i.val + 1) (transposePermutationValues perm i j).toList))[k] =
          (transposePermutationValues perm i j)[i.val + 1 + k]'hrlt := by
        simp [Vector.getElem_toList]
      _ = perm[i.val + 1 + k]'hrlt := by
        change (transposePermutationValues perm i j)[(⟨i.val + 1 + k, hrlt⟩ : Fin n)] =
          perm[(⟨i.val + 1 + k, hrlt⟩ : Fin n)]
        rw [transposePermutationValues_get]
        exact vector_get_fin_congr perm
          (finTranspose_of_ne i j ⟨i.val + 1 + k, hrlt⟩ hri hrj)
      _ =
          (List.take (j.val - i.val - 1) (List.drop (i.val + 1) perm.toList))[k] := by
        simp [Vector.getElem_toList]

/-- `transposePermutationValues_drop_of_lt` identifies the unchanged suffix after the second transposed index. -/
private theorem transposePermutationValues_drop_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    (transposePermutationValues perm i j).toList.drop (j.val + 1) =
      perm.toList.drop (j.val + 1) := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp [Vector.length_toList] at hk₁ hk₂
    have hrlt : j.val + 1 + k < n := by
      omega
    have hri : (⟨j.val + 1 + k, hrlt⟩ : Fin n) ≠ i := by
      intro h
      have : j.val + 1 + k = i.val := by simpa using congrArg Fin.val h
      omega
    have hrj : (⟨j.val + 1 + k, hrlt⟩ : Fin n) ≠ j := by
      intro h
      have : j.val + 1 + k = j.val := by simpa using congrArg Fin.val h
      omega
    calc
      (List.drop (j.val + 1) (transposePermutationValues perm i j).toList)[k] =
          (transposePermutationValues perm i j)[j.val + 1 + k]'hrlt := by
        simp [Vector.getElem_toList]
      _ = perm[j.val + 1 + k]'hrlt := by
        change (transposePermutationValues perm i j)[(⟨j.val + 1 + k, hrlt⟩ : Fin n)] =
          perm[(⟨j.val + 1 + k, hrlt⟩ : Fin n)]
        rw [transposePermutationValues_get]
        exact vector_get_fin_congr perm
          (finTranspose_of_ne i j ⟨j.val + 1 + k, hrlt⟩ hri hrj)
      _ = (List.drop (j.val + 1) perm.toList)[k] := by
        simp [Vector.getElem_toList]

/-- `transposePermutationValues_toList_of_lt` expands the list view when the left transposed index is strictly before the right one. -/
private theorem transposePermutationValues_toList_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    (transposePermutationValues perm i j).toList =
      perm.toList.take i.val ++ perm[j] ::
        (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          perm[i] :: perm.toList.drop (j.val + 1) := by
  rw [vector_toList_split_two (transposePermutationValues perm i j) hij]
  rw [transposePermutationValues_take_of_lt perm hij]
  rw [transposePermutationValues_middle_of_lt perm hij]
  rw [transposePermutationValues_drop_of_lt perm hij]
  have hi : (transposePermutationValues perm i j)[i] = perm[j] := by
    rw [transposePermutationValues_get]
    exact vector_get_fin_congr perm (finTranspose_left i j)
  have hj : (transposePermutationValues perm i j)[j] = perm[i] := by
    rw [transposePermutationValues_get]
    exact vector_get_fin_congr perm (finTranspose_right i j)
  rw [hi, hj]

/-- `transposePermutationValues_toList_of_gt` expands the list view when the right transposed index is strictly before the left one. -/
private theorem transposePermutationValues_toList_of_gt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hji : j.val < i.val) :
    (transposePermutationValues perm i j).toList =
      perm.toList.take j.val ++ perm[i] ::
        (perm.toList.drop (j.val + 1)).take (i.val - j.val - 1) ++
          perm[j] :: perm.toList.drop (i.val + 1) := by
  have hcomm : transposePermutationValues perm i j = transposePermutationValues perm j i := by
    apply Vector.ext
    intro r hr
    change (transposePermutationValues perm i j)[(⟨r, hr⟩ : Fin n)] =
      (transposePermutationValues perm j i)[(⟨r, hr⟩ : Fin n)]
    repeat rw [transposePermutationValues_get]
    by_cases hri : (⟨r, hr⟩ : Fin n) = i
    · subst i
      exact vector_get_fin_congr perm
        ((finTranspose_left ⟨r, hr⟩ j).trans
          (finTranspose_right j ⟨r, hr⟩).symm)
    · by_cases hrj : (⟨r, hr⟩ : Fin n) = j
      · subst j
        exact vector_get_fin_congr perm
          ((finTranspose_right i ⟨r, hr⟩).trans
            (finTranspose_left ⟨r, hr⟩ i).symm)
      · exact vector_get_fin_congr perm
          ((finTranspose_of_ne i j ⟨r, hr⟩ hri hrj).trans
            (finTranspose_of_ne j i ⟨r, hr⟩ hrj hri).symm)
  rw [hcomm]
  exact
    (transposePermutationValues_toList_of_lt perm (i := j) (j := i) hji)

/-- `transposePermutationValues_involutive` states that transposing the same two vector positions twice returns the original vector. -/
private theorem transposePermutationValues_involutive {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) :
    transposePermutationValues (transposePermutationValues perm i j) i j = perm := by
  apply Vector.ext
  intro r hr
  simp [transposePermutationValues, finTranspose_involutive]

/-- `transposePermutationValues_map_permutationVectors_perm` shows that mapping a fixed value transpose permutes `permutationVectors n`. -/
private theorem transposePermutationValues_map_permutationVectors_perm {n : Nat}
    (i j : Fin n) :
    ((permutationVectors n).map fun perm => transposePermutationValues perm i j).Perm
      (permutationVectors n) := by
  have hmapNodup :
      ((permutationVectors n).map fun perm => transposePermutationValues perm i j).Nodup := by
    exact list_nodup_map_of_injective
      (f := fun perm => transposePermutationValues perm i j)
      (fun a b h => by
        have h' := congrArg (fun perm => transposePermutationValues perm i j) h
        change
          transposePermutationValues (transposePermutationValues a i j) i j =
            transposePermutationValues (transposePermutationValues b i j) i j at h'
        rw [transposePermutationValues_involutive] at h'
        rw [transposePermutationValues_involutive] at h'
        exact h')
      permutationVectors_nodup_list
  apply (List.perm_ext_iff_of_nodup hmapNodup permutationVectors_nodup_list).mpr
  intro perm
  constructor
  · intro hmem
    simp only [List.mem_map] at hmem
    rcases hmem with ⟨pre, hpre, rfl⟩
    exact transposePermutationValues_mem_permutationVectors i j hpre
  · intro hmem
    simp only [List.mem_map]
    refine ⟨transposePermutationValues perm i j,
      transposePermutationValues_mem_permutationVectors i j hmem, ?_⟩
    exact transposePermutationValues_involutive perm i j

/-- Swap the values `i` and `j` inside a permutation vector, leaving positions
fixed. This models the column permutation induced by exchanging two columns. -/
def swapPermutationValues {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) : Vector (Fin n) n :=
  perm.map (finTranspose i j)

private theorem swapPermutationValues_get {n : Nat}
    (perm : Vector (Fin n) n) (i j r : Fin n) :
    (swapPermutationValues perm i j)[r] = finTranspose i j perm[r] := by
  simp [swapPermutationValues]

/-- Entrywise characterization of `swapPermutationValues`: occurrences of
`i` become `j`, occurrences of `j` become `i`, and all other values stay put. -/
theorem swapPermutationValues_get_if {n : Nat}
    (perm : Vector (Fin n) n) (i j r : Fin n) :
    (swapPermutationValues perm i j)[r] =
      if perm[r] = i then j else if perm[r] = j then i else perm[r] := by
  rw [swapPermutationValues_get]
  rfl

private theorem swapPermutationValues_toList_nodup {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) :
    (swapPermutationValues perm i j).toList.Nodup := by
  change (perm.map (finTranspose i j)).toList.Nodup
  rw [vector_toList_map]
  exact list_nodup_map_of_injective (finTranspose_injective i j) hnodup

private theorem swapPermutationValues_mem_permutationVectors {n : Nat}
    {perm : Vector (Fin n) n} (i j : Fin n)
    (hmem : perm ∈ permutationVectors n) :
    swapPermutationValues perm i j ∈ permutationVectors n := by
  apply permutationVectors_complete
  exact swapPermutationValues_toList_nodup perm i j (permutationVectors_nodup hmem)

private theorem swapPermutationValues_involutive {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) :
    swapPermutationValues (swapPermutationValues perm i j) i j = perm := by
  apply Vector.ext
  intro r hr
  simp [swapPermutationValues, finTranspose_involutive]

/-- `fin_mem_of_full_nodup` shows that a length-`n` nodup list of `Fin n`
values contains every `x : Fin n`, the pigeonhole fact that makes the
`inversePermutationValues` index lookup total. -/
private theorem fin_mem_of_full_nodup {n : Nat} {xs : List (Fin n)}
    (x : Fin n) (hlen : xs.length = n) (hnodup : xs.Nodup) :
    x ∈ xs := by
  by_cases hmem : x ∈ xs
  · exact hmem
  · exfalso
    have hsub : List.Subperm xs ((List.finRange n).erase x) := by
      apply List.subperm_of_subset hnodup
      intro y hy
      exact (List.mem_erase_of_ne (by
        intro hyx
        exact hmem (hyx ▸ hy))).2 (List.mem_finRange y)
    have hle : xs.length ≤ ((List.finRange n).erase x).length :=
      List.Subperm.length_le hsub
    have herase : ((List.finRange n).erase x).length = n - 1 := by
      rw [List.length_erase]
      simp [List.mem_finRange, List.length_finRange]
    rw [hlen, herase] at hle
    cases n with
    | zero => exact Fin.elim0 x
    | succ n => omega

/-- `fin_idxOf_lt_of_full_nodup` bounds `xs.idxOf x` below `xs.length` for a
full nodup list, supplying the `Fin n` index proof obligation for the
`inversePermutationValues` entries. -/
private theorem fin_idxOf_lt_of_full_nodup {n : Nat} {xs : List (Fin n)}
    (x : Fin n) (hlen : xs.length = n) (hnodup : xs.Nodup) :
    xs.idxOf x < xs.length := by
  exact List.idxOf_lt_length_of_mem (fin_mem_of_full_nodup x hlen hnodup)

/-- The inverse permutation vector: at value `c`, return the position where
`c` occurs in `perm`. -/
private def inversePermutationValues {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    Vector (Fin n) n :=
  Vector.ofFn fun c =>
    ⟨perm.toList.idxOf c,
      by
        simpa [Vector.length_toList] using
          fin_idxOf_lt_of_full_nodup c (by simp [Vector.length_toList]) hnodup⟩

/-- `inversePermutationValues_get_value` is the right-inverse law
`perm[inv[c]] = c`, recovering the value `c` by reading `perm` at the position
the inverse records for it. -/
private theorem inversePermutationValues_get_value {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) (c : Fin n) :
    perm[(inversePermutationValues perm hnodup)[c]] = c := by
  change
    perm.toList[(inversePermutationValues perm hnodup)[c].val]'(by
      simp [Vector.length_toList]) = c
  simp [inversePermutationValues]

/-- `inversePermutationValues_get_index` is the left-inverse law
`inv[perm[i]] = i`, recovering the position `i` from the value `perm` places
there. -/
private theorem inversePermutationValues_get_index {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) (i : Fin n) :
    (inversePermutationValues perm hnodup)[perm[i]] = i := by
  apply Fin.ext
  simp [inversePermutationValues]
  exact hnodup.idxOf_getElem i.val (by simp [Vector.length_toList])

/-- `inversePermutationValues_nodup` shows the inverse permutation vector is
itself nodup, so it is again a valid permutation usable in the determinant
sign-tracking expansion. -/
private theorem inversePermutationValues_nodup {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    (inversePermutationValues perm hnodup).toList.Nodup := by
  rw [vector_toList_eq_finRange_map_get]
  apply list_nodup_map_of_injective
  · intro a b h
    have hval :
        perm[(inversePermutationValues perm hnodup)[a]] =
          perm[(inversePermutationValues perm hnodup)[b]] :=
      congrArg (fun k => perm[k]) h
    rw [inversePermutationValues_get_value perm hnodup a] at hval
    rw [inversePermutationValues_get_value perm hnodup b] at hval
    exact hval
  · exact List.nodup_finRange n

/-- `inversePermutationValues_insertAt_last_castSucc` says inversion commutes
with inserting `Fin.last n`: the inverse of the extended permutation inserts the
original inverse (raised above `i`) at position `i` with value `Fin.last n`, the
recurrence step underlying the inversion-count tracking. -/
private theorem inversePermutationValues_insertAt_last_castSucc {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1)) (hnodup : v.toList.Nodup) :
    inversePermutationValues
        (insertAt (Fin.last n) (v.map Fin.castSucc) i)
        (insertAt_last_castSucc_nodup v i hnodup) =
      insertAt i ((inversePermutationValues v hnodup).map (raiseFinAbove i))
        (Fin.last n) := by
  apply Vector.ext
  intro k hk
  let c : Fin (n + 1) := ⟨k, hk⟩
  by_cases hlast : k = n
  · subst k
    have hleft :
        (inversePermutationValues
          (insertAt (Fin.last n) (v.map Fin.castSucc) i)
          (insertAt_last_castSucc_nodup v i hnodup))[Fin.last n] = i := by
      apply Fin.ext
      simp [inversePermutationValues]
      exact insertAt_last_castSucc_idxOf v i hnodup
    have hright :
        (insertAt i ((inversePermutationValues v hnodup).map (raiseFinAbove i))
          (Fin.last n))[Fin.last n] = i := by
      exact insertAt_get_self i ((inversePermutationValues v hnodup).map (raiseFinAbove i))
        (Fin.last n)
    exact hleft.trans hright.symm
  · have hklt : k < n := by omega
    let old : Fin n := ⟨k, hklt⟩
    have hc : c = old.castSucc := Fin.ext rfl
    have hget :
        (insertAt (Fin.last n) (v.map Fin.castSucc) i)[
            raiseFinAbove i ((inversePermutationValues v hnodup)[old])] =
          old.castSucc := by
      rw [insertAt_get_raiseFinAbove]
      simpa using congrArg Fin.castSucc (inversePermutationValues_get_value v hnodup old)
    have hleft :
        (inversePermutationValues
          (insertAt (Fin.last n) (v.map Fin.castSucc) i)
          (insertAt_last_castSucc_nodup v i hnodup))[old.castSucc] =
          raiseFinAbove i ((inversePermutationValues v hnodup)[old]) := by
      apply Fin.ext
      have hgetList :
          (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList[
              (raiseFinAbove i ((inversePermutationValues v hnodup)[old])).val] =
            old.castSucc := by
        simpa [Vector.getElem_toList] using hget
      have hidxOf :=
        (insertAt_last_castSucc_nodup v i hnodup).idxOf_getElem
          (raiseFinAbove i ((inversePermutationValues v hnodup)[old])).val
          (by simp [Vector.length_toList])
      have hidx :
          (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.idxOf old.castSucc =
            (raiseFinAbove i ((inversePermutationValues v hnodup)[old])).val := by
        exact hgetList ▸ hidxOf
      have hidx' :
          (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.idxOf
              (⟨old.val, by omega⟩ : Fin (n + 1)) =
            (raiseFinAbove i ((inversePermutationValues v hnodup)[old])).val := by
        simpa using hidx
      simpa [inversePermutationValues] using hidx'
    have hright :
        (insertAt i ((inversePermutationValues v hnodup).map (raiseFinAbove i))
          (Fin.last n))[old.castSucc] =
          raiseFinAbove i ((inversePermutationValues v hnodup)[old]) := by
      simpa using
        insertAt_last_get_castSucc i
          ((inversePermutationValues v hnodup).map (raiseFinAbove i)) old
    simpa [c, hc] using hleft.trans hright.symm

/-- `inversionCount_inversePermutationValues_insertAt_last_castSucc` gives the
inversion-count recurrence for the inverse permutation under the `Fin.last n`
insertion, adding `n - i` to the original count and so supplying the sign change
for the determinant's column-insertion step. -/
private theorem inversionCount_inversePermutationValues_insertAt_last_castSucc {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1)) (hnodup : v.toList.Nodup) :
    inversionCount
        (inversePermutationValues
          (insertAt (Fin.last n) (v.map Fin.castSucc) i)
          (insertAt_last_castSucc_nodup v i hnodup)).toList =
      inversionCount (inversePermutationValues v hnodup).toList + (n - i.val) := by
  rw [inversePermutationValues_insertAt_last_castSucc v i hnodup]
  rw [insertAt_last_toList]
  rw [vector_toList_map]
  rw [inversionCount_map_raiseFinAbove_append_self]
  rw [foldCount_full_nodup_ge i]
  · simp [Vector.length_toList]
  · exact inversePermutationValues_nodup v hnodup

private theorem inversionCount_inversePermutationValues_mod_two {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    inversionCount (inversePermutationValues perm hnodup).toList % 2 =
      inversionCount perm.toList % 2 := by
  induction n with
  | zero =>
      have hperm_nil : perm.toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      have hinv_nil : (inversePermutationValues perm hnodup).toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      simp [hperm_nil, hinv_nil, inversionCount]
  | succ n ih =>
      let k := perm.toList.idxOf (Fin.last n)
      have hk : k < n + 1 := by
        simpa [k, Vector.length_toList] using
          finLast_idxOf_lt_of_full_nodup (by simp [Vector.length_toList]) hnodup
      have hidx : perm.toList.idxOf (Fin.last n) = k := rfl
      let peeled := peelLastVector perm k hk hidx hnodup
      have hpeeled_nodup : peeled.toList.Nodup :=
        peelLastVector_nodup perm k hk hidx hnodup
      let pos : Fin (n + 1) := ⟨k, hk⟩
      have hinsert :
          insertAt (Fin.last n) (peeled.map Fin.castSucc) pos = perm := by
        simpa [peeled, pos] using
          insertAt_peelLastVector perm k hk hidx hnodup
      have hinv_count :
          inversionCount (inversePermutationValues perm hnodup).toList =
            inversionCount (inversePermutationValues peeled hpeeled_nodup).toList +
              (n - pos.val) := by
        have hnodup_insert :
            (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos).toList.Nodup :=
          insertAt_last_castSucc_nodup peeled pos hpeeled_nodup
        have hinv_eq :
            inversePermutationValues perm hnodup =
              inversePermutationValues
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos)
                hnodup_insert := by
          apply Vector.ext
          intro c hc
          simp [inversePermutationValues, hinsert]
        rw [hinv_eq]
        simpa [peeled, pos] using
          inversionCount_inversePermutationValues_insertAt_last_castSucc
            peeled pos hpeeled_nodup
      have hperm_count :
          inversionCount perm.toList =
            inversionCount peeled.toList + (n - pos.val) := by
        rw [← hinsert]
        rw [insertAt_toList, vector_toList_map]
        simpa [peeled, pos, Vector.length_toList] using
          inversionCount_insertIdx_castSucc_last_eq peeled.toList pos.val (by
            simp [Vector.length_toList, pos]
            omega)
      rw [hinv_count, hperm_count]
      have hih := ih peeled hpeeled_nodup
      omega

private theorem detSign_inversePermutationValues {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detSign (R := R) (inversePermutationValues perm hnodup) = detSign (R := R) perm := by
  unfold detSign
  rw [inversionCount_inversePermutationValues_mod_two perm hnodup]

private theorem inversePermutationValues_mem_permutationVectors {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    inversePermutationValues perm (permutationVectors_nodup hmem) ∈ permutationVectors n := by
  exact permutationVectors_complete
    (inversePermutationValues_nodup perm (permutationVectors_nodup hmem))

private theorem inversePermutationValues_involutive {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    inversePermutationValues
        (inversePermutationValues perm hnodup)
        (inversePermutationValues_nodup perm hnodup) = perm := by
  apply Vector.ext
  intro k hk
  let i : Fin n := ⟨k, hk⟩
  have h :=
    inversePermutationValues_get_index
      (inversePermutationValues perm hnodup)
      (inversePermutationValues_nodup perm hnodup) (perm[i])
  have hi := inversePermutationValues_get_index perm hnodup i
  have hleft :
      (inversePermutationValues
        (inversePermutationValues perm hnodup)
        (inversePermutationValues_nodup perm hnodup))[i] =
        (inversePermutationValues
          (inversePermutationValues perm hnodup)
          (inversePermutationValues_nodup perm hnodup))[
            (inversePermutationValues perm hnodup)[perm[i]]] :=
    congrArg
      (fun x =>
        (inversePermutationValues
          (inversePermutationValues perm hnodup)
          (inversePermutationValues_nodup perm hnodup))[x])
      hi.symm
  exact hleft.trans h

private def inversePermutationVector {n : Nat}
    (perm : Vector (Fin n) n) : Vector (Fin n) n :=
  if hnodup : perm.toList.Nodup then
    inversePermutationValues perm hnodup
  else
    perm

private theorem inversePermutationVector_eq {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    inversePermutationVector perm = inversePermutationValues perm hnodup := by
  simp [inversePermutationVector, hnodup]

private theorem inversePermutationVector_mem_permutationVectors {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    inversePermutationVector perm ∈ permutationVectors n := by
  rw [inversePermutationVector_eq perm (permutationVectors_nodup hmem)]
  exact inversePermutationValues_mem_permutationVectors hmem

private theorem inversePermutationVector_involutive_of_mem {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    inversePermutationVector (inversePermutationVector perm) = perm := by
  rw [inversePermutationVector_eq perm (permutationVectors_nodup hmem)]
  rw [inversePermutationVector_eq
    (inversePermutationValues perm (permutationVectors_nodup hmem))
    (inversePermutationValues_nodup perm (permutationVectors_nodup hmem))]
  exact inversePermutationValues_involutive perm (permutationVectors_nodup hmem)

private def composePermutationValues {n : Nat}
    (sigma tau : Vector (Fin n) n) : Vector (Fin n) n :=
  Vector.ofFn fun i => sigma[tau[i]]

private theorem composePermutationValues_get {n : Nat}
    (sigma tau : Vector (Fin n) n) (i : Fin n) :
    (composePermutationValues sigma tau)[i] = sigma[tau[i]] := by
  simp [composePermutationValues]

private theorem composePermutationValues_nodup {n : Nat}
    {sigma tau : Vector (Fin n) n}
    (hsigma : sigma.toList.Nodup) (htau : tau.toList.Nodup) :
    (composePermutationValues sigma tau).toList.Nodup := by
  rw [vector_toList_eq_finRange_map_get (composePermutationValues sigma tau)]
  apply list_nodup_map_of_injective
    (f := fun i : Fin n => (composePermutationValues sigma tau)[i])
    ?_ (List.nodup_finRange n)
  intro i j hij
  have hsigma_inj :
      Function.Injective (fun k : Fin n => sigma[k]) := by
    intro a b hab
    have ha_idx :
        sigma.toList.idxOf sigma[a] = a.val := by
      have ha_len : a.val < sigma.toList.length := by
        simp [Vector.length_toList]
      have hget : sigma.toList[a.val] = sigma[a] := by
        simp [Vector.toList]
      simpa [hget] using hsigma.idxOf_getElem a.val ha_len
    have hb_idx :
        sigma.toList.idxOf sigma[b] = b.val := by
      have hb_len : b.val < sigma.toList.length := by
        simp [Vector.length_toList]
      have hget : sigma.toList[b.val] = sigma[b] := by
        simp [Vector.toList]
      simpa [hget] using hsigma.idxOf_getElem b.val hb_len
    apply Fin.ext
    change sigma[a] = sigma[b] at hab
    rw [← ha_idx, ← hb_idx, hab]
  have htau_inj :
      Function.Injective (fun k : Fin n => tau[k]) := by
    intro a b hab
    have ha_idx :
        tau.toList.idxOf tau[a] = a.val := by
      have ha_len : a.val < tau.toList.length := by
        simp [Vector.length_toList]
      have hget : tau.toList[a.val] = tau[a] := by
        simp [Vector.toList]
      simpa [hget] using htau.idxOf_getElem a.val ha_len
    have hb_idx :
        tau.toList.idxOf tau[b] = b.val := by
      have hb_len : b.val < tau.toList.length := by
        simp [Vector.length_toList]
      have hget : tau.toList[b.val] = tau[b] := by
        simp [Vector.toList]
      simpa [hget] using htau.idxOf_getElem b.val hb_len
    apply Fin.ext
    change tau[a] = tau[b] at hab
    rw [← ha_idx, ← hb_idx, hab]
  exact htau_inj (hsigma_inj (by simpa [composePermutationValues] using hij))

private theorem composePermutationValues_mem_permutationVectors {n : Nat}
    {sigma tau : Vector (Fin n) n}
    (hsigma : sigma ∈ permutationVectors n)
    (htau : tau ∈ permutationVectors n) :
    composePermutationValues sigma tau ∈ permutationVectors n := by
  exact permutationVectors_complete
    (composePermutationValues_nodup
      (permutationVectors_nodup hsigma) (permutationVectors_nodup htau))

private theorem composePermutationValues_left_involutive_of_inverse {n : Nat}
    {sigma tau : Vector (Fin n) n}
    (hsigma : sigma ∈ permutationVectors n) :
    composePermutationValues
        (inversePermutationVector sigma)
        (composePermutationValues sigma tau) = tau := by
  apply Vector.ext
  intro k hk
  let i : Fin n := ⟨k, hk⟩
  change
    (composePermutationValues
        (inversePermutationVector sigma)
        (composePermutationValues sigma tau))[i] = tau[i]
  have hnodup := permutationVectors_nodup hsigma
  rw [inversePermutationVector_eq sigma hnodup]
  simpa [composePermutationValues] using
    inversePermutationValues_get_index sigma hnodup tau[i]

private theorem composePermutationValues_left_inverse_of_inverse {n : Nat}
    {sigma tau : Vector (Fin n) n}
    (hsigma : sigma ∈ permutationVectors n) :
    composePermutationValues sigma
        (composePermutationValues (inversePermutationVector sigma) tau) = tau := by
  have h :=
    composePermutationValues_left_involutive_of_inverse
      (sigma := inversePermutationVector sigma) (tau := tau)
      (inversePermutationVector_mem_permutationVectors hsigma)
  rw [inversePermutationVector_involutive_of_mem hsigma] at h
  exact h

private theorem composePermutationValues_left_map_permutationVectors_perm {n : Nat}
    (sigma : Vector (Fin n) n) (hsigma : sigma ∈ permutationVectors n) :
    ((permutationVectors n).map fun tau => composePermutationValues sigma tau).Perm
      (permutationVectors n) := by
  have hmapNodup :
      ((permutationVectors n).map fun tau => composePermutationValues sigma tau).Nodup := by
    exact list_nodup_map_on permutationVectors_nodup_list (by
      intro a ha b hb hab
      have h' := congrArg
        (fun perm => composePermutationValues (inversePermutationVector sigma) perm) hab
      exact
        (composePermutationValues_left_involutive_of_inverse (sigma := sigma) (tau := a) hsigma).symm.trans
          (h'.trans
            (composePermutationValues_left_involutive_of_inverse (sigma := sigma) (tau := b) hsigma)))
  apply (List.perm_ext_iff_of_nodup hmapNodup permutationVectors_nodup_list).mpr
  intro perm
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨pre, hpre, rfl⟩
    exact composePermutationValues_mem_permutationVectors hsigma hpre
  · intro hmem
    apply List.mem_map.mpr
    refine ⟨composePermutationValues (inversePermutationVector sigma) perm,
      ?_, ?_⟩
    · exact composePermutationValues_mem_permutationVectors
        (inversePermutationVector_mem_permutationVectors hsigma) hmem
    · exact composePermutationValues_left_inverse_of_inverse hsigma

private theorem inversePermutationVector_map_permutationVectors_perm {n : Nat} :
    ((permutationVectors n).map inversePermutationVector).Perm
      (permutationVectors n) := by
  have hmapNodup :
      ((permutationVectors n).map inversePermutationVector).Nodup := by
    exact list_nodup_map_on permutationVectors_nodup_list (by
      intro a ha b hb hab
      have h' := congrArg inversePermutationVector hab
      rw [inversePermutationVector_involutive_of_mem ha] at h'
      rw [inversePermutationVector_involutive_of_mem hb] at h'
      exact h')
  apply (List.perm_ext_iff_of_nodup hmapNodup permutationVectors_nodup_list).mpr
  intro perm
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨pre, hpre, rfl⟩
    exact inversePermutationVector_mem_permutationVectors hpre
  · intro hmem
    exact List.mem_map.mpr ⟨inversePermutationVector perm,
      inversePermutationVector_mem_permutationVectors hmem,
      inversePermutationVector_involutive_of_mem hmem⟩

private theorem permutationVectors_inverseVector_sum {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (f : Vector (Fin n) n → R) :
    (permutationVectors n).foldl
        (fun acc perm => acc + f (inversePermutationVector perm)) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + f perm) 0 := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + f (inversePermutationVector perm)) 0 =
      ((permutationVectors n).map inversePermutationVector).foldl
        (fun acc perm => acc + f perm) 0 := by
        simp [List.foldl_map]
    _ = (permutationVectors n).foldl (fun acc perm => acc + f perm) 0 := by
        exact foldl_det_sum_perm f inversePermutationVector_map_permutationVectors_perm 0

private theorem permutationVectors_composePermutationValues_left_sum {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (sigma : Vector (Fin n) n) (hsigma : sigma ∈ permutationVectors n)
    (f : Vector (Fin n) n → R) :
    (permutationVectors n).foldl
        (fun acc perm => acc + f (composePermutationValues sigma perm)) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + f perm) 0 := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + f (composePermutationValues sigma perm)) 0 =
      ((permutationVectors n).map fun perm => composePermutationValues sigma perm).foldl
        (fun acc perm => acc + f perm) 0 := by
        simp [List.foldl_map]
    _ = (permutationVectors n).foldl (fun acc perm => acc + f perm) 0 := by
        exact foldl_det_sum_perm f
          (composePermutationValues_left_map_permutationVectors_perm sigma hsigma) 0

private theorem finRange_map_perm_get_perm {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    ((List.finRange n).map fun i => perm[i]).Perm (List.finRange n) := by
  rw [← vector_toList_eq_finRange_map_get perm]
  apply (List.perm_ext_iff_of_nodup hnodup (List.nodup_finRange n)).mpr
  intro x
  constructor
  · intro _h
    exact List.mem_finRange x
  · intro _h
    exact fin_mem_of_full_nodup x (by simp [Vector.length_toList]) hnodup

private theorem detProduct_colPermute_vector {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (sigma tau : Vector (Fin n) n) :
    detProduct (ofFn fun r c => M[r][sigma[c]]) tau =
      detProduct M (composePermutationValues sigma tau) := by
  unfold detProduct
  apply foldl_det_product_congr
  intro r _hr
  simp [ofFn, composePermutationValues]

private theorem detProduct_transpose_inversePermutationValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detProduct M.transpose perm =
      detProduct M (inversePermutationValues perm hnodup) := by
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc r => acc * M.transpose[r][perm[r]]) 1 =
      (List.finRange n).foldl
        (fun acc r => acc * M[perm[r]][r]) 1 := by
        apply foldl_det_product_congr
        intro r _hmem
        simp [Matrix.transpose, Matrix.col]
    _ =
      ((List.finRange n).map fun r => perm[r]).foldl
        (fun acc c => acc * M[c][(inversePermutationValues perm hnodup)[c]]) 1 := by
        simp only [List.foldl_map]
        apply foldl_det_product_congr
        intro r _hmem
        exact congrArg (fun c => M[perm[r]][c])
          (inversePermutationValues_get_index perm hnodup r).symm
    _ =
      (List.finRange n).foldl
        (fun acc c => acc * M[c][(inversePermutationValues perm hnodup)[c]]) 1 := by
        exact foldl_det_product_perm
          (fun c => M[c][(inversePermutationValues perm hnodup)[c]])
          (finRange_map_perm_get_perm perm hnodup) 1

private theorem swapPermutationValues_eq_transposePermutationValues {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) :
    let pi : Fin n := ⟨perm.toList.idxOf i,
      by simpa [Vector.length_toList] using
        fin_idxOf_lt_of_full_nodup i (by simp [Vector.length_toList]) hnodup⟩
    let pj : Fin n := ⟨perm.toList.idxOf j,
      by simpa [Vector.length_toList] using
        fin_idxOf_lt_of_full_nodup j (by simp [Vector.length_toList]) hnodup⟩
    swapPermutationValues perm i j = transposePermutationValues perm pi pj := by
  dsimp
  apply Vector.ext
  intro r hr
  let pi : Fin n := ⟨perm.toList.idxOf i,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt_of_full_nodup i (by simp [Vector.length_toList]) hnodup⟩
  let pj : Fin n := ⟨perm.toList.idxOf j,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt_of_full_nodup j (by simp [Vector.length_toList]) hnodup⟩
  have hpi_get : perm[pi] = i := by
    have hlt : perm.toList.idxOf i < perm.toList.length := by
      simpa [pi, Vector.length_toList] using pi.isLt
    have hget : perm.toList[perm.toList.idxOf i]'hlt = i :=
      List.getElem_idxOf (x := i) (xs := perm.toList) hlt
    exact hget
  have hpj_get : perm[pj] = j := by
    have hlt : perm.toList.idxOf j < perm.toList.length := by
      simpa [pj, Vector.length_toList] using pj.isLt
    have hget : perm.toList[perm.toList.idxOf j]'hlt = j :=
      List.getElem_idxOf (x := j) (xs := perm.toList) hlt
    exact hget
  change (swapPermutationValues perm i j)[(⟨r, hr⟩ : Fin n)] =
    (transposePermutationValues perm pi pj)[(⟨r, hr⟩ : Fin n)]
  rw [swapPermutationValues_get, transposePermutationValues_get]
  by_cases hri : (⟨r, hr⟩ : Fin n) = pi
  · rw [hri]
    calc
      finTranspose i j perm[pi] = finTranspose i j i := by rw [hpi_get]
      _ = j := finTranspose_left i j
      _ = perm[pj] := hpj_get.symm
      _ = perm[finTranspose pi pj pi] := by
          exact congrArg (fun x => perm[x]) (finTranspose_left pi pj).symm
  · by_cases hrj : (⟨r, hr⟩ : Fin n) = pj
    · rw [hrj]
      calc
        finTranspose i j perm[pj] = finTranspose i j j := by rw [hpj_get]
        _ = i := finTranspose_right i j
        _ = perm[pi] := hpi_get.symm
        _ = perm[finTranspose pi pj pj] := by
            exact congrArg (fun x => perm[x]) (finTranspose_right pi pj).symm
    · have hnot_i : perm[(⟨r, hr⟩ : Fin n)] ≠ i := by
        intro hv
        have hridx : perm.toList.idxOf perm[(⟨r, hr⟩ : Fin n)] = r := by
          have hrlen : r < perm.toList.length := by
            simpa [Vector.length_toList] using hr
          exact hnodup.idxOf_getElem r hrlen
        have hval : r = pi.val := by
          calc
            r = perm.toList.idxOf perm[(⟨r, hr⟩ : Fin n)] := hridx.symm
            _ = perm.toList.idxOf i := by rw [hv]
            _ = pi.val := rfl
        exact hri (Fin.ext hval)
      have hnot_j : perm[(⟨r, hr⟩ : Fin n)] ≠ j := by
        intro hv
        have hridx : perm.toList.idxOf perm[(⟨r, hr⟩ : Fin n)] = r := by
          have hrlen : r < perm.toList.length := by
            simpa [Vector.length_toList] using hr
          exact hnodup.idxOf_getElem r hrlen
        have hval : r = pj.val := by
          calc
            r = perm.toList.idxOf perm[(⟨r, hr⟩ : Fin n)] := hridx.symm
            _ = perm.toList.idxOf j := by rw [hv]
            _ = pj.val := rfl
        exact hrj (Fin.ext hval)
      rw [finTranspose_of_ne i j perm[(⟨r, hr⟩ : Fin n)] hnot_i hnot_j]
      exact vector_get_fin_congr perm (finTranspose_of_ne pi pj ⟨r, hr⟩ hri hrj).symm

private theorem inversionCount_transposePermutationValues_parity {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    inversionCount (transposePermutationValues perm i j).toList % 2 =
      (inversionCount perm.toList + 1) % 2 := by
  have hval : i.val ≠ j.val := by
    intro hv
    exact h (Fin.ext hv)
  cases Nat.lt_or_gt_of_ne hval with
  | inl hij =>
      have hnodup_split :
          (perm.toList.take i.val ++ perm[i] ::
              (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
                perm[j] :: perm.toList.drop (j.val + 1)).Nodup := by
        rw [← vector_toList_split_two perm hij]
        exact hnodup
      have hpar :
          inversionCount
              (perm.toList.take i.val ++ perm[j] ::
                (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
                  perm[i] :: perm.toList.drop (j.val + 1)) %
              2 =
            (inversionCount perm.toList + 1) % 2 := by
        have hswap :=
          inversionCount_swap_separated_parity
            (perm.toList.take i.val)
            ((perm.toList.drop (i.val + 1)).take (j.val - i.val - 1))
            (perm.toList.drop (j.val + 1)) perm[i] perm[j] hnodup_split
        rw [← vector_toList_split_two perm hij] at hswap
        exact hswap
      rw [transposePermutationValues_toList_of_lt perm hij]
      exact hpar
  | inr hji =>
      have hnodup_split :
          (perm.toList.take j.val ++ perm[j] ::
              (perm.toList.drop (j.val + 1)).take (i.val - j.val - 1) ++
                perm[i] :: perm.toList.drop (i.val + 1)).Nodup := by
        rw [← vector_toList_split_two perm hji]
        exact hnodup
      have hpar :
          inversionCount
              (perm.toList.take j.val ++ perm[i] ::
                (perm.toList.drop (j.val + 1)).take (i.val - j.val - 1) ++
                  perm[j] :: perm.toList.drop (i.val + 1)) %
              2 =
            (inversionCount perm.toList + 1) % 2 := by
        have hswap :=
          inversionCount_swap_separated_parity
            (perm.toList.take j.val)
            ((perm.toList.drop (j.val + 1)).take (i.val - j.val - 1))
            (perm.toList.drop (i.val + 1)) perm[j] perm[i] hnodup_split
        rw [← vector_toList_split_two perm hji] at hswap
        exact hswap
      rw [transposePermutationValues_toList_of_gt perm hji]
      exact hpar

private theorem detProduct_rowSwap_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) (perm : Vector (Fin n) n) :
    detProduct (rowSwap M i j) perm =
      detProduct M (transposePermutationValues perm i j) := by
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc r => acc * (rowSwap M i j)[r][perm[r]]) 1 =
      (List.finRange n).foldl
        (fun acc r => acc * M[finTranspose i j r][perm[r]]) 1 := by
        apply foldl_det_product_congr
        intro r _hmem
        exact rowSwap_get_finTranspose M i j r h perm[r]
    _ =
      ((List.finRange n).map (finTranspose i j)).foldl
        (fun acc r => acc * M[r][perm[finTranspose i j r]]) 1 := by
        simp only [List.foldl_map]
        apply foldl_det_product_congr
        intro r _hmem
        exact congrArg (fun k => M[finTranspose i j r][k])
          (vector_get_fin_congr perm (finTranspose_involutive i j r).symm)
    _ =
      (List.finRange n).foldl
        (fun acc r => acc * M[r][perm[finTranspose i j r]]) 1 := by
        exact foldl_det_product_perm
          (fun r => M[r][perm[finTranspose i j r]])
          (finRange_map_finTranspose_perm i j) 1
    _ =
      (List.finRange n).foldl
        (fun acc r => acc * M[r][(transposePermutationValues perm i j)[r]]) 1 := by
        apply foldl_det_product_congr
        intro r _hmem
        exact congrArg (fun k => M[r][k])
          (transposePermutationValues_get perm i j r).symm

private theorem detSign_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    detSign (R := R) perm = -detSign (R := R) (transposePermutationValues perm i j) := by
  unfold detSign
  have hpar :=
    inversionCount_transposePermutationValues_parity perm i j hnodup h
  by_cases hp : inversionCount perm.toList % 2 = 0
  · have ht : inversionCount (transposePermutationValues perm i j).toList % 2 ≠ 0 := by
      omega
    simp [hp, ht]
    grind
  · have hpone : inversionCount perm.toList % 2 = 1 := by
      have hlt : inversionCount perm.toList % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    have ht : inversionCount (transposePermutationValues perm i j).toList % 2 = 0 := by
      omega
    simp [hp, ht]

/-- Swapping two distinct values in a duplicate-free permutation vector flips
the determinant sign. This is the sign bookkeeping for column swaps. -/
theorem detSign_swapPermutationValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    detSign (R := R) perm = -detSign (R := R) (swapPermutationValues perm i j) := by
  let pi : Fin n := ⟨perm.toList.idxOf i,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt_of_full_nodup i (by simp [Vector.length_toList]) hnodup⟩
  let pj : Fin n := ⟨perm.toList.idxOf j,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt_of_full_nodup j (by simp [Vector.length_toList]) hnodup⟩
  have hpij : pi ≠ pj := by
    intro hp
    have hpi_get : perm[pi] = i := by
      have hlt : perm.toList.idxOf i < perm.toList.length := by
        simpa [pi, Vector.length_toList] using pi.isLt
      have hget : perm.toList[perm.toList.idxOf i]'hlt = i :=
        List.getElem_idxOf (x := i) (xs := perm.toList) hlt
      exact hget
    have hpj_get : perm[pj] = j := by
      have hlt : perm.toList.idxOf j < perm.toList.length := by
        simpa [pj, Vector.length_toList] using pj.isLt
      have hget : perm.toList[perm.toList.idxOf j]'hlt = j :=
        List.getElem_idxOf (x := j) (xs := perm.toList) hlt
      exact hget
    exact h (by rw [← hpi_get, ← hpj_get, hp])
  have hswap :
      swapPermutationValues perm i j = transposePermutationValues perm pi pj := by
    simpa [pi, pj] using swapPermutationValues_eq_transposePermutationValues perm i j hnodup
  rw [hswap]
  exact detSign_transposeValues (R := R) perm pi pj hnodup hpij

/-- An adjacent swap at a descent strictly decreases inversion count by 1. -/
private theorem inversionCount_adjacent_swap_descent {n : Nat}
    (pre post : List (Fin n)) (a b : Fin n) (hba : b < a) :
    inversionCount (pre ++ a :: b :: post) =
      inversionCount (pre ++ b :: a :: post) + 1 := by
  rw [show pre ++ a :: b :: post = pre ++ ([a, b] ++ post) by simp]
  rw [show pre ++ b :: a :: post = pre ++ ([b, a] ++ post) by simp]
  have hcross :
      crossInversionCount pre ([a, b] ++ post) =
        crossInversionCount pre ([b, a] ++ post) := by
    repeat rw [crossInversionCount_append_right]
    rw [crossInversionCount_pair_swap_right]
  have htail :
      crossInversionCount [a, b] post =
        crossInversionCount [b, a] post :=
    crossInversionCount_pair_swap_left post a b
  rw [inversionCount_append pre ([a, b] ++ post)]
  rw [inversionCount_append pre ([b, a] ++ post)]
  rw [hcross]
  rw [inversionCount_append [a, b] post]
  rw [inversionCount_append [b, a] post]
  rw [htail]
  rw [inversionCount_pair a b]
  rw [inversionCount_pair b a]
  have hab' : ¬ a < b := by omega
  simp [hba, hab']
  omega

/-- For an adjacent descent pair in a permutation vector, transposing the two
positions decreases the inversion count by exactly one. -/
private theorem inversionCount_transposePermutationValues_adjacent_descent
    {n : Nat} (perm : Vector (Fin n) n)
    {i j : Fin n} (hij : i.val + 1 = j.val) (hdesc : perm[j] < perm[i]) :
    inversionCount perm.toList =
      inversionCount (transposePermutationValues perm i j).toList + 1 := by
  have hlt : i.val < j.val := by omega
  have hmid : j.val - i.val - 1 = 0 := by omega
  rw [vector_toList_split_two perm hlt, hmid,
      transposePermutationValues_toList_of_lt perm hlt, hmid]
  simp only [List.take_zero]
  -- After simplification, both lists have the form `pre ++ x :: y :: post`,
  -- and we apply the strict-decrease lemma.
  have h := inversionCount_adjacent_swap_descent
    (perm.toList.take i.val) (perm.toList.drop (j.val + 1))
    perm[i] perm[j] hdesc
  simpa using h

/-- Composition distributes over right transposition of positions. -/
private theorem composePermutationValues_transposePermutationValues_right
    {n : Nat} (sigma tau : Vector (Fin n) n) (i j : Fin n) :
    composePermutationValues sigma (transposePermutationValues tau i j) =
      transposePermutationValues (composePermutationValues sigma tau) i j := by
  apply Vector.ext
  intro k hk
  let r : Fin n := ⟨k, hk⟩
  show
    (composePermutationValues sigma (transposePermutationValues tau i j))[r] =
      (transposePermutationValues (composePermutationValues sigma tau) i j)[r]
  have h1 : (composePermutationValues sigma (transposePermutationValues tau i j))[r] =
      sigma[(transposePermutationValues tau i j)[r]] :=
    composePermutationValues_get sigma (transposePermutationValues tau i j) r
  have h2 : (transposePermutationValues tau i j)[r] = tau[finTranspose i j r] :=
    transposePermutationValues_get tau i j r
  have h3 : (transposePermutationValues (composePermutationValues sigma tau) i j)[r] =
      (composePermutationValues sigma tau)[finTranspose i j r] :=
    transposePermutationValues_get (composePermutationValues sigma tau) i j r
  have h4 : (composePermutationValues sigma tau)[finTranspose i j r] =
      sigma[tau[finTranspose i j r]] :=
    composePermutationValues_get sigma tau (finTranspose i j r)
  rw [h1, h3, h4]
  exact congrArg (fun x => sigma[x]) h2

private theorem exists_adjacent_descent {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup)
    (hpos : 0 < inversionCount perm.toList) :
    ∃ i : Fin n, ∃ hij : i.val + 1 < n,
      perm[(⟨i.val + 1, hij⟩ : Fin n)] < perm[i] := by
  induction n with
  | zero =>
      have hnil : perm.toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      simp [hnil, inversionCount] at hpos
  | succ n ih =>
      let k := perm.toList.idxOf (Fin.last n)
      have hk : k < n + 1 := by
        simpa [k, Vector.length_toList] using
          finLast_idxOf_lt_of_full_nodup (by simp [Vector.length_toList]) hnodup
      have hidx : perm.toList.idxOf (Fin.last n) = k := rfl
      let peeled := peelLastVector perm k hk hidx hnodup
      have hpeeled_nodup : peeled.toList.Nodup :=
        peelLastVector_nodup perm k hk hidx hnodup
      let pos : Fin (n + 1) := ⟨k, hk⟩
      have hinsert :
          insertAt (Fin.last n) (peeled.map Fin.castSucc) pos = perm := by
        simpa [peeled, pos] using
          insertAt_peelLastVector perm k hk hidx hnodup
      have hcount :
          inversionCount perm.toList =
            inversionCount peeled.toList + (n - pos.val) := by
        rw [← hinsert]
        rw [insertAt_toList, vector_toList_map]
        simpa [peeled, pos, Vector.length_toList] using
          inversionCount_insertIdx_castSucc_last_eq peeled.toList pos.val (by
            simp [Vector.length_toList, pos]
            omega)
      by_cases hlast : pos.val = n
      · have hpeeled_pos : 0 < inversionCount peeled.toList := by
          rw [hcount] at hpos
          omega
        rcases ih peeled hpeeled_nodup hpeeled_pos with ⟨i, hij, hdesc⟩
        have hijSucc : i.val + 1 < n + 1 := by omega
        let iUp : Fin (n + 1) := ⟨i.val, by omega⟩
        have hijUp : iUp.val + 1 < n + 1 := by simp [iUp, hijSucc]
        refine ⟨iUp, hijUp, ?_⟩
        · have hpos_eq : pos = Fin.last n := Fin.ext hlast
          have hget_next :
              perm[(⟨i.val + 1, hijSucc⟩ : Fin (n + 1))] =
                (peeled[(⟨i.val + 1, hij⟩ : Fin n)]).castSucc := by
            have hraw :
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))[
                    (⟨i.val + 1, hijSucc⟩ : Fin (n + 1))] =
                  (peeled[(⟨i.val + 1, hij⟩ : Fin n)]).castSucc := by
              have hraise :
                  raiseFinAbove (Fin.last n) (⟨i.val + 1, hij⟩ : Fin n) =
                    (⟨i.val + 1, hijSucc⟩ : Fin (n + 1)) := by
                apply Fin.ext
                simp [raiseFinAbove, hij]
              have hbase := insertAt_get_raiseFinAbove
                (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n)
                (⟨i.val + 1, hij⟩ : Fin n)
              have hbase' :
                  (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))[
                      raiseFinAbove (Fin.last n) (⟨i.val + 1, hij⟩ : Fin n)] =
                    (peeled[(⟨i.val + 1, hij⟩ : Fin n)]).castSucc := by
                simpa using hbase
              exact (vector_get_fin_congr
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))
                hraise).symm.trans hbase'
            have hinsert_last :
                insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n) = perm :=
              (congrArg (fun p => insertAt (Fin.last n) (peeled.map Fin.castSucc) p)
                hpos_eq).symm.trans hinsert
            have hperm :=
              congrArg
                (fun v : Vector (Fin (n + 1)) (n + 1) =>
                  v[(⟨i.val + 1, hijSucc⟩ : Fin (n + 1))])
                hinsert_last
            exact hperm.symm.trans hraw
          have hget_i :
                perm[iUp] = (peeled[i]).castSucc := by
              have hraw :
                  (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))[iUp] =
                    (peeled[i]).castSucc := by
                have hraise : raiseFinAbove (Fin.last n) i = iUp := by
                  apply Fin.ext
                  simp [raiseFinAbove, iUp]
                have hbase := insertAt_get_raiseFinAbove
                  (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n) i
                have hbase' :
                    (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))[
                        raiseFinAbove (Fin.last n) i] = (peeled[i]).castSucc := by
                  simpa using hbase
                exact (vector_get_fin_congr
                  (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))
                  hraise).symm.trans hbase'
              have hinsert_last :
                  insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n) = perm :=
                (congrArg (fun p => insertAt (Fin.last n) (peeled.map Fin.castSucc) p)
                  hpos_eq).symm.trans hinsert
              have hperm :=
                congrArg
                  (fun v : Vector (Fin (n + 1)) (n + 1) => v[iUp])
                  hinsert_last
              exact hperm.symm.trans hraw
          have hidx_up :
              (⟨iUp.val + 1, hijUp⟩ : Fin (n + 1)) =
                (⟨i.val + 1, hijSucc⟩ : Fin (n + 1)) := by
            apply Fin.ext
            simp [iUp]
          have hget_next_up :
              perm[(⟨iUp.val + 1, hijUp⟩ : Fin (n + 1))] =
                (peeled[(⟨i.val + 1, hij⟩ : Fin n)]).castSucc :=
            (vector_get_fin_congr perm hidx_up).trans hget_next
          rw [hget_next_up, hget_i]
          simpa [Fin.lt_def] using hdesc
      · have hk_lt_n : k < n := by
          have hk_le : k ≤ n := Nat.lt_succ_iff.mp hk
          have hpos_val : pos.val = k := rfl
          omega
        have hnextK : (⟨k, hk⟩ : Fin (n + 1)).val + 1 < n + 1 := by
          simpa using Nat.succ_lt_succ hk_lt_n
        refine ⟨(⟨k, hk⟩ : Fin (n + 1)), hnextK, ?_⟩
        · have hget_left : perm[(⟨k, hk⟩ : Fin (n + 1))] = Fin.last n := by
            have hraw :
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos)[pos] = Fin.last n :=
              insertAt_get_self (Fin.last n) (peeled.map Fin.castSucc) pos
            have hperm :=
              congrArg (fun v : Vector (Fin (n + 1)) (n + 1) => v[pos]) hinsert
            exact hperm.symm.trans hraw
          have hget_right :
              perm[(⟨k + 1, hnextK⟩ : Fin (n + 1))] =
                (peeled[(⟨k, hk_lt_n⟩ : Fin n)]).castSucc := by
            have hraise :
                raiseFinAbove pos (⟨k, hk_lt_n⟩ : Fin n) =
                  (⟨k + 1, hnextK⟩ : Fin (n + 1)) := by
              apply Fin.ext
              simp [raiseFinAbove, pos]
            have hraw :
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos)[
                    (⟨k + 1, hnextK⟩ : Fin (n + 1))] =
                  (peeled[(⟨k, hk_lt_n⟩ : Fin n)]).castSucc := by
              have hbase := insertAt_get_raiseFinAbove
                (Fin.last n) (peeled.map Fin.castSucc) pos (⟨k, hk_lt_n⟩ : Fin n)
              have hbase' :
                  (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos)[
                      raiseFinAbove pos (⟨k, hk_lt_n⟩ : Fin n)] =
                    (peeled[(⟨k, hk_lt_n⟩ : Fin n)]).castSucc := by
                simpa using hbase
              exact (vector_get_fin_congr
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos)
                hraise).symm.trans hbase'
            have hperm :=
              congrArg
                (fun v : Vector (Fin (n + 1)) (n + 1) =>
                  v[(⟨k + 1, hnextK⟩ : Fin (n + 1))])
                hinsert
            exact hperm.symm.trans hraw
          rw [hget_right, hget_left]
          simp [Fin.lt_def]

private theorem perm_eq_identity_of_inversionCount_zero {n : Nat}
    (perm : Vector (Fin n) n) (hmem : perm ∈ permutationVectors n)
    (hinv : inversionCount perm.toList = 0) :
    perm = Vector.ofFn fun i : Fin n => i := by
  induction n with
  | zero =>
      apply Vector.ext
      intro i hi
      omega
  | succ n ih =>
      have hnodup : perm.toList.Nodup := permutationVectors_nodup hmem
      let k := perm.toList.idxOf (Fin.last n)
      have hk : k < n + 1 := by
        simpa [k, Vector.length_toList] using
          finLast_idxOf_lt_of_full_nodup (by simp [Vector.length_toList]) hnodup
      have hidx : perm.toList.idxOf (Fin.last n) = k := rfl
      let peeled := peelLastVector perm k hk hidx hnodup
      have hpeeled_nodup : peeled.toList.Nodup :=
        peelLastVector_nodup perm k hk hidx hnodup
      have hpeeled_mem : peeled ∈ permutationVectors n :=
        permutationVectors_complete hpeeled_nodup
      let pos : Fin (n + 1) := ⟨k, hk⟩
      have hinsert :
          insertAt (Fin.last n) (peeled.map Fin.castSucc) pos = perm := by
        simpa [peeled, pos] using
          insertAt_peelLastVector perm k hk hidx hnodup
      have hcount :
          inversionCount perm.toList =
            inversionCount peeled.toList + (n - pos.val) := by
        rw [← hinsert]
        rw [insertAt_toList, vector_toList_map]
        simpa [peeled, pos, Vector.length_toList] using
          inversionCount_insertIdx_castSucc_last_eq peeled.toList pos.val (by
            simp [Vector.length_toList, pos]
            omega)
      have hpos : pos.val = n := by
        rw [hcount] at hinv
        omega
      have hpeeled_zero : inversionCount peeled.toList = 0 := by
        rw [hcount] at hinv
        omega
      have hpeeled_id : peeled = Vector.ofFn fun i : Fin n => i :=
        ih peeled hpeeled_mem hpeeled_zero
      rw [← hinsert, hpeeled_id]
      have hpos_eq : pos = Fin.last n := Fin.ext hpos
      rw [hpos_eq]
      have hvec :
          (Vector.ofFn fun i : Fin (n + 1) => i) =
            insertAt (Fin.last n)
              ((Vector.ofFn fun i : Fin n => i).map Fin.castSucc) (Fin.last n) := by
        apply Vector.ext
        intro r hr
        by_cases hlast : r = n
        · subst r
          simp [insertAt, List.getElem_insertIdx_self]
          exact Fin.ext rfl
        · have hr_lt : r < n := by omega
          simp [insertAt, List.getElem_insertIdx_of_lt, hr_lt]
      exact hvec.symm

/-- Multiplicativity of `detSign` under composition of permutation vectors.
The sign of a composed permutation equals the product of the component signs. -/
theorem detSign_composePermutationValues
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (sigma tau : Vector (Fin n) n)
    (hsigma : sigma ∈ permutationVectors n)
    (htau : tau ∈ permutationVectors n) :
    detSign (R := R) (composePermutationValues sigma tau) =
      detSign (R := R) sigma * detSign (R := R) tau := by
  suffices h : ∀ k, ∀ tau' : Vector (Fin n) n,
      tau' ∈ permutationVectors n →
      inversionCount tau'.toList = k →
      detSign (R := R) (composePermutationValues sigma tau') =
        detSign (R := R) sigma * detSign (R := R) tau' by
    exact h _ tau htau rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro tau' htau' hcount
    by_cases hk : k = 0
    · subst hk
      have hid : tau' = Vector.ofFn fun i : Fin n => i :=
        perm_eq_identity_of_inversionCount_zero tau' htau' hcount
      have hcompose_id :
          composePermutationValues sigma tau' = sigma := by
        rw [hid]
        apply Vector.ext
        intro r hr
        simp [composePermutationValues]
      rw [hcompose_id, hid, detSign_identity]
      grind
    · have hpos : 0 < inversionCount tau'.toList := by
        rw [hcount]; omega
      have hnodup_tau' := permutationVectors_nodup htau'
      obtain ⟨i, hij, hdesc⟩ := exists_adjacent_descent tau' hnodup_tau' hpos
      let j : Fin n := ⟨i.val + 1, hij⟩
      have hij_eq : i.val + 1 = j.val := rfl
      have hi_ne_j : i ≠ j := by
        intro h
        have hvals := congrArg Fin.val h
        have hjval : j.val = i.val + 1 := rfl
        omega
      have hdesc' : tau'[j] < tau'[i] := hdesc
      have hcount_dec :
          inversionCount tau'.toList =
            inversionCount (transposePermutationValues tau' i j).toList + 1 :=
        inversionCount_transposePermutationValues_adjacent_descent
          tau' hij_eq hdesc'
      have htau''_mem :
          transposePermutationValues tau' i j ∈ permutationVectors n :=
        transposePermutationValues_mem_permutationVectors i j htau'
      have hk_dec :
          inversionCount (transposePermutationValues tau' i j).toList < k := by
        omega
      have ih_eq :=
        ih _ hk_dec (transposePermutationValues tau' i j) htau''_mem rfl
      have hcompose :
          composePermutationValues sigma (transposePermutationValues tau' i j) =
            transposePermutationValues
              (composePermutationValues sigma tau') i j :=
        composePermutationValues_transposePermutationValues_right sigma tau' i j
      have hsign_tau :
          detSign (R := R) tau' =
            -detSign (R := R) (transposePermutationValues tau' i j) :=
        detSign_transposeValues (R := R) tau' i j hnodup_tau' hi_ne_j
      have hnodup_compose :
          (composePermutationValues sigma tau').toList.Nodup :=
        composePermutationValues_nodup
          (permutationVectors_nodup hsigma) hnodup_tau'
      have hsign_compose :
          detSign (R := R) (composePermutationValues sigma tau') =
            -detSign (R := R)
                (transposePermutationValues
                  (composePermutationValues sigma tau') i j) :=
        detSign_transposeValues (R := R)
          (composePermutationValues sigma tau') i j hnodup_compose hi_ne_j
      rw [hsign_compose, ← hcompose, ih_eq, hsign_tau]
      grind

/-- Inverse-orientation form of `detSign_composePermutationValues`: the sign of
`tau` is the sign of `sigma` times the sign of `composePermutationValues sigma tau`. -/
theorem detSign_eq_mul_detSign_composePermutationValues
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (sigma tau : Vector (Fin n) n)
    (hsigma : sigma ∈ permutationVectors n)
    (htau : tau ∈ permutationVectors n) :
    detSign (R := R) tau =
      detSign (R := R) sigma *
        detSign (R := R) (composePermutationValues sigma tau) := by
  have hmul :=
    detSign_composePermutationValues (R := R) sigma tau hsigma htau
  have hsq : detSign (R := R) sigma * detSign (R := R) sigma = 1 := by
    unfold detSign
    by_cases hp : inversionCount sigma.toList % 2 = 0
    · simp [hp]; grind
    · simp [hp]; grind
  rw [hmul]
  grind

private theorem swapPermutationValues_idxOf_left {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) :
    (swapPermutationValues perm i j).toList.idxOf i = perm.toList.idxOf j := by
  let pi : Fin n := ⟨perm.toList.idxOf i,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt_of_full_nodup i (by simp [Vector.length_toList]) hnodup⟩
  let pj : Fin n := ⟨perm.toList.idxOf j,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt_of_full_nodup j (by simp [Vector.length_toList]) hnodup⟩
  have hpi_get : perm[pi] = i := by
    have hlt : perm.toList.idxOf i < perm.toList.length := by
      simpa [pi, Vector.length_toList] using pi.isLt
    exact List.getElem_idxOf (x := i) (xs := perm.toList) hlt
  have hswap :
      swapPermutationValues perm i j = transposePermutationValues perm pi pj := by
    simpa [pi, pj] using swapPermutationValues_eq_transposePermutationValues perm i j hnodup
  have hpj_swap : (swapPermutationValues perm i j)[pj] = i := by
    rw [hswap, transposePermutationValues_get]
    calc
      perm[finTranspose pi pj pj] = perm[pi] := by
        exact congrArg (fun x => perm[x]) (finTranspose_right pi pj)
      _ = i := hpi_get
  have hnodupSwap := swapPermutationValues_toList_nodup perm i j hnodup
  have hpjLen : pj.val < (swapPermutationValues perm i j).toList.length := by
    simp [Vector.length_toList]
  have hidx :
      (swapPermutationValues perm i j).toList.idxOf
          ((swapPermutationValues perm i j).toList[pj.val]'hpjLen) = pj.val := by
    exact hnodupSwap.idxOf_getElem pj.val hpjLen
  have hget :
      (swapPermutationValues perm i j).toList[pj.val]'hpjLen = i := by
    exact hpj_swap
  rw [hget] at hidx
  exact hidx

private theorem swapPermutationValues_idxOf_right {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) :
    (swapPermutationValues perm i j).toList.idxOf j = perm.toList.idxOf i := by
  have hcomm : swapPermutationValues perm i j = swapPermutationValues perm j i := by
    apply Vector.ext
    intro r hr
    change (swapPermutationValues perm i j)[(⟨r, hr⟩ : Fin n)] =
      (swapPermutationValues perm j i)[(⟨r, hr⟩ : Fin n)]
    repeat rw [swapPermutationValues_get]
    by_cases hpi : perm[(⟨r, hr⟩ : Fin n)] = i
    · rw [hpi]
      exact (finTranspose_left i j).trans (finTranspose_right j i).symm
    · by_cases hpj : perm[(⟨r, hr⟩ : Fin n)] = j
      · rw [hpj]
        exact (finTranspose_right i j).trans (finTranspose_left j i).symm
      · exact
          (finTranspose_of_ne i j perm[(⟨r, hr⟩ : Fin n)] hpi hpj).trans
            (finTranspose_of_ne j i perm[(⟨r, hr⟩ : Fin n)] hpj hpi).symm
  rw [hcomm]
  exact swapPermutationValues_idxOf_left perm j i hnodup

private theorem permutation_idxOf_ne_of_ne {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    perm.toList.idxOf i ≠ perm.toList.idxOf j := by
  intro hidx
  have hiLt : perm.toList.idxOf i < perm.toList.length :=
    fin_idxOf_lt_of_full_nodup i (by simp [Vector.length_toList]) hnodup
  have hjLt : perm.toList.idxOf j < perm.toList.length :=
    fin_idxOf_lt_of_full_nodup j (by simp [Vector.length_toList]) hnodup
  have hiGet : perm.toList[perm.toList.idxOf i]'hiLt = i :=
    List.getElem_idxOf (x := i) (xs := perm.toList) hiLt
  have hjGet : perm.toList[perm.toList.idxOf j]'hjLt = j :=
    List.getElem_idxOf (x := j) (xs := perm.toList) hjLt
  apply h
  have hfin :
      (⟨perm.toList.idxOf i, hiLt⟩ : Fin perm.toList.length) =
        ⟨perm.toList.idxOf j, hjLt⟩ := Fin.ext hidx
  have hgeteq := congrArg (fun k : Fin perm.toList.length => perm.toList[k]) hfin
  exact hiGet.symm.trans (hgeteq.trans hjGet)

/-- When columns `src` and `dst` of `M` are equal, swapping those two values
in a permutation leaves the product term `detProduct M perm` unchanged. -/
private theorem detProduct_colDuplicate_swapValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst])
    (perm : Vector (Fin n) n) :
    detProduct M perm = detProduct M (swapPermutationValues perm src dst) := by
  unfold detProduct
  apply foldl_det_product_congr
  intro r _hmem
  by_cases hsrc : perm[r] = src
  · have hswap : (swapPermutationValues perm src dst)[r] = dst := by
      rw [swapPermutationValues_get]
      exact hsrc ▸ finTranspose_left src dst
    calc
      M[r][perm[r]] = M[r][src] := congrArg (fun c => M[r][c]) hsrc
      _ = M[r][dst] := hcol r
      _ = M[r][(swapPermutationValues perm src dst)[r]] :=
          (congrArg (fun c => M[r][c]) hswap).symm
  · by_cases hdst : perm[r] = dst
    · have hswap : (swapPermutationValues perm src dst)[r] = src := by
        rw [swapPermutationValues_get]
        exact hdst ▸ finTranspose_right src dst
      calc
        M[r][perm[r]] = M[r][dst] := congrArg (fun c => M[r][c]) hdst
        _ = M[r][src] := (hcol r).symm
        _ = M[r][(swapPermutationValues perm src dst)[r]] :=
            (congrArg (fun c => M[r][c]) hswap).symm
    · have hswap : (swapPermutationValues perm src dst)[r] = perm[r] := by
        rw [swapPermutationValues_get]
        exact finTranspose_of_ne src dst perm[r] hsrc hdst
      exact (congrArg (fun c => M[r][c]) hswap).symm

/-- For a nodup permutation with `src ≠ dst` and equal columns `src`, `dst`,
swapping those two values negates the signed determinant term `detTerm M perm`. -/
private theorem detTerm_colDuplicate_swapValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst])
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm M perm = -detTerm M (swapPermutationValues perm src dst) := by
  unfold detTerm
  rw [detProduct_colDuplicate_swapValues M src dst hcol perm]
  rw [detSign_swapPermutationValues (R := R) perm src dst hnodup h]
  grind

/-- `M` with column `dst` overwritten by a copy of column `src`. -/
private def colAddDuplicate {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) : Matrix R n n :=
  Matrix.ofFn fun r c => if c = dst then M[r][src] else M[r][c]

/-- Entrywise value of `colAddDuplicate M src dst`: column `dst` reads from
column `src`, every other column is left unchanged. -/
private theorem colAddDuplicate_get {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst r c : Fin n) :
    (colAddDuplicate M src dst)[r][c] = if c = dst then M[r][src] else M[r][c] := by
  simp [colAddDuplicate, Matrix.ofFn]

/-- Entrywise value of `colAdd M src dst c`: column `dst` becomes
`M[r][dst] + c · M[r][src]`, every other column is left unchanged. -/
private theorem colAdd_get {R : Type u} [Mul R] [Add R] {n : Nat}
    (M : Matrix R n n) (src dst r cidx : Fin n) (c : R) :
    (colAdd M src dst c)[r][cidx] =
      if cidx = dst then M[r][cidx] + c * M[r][src] else M[r][cidx] := by
  simp [colAdd, Matrix.ofFn]

/-- For a nodup permutation, the product term of `colAdd M src dst c` splits as
`detProduct M perm + c · detProduct (colAddDuplicate M src dst) perm`. -/
private theorem detProduct_colAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detProduct (colAdd M src dst c) perm =
      detProduct M perm + c * detProduct (colAddDuplicate M src dst) perm := by
  let pivot : Fin n := ⟨perm.toList.idxOf dst,
    by
      simpa [Vector.length_toList] using
        fin_idxOf_lt_of_full_nodup dst (by simp [Vector.length_toList]) hnodup⟩
  have hpivot : perm[pivot] = dst := by
    have hlt : perm.toList.idxOf dst < perm.toList.length :=
      fin_idxOf_lt_of_full_nodup dst (by simp [Vector.length_toList]) hnodup
    have hget : perm.toList[perm.toList.idxOf dst]'hlt = dst :=
      List.getElem_idxOf (x := dst) (xs := perm.toList) hlt
    change perm.toList[pivot.val]'(by simp [Vector.length_toList, pivot.isLt]) = dst
    simp [pivot] at hget ⊢
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc i => acc * (colAdd M src dst c)[i][perm[i]]) 1 =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            M[x][perm[x]] + c * (colAddDuplicate M src dst)[x][perm[x]]
          else
            M[x][perm[x]]) 1 := by
        apply foldl_det_product_congr
        intro x _hx
        rw [colAdd_get]
        by_cases hxp : x = pivot
        · subst x
          rw [if_pos hpivot, if_pos rfl, colAddDuplicate_get, if_pos hpivot]
        · rw [if_neg hxp]
          have hperm_ne : perm[x] ≠ dst := by
            intro hperm
            have hxidx : perm.toList.idxOf perm[x] = x.val := by
              simpa [Vector.getElem_toList, Vector.length_toList] using
                hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
            have hpidx : perm.toList.idxOf dst = pivot.val := rfl
            have hval : x.val = pivot.val := by
              rw [← hxidx, hperm, hpidx]
            exact hxp (Fin.ext hval)
          rw [if_neg hperm_ne]
    _ =
      (List.finRange n).foldl (fun acc x => acc * M[x][perm[x]]) 1 +
        c * (List.finRange n).foldl
          (fun acc x => acc * (colAddDuplicate M src dst)[x][perm[x]]) 1 := by
      exact
        foldl_det_product_single_add (R := R) (β := Fin n)
          (List.finRange n) pivot c
          (fun x => M[x][perm[x]])
          (fun x => (colAddDuplicate M src dst)[x][perm[x]])
          1 (List.mem_finRange pivot) (List.nodup_finRange n)
          (by
            intro x _hx hxp
            change (colAddDuplicate M src dst)[x][perm[x]] = M[x][perm[x]]
            rw [colAddDuplicate_get]
            have hperm_ne : perm[x] ≠ dst := by
              intro hperm
              have hxidx : perm.toList.idxOf perm[x] = x.val := by
                simpa [Vector.getElem_toList, Vector.length_toList] using
                  hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
              have hpidx : perm.toList.idxOf dst = pivot.val := rfl
              have hval : x.val = pivot.val := by
                rw [← hxidx, hperm, hpidx]
              exact hxp (Fin.ext hval)
            rw [if_neg hperm_ne])

/-- For a nodup permutation, the signed term of `colAdd M src dst c` splits as
`detTerm M perm + c · detTerm (colAddDuplicate M src dst) perm`. -/
private theorem detTerm_colAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (colAdd M src dst c) perm =
      detTerm M perm + c * detTerm (colAddDuplicate M src dst) perm := by
  unfold detTerm
  rw [detProduct_colAdd M src dst c perm hnodup]
  grind

private theorem detTerm_rowSwap_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (rowSwap M i j) perm =
      -detTerm M (transposePermutationValues perm i j) := by
  unfold detTerm
  rw [detProduct_rowSwap_transposeValues M i j h perm]
  rw [detSign_transposeValues (R := R) perm i j hnodup h]
  grind

private theorem permutationVectors_transposeValues_neg_sum {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (_h : i ≠ j) :
    (permutationVectors n).foldl
        (fun acc perm => acc + -detTerm M (transposePermutationValues perm i j)) 0 =
      -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + -detTerm M (transposePermutationValues perm i j)) 0 =
      ((permutationVectors n).map fun perm => transposePermutationValues perm i j).foldl
        (fun acc perm => acc + -detTerm M perm) 0 := by
        simp [List.foldl_map]
    _ =
      (permutationVectors n).foldl
        (fun acc perm => acc + -detTerm M perm) 0 := by
        exact foldl_det_sum_perm
          (fun perm => -detTerm M perm)
          (transposePermutationValues_map_permutationVectors_perm i j) 0
    _ =
      (permutationVectors n).foldl
        (fun acc perm => acc + (-1 : R) * detTerm M perm) 0 := by
        apply foldl_det_sum_congr
        intro perm _hmem
        grind
    _ =
      (-1 : R) *
        ((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
        exact foldl_det_sum_mul_left_zero (permutationVectors n) (-1 : R) (detTerm M)
    _ = -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
        grind

/-- The permutation-vector enumeration contributes `1` on the identity
matrix: all non-identity terms vanish and the identity vector appears once. -/
private theorem permutationVectors_identity_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (1 : Matrix R n n) perm) 0 = 1 := by
  induction n with
  | zero =>
      simp [permutationVectors, emptyVec, detTerm, detSign, detProduct, inversionCount]
      grind
  | succ n ih =>
      simp only [permutationVectors]
      rw [foldl_det_sum_flatMap]
      simp only [List.foldl_map, foldl_detTerm_identity_insertions]
      exact ih

/-- Row swapping pairs the permutation-vector Leibniz terms with opposite sign. -/
private theorem permutationVectors_rowSwap_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowSwap M i j) perm) 0 =
      -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowSwap M i j) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + -detTerm M (transposePermutationValues perm i j)) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        exact detTerm_rowSwap_transposeValues M i j h perm (permutationVectors_nodup hmem)
    _ = -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
        exact permutationVectors_transposeValues_neg_sum M i j h

/-- Scaling one matrix row scales each Leibniz term by the same scalar. -/
private theorem detTerm_rowScale {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detTerm (rowScale M i c) perm = c * detTerm M perm := by
  unfold detTerm
  rw [detProduct_rowScale]
  grind

/-- `M` with row `dst` overwritten by a copy of row `src` (row analogue of
`colAddDuplicate`). -/
private def rowAddDuplicate {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) : Matrix R n n :=
  M.set dst M[src]

/-- Entrywise value of `rowAdd M src dst c`: row `dst` becomes
`M[dst][k] + c · M[src][k]`, every other row is left unchanged. -/
private theorem rowAdd_get {R : Type u} [Mul R] [Add R] {n : Nat}
    (M : Matrix R n n) (src dst r : Fin n) (c : R) (k : Fin n) :
    (rowAdd M src dst c)[r][k] =
      if r = dst then M[dst][k] + c * M[src][k] else M[r][k] := by
  by_cases h : r = dst
  · subst r
    simp [rowAdd]
  · simp [rowAdd, h]
    have hval : dst.val ≠ r.val := by
      intro hval
      exact h (Fin.ext hval.symm)
    have hrow :
        (M.set dst (Vector.ofFn fun k => M[dst][k] + c * M[src][k]))[r] = M[r] := by
      exact
        (Vector.getElem_set_ne
          (xs := M) (x := Vector.ofFn fun k => M[dst][k] + c * M[src][k])
          dst.isLt r.isLt hval)
    simpa [rowAdd] using congrArg (fun row => row[k]) hrow

/-- Entrywise value of `rowAddDuplicate M src dst`: row `dst` reads from row
`src`, every other row is left unchanged. -/
private theorem rowAddDuplicate_get {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst r : Fin n) (k : Fin n) :
    (rowAddDuplicate M src dst)[r][k] =
      if r = dst then M[src][k] else M[r][k] := by
  by_cases h : r = dst
  · subst r
    simp [rowAddDuplicate]
  · simp [rowAddDuplicate, h]
    have hval : dst.val ≠ r.val := by
      intro hval
      exact h (Fin.ext hval.symm)
    have hrow : (M.set dst M[src])[r] = M[r] := by
      exact (Vector.getElem_set_ne (xs := M) (x := M[src]) dst.isLt r.isLt hval)
    simpa [rowAddDuplicate] using congrArg (fun row => row[k]) hrow

/-- The product term of `rowAdd M src dst c` splits as
`detProduct M perm + c · detProduct (rowAddDuplicate M src dst) perm`. -/
private theorem detProduct_rowAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detProduct (rowAdd M src dst c) perm =
      detProduct M perm + c * detProduct (rowAddDuplicate M src dst) perm := by
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc r => acc * (rowAdd M src dst c)[r][perm[r]]) 1 =
      (List.finRange n).foldl
        (fun acc r =>
          acc * if r = dst then
            M[r][perm[r]] + c * (rowAddDuplicate M src dst)[r][perm[r]]
          else
            M[r][perm[r]]) 1 := by
        apply foldl_det_product_congr
        intro r _hmem
        by_cases h : r = dst
        · subst r
          rw [rowAdd_get M src dst dst c perm[dst]]
          rw [rowAddDuplicate_get M src dst dst perm[dst]]
          simp
        · rw [rowAdd_get, rowAddDuplicate_get]
          simp [h]
    _ =
      (List.finRange n).foldl (fun acc r => acc * M[r][perm[r]]) 1 +
        c * (List.finRange n).foldl
          (fun acc r => acc * (rowAddDuplicate M src dst)[r][perm[r]]) 1 := by
        exact foldl_det_product_single_add
          (List.finRange n) dst c
          (fun r => M[r][perm[r]])
          (fun r => (rowAddDuplicate M src dst)[r][perm[r]]) 1
          (List.mem_finRange dst) (List.nodup_finRange n)
          (fun r _hmem hne => by
            change (rowAddDuplicate M src dst)[r][perm[r]] = M[r][perm[r]]
            rw [rowAddDuplicate_get]
            simp [hne])

/-- The signed term of `rowAdd M src dst c` splits as
`detTerm M perm + c · detTerm (rowAddDuplicate M src dst) perm`. -/
private theorem detTerm_rowAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detTerm (rowAdd M src dst c) perm =
      detTerm M perm + c * detTerm (rowAddDuplicate M src dst) perm := by
  unfold detTerm
  rw [detProduct_rowAdd]
  grind

private theorem foldl_det_sum_filter_split_start {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (p : β → Bool) (f : β → R) :
    ∀ a b : R,
      xs.foldl (fun acc x => acc + f x) (a + b) =
        (xs.filter p).foldl (fun acc x => acc + f x) a +
          (xs.filter fun x => !p x).foldl (fun acc x => acc + f x) b := by
  induction xs with
  | nil =>
      intro a b
      rfl
  | cons x xs ih =>
      intro a b
      simp only [List.foldl_cons]
      by_cases hp : p x
      · simp [hp]
        have hstart : a + b + f x = a + f x + b := by grind
        rw [hstart]
        exact ih (a + f x) b
      · simp [hp]
        have hstart : a + b + f x = a + (b + f x) := by grind
        rw [hstart]
        exact ih a (b + f x)

private theorem foldl_det_sum_filter_split {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (p : β → Bool) (f : β → R) :
    xs.foldl (fun acc x => acc + f x) 0 =
      (xs.filter p).foldl (fun acc x => acc + f x) 0 +
        (xs.filter fun x => !p x).foldl (fun acc x => acc + f x) 0 := by
  calc
    xs.foldl (fun acc x => acc + f x) 0 =
      xs.foldl (fun acc x => acc + f x) ((0 : R) + 0) := by
        have hzero : (0 : R) + 0 = 0 := by grind
        rw [hzero]
    _ =
      (xs.filter p).foldl (fun acc x => acc + f x) 0 +
        (xs.filter fun x => !p x).foldl (fun acc x => acc + f x) 0 := by
      exact foldl_det_sum_filter_split_start xs p f 0 0

private theorem foldl_det_sum_map {R : Type u} [Zero R] [Add R]
    {β : Type v} {γ : Type w} (xs : List β) (map : β → γ) (f : γ → R) :
    (xs.map map).foldl (fun acc x => acc + f x) 0 =
      xs.foldl (fun acc x => acc + f (map x)) 0 := by
  simp [List.foldl_map]

private theorem rowSwap_rowAddDuplicate_eq {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (_h : src ≠ dst) :
    rowSwap (rowAddDuplicate M src dst) src dst = rowAddDuplicate M src dst := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro k hk
  change
    (rowSwap (rowAddDuplicate M src dst) src dst)[(⟨r, hr⟩ : Fin n)][(⟨k, hk⟩ : Fin n)] =
      (rowAddDuplicate M src dst)[(⟨r, hr⟩ : Fin n)][(⟨k, hk⟩ : Fin n)]
  rw [rowSwap_get]
  let fr : Fin n := ⟨r, hr⟩
  let fk : Fin n := ⟨k, hk⟩
  change
    (if fr = dst then (rowAddDuplicate M src dst)[src][fk]
      else if fr = src then (rowAddDuplicate M src dst)[dst][fk]
      else (rowAddDuplicate M src dst)[fr][fk]) =
      (rowAddDuplicate M src dst)[fr][fk]
  by_cases hrd : fr = dst
  · rw [if_pos hrd]
    rw [rowAddDuplicate_get M src dst src fk, rowAddDuplicate_get M src dst fr fk]
    simp [hrd]
  · by_cases hrs : fr = src
    · rw [if_neg hrd, if_pos hrs]
      rw [rowAddDuplicate_get M src dst dst fk, rowAddDuplicate_get M src dst fr fk]
      simp [hrs]
    · simp [hrd, hrs]

private theorem detProduct_rowAddDuplicate_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (perm : Vector (Fin n) n) :
    detProduct (rowAddDuplicate M src dst) perm =
      detProduct (rowAddDuplicate M src dst)
        (transposePermutationValues perm src dst) := by
  have hswap :=
    detProduct_rowSwap_transposeValues
      (rowAddDuplicate M src dst) src dst h perm
  rw [rowSwap_rowAddDuplicate_eq M src dst h] at hswap
  exact hswap

private theorem detTerm_rowAddDuplicate_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (rowAddDuplicate M src dst) perm =
      -detTerm (rowAddDuplicate M src dst)
        (transposePermutationValues perm src dst) := by
  unfold detTerm
  rw [detProduct_rowAddDuplicate_transposeValues M src dst h perm]
  rw [detSign_transposeValues (R := R) perm src dst hnodup h]
  grind

private theorem permutationVectors_duplicateRow_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowAddDuplicate M src dst) perm) 0 = 0 := by
  let p : Vector (Fin n) n → Bool := fun perm => perm[src] < perm[dst]
  let term : Vector (Fin n) n → R := detTerm (rowAddDuplicate M src dst)
  have hsplit :=
    foldl_det_sum_filter_split (R := R) (permutationVectors n) p term
  rw [hsplit]
  have hright :
      ((permutationVectors n).filter fun perm => !p perm).foldl
          (fun acc perm => acc + term perm) 0 =
        ((permutationVectors n).filter p).foldl
          (fun acc perm =>
            acc + term (transposePermutationValues perm src dst)) 0 := by
    have hperm :
        (((permutationVectors n).filter p).map
            fun perm => transposePermutationValues perm src dst).Perm
          ((permutationVectors n).filter fun perm => !p perm) := by
      have hleftNodup :
          (((permutationVectors n).filter p).map
              fun perm => transposePermutationValues perm src dst).Nodup := by
        exact list_nodup_map_of_injective
          (f := fun perm => transposePermutationValues perm src dst)
          (fun a b hab => by
            have h' := congrArg (fun perm => transposePermutationValues perm src dst) hab
            change
              transposePermutationValues (transposePermutationValues a src dst) src dst =
                transposePermutationValues (transposePermutationValues b src dst) src dst at h'
            rw [transposePermutationValues_involutive] at h'
            rw [transposePermutationValues_involutive] at h'
            exact h')
          (permutationVectors_nodup_list.filter p)
      have hrightNodup :
          ((permutationVectors n).filter fun perm => !p perm).Nodup :=
        permutationVectors_nodup_list.filter _
      apply (List.perm_ext_iff_of_nodup hleftNodup hrightNodup).mpr
      intro perm
      constructor
      · intro hmem
        simp only [List.mem_map, List.mem_filter] at hmem ⊢
        rcases hmem with ⟨pre, ⟨hpreMem, hpreP⟩, rfl⟩
        constructor
        · exact transposePermutationValues_mem_permutationVectors src dst hpreMem
        · have hsrc : (transposePermutationValues pre src dst)[src] = pre[dst] := by
            rw [transposePermutationValues_get]
            exact vector_get_fin_congr pre (finTranspose_left src dst)
          have hdst : (transposePermutationValues pre src dst)[dst] = pre[src] := by
            rw [transposePermutationValues_get]
            exact vector_get_fin_congr pre (finTranspose_right src dst)
          simp [p] at hpreP ⊢
          calc
            (transposePermutationValues pre src dst)[dst] = pre[src] := hdst
            _ ≤ pre[dst] := by
              change pre[src].val ≤ pre[dst].val
              have hpreP' : pre[src].val < pre[dst].val := hpreP
              omega
            _ = (transposePermutationValues pre src dst)[src] := hsrc.symm
      · intro hmem
        simp only [List.mem_filter] at hmem
        rcases hmem with ⟨hpermMem, hpfalse⟩
        simp only [List.mem_map, List.mem_filter]
        refine ⟨transposePermutationValues perm src dst,
          ⟨transposePermutationValues_mem_permutationVectors src dst hpermMem, ?_⟩, ?_⟩
        · have hsrc : (transposePermutationValues perm src dst)[src] = perm[dst] := by
            rw [transposePermutationValues_get]
            exact vector_get_fin_congr perm (finTranspose_left src dst)
          have hdst : (transposePermutationValues perm src dst)[dst] = perm[src] := by
            rw [transposePermutationValues_get]
            exact vector_get_fin_congr perm (finTranspose_right src dst)
          simp [p] at hpfalse
          have hne_values : perm[src] ≠ perm[dst] := by
            intro hvals
            have hnodup := permutationVectors_nodup hpermMem
            have hsrcidx : perm.toList.idxOf perm[src] = src.val := by
              simpa [Vector.getElem_toList, Vector.length_toList] using
                hnodup.idxOf_getElem src.val (by simp [Vector.length_toList])
            have hdstidx : perm.toList.idxOf perm[dst] = dst.val := by
              simpa [Vector.getElem_toList, Vector.length_toList] using
                hnodup.idxOf_getElem dst.val (by simp [Vector.length_toList])
            have hvals_idx : perm.toList.idxOf perm[src] = perm.toList.idxOf perm[dst] := by
              rw [hvals]
            have hvaleq : src.val = dst.val := by
              rw [← hsrcidx, ← hdstidx]
              exact hvals_idx
            exact h (Fin.ext hvaleq)
          rw [show p (transposePermutationValues perm src dst) =
              decide ((transposePermutationValues perm src dst)[src] <
                (transposePermutationValues perm src dst)[dst]) by rfl]
          exact decide_eq_true (by
            rw [hsrc, hdst]
            change perm[dst].val < perm[src].val
            have hle : perm[dst].val ≤ perm[src].val := hpfalse
            have hneVal : perm[dst].val ≠ perm[src].val := by
              intro hval
              exact hne_values.symm (Fin.ext hval)
            omega)
        · exact transposePermutationValues_involutive perm src dst
    calc
      ((permutationVectors n).filter fun perm => !p perm).foldl
          (fun acc perm => acc + term perm) 0 =
        (((permutationVectors n).filter p).map
            fun perm => transposePermutationValues perm src dst).foldl
          (fun acc perm => acc + term perm) 0 := by
          exact (foldl_det_sum_perm term hperm 0).symm
      _ =
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (transposePermutationValues perm src dst)) 0 := by
          exact foldl_det_sum_map ((permutationVectors n).filter p)
            (fun perm => transposePermutationValues perm src dst) term
  rw [hright]
  calc
    ((permutationVectors n).filter p).foldl (fun acc perm => acc + term perm) 0 +
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (transposePermutationValues perm src dst)) 0 =
      ((permutationVectors n).filter p).foldl
          (fun acc perm =>
            acc + (term perm + term (transposePermutationValues perm src dst))) 0 := by
        exact (foldl_det_sum_add_zero
          ((permutationVectors n).filter p) term
          (fun perm => term (transposePermutationValues perm src dst))).symm
    _ = ((permutationVectors n).filter p).foldl (fun acc _ => acc + 0) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        simp only [term]
        rw [detTerm_rowAddDuplicate_transposeValues M src dst h perm]
        · grind
        · exact permutationVectors_nodup (List.mem_filter.mp hmem).1
    _ = 0 := by
        exact foldl_det_sum_zero ((permutationVectors n).filter p) 0

private theorem permutationVectors_duplicateCol_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst]) :
    (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 = 0 := by
  let p : Vector (Fin n) n → Bool :=
    fun perm => perm.toList.idxOf src < perm.toList.idxOf dst
  let term : Vector (Fin n) n → R := detTerm M
  have hsplit :=
    foldl_det_sum_filter_split (R := R) (permutationVectors n) p term
  rw [hsplit]
  have hright :
      ((permutationVectors n).filter fun perm => !p perm).foldl
          (fun acc perm => acc + term perm) 0 =
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (swapPermutationValues perm src dst)) 0 := by
    have hperm :
        (((permutationVectors n).filter p).map
            fun perm => swapPermutationValues perm src dst).Perm
          ((permutationVectors n).filter fun perm => !p perm) := by
      have hleftNodup :
          (((permutationVectors n).filter p).map
              fun perm => swapPermutationValues perm src dst).Nodup := by
        exact list_nodup_map_of_injective
          (f := fun perm => swapPermutationValues perm src dst)
          (fun a b hab => by
            have h' := congrArg (fun perm => swapPermutationValues perm src dst) hab
            change
              swapPermutationValues (swapPermutationValues a src dst) src dst =
                swapPermutationValues (swapPermutationValues b src dst) src dst at h'
            rw [swapPermutationValues_involutive] at h'
            rw [swapPermutationValues_involutive] at h'
            exact h')
          (permutationVectors_nodup_list.filter p)
      have hrightNodup :
          ((permutationVectors n).filter fun perm => !p perm).Nodup :=
        permutationVectors_nodup_list.filter _
      apply (List.perm_ext_iff_of_nodup hleftNodup hrightNodup).mpr
      intro perm
      constructor
      · intro hmem
        simp only [List.mem_map, List.mem_filter] at hmem ⊢
        rcases hmem with ⟨pre, ⟨hpreMem, hpreP⟩, rfl⟩
        constructor
        · exact swapPermutationValues_mem_permutationVectors src dst hpreMem
        · have hpreNodup := permutationVectors_nodup hpreMem
          simp [p] at hpreP ⊢
          rw [swapPermutationValues_idxOf_left pre src dst hpreNodup]
          rw [swapPermutationValues_idxOf_right pre src dst hpreNodup]
          omega
      · intro hmem
        simp only [List.mem_filter] at hmem
        rcases hmem with ⟨hpermMem, hpfalse⟩
        simp only [List.mem_map, List.mem_filter]
        refine ⟨swapPermutationValues perm src dst,
          ⟨swapPermutationValues_mem_permutationVectors src dst hpermMem, ?_⟩, ?_⟩
        · have hpermNodup := permutationVectors_nodup hpermMem
          simp [p] at hpfalse ⊢
          rw [swapPermutationValues_idxOf_left perm src dst hpermNodup]
          rw [swapPermutationValues_idxOf_right perm src dst hpermNodup]
          have hneIdx := permutation_idxOf_ne_of_ne perm src dst hpermNodup h
          omega
        · exact swapPermutationValues_involutive perm src dst
    calc
      ((permutationVectors n).filter fun perm => !p perm).foldl
          (fun acc perm => acc + term perm) 0 =
        (((permutationVectors n).filter p).map
            fun perm => swapPermutationValues perm src dst).foldl
          (fun acc perm => acc + term perm) 0 := by
          exact (foldl_det_sum_perm term hperm 0).symm
      _ =
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (swapPermutationValues perm src dst)) 0 := by
          exact foldl_det_sum_map ((permutationVectors n).filter p)
            (fun perm => swapPermutationValues perm src dst) term
  rw [hright]
  calc
    ((permutationVectors n).filter p).foldl (fun acc perm => acc + term perm) 0 +
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (swapPermutationValues perm src dst)) 0 =
      ((permutationVectors n).filter p).foldl
          (fun acc perm =>
            acc + (term perm + term (swapPermutationValues perm src dst))) 0 := by
        exact (foldl_det_sum_add_zero
          ((permutationVectors n).filter p) term
          (fun perm => term (swapPermutationValues perm src dst))).symm
    _ = ((permutationVectors n).filter p).foldl (fun acc _ => acc + 0) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        simp only [term]
        rw [detTerm_colDuplicate_swapValues M src dst h hcol perm]
        · grind
        · exact permutationVectors_nodup (List.mem_filter.mp hmem).1
    _ = 0 := by
        exact foldl_det_sum_zero ((permutationVectors n).filter p) 0

/-- The multilinear expansion of a column addition has zero total
duplicate-column contribution, so the Leibniz sum is unchanged. -/
private theorem permutationVectors_colAdd_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (colAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (colAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm =>
          acc + (detTerm M perm + c * detTerm (colAddDuplicate M src dst) perm)) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        exact detTerm_colAdd M src dst c perm (permutationVectors_nodup hmem)
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 +
        (permutationVectors n).foldl
          (fun acc perm => acc + c * detTerm (colAddDuplicate M src dst) perm) 0 := by
        exact foldl_det_sum_add_zero
          (permutationVectors n) (detTerm M)
          (fun perm => c * detTerm (colAddDuplicate M src dst) perm)
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 +
        c * (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (colAddDuplicate M src dst) perm) 0 := by
        rw [foldl_det_sum_mul_left_zero]
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
        rw [permutationVectors_duplicateCol_sum (colAddDuplicate M src dst) src dst h]
        · grind
        · intro r
          rw [colAddDuplicate_get, colAddDuplicate_get]
          simp

/-- The multilinear expansion of a row addition has zero total duplicate-row
contribution, so the Leibniz sum is unchanged. -/
private theorem permutationVectors_rowAdd_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm =>
          acc + (detTerm M perm + c * detTerm (rowAddDuplicate M src dst) perm)) 0 := by
        apply foldl_det_sum_congr
        intro perm _hmem
        exact detTerm_rowAdd M src dst c perm
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 +
        (permutationVectors n).foldl
          (fun acc perm => acc + c * detTerm (rowAddDuplicate M src dst) perm) 0 := by
        exact foldl_det_sum_add_zero
          (permutationVectors n) (detTerm M) (fun perm => c * detTerm (rowAddDuplicate M src dst) perm)
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 +
        c * (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (rowAddDuplicate M src dst) perm) 0 := by
        rw [foldl_det_sum_mul_left_zero]
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
        rw [permutationVectors_duplicateRow_sum M src dst h]
        grind

/-- The Leibniz sum for the identity matrix has exactly the identity
permutation as its nonzero contribution. -/
private theorem det_identity_leibniz {R : Type u} [Lean.Grind.CommRing R] {n : Nat} :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (1 : Matrix R n n) perm) 0 = 1 := by
  exact permutationVectors_identity_sum

/-- Swapping two rows pairs each Leibniz summand with the corresponding
transposed permutation and flips the computed inversion parity. -/
private theorem det_rowSwap_leibniz {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowSwap M i j) perm) 0 =
      -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
  exact permutationVectors_rowSwap_sum M i j h

/-- Scaling one row factors the scalar out of every nonzero Leibniz summand. -/
private theorem det_rowScale_leibniz {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowScale M i c) perm) 0 =
      c * ((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowScale M i c) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + c * detTerm M perm) 0 := by
        apply foldl_det_sum_congr
        intro perm _hmem
        exact detTerm_rowScale M i c perm
    _ = c * ((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
        exact foldl_det_sum_mul_left_zero (permutationVectors n) c (detTerm M)

/-- Adding a multiple of one row to a distinct row leaves the Leibniz sum
unchanged; the extra multilinear contribution has two equal rows. -/
private theorem det_rowAdd_leibniz {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
  exact permutationVectors_rowAdd_sum M src dst c h

/-- The determinant of the identity matrix is one. -/
@[grind =]
theorem det_one {R : Type u} [Lean.Grind.CommRing R] {n : Nat} :
    det (1 : Matrix R n n) = 1 := by
  simpa [det] using (det_identity_leibniz (R := R) (n := n))

/-- Swapping two distinct rows negates the determinant. -/
@[grind =]
theorem det_rowSwap {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    det (rowSwap M i j) = -det M := by
  simpa [det] using det_rowSwap_leibniz M i j h

/-- Scaling a row by `c` scales the determinant by `c`. -/
@[grind =]
theorem det_rowScale {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) :
    det (rowScale M i c) = c * det M := by
  simpa [det] using det_rowScale_leibniz M i c

/-- Adding a multiple of one row to a distinct row preserves the determinant. -/
@[grind =]
theorem det_rowAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    det (rowAdd M src dst c) = det M := by
  simpa [det] using det_rowAdd_leibniz M src dst c h

/-- The determinant is invariant under matrix transpose. -/
theorem det_transpose {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) :
    det M.transpose = det M := by
  unfold det
  calc
    (permutationVectors n).foldl (fun acc perm => acc + detTerm M.transpose perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + detTerm M (inversePermutationVector perm)) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        have hnodup := permutationVectors_nodup hmem
        rw [inversePermutationVector_eq perm hnodup]
        unfold detTerm
        rw [detProduct_transpose_inversePermutationValues M perm hnodup]
        rw [← detSign_inversePermutationValues (R := R) perm hnodup]
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
        exact permutationVectors_inverseVector_sum (R := R) (n := n) (fun perm => detTerm M perm)

/-- Cofactors commute with transpose after swapping the row and column
indices. -/
theorem cofactor_transpose {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row col : Fin (n + 1)) :
    cofactor M.transpose row col = cofactor M col row := by
  unfold cofactor
  have hsign :
      cofactorSign (R := R) row col = cofactorSign (R := R) col row := by
    unfold cofactorSign
    have hsum : row.val + col.val = col.val + row.val := Nat.add_comm _ _
    rw [hsum]
  rw [hsign]
  rw [deleteRowCol_transpose]
  rw [det_transpose]

/-- Diagonal-product formula for the determinant of a lower-triangular matrix
(entries above the diagonal are zero). Derived from the upper-triangular form
via `det_transpose`. -/
theorem det_lowerTriangular_eq_finFoldl_diag
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat} (M : Matrix R n n)
    (hzero : ∀ i j : Fin n, i.val < j.val → M[i][j] = 0) :
    det M = Fin.foldl n (fun acc i => acc * M[i][i]) 1 := by
  rw [← det_transpose M]
  have htransposeZero :
      ∀ i j : Fin n, j.val < i.val → M.transpose[i][j] = 0 := by
    intro i j hij
    have hentry : M.transpose[i][j] = M[j][i] := by
      simp [transpose, col]
    rw [hentry]
    exact hzero j i hij
  rw [det_upperTriangular_eq_finFoldl_diag M.transpose htransposeZero]
  have hdiag : ∀ i : Fin n, M.transpose[i][i] = M[i][i] := by
    intro i
    simp [transpose, col]
  -- Rewrite the foldl over `M.transpose[i][i]` to `M[i][i]`.
  rw [Fin.foldl_eq_foldl_finRange, Fin.foldl_eq_foldl_finRange]
  apply foldl_acc_congr
  intro acc i _hmem
  rw [hdiag]

/-- The determinant of a lower-triangular square matrix as a `List.foldl`
product over the diagonal indices in `Fin.finRange`. -/
theorem det_lowerTriangular_eq_foldl_diag
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat} (M : Matrix R n n)
    (hzero : ∀ i j : Fin n, i.val < j.val → M[i][j] = 0) :
    det M = (List.finRange n).foldl (fun acc i => acc * M[i][i]) 1 := by
  rw [det_lowerTriangular_eq_finFoldl_diag M hzero]
  rw [Fin.foldl_eq_foldl_finRange]

/-- Permuting columns multiplies the determinant by the sign of the column permutation. -/
theorem det_colPermute_vector {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (sigma : Vector (Fin n) n)
    (hsigma : sigma ∈ permutationVectors n) :
    det ((ofFn fun r c => M[r][sigma[c]]) : Matrix R n n) =
      detSign (R := R) sigma * det M := by
  unfold det
  calc
    (permutationVectors n).foldl
        (fun acc tau =>
          acc + detTerm ((ofFn fun r c => M[r][sigma[c]]) : Matrix R n n) tau) 0 =
      (permutationVectors n).foldl
        (fun acc tau =>
          acc + detSign (R := R) sigma *
            detTerm M (composePermutationValues sigma tau)) 0 := by
        apply foldl_det_sum_congr
        intro tau htau
        unfold detTerm
        rw [detProduct_colPermute_vector]
        rw [detSign_eq_mul_detSign_composePermutationValues
          (R := R) sigma tau hsigma htau]
        grind
    _ =
      detSign (R := R) sigma *
        (permutationVectors n).foldl
          (fun acc tau => acc + detTerm M (composePermutationValues sigma tau)) 0 := by
        exact foldl_det_sum_mul_left_zero
          (permutationVectors n) (detSign (R := R) sigma)
          (fun tau => detTerm M (composePermutationValues sigma tau))
    _ =
      detSign (R := R) sigma *
        (permutationVectors n).foldl (fun acc tau => acc + detTerm M tau) 0 := by
        rw [permutationVectors_composePermutationValues_left_sum
          (R := R) sigma hsigma (fun tau => detTerm M tau)]

/-- Swapping two columns negates determinant. -/
theorem det_colSwap {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    det (ofFn fun r c => M[r][finTranspose i j c]) = -det M := by
  let C : Matrix R n n := ofFn fun r c => M[r][finTranspose i j c]
  have htranspose : C.transpose = rowSwap M.transpose i j := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro c hc
    let rr : Fin n := ⟨r, hr⟩
    let cc : Fin n := ⟨c, hc⟩
    change C.transpose[rr][cc] = (rowSwap M.transpose i j)[rr][cc]
    rw [rowSwap_get_finTranspose M.transpose i j rr h cc]
    rw [show C.transpose[rr][cc] = C[cc][rr] by simp [Matrix.transpose, Matrix.col]]
    rw [show C[cc][rr] = M[cc][finTranspose i j rr] by simp [C, ofFn]]
    simp [Matrix.transpose, Matrix.col]
  calc
    det C = det C.transpose := (det_transpose C).symm
    _ = det (rowSwap M.transpose i j) := by rw [htranspose]
    _ = -det M.transpose := det_rowSwap M.transpose i j h
    _ = -det M := by rw [det_transpose M]

/-- Adding a multiple of one column to a distinct column preserves determinant. -/
theorem det_colAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    det (colAdd M src dst c) = det M := by
  simpa [det] using permutationVectors_colAdd_sum M src dst c h

/-- Replace one column of a square matrix by the supplied column function. -/
def colReplace {R : Type u} {n : Nat} (M : Matrix R n n) (dst : Fin n)
    (v : Fin n → R) : Matrix R n n :=
  Matrix.ofFn fun r c => if c = dst then v r else M[r][c]

/-- Entrywise characterization of `colReplace`: the destination column is
read from the replacement function and every other column is read from `M`. -/
theorem colReplace_get {R : Type u} {n : Nat} (M : Matrix R n n) (dst r c : Fin n)
    (v : Fin n → R) :
    (colReplace M dst v)[r][c] = if c = dst then v r else M[r][c] := by
  simp [colReplace, Matrix.ofFn]

/-- The per-permutation product `detProduct` is additive in the replaced
column: splitting that column's entries as `v + w` splits the product as a sum. -/
private theorem detProduct_colReplace_add {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detProduct (colReplace M dst (fun r => v r + w r)) perm =
      detProduct (colReplace M dst v) perm +
        detProduct (colReplace M dst w) perm := by
  let pivot : Fin n := ⟨perm.toList.idxOf dst,
    by
      simpa [Vector.length_toList] using
        fin_idxOf_lt_of_full_nodup dst (by simp [Vector.length_toList]) hnodup⟩
  have hpivot : perm[pivot] = dst := by
    have hlt : perm.toList.idxOf dst < perm.toList.length :=
      fin_idxOf_lt_of_full_nodup dst (by simp [Vector.length_toList]) hnodup
    have hget : perm.toList[perm.toList.idxOf dst]'hlt = dst :=
      List.getElem_idxOf (x := dst) (xs := perm.toList) hlt
    change perm.toList[pivot.val]'(by simp [Vector.length_toList, pivot.isLt]) = dst
    simp [pivot] at hget ⊢
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc i => acc * (colReplace M dst (fun r => v r + w r))[i][perm[i]]) 1 =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            (colReplace M dst v)[x][perm[x]] + (colReplace M dst w)[x][perm[x]]
          else
            (colReplace M dst v)[x][perm[x]]) 1 := by
        apply foldl_det_product_congr
        intro x _hx
        rw [colReplace_get, colReplace_get, colReplace_get]
        by_cases hxp : x = pivot
        · subst x
          rw [if_pos hpivot, if_pos hpivot, if_pos hpivot, if_pos rfl]
        · rw [if_neg hxp]
          have hperm_ne : perm[x] ≠ dst := by
            intro hperm
            have hxidx : perm.toList.idxOf perm[x] = x.val := by
              simpa [Vector.getElem_toList, Vector.length_toList] using
                hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
            have hpidx : perm.toList.idxOf dst = pivot.val := rfl
            have hval : x.val = pivot.val := by
              rw [← hxidx, hperm, hpidx]
            exact hxp (Fin.ext hval)
          change (if perm[x] = dst then v x + w x else M[x][perm[x]]) =
            (if perm[x] = dst then v x else M[x][perm[x]])
          rw [if_neg hperm_ne, if_neg hperm_ne]
    _ =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            (colReplace M dst v)[x][perm[x]] + (1 : R) * (colReplace M dst w)[x][perm[x]]
          else
            (colReplace M dst v)[x][perm[x]]) 1 := by
        apply foldl_det_product_congr
        intro x _hx
        by_cases hxp : x = pivot
        · rw [if_pos hxp]
          grind
        · simp [hxp]
    _ =
      (List.finRange n).foldl
          (fun acc x => acc * (colReplace M dst v)[x][perm[x]]) 1 +
        (1 : R) * (List.finRange n).foldl
          (fun acc x => acc * (colReplace M dst w)[x][perm[x]]) 1 := by
        exact
          foldl_det_product_single_add (R := R) (β := Fin n)
            (List.finRange n) pivot (1 : R)
            (fun x => (colReplace M dst v)[x][perm[x]])
            (fun x => (colReplace M dst w)[x][perm[x]])
            1 (List.mem_finRange pivot) (List.nodup_finRange n)
            (by
              intro x _hx hxp
              have hperm_ne : perm[x] ≠ dst := by
                intro hperm
                have hxidx : perm.toList.idxOf perm[x] = x.val := by
                  simpa [Vector.getElem_toList, Vector.length_toList] using
                    hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
                have hpidx : perm.toList.idxOf dst = pivot.val := rfl
                have hval : x.val = pivot.val := by
                  rw [← hxidx, hperm, hpidx]
                exact hxp (Fin.ext hval)
              change (colReplace M dst w)[x][perm[x]] =
                (colReplace M dst v)[x][perm[x]]
              rw [colReplace_get, colReplace_get]
              change (if perm[x] = dst then w x else M[x][perm[x]]) =
                (if perm[x] = dst then v x else M[x][perm[x]])
              rw [if_neg hperm_ne, if_neg hperm_ne])
    _ =
      (List.finRange n).foldl
          (fun acc x => acc * (colReplace M dst v)[x][perm[x]]) 1 +
        (List.finRange n).foldl
          (fun acc x => acc * (colReplace M dst w)[x][perm[x]]) 1 := by
        grind

/-- The per-permutation product `detProduct` is homogeneous in the replaced
column: scaling that column's entries by `c` scales the product by `c`. -/
private theorem detProduct_colReplace_smul {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (c : R) (v : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detProduct (colReplace M dst (fun r => c * v r)) perm =
      c * detProduct (colReplace M dst v) perm := by
  let pivot : Fin n := ⟨perm.toList.idxOf dst,
    by
      simpa [Vector.length_toList] using
        fin_idxOf_lt_of_full_nodup dst (by simp [Vector.length_toList]) hnodup⟩
  have hpivot : perm[pivot] = dst := by
    have hlt : perm.toList.idxOf dst < perm.toList.length :=
      fin_idxOf_lt_of_full_nodup dst (by simp [Vector.length_toList]) hnodup
    have hget : perm.toList[perm.toList.idxOf dst]'hlt = dst :=
      List.getElem_idxOf (x := dst) (xs := perm.toList) hlt
    change perm.toList[pivot.val]'(by simp [Vector.length_toList, pivot.isLt]) = dst
    simp [pivot] at hget ⊢
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc i => acc * (colReplace M dst (fun r => c * v r))[i][perm[i]]) 1 =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            c * (colReplace M dst v)[x][perm[x]]
          else
            (colReplace M dst v)[x][perm[x]]) 1 := by
        apply foldl_det_product_congr
        intro x _hx
        rw [colReplace_get, colReplace_get]
        by_cases hxp : x = pivot
        · subst x
          rw [if_pos hpivot, if_pos hpivot, if_pos rfl]
        · rw [if_neg hxp]
          have hperm_ne : perm[x] ≠ dst := by
            intro hperm
            have hxidx : perm.toList.idxOf perm[x] = x.val := by
              simpa [Vector.getElem_toList, Vector.length_toList] using
                hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
            have hpidx : perm.toList.idxOf dst = pivot.val := rfl
            have hval : x.val = pivot.val := by
              rw [← hxidx, hperm, hpidx]
            exact hxp (Fin.ext hval)
          change (if perm[x] = dst then c * v x else M[x][perm[x]]) =
            (if perm[x] = dst then v x else M[x][perm[x]])
          rw [if_neg hperm_ne, if_neg hperm_ne]
    _ =
      c * (List.finRange n).foldl
          (fun acc x => acc * (colReplace M dst v)[x][perm[x]]) 1 := by
        exact
          foldl_det_product_single_scale (R := R) (β := Fin n)
            (List.finRange n) pivot c
            (fun x => (colReplace M dst v)[x][perm[x]])
            1 (List.mem_finRange pivot) (List.nodup_finRange n)

/-- The signed Leibniz term `detTerm` is additive in the replaced column:
splitting that column's entries as `v + w` splits the term as a sum. -/
private theorem detTerm_colReplace_add {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (colReplace M dst (fun r => v r + w r)) perm =
      detTerm (colReplace M dst v) perm + detTerm (colReplace M dst w) perm := by
  unfold detTerm
  rw [detProduct_colReplace_add M dst v w perm hnodup]
  grind

/-- The signed Leibniz term `detTerm` is homogeneous in the replaced column:
scaling that column's entries by `c` scales the term by `c`. -/
private theorem detTerm_colReplace_smul {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (c : R) (v : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (colReplace M dst (fun r => c * v r)) perm =
      c * detTerm (colReplace M dst v) perm := by
  unfold detTerm
  rw [detProduct_colReplace_smul M dst c v perm hnodup]
  grind

/-- Determinant linearity in one replaced column, additive form. -/
theorem det_colReplace_add {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R) :
    det (colReplace M dst (fun r => v r + w r)) =
      det (colReplace M dst v) + det (colReplace M dst w) := by
  simp [det]
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (colReplace M dst (fun r => v r + w r)) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm =>
          acc + (detTerm (colReplace M dst v) perm +
            detTerm (colReplace M dst w) perm)) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        exact detTerm_colReplace_add M dst v w perm (permutationVectors_nodup hmem)
    _ =
      (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (colReplace M dst v) perm) 0 +
        (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (colReplace M dst w) perm) 0 := by
        exact foldl_det_sum_add_zero
          (permutationVectors n)
          (detTerm (colReplace M dst v))
          (detTerm (colReplace M dst w))

/-- Determinant linearity in one replaced column, scalar form. -/
theorem det_colReplace_smul {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) (c : R) (v : Fin n → R) :
    det (colReplace M dst (fun r => c * v r)) =
      c * det (colReplace M dst v) := by
  simp [det]
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (colReplace M dst (fun r => c * v r)) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + c * detTerm (colReplace M dst v) perm) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        exact detTerm_colReplace_smul M dst c v perm (permutationVectors_nodup hmem)
    _ =
      c * (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (colReplace M dst v) perm) 0 := by
        exact foldl_det_sum_mul_left_zero
          (permutationVectors n) c (detTerm (colReplace M dst v))

/-- The assembled determinant `det` vanishes when the replaced column is zero. -/
private theorem det_colReplace_zero {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) :
    det (colReplace M dst (fun _ => (0 : R))) = 0 := by
  have h := det_colReplace_smul M dst (0 : R) (fun _ => (1 : R))
  have hcol : (fun r : Fin n => (0 : R) * (1 : R)) = fun _ => (0 : R) := by
    funext r
    grind
  rw [hcol] at h
  grind

/-- Replacing a column by itself leaves the matrix unchanged. -/
theorem colReplace_self {R : Type u} {n : Nat}
    (M : Matrix R n n) (dst : Fin n) :
    colReplace M dst (fun r => M[r][dst]) = M := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change (colReplace M dst (fun r => M[r][dst]))[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
    M[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [colReplace_get]
  by_cases hc' : (⟨c, hc⟩ : Fin n) = dst
  · rw [if_pos hc']
    exact congrArg (fun c' : Fin n => M[(⟨r, hr⟩ : Fin n)][c']) hc'.symm
  · rw [if_neg hc']

/-- Determinant linearity in one replaced column, finite-list form. -/
theorem det_colReplace_sum_list {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) {β : Type v} (xs : List β)
    (coeff : β → R) (source : β → Fin n → R) :
    det (colReplace M dst
        (fun r => xs.foldl (fun acc x => acc + coeff x * source x r) 0)) =
      xs.foldl
        (fun acc x => acc + coeff x * det (colReplace M dst (source x))) 0 := by
  induction xs with
  | nil =>
      exact det_colReplace_zero M dst
  | cons x xs ih =>
      simp only [List.foldl_cons]
      let tail : Fin n → R :=
        fun r => xs.foldl (fun acc x => acc + coeff x * source x r) 0
      have hcol :
          (fun r : Fin n =>
              xs.foldl (fun acc x => acc + coeff x * source x r)
                (0 + coeff x * source x r)) =
            fun r => coeff x * source x r + tail r := by
        funext r
        rw [foldl_det_sum_start]
        simp [tail]
        grind
      calc
        det (colReplace M dst
            (fun r => xs.foldl (fun acc x => acc + coeff x * source x r)
              (0 + coeff x * source x r))) =
          det (colReplace M dst (fun r => coeff x * source x r + tail r)) := by
            rw [hcol]
        _ =
          det (colReplace M dst (fun r => coeff x * source x r)) +
            det (colReplace M dst tail) := by
            exact det_colReplace_add M dst (fun r => coeff x * source x r) tail
        _ =
          coeff x * det (colReplace M dst (source x)) +
            xs.foldl (fun acc x => acc + coeff x * det (colReplace M dst (source x))) 0 := by
            rw [det_colReplace_smul]
            simp [tail]
            rw [ih]
        _ =
          xs.foldl (fun acc x => acc + coeff x * det (colReplace M dst (source x)))
            (0 + coeff x * det (colReplace M dst (source x))) := by
            have hstart :=
              (foldl_det_sum_start (R := R) xs
                (fun x => coeff x * det (colReplace M dst (source x)))
                (0 + coeff x * det (colReplace M dst (source x)))).symm
            calc
              coeff x * det (colReplace M dst (source x)) +
                  xs.foldl
                    (fun acc x => acc + coeff x * det (colReplace M dst (source x))) 0 =
                (0 + coeff x * det (colReplace M dst (source x))) +
                  xs.foldl
                    (fun acc x => acc + coeff x * det (colReplace M dst (source x))) 0 := by
                  grind
              _ =
                xs.foldl
                  (fun acc x => acc + coeff x * det (colReplace M dst (source x)))
                  (0 + coeff x * det (colReplace M dst (source x))) := hstart

/-- Determinant linearity in one replaced column, indexed by `Fin m`. -/
theorem det_colReplace_sum_finRange {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (M : Matrix R n n) (dst : Fin n) (coeff : Fin m → R)
    (source : Fin m → Fin n → R) :
    det (colReplace M dst
        (fun r => (List.finRange m).foldl
          (fun acc x => acc + coeff x * source x r) 0)) =
      (List.finRange m).foldl
        (fun acc x => acc + coeff x * det (colReplace M dst (source x))) 0 :=
  det_colReplace_sum_list M dst (List.finRange m) coeff source

/-- Square matrix whose `j`-th column is the finite linear combination of the
columns of `source` with coefficients from row `j` of `coeff`. -/
private def columnSumMatrix {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) : Matrix R n n :=
  ofFn fun r j =>
    (List.finRange m).foldl (fun acc k => acc + coeff[j][k] * source[r][k]) 0

@[grind =] private theorem columnSumMatrix_entry
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (r j : Fin n) :
    (columnSumMatrix source coeff)[r][j] =
      (List.finRange m).foldl (fun acc k => acc + coeff[j][k] * source[r][k]) 0 := by
  simp [columnSumMatrix, ofFn]

private theorem colReplace_columnSumMatrix_self
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (dst : Fin n) :
    colReplace (columnSumMatrix source coeff) dst
        (fun r => (List.finRange m).foldl
          (fun acc k => acc + coeff[dst][k] * source[r][k]) 0) =
      columnSumMatrix source coeff := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change
    (colReplace (columnSumMatrix source coeff) dst
        (fun r => (List.finRange m).foldl
          (fun acc k => acc + coeff[dst][k] * source[r][k]) 0))[
          (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrix source coeff)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [colReplace_get]
  by_cases hcol : (⟨c, hc⟩ : Fin n) = dst
  · subst dst
    rw [if_pos rfl]
    exact (columnSumMatrix_entry source coeff (⟨r, hr⟩ : Fin n) (⟨c, hc⟩ : Fin n)).symm
  · simp [hcol]

private theorem det_columnSumMatrix_expand_column
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (dst : Fin n) :
    det (columnSumMatrix source coeff) =
      (List.finRange m).foldl
        (fun acc k =>
          acc + coeff[dst][k] *
            det (colReplace (columnSumMatrix source coeff) dst (fun r => source[r][k]))) 0 := by
  have hsum :=
    det_colReplace_sum_list
    (columnSumMatrix source coeff) dst (List.finRange m)
    (fun k => coeff[dst][k]) (fun k r => source[r][k])
  have hself := colReplace_columnSumMatrix_self source coeff dst
  rw [hself] at hsum
  exact hsum

/-- Matrix obtained during the ordered column expansion: columns with
`choices c = some k` have already been specialized to source column `k`, while
unassigned columns remain the finite coefficient-weighted column sum. -/
private def columnChoiceMatrix {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (choices : Fin n → Option (Fin m)) : Matrix R n n :=
  ofFn fun r c =>
    match choices c with
    | some k => source[r][k]
    | none => (List.finRange m).foldl (fun acc k => acc + coeff[c][k] * source[r][k]) 0

@[grind =] private theorem columnChoiceMatrix_entry
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (choices : Fin n → Option (Fin m)) (r c : Fin n) :
    (columnChoiceMatrix source coeff choices)[r][c] =
      match choices c with
      | some k => source[r][k]
      | none => (List.finRange m).foldl (fun acc k => acc + coeff[c][k] * source[r][k]) 0 := by
  simp [columnChoiceMatrix, ofFn]

/-- A determinant with two equal rows is zero. -/
theorem det_eq_zero_of_row_eq {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (hrow : M[src] = M[dst]) :
    det M = 0 := by
  have hdup : rowAddDuplicate M src dst = M := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro c hc
    change (rowAddDuplicate M src dst)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      M[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
    rw [rowAddDuplicate_get]
    by_cases hdst : (⟨r, hr⟩ : Fin n) = dst
    · subst hdst
      simpa using congrArg (fun row => row[(⟨c, hc⟩ : Fin n)]) hrow
    · simp [hdst]
  have hsum := permutationVectors_duplicateRow_sum M src dst h
  rw [hdup] at hsum
  simpa [det] using hsum

/-- A determinant with two equal columns is zero. -/
theorem det_eq_zero_of_col_eq {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst]) :
    det M = 0 := by
  simpa [det] using permutationVectors_duplicateCol_sum M src dst h hcol

/-- Replacing a column by an already-present different column creates a
duplicate column, so the determinant is zero. -/
theorem det_colReplace_existing_col_eq_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst src : Fin n) (hsrcdst : src ≠ dst) :
    det (colReplace M dst (fun r => M[r][src])) = 0 := by
  apply det_eq_zero_of_col_eq (colReplace M dst (fun r => M[r][src])) src dst hsrcdst
  intro r
  rw [colReplace_get, colReplace_get]
  rw [if_neg hsrcdst, if_pos rfl]

/-- Adding a finite linear combination of other columns of `M` to column `dst`
preserves the determinant. The sources are given as a list and each source is
required to differ from `dst`. -/
theorem det_colReplace_add_otherCols {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) (sources : List (Fin n)) (coeff : Fin n → R)
    (hsrc : ∀ s ∈ sources, s ≠ dst) :
    det (colReplace M dst
        (fun r => M[r][dst] +
          sources.foldl (fun acc s => acc + coeff s * M[r][s]) 0)) = det M := by
  rw [det_colReplace_add M dst (fun r => M[r][dst])
    (fun r => sources.foldl (fun acc s => acc + coeff s * M[r][s]) 0)]
  rw [colReplace_self M dst]
  have hcomb : det (colReplace M dst
        (fun r => sources.foldl (fun acc s => acc + coeff s * M[r][s]) 0)) = 0 := by
    rw [det_colReplace_sum_list M dst sources coeff (fun s r => M[r][s])]
    -- Show each summand is zero; we use the fact that the foldl over sources
    -- yields zero because each replaced det is zero.
    have hzero_each : ∀ s ∈ sources, coeff s * det (colReplace M dst (fun r => M[r][s])) = 0 := by
      intro s hs
      have hne : s ≠ dst := hsrc s hs
      rw [det_colReplace_existing_col_eq_zero M dst s hne]
      grind
    -- Foldl of a sum that is always zero adds nothing.
    have hfoldl : sources.foldl
        (fun acc s => acc + coeff s * det (colReplace M dst (fun r => M[r][s]))) 0 = 0 := by
      clear hzero_each
      induction sources with
      | nil => rfl
      | cons s ss ih =>
          simp only [List.foldl_cons]
          have hs : coeff s * det (colReplace M dst (fun r => M[r][s])) = 0 := by
            have hne : s ≠ dst := hsrc s (by simp)
            rw [det_colReplace_existing_col_eq_zero M dst s hne]
            grind
          rw [hs]
          have hsrc' : ∀ s' ∈ ss, s' ≠ dst := fun s' hs' => hsrc s' (by simp [hs'])
          have hzero_acc : (0 : R) + 0 = 0 := by grind
          rw [hzero_acc]
          exact ih hsrc'
    exact hfoldl
  rw [hcomb]
  grind

/-- Square submatrix obtained by selecting an ordered tuple of columns. -/
def columnTupleMatrix {R : Type u} {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m) : Matrix R n n :=
  ofFn fun r c => A[r][cols c]

/-- Entry `(r, c)` of the column-selected minor is the source entry
`A[r][cols c]`. -/
@[grind =] theorem columnTupleMatrix_entry {R : Type u} {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m) (r c : Fin n) :
    (columnTupleMatrix A cols)[r][c] = A[r][cols c] := by
  simp [columnTupleMatrix, ofFn]

/-- Interpret an ordered column tuple vector as its column-selection function. -/
def columnTupleVectorFn {n m : Nat} (cols : Vector (Fin m) n) : Fin n → Fin m :=
  fun i => cols[i]

/-- Applying the column-selection function at `i` reads the `i`-th entry
`cols[i]` of the tuple vector. -/
@[simp, grind =] theorem columnTupleVectorFn_apply {n m : Nat}
    (cols : Vector (Fin m) n) (i : Fin n) :
    columnTupleVectorFn cols i = cols[i] := rfl

/-- Reindexing the selected columns by a permutation is entrywise the generic
column permutation of the selected minor.

Unattributed: the LHS `[r][c]` is not in simp-normal form (`Fin.getElem_fin`
rewrites the `Fin` indices to `↑r`/`↑c`), and `grind =` rejects the pattern
because the columns `s sigma` appear only under the `fun i => s[sigma[i]]`
binder, so the LHS cannot instantiate them. Invoked explicitly via `rw`. -/
theorem columnTupleMatrix_compose_perm_entry
    {R : Type u} {n m : Nat} (A : Matrix R n m)
    (s : Vector (Fin m) n) (sigma : Vector (Fin n) n)
    (r c : Fin n) :
    (columnTupleMatrix A (fun i => s[sigma[i]]))[r][c] =
      (columnTupleMatrix A (columnTupleVectorFn s))[r][sigma[c]] := by
  rw [columnTupleMatrix_entry, columnTupleMatrix_entry]
  exact (congrArg (fun col : Fin m => A[r][col])
    (columnTupleVectorFn_apply s (sigma[c]))).symm

/-- Reindexing the selected columns by a permutation is the generic column
permutation of the selected minor. -/
theorem columnTupleMatrix_compose_perm_eq_colPermute
    {R : Type u} {n m : Nat} (A : Matrix R n m)
    (s : Vector (Fin m) n) (sigma : Vector (Fin n) n) :
    columnTupleMatrix A (fun i => s[sigma[i]]) =
      (ofFn fun r c => (columnTupleMatrix A (columnTupleVectorFn s))[r][sigma[c]]) := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change
    (columnTupleMatrix A (fun i => s[sigma[i]]))[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (ofFn fun r c =>
        (columnTupleMatrix A (columnTupleVectorFn s))[r][sigma[c]])[
          (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnTupleMatrix_compose_perm_entry]
  simp [Matrix.ofFn]

/-- Specialization of the generic column-permutation determinant sign theorem
to selected-minor matrices. -/
theorem det_columnTupleMatrix_compose_perm
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (s : Vector (Fin m) n) (sigma : Vector (Fin n) n)
    (hsigma : sigma ∈ permutationVectors n) :
    det (columnTupleMatrix A (fun i => s[sigma[i]])) =
      detSign (R := R) sigma * det (columnTupleMatrix A (columnTupleVectorFn s)) := by
  rw [columnTupleMatrix_compose_perm_eq_colPermute A s sigma]
  exact det_colPermute_vector (columnTupleMatrix A (columnTupleVectorFn s)) sigma hsigma

/-- Enumerate all ordered `n`-tuples of columns from `Fin m`. -/
def columnTupleVectors : (n m : Nat) → List (Vector (Fin m) n)
  | 0, _ => [emptyVec]
  | n + 1, m =>
      (columnTupleVectors n m).flatMap fun pref =>
        (List.finRange m).map fun c =>
          insertAt c pref (Fin.last n)

private theorem columnTupleVectors_ofFn_succ
    {n m : Nat} (cols : Fin (n + 1) → Fin m) :
    Vector.ofFn cols =
      insertAt (cols (Fin.last n)) (Vector.ofFn fun i : Fin n => cols i.castSucc)
        (Fin.last n) := by
  apply Vector.ext
  intro i hi
  change (Vector.ofFn cols)[(⟨i, hi⟩ : Fin (n + 1))] =
    (insertAt (cols (Fin.last n)) (Vector.ofFn fun i : Fin n => cols i.castSucc)
      (Fin.last n))[(⟨i, hi⟩ : Fin (n + 1))]
  by_cases hlast : i = n
  · subst i
    simp [insertAt, List.getElem_insertIdx_self]
    exact congrArg cols (Fin.ext rfl)
  · have hi_lt : i < n := by omega
    simp [insertAt, List.getElem_insertIdx_of_lt, hi_lt]

/-- Every ordered column-selection function occurs in `columnTupleVectors`. -/
theorem columnTupleVectors_mem_ofFn {n m : Nat} (cols : Fin n → Fin m) :
    Vector.ofFn cols ∈ columnTupleVectors n m := by
  induction n with
  | zero =>
      simp [columnTupleVectors, emptyVec]
  | succ n ih =>
      rw [columnTupleVectors_ofFn_succ cols]
      rw [columnTupleVectors, List.mem_flatMap]
      refine ⟨Vector.ofFn fun i : Fin n => cols i.castSucc, ih (fun i => cols i.castSucc), ?_⟩
      rw [List.mem_map]
      exact ⟨cols (Fin.last n), List.mem_finRange (cols (Fin.last n)), rfl⟩

private theorem insertAt_last_injective_pair {α : Type u} {n : Nat}
    {c c' : α} {pref pref' : Vector α n}
    (h : insertAt c pref (Fin.last n) = insertAt c' pref' (Fin.last n)) :
    c = c' ∧ pref = pref' := by
  constructor
  · have hlast :
        (insertAt c pref (Fin.last n))[Fin.last n] =
          (insertAt c' pref' (Fin.last n))[Fin.last n] := by
      rw [h]
    rw [insertAt_get_self, insertAt_get_self] at hlast
    exact hlast
  · apply Vector.ext
    intro i hi
    let idx : Fin n := ⟨i, hi⟩
    have hidx :
        (insertAt c pref (Fin.last n))[idx.castSucc] =
          (insertAt c' pref' (Fin.last n))[idx.castSucc] := by
      rw [h]
    rw [insertAt_last_get_castSucc, insertAt_last_get_castSucc] at hidx
    exact hidx

private theorem columnTupleVectors_flatMap_last_nodup {n m : Nat} :
    ∀ (prefs : List (Vector (Fin m) n)), prefs.Nodup →
      (prefs.flatMap fun pref =>
        (List.finRange m).map fun c => insertAt c pref (Fin.last n)).Nodup
  | [], _ => by simp
  | pref :: prefs, hnodup => by
      simp only [List.flatMap_cons]
      simp only [List.nodup_cons] at hnodup
      rw [List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · apply list_nodup_map_on (List.nodup_finRange m)
        intro c _hc c' _hc' h
        exact (insertAt_last_injective_pair h).1
      · exact columnTupleVectors_flatMap_last_nodup prefs hnodup.2
      · intro a hahead b hbsuffix hab
        rcases List.mem_map.mp hahead with ⟨c, _hc, rfl⟩
        rcases List.mem_flatMap.mp hbsuffix with ⟨pref', hpref', hb⟩
        rcases List.mem_map.mp hb with ⟨c', _hc', hb_eq⟩
        have hrec :
            insertAt c pref (Fin.last n) =
              insertAt c' pref' (Fin.last n) := hab.trans hb_eq.symm
        have hpref_eq := (insertAt_last_injective_pair hrec).2
        subst hpref_eq
        exact hnodup.1 hpref'

private theorem columnTupleVectors_nodup {n m : Nat} :
    (columnTupleVectors n m).Nodup := by
  induction n with
  | zero =>
      simp [columnTupleVectors]
  | succ n ih =>
      rw [columnTupleVectors]
      exact columnTupleVectors_flatMap_last_nodup (columnTupleVectors n m) ih

/-- Product coefficient attached to an ordered column tuple in the Gram expansion. -/
def columnTupleCoeff {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (A : Matrix R n m) (cols : Vector (Fin m) n) : R :=
  (List.finRange n).foldl (fun acc i => acc * A[i][cols[i]]) 1

/-- The determinant summand associated to an ordered column tuple. -/
def columnTupleExpansionTerm {R : Type u} [Lean.Grind.Ring R] {n m : Nat}
    (A : Matrix R n m) (cols : Vector (Fin m) n) : R :=
  columnTupleCoeff A cols * det (columnTupleMatrix A (columnTupleVectorFn cols))

/-- An ordered column-tuple minor with a repeated selected column has determinant zero. -/
theorem det_columnTupleMatrix_eq_zero_of_col_eq
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m)
    {src dst : Fin n} (h : src ≠ dst) (hcols : cols src = cols dst) :
    det (columnTupleMatrix A cols) = 0 := by
  apply det_eq_zero_of_col_eq (columnTupleMatrix A cols) src dst h
  intro r
  rw [columnTupleMatrix_entry, columnTupleMatrix_entry]
  exact congrArg (fun c : Fin m => A[r][c]) hcols

/-- An ordered column-tuple minor with a non-injective selected-column map has
determinant zero. -/
theorem det_columnTupleMatrix_eq_zero_of_not_injective
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m)
    (hcols : ¬ Function.Injective cols) :
    det (columnTupleMatrix A cols) = 0 := by
  classical
  have hdup : ∃ src dst : Fin n, cols src = cols dst ∧ src ≠ dst := by
    rw [Function.Injective] at hcols
    rcases Classical.not_forall.mp hcols with ⟨src, hsrc⟩
    rcases Classical.not_forall.mp hsrc with ⟨dst, hdst⟩
    exact ⟨src, dst, (not_imp.mp hdst).1, fun h => (not_imp.mp hdst).2 h⟩
  rcases hdup with ⟨src, dst, hsame, hne⟩
  exact det_columnTupleMatrix_eq_zero_of_col_eq A cols hne hsame

/-! ### All-column ordered tuple expansion

Iterates `det_columnSumMatrix_expand_column` over every column to express
`det (columnSumMatrix source coeff)` as a sum over ordered column tuples.
Uses a list-based "left prefix" partial assignment, with a Fubini-style
sum-swap to align the iteration order with `columnTupleVectors`.
-/

/-- Sum-swap (Fubini) for the standard determinant-style nested folds. -/
theorem foldl_det_sum_swap {R : Type u} [Lean.Grind.CommRing R]
    {β γ : Type v} (xs : List β) (ys : List γ) (f : β → γ → R) :
    xs.foldl (fun acc x => acc + ys.foldl (fun acc' y => acc' + f x y) 0) 0 =
      ys.foldl (fun acc y => acc + xs.foldl (fun acc' x => acc' + f x y) 0) 0 := by
  induction xs with
  | nil =>
      simp only [List.foldl_nil]
      exact (foldl_det_sum_zero ys 0).symm
  | cons x xs ih =>
      have hLHS :
          (x :: xs).foldl
              (fun acc x' => acc + ys.foldl (fun acc' y => acc' + f x' y) 0) 0 =
            ys.foldl (fun acc' y => acc' + f x y) 0 +
              xs.foldl
                (fun acc x' => acc + ys.foldl (fun acc' y => acc' + f x' y) 0) 0 := by
        simp only [List.foldl_cons]
        rw [foldl_det_sum_start xs
              (fun x' => ys.foldl (fun acc' y => acc' + f x' y) 0)
              (0 + ys.foldl (fun acc' y => acc' + f x y) 0)]
        grind
      have hRHS :
          ys.foldl
              (fun acc y => acc + (x :: xs).foldl
                (fun acc' x' => acc' + f x' y) 0) 0 =
            ys.foldl (fun acc' y => acc' + f x y) 0 +
              ys.foldl
                (fun acc y => acc + xs.foldl
                  (fun acc' x' => acc' + f x' y) 0) 0 := by
        have hfun :
            (fun (acc : R) y =>
                acc + (x :: xs).foldl (fun acc' x' => acc' + f x' y) 0) =
              (fun (acc : R) y =>
                acc + (f x y + xs.foldl (fun acc' x' => acc' + f x' y) 0)) := by
          funext acc y
          congr 1
          simp only [List.foldl_cons]
          rw [foldl_det_sum_start xs (fun x' => f x' y) (0 + f x y)]
          grind
        rw [hfun]
        exact foldl_det_sum_add_zero ys (fun y => f x y)
          (fun y => xs.foldl (fun acc' x' => acc' + f x' y) 0)
      rw [hLHS, hRHS, ih]

private theorem foldl_det_sum_nested_start {R : Type u} [Lean.Grind.CommRing R]
    {β γ : Type v} (xs : List β) (ys : List γ) (f : β → γ → R) (z : R) :
    xs.foldl (fun acc x => ys.foldl (fun acc' y => acc' + f x y) acc) z =
      z + xs.foldl
        (fun acc x => acc + ys.foldl (fun acc' y => acc' + f x y) 0) 0 := by
  induction xs generalizing z with
  | nil =>
      simp only [List.foldl_nil]
      grind
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [foldl_det_sum_start ys (fun y => f x y) z]
      rw [ih (z + ys.foldl (fun acc' y => acc' + f x y) 0)]
      rw [foldl_det_sum_start xs
        (fun x => ys.foldl (fun acc' y => acc' + f x y) 0)
        (0 + ys.foldl (fun acc' y => acc' + f x y) 0)]
      grind

private theorem foldl_det_sum_nested_zero {R : Type u} [Lean.Grind.CommRing R]
    {β γ : Type v} (xs : List β) (ys : List γ) (f : β → γ → R) :
    xs.foldl (fun acc x => ys.foldl (fun acc' y => acc' + f x y) acc) 0 =
      xs.foldl
        (fun acc x => acc + ys.foldl (fun acc' y => acc' + f x y) 0) 0 := by
  exact (foldl_det_sum_nested_start xs ys f (0 : R)).trans (by grind)

/-- Inner sum-over-permutations collapse: for any row `i`, the Leibniz terms whose
permutation sends row `i` to the last column collapse to `M[i][last] * cofactor M i last`. -/
private theorem foldl_detTerm_insertions_eq_cofactor
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i : Fin (n + 1)) :
    (permutationVectors n).foldl
        (fun acc v => acc + detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i)) 0 =
      M[i][Fin.last n] * cofactor M i (Fin.last n) := by
  have hsumands : (permutationVectors n).foldl
        (fun acc v => acc + detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i)) 0 =
      (permutationVectors n).foldl
        (fun acc v => acc + cofactorSign (R := R) i (Fin.last n) *
          (M[i][Fin.last n] * detTerm (deleteRowCol M i (Fin.last n)) v)) 0 := by
    apply foldl_det_sum_congr
    intro v _hmem
    exact detTerm_insertAt_general M v i
  rw [hsumands]
  rw [foldl_det_sum_mul_left_zero (permutationVectors n)
    (cofactorSign (R := R) i (Fin.last n))
    (fun v => M[i][Fin.last n] * detTerm (deleteRowCol M i (Fin.last n)) v)]
  rw [foldl_det_sum_mul_left_zero (permutationVectors n) M[i][Fin.last n]
    (fun v => detTerm (deleteRowCol M i (Fin.last n)) v)]
  show cofactorSign (R := R) i (Fin.last n) *
       (M[i][Fin.last n] * det (deleteRowCol M i (Fin.last n))) = _
  unfold cofactor
  grind

/-- Laplace expansion of the determinant along the final column. -/
theorem det_eq_foldl_laplace_last
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) :
    det M =
      (List.finRange (n + 1)).foldl
        (fun acc row => acc + M[row][Fin.last n] * cofactor M row (Fin.last n)) 0 := by
  unfold det
  rw [show permutationVectors (n + 1) =
      List.flatMap
        (fun v =>
          (List.finRange (n + 1)).map fun i =>
            insertAt (Fin.last n) (v.map Fin.castSucc) i)
        (permutationVectors n) from rfl]
  rw [foldl_det_sum_flatMap]
  have hmap :
      (permutationVectors n).foldl
        (fun acc v =>
          ((List.finRange (n + 1)).map
            (fun i => insertAt (Fin.last n) (v.map Fin.castSucc) i)).foldl
            (fun acc perm => acc + detTerm M perm) acc) 0 =
      (permutationVectors n).foldl
        (fun acc v =>
          (List.finRange (n + 1)).foldl
            (fun acc i =>
              acc + detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i)) acc) 0 := by
    apply foldl_acc_congr
    intro acc v _hmem
    simp only [List.foldl_map]
  rw [hmap]
  rw [foldl_det_sum_nested_zero (permutationVectors n) (List.finRange (n + 1))
    (fun v i => detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i))]
  rw [foldl_det_sum_swap (permutationVectors n) (List.finRange (n + 1))
    (fun v i => detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i))]
  apply foldl_acc_congr
  intro acc i _hmem
  congr 1
  exact foldl_detTerm_insertions_eq_cofactor M i

/-- Laplace expansion of the determinant along the final row. -/
theorem det_eq_foldl_laplace_last_row
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) :
    det M =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M[Fin.last n][col] * cofactor M (Fin.last n) col) 0 := by
  calc
    det M = det M.transpose := (det_transpose M).symm
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M.transpose[col][Fin.last n] *
          cofactor M.transpose col (Fin.last n)) 0 := det_eq_foldl_laplace_last M.transpose
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M[Fin.last n][col] * cofactor M (Fin.last n) col) 0 := by
        apply foldl_acc_congr
        intro acc col _hmem
        rw [cofactor_transpose]
        simp [Matrix.transpose, Matrix.col]

/-- Column permutation that preserves the relative order of every column except
`col`, which is moved to the final position. -/
private def moveColumnToLastValues {n : Nat} (col : Fin (n + 1)) :
    Vector (Fin (n + 1)) (n + 1) :=
  insertAt col (Vector.ofFn fun i : Fin n => skipIndex col i) (Fin.last n)

/-- `moveColumnToLastValues_last` states that the moved column `col` lands in the
final position of the permutation, the defining property that sends the cofactor
column to the last column. -/
private theorem moveColumnToLastValues_last {n : Nat} (col : Fin (n + 1)) :
    (moveColumnToLastValues col)[Fin.last n] = col := by
  exact insertAt_get_self col (Vector.ofFn fun i : Fin n => skipIndex col i) (Fin.last n)

/-- `moveColumnToLastValues_castSucc` states that every non-final position
`i.castSucc` of the permutation holds the original columns with `col` skipped over,
preserving the relative order of the surviving columns. -/
private theorem moveColumnToLastValues_castSucc {n : Nat} (col : Fin (n + 1)) (i : Fin n) :
    (moveColumnToLastValues col)[i.castSucc] = skipIndex col i := by
  rw [moveColumnToLastValues]
  simpa using
    insertAt_last_get_castSucc col (Vector.ofFn fun i : Fin n => skipIndex col i) i

/-- `moveColumnToLastValues_nodup` states that the permutation's values are
pairwise distinct, the no-repeat condition needed to certify it as a genuine
permutation of the columns. -/
private theorem moveColumnToLastValues_nodup {n : Nat} (col : Fin (n + 1)) :
    (moveColumnToLastValues col).toList.Nodup := by
  rw [moveColumnToLastValues, insertAt_last_toList]
  rw [vector_toList_eq_finRange_map_get]
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · apply list_nodup_map_of_injective
    · intro i j h
      exact skipIndex_injective col (by simpa using h)
    · exact List.nodup_finRange n
  · simp
  · intro x hx y hy hxy
    simp only [List.mem_singleton] at hy
    have hxcol : x = col := hxy.trans hy
    rcases List.mem_map.mp hx with ⟨i, _hi, rfl⟩
    exact skipIndex_ne col i (by simpa using hxcol)

/-- `moveColumnToLastValues_mem_permutationVectors` states that the column move is
a member of `permutationVectors (n + 1)`, packaging the nodup proof so the move can
be fed to the determinant column-permutation machinery. -/
private theorem moveColumnToLastValues_mem_permutationVectors {n : Nat}
    (col : Fin (n + 1)) :
    moveColumnToLastValues col ∈ permutationVectors (n + 1) :=
  permutationVectors_complete (moveColumnToLastValues_nodup col)

/-- `skipIndex_eq_raiseFinAbove` states that the two index-shifting functions agree,
letting the column-move list be rewritten in the `raiseFinAbove` form used by the
inversion-count sign computation. -/
private theorem skipIndex_eq_raiseFinAbove {n : Nat} (col : Fin (n + 1)) (i : Fin n) :
    skipIndex col i = raiseFinAbove col i := by
  unfold skipIndex raiseFinAbove
  split <;> rfl

/-- `moveColumnToLastValues_toList` gives the explicit list form of the column move:
the `n` surviving columns in order (via `raiseFinAbove col`) followed by `col`, the
shape consumed by the inversion-count sign lemma. -/
private theorem moveColumnToLastValues_toList {n : Nat} (col : Fin (n + 1)) :
    (moveColumnToLastValues col).toList =
      ((List.finRange n).map (raiseFinAbove col)) ++ [col] := by
  rw [moveColumnToLastValues, insertAt_last_toList]
  rw [vector_toList_eq_finRange_map_get]
  apply congrArg (fun xs => xs ++ [col])
  apply List.map_congr_left
  intro i _hi
  simpa using skipIndex_eq_raiseFinAbove col i

/-- `detSign_moveColumnToLastValues` evaluates the sign of the column move to
`(-1) ^ (n - col.val)`, the parity contributed by sliding `col` past the `n - col.val`
columns to its right. -/
private theorem detSign_moveColumnToLastValues
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat} (col : Fin (n + 1)) :
    detSign (R := R) (moveColumnToLastValues col) =
      (-1 : R) ^ (n - col.val) := by
  have hidList :
      (Vector.ofFn fun i : Fin n => i).toList = List.finRange n := by
    rw [vector_toList_eq_finRange_map_get]
    simp
  calc
    detSign (R := R) (moveColumnToLastValues col) =
        (-1 : R) ^ (n - col.val) *
          detSign (R := R) (Vector.ofFn fun i : Fin n => i) := by
      apply detSign_of_inversionCount_add
      rw [moveColumnToLastValues_toList, hidList]
      rw [inversionCount_map_raiseFinAbove_append_self]
      rw [foldCount_finRange_ge]
    _ = (-1 : R) ^ (n - col.val) := by
      rw [detSign_identity]
      grind

/-- `neg_one_pow_mul_self` states that a sign `(-1) ^ k` squares to one, the
cancellation used to undo the column-move sign factor when transporting the Laplace
expansion back to the original column. -/
private theorem neg_one_pow_mul_self {R : Type u} [Lean.Grind.CommRing R] (k : Nat) :
    (-1 : R) ^ k * (-1 : R) ^ k = 1 := by
  induction k with
  | zero =>
      grind
  | succ k ih =>
      grind

/-- `cofactorSign_col_eq_move_mul_last` relates the cofactor sign at column `col` to
the sign at the last column through the `(-1) ^ (n - col.val)` column-move factor, the
parity bookkeeping that turns last-column Laplace expansion into expansion along `col`. -/
private theorem cofactorSign_col_eq_move_mul_last
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (row col : Fin (n + 1)) :
    cofactorSign (R := R) row col =
      (-1 : R) ^ (n - col.val) * cofactorSign (R := R) row (Fin.last n) := by
  unfold cofactorSign
  simp only [Fin.val_last]
  have hle : col.val ≤ n := Nat.le_of_lt_succ col.isLt
  have h := detSignParity_add (R := R) (row.val + col.val) (n - col.val)
  have hsum : row.val + col.val + (n - col.val) = row.val + n := by omega
  rw [hsum] at h
  let s : R := (-1 : R) ^ (n - col.val)
  let a : R := if (row.val + col.val) % 2 = 0 then 1 else -1
  let b : R := if (row.val + n) % 2 = 0 then 1 else -1
  have hs : s * s = 1 := neg_one_pow_mul_self (R := R) (n - col.val)
  have hb : b = s * a := by simpa [a, b, s] using h
  calc
    (if (row.val + col.val) % 2 = 0 then (1 : R) else -1) = a := rfl
    _ = s * (s * a) := by
      have hss : s * (s * a) = a := by
        calc
          s * (s * a) = (s * s) * a := by grind
          _ = 1 * a := by rw [hs]
          _ = a := by grind
      exact hss.symm
    _ = s * b := by rw [hb]
    _ = s * (if (row.val + n) % 2 = 0 then (1 : R) else -1) := rfl

/-- Laplace expansion of the determinant along an arbitrary fixed column. -/
theorem det_eq_foldl_laplace_col
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (col : Fin (n + 1)) :
    det M =
      (List.finRange (n + 1)).foldl
        (fun acc row => acc + M[row][col] * cofactor M row col) 0 := by
  let sigma := moveColumnToLastValues col
  let C : Matrix R (n + 1) (n + 1) := ofFn fun r c => M[r][sigma[c]]
  have hsigma : sigma ∈ permutationVectors (n + 1) :=
    moveColumnToLastValues_mem_permutationVectors col
  have hdetC : det C = (-1 : R) ^ (n - col.val) * det M := by
    calc
      det C = detSign (R := R) sigma * det M := by
        exact det_colPermute_vector M sigma hsigma
      _ = (-1 : R) ^ (n - col.val) * det M := by
        rw [detSign_moveColumnToLastValues col]
  have hsign_sq : (-1 : R) ^ (n - col.val) * ((-1 : R) ^ (n - col.val)) = 1 := by
    exact neg_one_pow_mul_self (R := R) (n - col.val)
  calc
    det M = (-1 : R) ^ (n - col.val) * det C := by
      rw [hdetC]
      grind
    _ =
      (-1 : R) ^ (n - col.val) *
        (List.finRange (n + 1)).foldl
          (fun acc row => acc + C[row][Fin.last n] * cofactor C row (Fin.last n)) 0 := by
        rw [det_eq_foldl_laplace_last C]
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc row =>
          acc + (-1 : R) ^ (n - col.val) *
            (C[row][Fin.last n] * cofactor C row (Fin.last n))) 0 := by
        rw [foldl_det_sum_mul_left_zero]
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc row => acc + M[row][col] * cofactor M row col) 0 := by
        apply foldl_acc_congr
        intro acc row _hmem
        congr 1
        unfold cofactor
        have hClast : C[row][Fin.last n] = M[row][col] := by
          rw [show C[row][Fin.last n] = M[row][sigma[Fin.last n]] by
            simp [C, ofFn]]
          exact congrArg (fun c => M[row][c]) (moveColumnToLastValues_last col)
        have hminor : deleteRowCol C row (Fin.last n) = deleteRowCol M row col := by
          apply Vector.ext
          intro i hi
          apply Vector.ext
          intro j hj
          let ii : Fin n := ⟨i, hi⟩
          let jj : Fin n := ⟨j, hj⟩
          change (deleteRowCol C row (Fin.last n))[ii][jj] =
            (deleteRowCol M row col)[ii][jj]
          rw [deleteRowCol_entry, deleteRowCol_entry]
          rw [show C[skipIndex row ii][skipIndex (Fin.last n) jj] =
              C[skipIndex row ii][jj.castSucc] by
            exact congrArg (fun c => C[skipIndex row ii][c]) (skipIndex_last jj)]
          rw [show C[skipIndex row ii][jj.castSucc] =
              M[skipIndex row ii][sigma[jj.castSucc]] by
            simp [C, ofFn]]
          exact congrArg (fun c => M[skipIndex row ii][c])
            (moveColumnToLastValues_castSucc col jj)
        rw [hClast, hminor]
        rw [cofactorSign_col_eq_move_mul_last (R := R) row col]
        grind

/-- Laplace expansion of the determinant along an arbitrary fixed row. -/
theorem det_eq_foldl_laplace_row
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row : Fin (n + 1)) :
    det M =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M[row][col] * cofactor M row col) 0 := by
  calc
    det M = det M.transpose := (det_transpose M).symm
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M.transpose[col][row] *
          cofactor M.transpose col row) 0 := det_eq_foldl_laplace_col M.transpose row
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M[row][col] * cofactor M row col) 0 := by
        apply foldl_acc_congr
        intro acc col _hmem
        rw [cofactor_transpose]
        simp [Matrix.transpose, Matrix.col]

/-- The square matrix obtained from `columnSumMatrix source coeff` by replacing
the first `chosen.length` columns with selected `source` columns indexed by
`chosen`. The remaining columns stay in finite-sum form. -/
private def columnSumMatrixWithPrefix
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m)) : Matrix R n n :=
  ofFn fun r j =>
    if h : j.val < chosen.length then
      source[r][chosen[j.val]'h]
    else
      (List.finRange m).foldl (fun acc k => acc + coeff[j][k] * source[r][k]) 0

@[grind =] private theorem columnSumMatrixWithPrefix_entry
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m)) (r j : Fin n) :
    (columnSumMatrixWithPrefix source coeff chosen)[r][j] =
      if h : j.val < chosen.length then
        source[r][chosen[j.val]'h]
      else
        (List.finRange m).foldl
          (fun acc k => acc + coeff[j][k] * source[r][k]) 0 := by
  simp [columnSumMatrixWithPrefix, ofFn]

/-! ### Suffix-based partial assignment

We use a SUFFIX-based parametrization (chosen represents right-fixed columns)
to align with the natural recursion of `columnTupleVectors`, which factors out
the LAST element of the suffix. After Fubini sum-swap, the inductive step
reduces to identity matching of the per-term values. -/

/-- Square matrix where the last `chosen.length` columns are fixed to selected
`source` columns indexed by `chosen` (in order), and the remaining left columns
stay in finite-sum form. -/
private def columnSumMatrixWithSuffix
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m)) : Matrix R n n :=
  ofFn fun r j =>
    if h : n - chosen.length ≤ j.val then
      source[r][chosen[j.val - (n - chosen.length)]'(by
        have : j.val < n := j.isLt; omega)]
    else
      (List.finRange m).foldl (fun acc k => acc + coeff[j][k] * source[r][k]) 0

@[grind =] private theorem columnSumMatrixWithSuffix_entry
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m)) (r j : Fin n) :
    (columnSumMatrixWithSuffix source coeff chosen)[r][j] =
      if h : n - chosen.length ≤ j.val then
        source[r][chosen[j.val - (n - chosen.length)]'(by
          have : j.val < n := j.isLt; omega)]
      else
        (List.finRange m).foldl
          (fun acc k => acc + coeff[j][k] * source[r][k]) 0 := by
  simp [columnSumMatrixWithSuffix, ofFn]

private theorem columnSumMatrixWithSuffix_nil
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) :
    columnSumMatrixWithSuffix source coeff [] = columnSumMatrix source coeff := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change (columnSumMatrixWithSuffix source coeff [])[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrix source coeff)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnSumMatrixWithSuffix_entry, columnSumMatrix_entry]
  rw [dif_neg (show ¬ n - ([] : List (Fin m)).length ≤ c by simp; omega)]

private theorem columnSumMatrixWithSuffix_eq_columnTupleMatrix
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hfull : chosen.length = n) :
    columnSumMatrixWithSuffix source coeff chosen =
      columnTupleMatrix source (fun j => chosen[j.val]'(by omega)) := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change (columnSumMatrixWithSuffix source coeff chosen)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnTupleMatrix source (fun j => chosen[j.val]'(by omega)))[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnSumMatrixWithSuffix_entry, dif_pos (by omega : n - chosen.length ≤ c)]
  simp [columnTupleMatrix, ofFn, hfull]

/-- Replacing the rightmost sum column of the suffix-partial matrix with a fixed
`source` column extends the suffix by prepending that selection. -/
private theorem colReplace_columnSumMatrixWithSuffix_extend
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) (c : Fin m) :
    colReplace (columnSumMatrixWithSuffix source coeff chosen)
        (⟨n - chosen.length - 1, by omega⟩ : Fin n) (fun r => source[r][c]) =
      columnSumMatrixWithSuffix source coeff (c :: chosen) := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro k hk2
  change (colReplace (columnSumMatrixWithSuffix source coeff chosen)
      (⟨n - chosen.length - 1, by omega⟩ : Fin n) (fun r => source[r][c]))[
      (⟨r, hr⟩ : Fin n)][(⟨k, hk2⟩ : Fin n)] =
    (columnSumMatrixWithSuffix source coeff (c :: chosen))[
      (⟨r, hr⟩ : Fin n)][(⟨k, hk2⟩ : Fin n)]
  rw [colReplace_get]
  simp only [columnSumMatrixWithSuffix_entry]
  have hccons_len : (c :: chosen).length = chosen.length + 1 := rfl
  by_cases hkd : (⟨k, hk2⟩ : Fin n) = (⟨n - chosen.length - 1, by omega⟩ : Fin n)
  · have hkeq : k = n - chosen.length - 1 := by
      have := congrArg Fin.val hkd; simpa using this
    rw [if_pos hkd]
    rw [dif_pos (show n - (c :: chosen).length ≤ k by rw [hccons_len]; omega)]
    have hsub0 : k - (n - (c :: chosen).length) = 0 := by rw [hccons_len]; omega
    have hgetval : (c :: chosen)[k - (n - (c :: chosen).length)]'(by
        have : k < n := hk2; rw [hccons_len]; omega) = c := by
      have h1 : (c :: chosen)[k - (n - (c :: chosen).length)]'(by
          have : k < n := hk2; rw [hccons_len]; omega) =
        (c :: chosen)[(0 : Nat)]'(by simp) := by
        congr 1
      rw [h1]
      rfl
    exact congrArg (fun x : Fin m => source[(⟨r, hr⟩ : Fin n)][x]) hgetval.symm
  · rw [if_neg hkd]
    have hkne : k ≠ n - chosen.length - 1 := fun h => hkd (Fin.ext h)
    by_cases hkge : n - chosen.length ≤ k
    · rw [dif_pos hkge]
      have hkge' : n - (c :: chosen).length ≤ k := by rw [hccons_len]; omega
      rw [dif_pos hkge']
      have hidx_eq : k - (n - (c :: chosen).length) = (k - (n - chosen.length)) + 1 := by
        rw [hccons_len]; omega
      have hgetval : (c :: chosen)[k - (n - (c :: chosen).length)]'(by
          have : k < n := hk2; rw [hccons_len]; omega) =
        chosen[k - (n - chosen.length)]'(by have : k < n := hk2; omega) := by
        have h1 : (c :: chosen)[k - (n - (c :: chosen).length)]'(by
            have : k < n := hk2; rw [hccons_len]; omega) =
          (c :: chosen)[(k - (n - chosen.length)) + 1]'(by
            have : k < n := hk2; rw [hccons_len]; omega) := by
          congr 1
        rw [h1]
        rfl
      exact congrArg (fun x : Fin m => source[(⟨r, hr⟩ : Fin n)][x]) hgetval.symm
    · rw [dif_neg hkge]
      have hkge' : ¬ n - (c :: chosen).length ≤ k := by rw [hccons_len]; omega
      rw [dif_neg hkge']

/-- One-step expansion of the suffix-partial matrix: peel off the rightmost sum
column as a sum over `Fin m`. -/
private theorem det_columnSumMatrixWithSuffix_expand
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) :
    det (columnSumMatrixWithSuffix source coeff chosen) =
      (List.finRange m).foldl
        (fun acc c => acc + coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
          det (columnSumMatrixWithSuffix source coeff (c :: chosen))) 0 := by
  let dst : Fin n := ⟨n - chosen.length - 1, by omega⟩
  have hself :
      colReplace (columnSumMatrixWithSuffix source coeff chosen) dst
          (fun r => (List.finRange m).foldl
            (fun acc k => acc + coeff[dst][k] * source[r][k]) 0) =
        columnSumMatrixWithSuffix source coeff chosen := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro c hc
    change (colReplace (columnSumMatrixWithSuffix source coeff chosen) dst _)[
        (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrixWithSuffix source coeff chosen)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
    rw [colReplace_get, columnSumMatrixWithSuffix_entry]
    by_cases hcd : (⟨c, hc⟩ : Fin n) = dst
    · rw [if_pos hcd, hcd]
      rw [dif_neg (show ¬ n - chosen.length ≤ dst.val by simp [dst]; omega)]
    · rw [if_neg hcd]
  have hsum := det_colReplace_sum_list
      (columnSumMatrixWithSuffix source coeff chosen) dst
      (List.finRange m) (fun k => coeff[dst][k]) (fun k r => source[r][k])
  rw [hself] at hsum
  rw [hsum]
  apply foldl_det_sum_congr
  intro c _hc
  congr 2
  exact colReplace_columnSumMatrixWithSuffix_extend source coeff chosen hk c

private def assembleColumnsSuffix {n m : Nat} (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length)) (hk : chosen.length ≤ n) :
    Vector (Fin m) n :=
  ⟨(pref.toList ++ chosen).toArray, by
    simp [hk]⟩

@[grind =] private theorem assembleColumnsSuffix_left
    {n m : Nat} (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length)) (hk : chosen.length ≤ n)
    (i : Fin (n - chosen.length)) :
    (assembleColumnsSuffix chosen pref hk)[
        (⟨i.val, by
          have hi : i.val < n - chosen.length := i.isLt
          omega⟩ : Fin n)] = pref[i] := by
  simp [assembleColumnsSuffix]

@[grind =] private theorem assembleColumnsSuffix_right
    {n m : Nat} (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length)) (hk : chosen.length ≤ n)
    (i : Fin chosen.length) :
    (assembleColumnsSuffix chosen pref hk)[
        (⟨n - chosen.length + i.val, by
          have hi : i.val < chosen.length := i.isLt
          omega⟩ : Fin n)] = chosen[i] := by
  unfold assembleColumnsSuffix
  simp [List.getElem_append_right]

private def vectorLengthCast {α : Type u} {n k : Nat} (h : n = k)
    (v : Vector α n) : Vector α k :=
  match v with
  | ⟨xs, hx⟩ => ⟨xs, by simpa [h] using hx⟩

private theorem columnTupleVectors_foldl_vectorLengthCast
    {α : Type u} {m k l : Nat} (h : k = l)
    (f : α → Vector (Fin m) l → α) (init : α) :
    (columnTupleVectors l m).foldl f init =
      (columnTupleVectors k m).foldl
        (fun acc pref => f acc (vectorLengthCast h pref)) init := by
  subst h
  rfl

private theorem assembleColumnsSuffix_insertAt_last
    {n m : Nat} (chosen : List (Fin m)) (c : Fin m)
    (pref : Vector (Fin m) (n - (c :: chosen).length))
    (hk : (c :: chosen).length ≤ n)
    (hlen : (n - (c :: chosen).length) + 1 = n - chosen.length := by
      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
      omega) :
    assembleColumnsSuffix chosen
        (vectorLengthCast hlen
          (insertAt c pref (Fin.last (n - (c :: chosen).length))))
        (by
          have hcons : (c :: chosen).length = chosen.length + 1 := rfl
          omega) =
      assembleColumnsSuffix (c :: chosen) pref hk := by
  apply Vector.toArray_inj.mp
  unfold assembleColumnsSuffix
  simp only [vectorLengthCast, Vector.toList, insertAt]
  have hidx : (Fin.last (n - (c :: chosen).length)).val = pref.toArray.toList.length := by
    simp
  rw [hidx, list_insertIdx_length]
  simp [List.append_assoc]

private theorem det_columnTupleMatrix_assembleColumnsSuffix_insertAt_last
    {R : Type u} [Lean.Grind.Ring R] {n m : Nat} (source : Matrix R n m)
    (chosen : List (Fin m)) (c : Fin m)
    (pref : Vector (Fin m) (n - (c :: chosen).length))
    (hk : (c :: chosen).length ≤ n)
    (hlen : (n - (c :: chosen).length) + 1 = n - chosen.length := by
      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
      omega) :
    det (columnTupleMatrix source
        (columnTupleVectorFn
          (assembleColumnsSuffix chosen
            (vectorLengthCast hlen
              (insertAt c pref (Fin.last (n - (c :: chosen).length))))
            (by
              have hcons : (c :: chosen).length = chosen.length + 1 := rfl
              omega)))) =
      det (columnTupleMatrix source
        (columnTupleVectorFn (assembleColumnsSuffix (c :: chosen) pref hk))) := by
  rw [assembleColumnsSuffix_insertAt_last chosen c pref hk hlen]

private def partialColumnTupleCoeff {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (coeff : Matrix R n m) (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length)) : R :=
  (List.finRange (n - chosen.length)).foldl
    (fun acc i => acc * coeff[(⟨i.val, by
      have hi : i.val < n - chosen.length := i.isLt
      omega⟩ : Fin n)][pref[i]]) 1

private theorem partialColumnTupleCoeff_nil
    {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (coeff : Matrix R n m) (cols : Vector (Fin m) n) :
    partialColumnTupleCoeff coeff [] cols = columnTupleCoeff coeff cols := by
  unfold partialColumnTupleCoeff columnTupleCoeff
  apply foldl_det_product_congr
  intro i _hmem
  congr 2

private theorem partialColumnTupleCoeff_insertAt_last_fold
    {R : Type u} [Mul R] [OfNat R 1] {n m rem : Nat}
    (coeff : Matrix R n m) (c : Fin m) (pref : Vector (Fin m) rem)
    (hrem : rem < n) :
    (List.finRange (rem + 1)).foldl
        (fun acc i => acc * coeff[(⟨i.val, by
          have hi : i.val < rem + 1 := i.isLt
          omega⟩ : Fin n)][(insertAt c pref (Fin.last rem))[i]]) 1 =
      (List.finRange rem).foldl
          (fun acc i => acc * coeff[(⟨i.val, by
            have hi : i.val < rem := i.isLt
            omega⟩ : Fin n)][pref[i]]) 1 *
        coeff[(⟨rem, hrem⟩ : Fin n)][c] := by
  rw [List.finRange_succ_last]
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  congr 1
  · simp only [List.foldl_map]
    apply foldl_det_product_congr
    intro i _hmem
    change
      coeff[(⟨i.val, by
        have hi : i.val < rem := i.isLt
        omega⟩ : Fin n)][(insertAt c pref (Fin.last rem))[i.castSucc]] =
      coeff[(⟨i.val, by
        have hi : i.val < rem := i.isLt
        omega⟩ : Fin n)][pref[i]]
    exact congrArg
      (fun x : Fin m => coeff[(⟨i.val, by
        have hi : i.val < rem := i.isLt
        omega⟩ : Fin n)][x])
      (insertAt_last_get_castSucc c pref i)
  · change
      coeff[(⟨rem, hrem⟩ : Fin n)][(insertAt c pref (Fin.last rem))[Fin.last rem]] =
        coeff[(⟨rem, hrem⟩ : Fin n)][c]
    exact congrArg (fun x : Fin m => coeff[(⟨rem, hrem⟩ : Fin n)][x])
      (insertAt_get_self c pref (Fin.last rem))

private theorem partialColumnTupleCoeff_vectorLengthCast
    {R : Type u} [Mul R] [OfNat R 1] {n m k : Nat}
    (coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : k = n - chosen.length) (hkn : k ≤ n) (v : Vector (Fin m) k) :
    partialColumnTupleCoeff coeff chosen (vectorLengthCast hk v) =
    (List.finRange k).foldl
      (fun acc (i : Fin k) => acc *
        coeff[(⟨i.val, Nat.lt_of_lt_of_le i.isLt hkn⟩ : Fin n)][v[i]]) 1 := by
  subst hk
  unfold partialColumnTupleCoeff
  rcases v with ⟨xs, hx⟩
  rfl

private theorem partialColumnTupleCoeff_insertAt_last
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (coeff : Matrix R n m) (chosen : List (Fin m)) (c : Fin m)
    (pref : Vector (Fin m) (n - (c :: chosen).length))
    (hk : (c :: chosen).length ≤ n)
    (hlen : (n - (c :: chosen).length) + 1 = n - chosen.length := by
      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
      omega) :
    partialColumnTupleCoeff coeff chosen
        (vectorLengthCast hlen
          (insertAt c pref (Fin.last (n - (c :: chosen).length)))) =
      coeff[(⟨n - chosen.length - 1, by
        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
        omega⟩ : Fin n)][c] *
        partialColumnTupleCoeff coeff (c :: chosen) pref := by
  have hcons : (c :: chosen).length = chosen.length + 1 := rfl
  have hrem_lt : n - (c :: chosen).length < n := by omega
  have hlen_le : (n - (c :: chosen).length) + 1 ≤ n := by omega
  rw [partialColumnTupleCoeff_vectorLengthCast coeff chosen hlen hlen_le
      (insertAt c pref (Fin.last (n - (c :: chosen).length)))]
  rw [partialColumnTupleCoeff_insertAt_last_fold coeff c pref hrem_lt]
  unfold partialColumnTupleCoeff
  refine Eq.trans (Lean.Grind.CommSemiring.mul_comm _ _) ?_
  congr 1

private theorem columnTupleVectors_suffix_rhs_step
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) :
    (columnTupleVectors ((n - (chosen.length + 1)) + 1) m).foldl
        (fun acc pref => acc +
          partialColumnTupleCoeff coeff chosen
            (vectorLengthCast (by omega : (n - (chosen.length + 1)) + 1 =
              n - chosen.length) pref) *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen
                  (vectorLengthCast (by omega : (n - (chosen.length + 1)) + 1 =
                    n - chosen.length) pref) (by omega))))) 0 =
      (List.finRange m).foldl
        (fun acc c => acc +
          coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
            (columnTupleVectors (n - (c :: chosen).length) m).foldl
              (fun acc pref => acc +
                partialColumnTupleCoeff coeff (c :: chosen) pref *
                  det (columnTupleMatrix source
                    (columnTupleVectorFn
                      (assembleColumnsSuffix (c :: chosen) pref (by
                        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                        omega))))) 0) 0 := by
  have hlen :
      n - chosen.length = (n - (chosen.length + 1)) + 1 := by
    omega
  change
    (((columnTupleVectors (n - (chosen.length + 1)) m).flatMap fun pref =>
        (List.finRange m).map fun c =>
          insertAt c pref (Fin.last (n - (chosen.length + 1)))).foldl
        (fun acc pref => acc +
          partialColumnTupleCoeff coeff chosen (vectorLengthCast hlen.symm pref) *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen (vectorLengthCast hlen.symm pref) (by omega))))) 0) =
      (List.finRange m).foldl
        (fun acc c => acc +
          coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
            (columnTupleVectors (n - (c :: chosen).length) m).foldl
              (fun acc pref => acc +
                partialColumnTupleCoeff coeff (c :: chosen) pref *
                  det (columnTupleMatrix source
                    (columnTupleVectorFn
                      (assembleColumnsSuffix (c :: chosen) pref (by
                        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                        omega))))) 0) 0
  rw [foldl_det_sum_flatMap]
  simp only [List.foldl_map]
  rw [foldl_det_sum_nested_zero]
  rw [foldl_det_sum_swap]
  apply foldl_det_sum_congr
  intro c _hc
  have hfactor :
      (columnTupleVectors (n - (chosen.length + 1)) m).foldl
          (fun acc pref => acc +
            coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
              (partialColumnTupleCoeff coeff (c :: chosen) pref *
                det (columnTupleMatrix source
                  (columnTupleVectorFn
                    (assembleColumnsSuffix (c :: chosen) pref (by
                      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                      omega)))))) 0 =
        coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
          (columnTupleVectors (n - (chosen.length + 1)) m).foldl
            (fun acc pref => acc +
              partialColumnTupleCoeff coeff (c :: chosen) pref *
                det (columnTupleMatrix source
                  (columnTupleVectorFn
                    (assembleColumnsSuffix (c :: chosen) pref (by
                      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                      omega))))) 0 := by
    exact foldl_det_sum_mul_left_zero
      (columnTupleVectors (n - (chosen.length + 1)) m)
      (coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c])
      (fun pref =>
        partialColumnTupleCoeff coeff (c :: chosen) pref *
          det (columnTupleMatrix source
            (columnTupleVectorFn
              (assembleColumnsSuffix (c :: chosen) pref (by
                have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                omega)))))
  change
    (columnTupleVectors (n - (chosen.length + 1)) m).foldl
        (fun acc' x => acc' +
          partialColumnTupleCoeff coeff chosen
              (vectorLengthCast hlen.symm (insertAt c x (Fin.last (n - (chosen.length + 1))))) *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen
                  (vectorLengthCast hlen.symm (insertAt c x (Fin.last (n - (chosen.length + 1)))))
                  (by omega))))) 0 =
      coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
        (columnTupleVectors (n - (chosen.length + 1)) m).foldl
          (fun acc pref => acc +
            partialColumnTupleCoeff coeff (c :: chosen) pref *
              det (columnTupleMatrix source
                (columnTupleVectorFn
                  (assembleColumnsSuffix (c :: chosen) pref (by
                    have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                    omega))))) 0
  rw [← hfactor]
  apply foldl_det_sum_congr
  intro pref _hpref
  have hcast :
      (n - (chosen.length + 1)) + 1 = n - chosen.length := by
    omega
  have hkcons : (c :: chosen).length ≤ n := by
    have hcons : (c :: chosen).length = chosen.length + 1 := rfl
    omega
  have hcoeff :
      partialColumnTupleCoeff coeff chosen
          (vectorLengthCast hcast
            (insertAt c pref (Fin.last (n - (chosen.length + 1))))) =
        coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
          partialColumnTupleCoeff coeff (c :: chosen) pref := by
    simpa only [List.length_cons] using
      (partialColumnTupleCoeff_insertAt_last coeff chosen c pref hkcons hcast)
  have hdet :
      det (columnTupleMatrix source
          (columnTupleVectorFn
            (assembleColumnsSuffix chosen
              (vectorLengthCast hcast
                (insertAt c pref (Fin.last (n - (chosen.length + 1)))))
              (by omega)))) =
        det (columnTupleMatrix source
          (columnTupleVectorFn (assembleColumnsSuffix (c :: chosen) pref hkcons))) := by
    simpa only [List.length_cons] using
      (det_columnTupleMatrix_assembleColumnsSuffix_insertAt_last
        source chosen c pref hkcons hcast)
  rw [hcoeff, hdet]
  grind

private theorem columnTupleVectors_suffix_rhs_step_natural
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) :
    (columnTupleVectors (n - chosen.length) m).foldl
        (fun acc pref => acc +
          partialColumnTupleCoeff coeff chosen pref *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen pref (by omega))))) 0 =
      (List.finRange m).foldl
        (fun acc c => acc +
          coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
            (columnTupleVectors (n - (c :: chosen).length) m).foldl
              (fun acc pref => acc +
                partialColumnTupleCoeff coeff (c :: chosen) pref *
                  det (columnTupleMatrix source
                    (columnTupleVectorFn
                      (assembleColumnsSuffix (c :: chosen) pref (by
                        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                        omega))))) 0) 0 := by
  rw [columnTupleVectors_foldl_vectorLengthCast
    (by omega : (n - (chosen.length + 1)) + 1 = n - chosen.length)]
  exact columnTupleVectors_suffix_rhs_step source coeff chosen hk

private theorem assembleColumnsSuffix_full
    {n m : Nat} (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length))
    (hk : chosen.length ≤ n) (hfull : chosen.length = n) :
    assembleColumnsSuffix chosen pref hk =
      Vector.ofFn (fun j : Fin n => chosen[j.val]'(by omega)) := by
  apply Vector.ext
  intro i hi
  change (assembleColumnsSuffix chosen pref hk)[(⟨i, hi⟩ : Fin n)] =
    (Vector.ofFn (fun j : Fin n => chosen[j.val]'(by omega)))[(⟨i, hi⟩ : Fin n)]
  simpa [hfull] using
    (assembleColumnsSuffix_right chosen pref hk (⟨i, by omega⟩ : Fin chosen.length))

private theorem partialColumnTupleCoeff_full
    {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (coeff : Matrix R n m) (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length))
    (hfull : chosen.length = n) :
    partialColumnTupleCoeff coeff chosen pref = 1 := by
  subst n
  unfold partialColumnTupleCoeff
  have hlist : List.finRange (chosen.length - chosen.length) = [] := by simp
  rw [hlist]
  rfl

private theorem det_columnSumMatrixWithSuffix_eq_sum
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length ≤ n) :
    det (columnSumMatrixWithSuffix source coeff chosen) =
      (columnTupleVectors (n - chosen.length) m).foldl
        (fun acc pref => acc +
          partialColumnTupleCoeff coeff chosen pref *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen pref hk)))) 0 := by
  by_cases hfull : chosen.length = n
  ·
      have hfull : chosen.length = n := by omega
      subst n
      rw [columnSumMatrixWithSuffix_eq_columnTupleMatrix source coeff chosen hfull]
      let hcast : 0 = chosen.length - chosen.length := by omega
      rw [columnTupleVectors_foldl_vectorLengthCast hcast]
      simp only [columnTupleVectors, List.foldl_cons, List.foldl_nil]
      rw [partialColumnTupleCoeff_full coeff chosen (vectorLengthCast hcast emptyVec) hfull]
      have hdet :
          det (columnTupleMatrix source (fun j : Fin chosen.length => chosen[j.val]'(by omega))) =
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen (vectorLengthCast hcast emptyVec) hk))) := by
        apply congrArg det
        apply congrArg (columnTupleMatrix source)
        funext j
        simp [columnTupleVectorFn]
        rw [assembleColumnsSuffix_full chosen (vectorLengthCast hcast emptyVec) hk hfull]
        simp
      rw [hdet]
      grind
  ·
      have hklt : chosen.length < n := by omega
      rw [det_columnSumMatrixWithSuffix_expand source coeff chosen hklt]
      rw [columnTupleVectors_suffix_rhs_step_natural source coeff chosen hklt]
      apply foldl_det_sum_congr
      intro c _hc
      congr 2
      have hkcons : (c :: chosen).length ≤ n := by
        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
        omega
      exact det_columnSumMatrixWithSuffix_eq_sum source coeff (c :: chosen) hkcons
termination_by n - chosen.length
decreasing_by
  simp_wf
  omega

/-- Expand the determinant of a matrix whose columns are linear combinations
of source columns as a finite sum over all ordered column tuples. This is the
Mathlib-free multilinearity form behind Cauchy-Binet. -/
theorem det_columnSumMatrix_eq_sum_columnTuples
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) :
    det (columnSumMatrix source coeff) =
      (columnTupleVectors n m).foldl
        (fun acc cols => acc +
          columnTupleCoeff coeff cols *
            det (columnTupleMatrix source (columnTupleVectorFn cols))) 0 := by
  rw [← columnSumMatrixWithSuffix_nil source coeff]
  rw [det_columnSumMatrixWithSuffix_eq_sum source coeff [] (by simp)]
  apply foldl_det_sum_congr
  intro cols _hcols
  have hcoeff : partialColumnTupleCoeff coeff [] cols = columnTupleCoeff coeff cols :=
    partialColumnTupleCoeff_nil coeff cols
  have hdet :
      det (columnTupleMatrix source (columnTupleVectorFn (assembleColumnsSuffix [] cols (by simp)))) =
        det (columnTupleMatrix source (columnTupleVectorFn cols)) := by
    apply congrArg det
    apply Vector.ext
    intro i hi
    change (columnTupleMatrix source (columnTupleVectorFn (assembleColumnsSuffix [] cols (by simp))))[
        (⟨i, hi⟩ : Fin n)] =
      (columnTupleMatrix source (columnTupleVectorFn cols))[(⟨i, hi⟩ : Fin n)]
    apply Vector.ext
    intro j hj
    simp [columnTupleMatrix, columnTupleVectorFn, ofFn]
    change source[(⟨i, hi⟩ : Fin n)][
        (assembleColumnsSuffix [] cols (by simp))[(⟨j, hj⟩ : Fin n)]] =
      source[(⟨i, hi⟩ : Fin n)][cols[(⟨j, hj⟩ : Fin n)]]
    exact congrArg (fun x : Fin m => source[(⟨i, hi⟩ : Fin n)][x])
      (assembleColumnsSuffix_left ([] : List (Fin m)) cols (by simp) (⟨j, by simp [hj]⟩))
  rw [hcoeff, hdet]

/-- The determinant of a row Gram matrix expands as the ordered-column tuple
sum induced by the generic column-sum determinant expansion. -/
theorem det_gramMatrix_eq_sum_columnTuples
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat} (A : Matrix R n m) :
    det (gramMatrix A) =
      (columnTupleVectors n m).foldl
        (fun acc cols => acc +
          columnTupleCoeff A cols *
            det (columnTupleMatrix A (columnTupleVectorFn cols))) 0 := by
  have hgram : gramMatrix A = columnSumMatrix A A := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro c hc
    change (gramMatrix A)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrix A A)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
    rw [columnSumMatrix_entry]
    simp [gramMatrix, ofFn, row, Hex.Vector.dotProduct]
    apply foldl_det_sum_congr
    intro k _hk
    exact Lean.Grind.CommSemiring.mul_comm A[(⟨r, hr⟩ : Fin n)][k] A[(⟨c, hc⟩ : Fin n)][k]
  rw [hgram]
  exact det_columnSumMatrix_eq_sum_columnTuples A A

/-! ### Strictly-increasing column-tuple enumeration

The Cauchy-Binet sum-of-squares formula needs a Mathlib-free enumeration of the
"essentially distinct" column choices: each strictly increasing length-`n`
selection from `Fin m` represents one orbit of injective ordered tuples under
the action of permutations of `Fin n`. The enumeration below builds these
tuples by appending the new largest element, recursing on a `bound` parameter
that constrains the next entry to be strictly less than `bound`.
-/

/-- All strictly increasing length-`n` column tuples in `Fin m` whose entries
are all `< bound`. The recursion appends a new largest element `c < bound` and
recurses on the remaining prefix with the smaller bound `c.val`. -/
private def selectedColumnTuplesUpTo (m : Nat) :
    (n : Nat) → (bound : Nat) → List (Vector (Fin m) n)
  | 0, _ => [emptyVec]
  | n + 1, bound =>
      ((List.finRange m).filter (fun c : Fin m => decide (c.val < bound))).flatMap
        fun c =>
          (selectedColumnTuplesUpTo m n c.val).map fun pref => pref.push c

/-- Enumerate all strictly increasing length-`n` column selections from `Fin m`.
This list of orbit representatives drives the Cauchy-Binet grouping argument
that re-folds the ordered-tuple Gram expansion as a sum of squared minors. -/
def selectedColumnTuples (n m : Nat) : List (Vector (Fin m) n) :=
  selectedColumnTuplesUpTo m n m

/-- A column tuple is strictly increasing as a function `Fin n → Fin m`. -/
def IsStrictlyIncreasingColumnTuple {m n : Nat} (cols : Vector (Fin m) n) : Prop :=
  ∀ i j : Fin n, i.val < j.val → cols[i].val < cols[j].val

private theorem isStrictlyIncreasingColumnTuple_emptyVec {m : Nat} :
    IsStrictlyIncreasingColumnTuple (m := m) (n := 0) emptyVec := by
  intro i _ _
  exact i.elim0

private theorem getElem_push_castSucc {α : Type u} {n : Nat}
    (v : Vector α n) (x : α) (i : Fin n) :
    (v.push x)[i.castSucc] = v[i] := by
  rcases i with ⟨i, hi⟩
  simp [Fin.castSucc, Fin.castAdd, Fin.castLE, Vector.getElem_push_lt, hi]

private theorem getElem_push_last_index {α : Type u} {n : Nat}
    (v : Vector α n) (x : α) :
    (v.push x)[Fin.last n] = x := by
  simp [Fin.last, Vector.getElem_push_eq]

/-- Pushing a new largest element preserves strict increase as long as the
old largest entry was still smaller than the new element. -/
private theorem isStrictlyIncreasingColumnTuple_push {m n : Nat}
    (pref : Vector (Fin m) n) (c : Fin m)
    (hpref : IsStrictlyIncreasingColumnTuple pref)
    (hbound : ∀ i : Fin n, pref[i].val < c.val) :
    IsStrictlyIncreasingColumnTuple (pref.push c) := by
  intro i j hij
  rcases Nat.lt_succ_iff_lt_or_eq.mp j.isLt with hjlt | hjeq
  · -- j < n, so both i, j are inside `pref`.
    have hilt : i.val < n := by omega
    have hi_eq : i = (⟨i.val, hilt⟩ : Fin n).castSucc := by
      apply Fin.ext; rfl
    have hj_eq : j = (⟨j.val, hjlt⟩ : Fin n).castSucc := by
      apply Fin.ext; rfl
    rw [hi_eq, hj_eq, getElem_push_castSucc, getElem_push_castSucc]
    exact hpref ⟨i.val, hilt⟩ ⟨j.val, hjlt⟩ hij
  · -- j.val = n, so j is the last index.
    have hilt : i.val < n := by omega
    have hi_eq : i = (⟨i.val, hilt⟩ : Fin n).castSucc := by
      apply Fin.ext; rfl
    have hj_eq : j = Fin.last n := by
      apply Fin.ext; simpa using hjeq
    rw [hi_eq, hj_eq, getElem_push_castSucc, getElem_push_last_index]
    exact hbound ⟨i.val, hilt⟩

/-- Forward characterization: every enumerated tuple is strictly increasing and
its entries are all bounded by the recursion bound. -/
private theorem mem_selectedColumnTuplesUpTo_imp {m : Nat} :
    ∀ (n bound : Nat) (v : Vector (Fin m) n),
      v ∈ selectedColumnTuplesUpTo m n bound →
        IsStrictlyIncreasingColumnTuple v ∧
          ∀ i : Fin n, v[i].val < bound
  | 0, _, v, hv => by
      simp [selectedColumnTuplesUpTo] at hv
      subst hv
      refine ⟨isStrictlyIncreasingColumnTuple_emptyVec, ?_⟩
      intro i; exact i.elim0
  | n + 1, bound, v, hv => by
      rw [selectedColumnTuplesUpTo, List.mem_flatMap] at hv
      rcases hv with ⟨c, hc, hmem⟩
      have hclt : c.val < bound := by
        rw [List.mem_filter] at hc
        simpa using hc.2
      rw [List.mem_map] at hmem
      rcases hmem with ⟨pref, hpref, rfl⟩
      have ih := mem_selectedColumnTuplesUpTo_imp n c.val pref hpref
      refine ⟨?_, ?_⟩
      · -- strict increase of `pref.push c`
        apply isStrictlyIncreasingColumnTuple_push pref c ih.1
        intro i
        exact ih.2 i
      · -- every entry of `pref.push c` is `< bound`
        intro i
        rcases Nat.lt_succ_iff_lt_or_eq.mp i.isLt with hilt | hieq
        · have hi_eq : i = (⟨i.val, hilt⟩ : Fin n).castSucc := by
            apply Fin.ext; rfl
          rw [hi_eq, getElem_push_castSucc]
          exact Nat.lt_of_lt_of_le (ih.2 ⟨i.val, hilt⟩) (Nat.le_of_lt hclt)
        · have hi_eq : i = Fin.last n := by
            apply Fin.ext; simpa using hieq
          rw [hi_eq, getElem_push_last_index]
          exact hclt

/-- Backward characterization: every strictly increasing tuple whose entries
are all `< bound` is enumerated by the recursive helper. -/
private theorem mem_selectedColumnTuplesUpTo_of_strictly_increasing {m : Nat} :
    ∀ (n bound : Nat) (v : Vector (Fin m) n),
      IsStrictlyIncreasingColumnTuple v →
        (∀ i : Fin n, v[i].val < bound) →
        v ∈ selectedColumnTuplesUpTo m n bound
  | 0, _, v, _, _ => by
      have hv : v = emptyVec := by
        apply Vector.ext
        intro i hi
        exact absurd hi (by omega)
      simp [selectedColumnTuplesUpTo, hv]
  | n + 1, bound, v, hsi, hbound => by
      -- factor v as `(v.pop).push v[n]`
      have hpush : (v.pop).push (v[Fin.last n]) = v := by
        have hback : v.back = v[Fin.last n] := by
          simp [Vector.back, Fin.last]
        rw [← hback]
        exact Vector.push_pop_back v
      have hpop_get : ∀ i : Fin n,
          v.pop[i] = v[(⟨i.val, by have := i.isLt; omega⟩ : Fin (n + 1))] := by
        intro i
        rcases i with ⟨i, hi⟩
        change v.pop[i]'(by simp; omega) = v[i]'(by omega)
        exact Vector.getElem_pop (h := by simp; omega)
      rw [selectedColumnTuplesUpTo, List.mem_flatMap]
      refine ⟨v[Fin.last n], ?_, ?_⟩
      · -- v[last] is in the filtered finRange
        rw [List.mem_filter]
        refine ⟨List.mem_finRange _, ?_⟩
        simpa using hbound (Fin.last n)
      · rw [List.mem_map]
        refine ⟨v.pop, ?_, hpush⟩
        apply mem_selectedColumnTuplesUpTo_of_strictly_increasing n (v[Fin.last n]).val
        · -- pop preserves strict increase
          intro i j hij
          have h1 := hpop_get i
          have h2 := hpop_get j
          have base := hsi
            (⟨i.val, by have := i.isLt; omega⟩ : Fin (n + 1))
            (⟨j.val, by have := j.isLt; omega⟩ : Fin (n + 1)) hij
          rw [← h1, ← h2] at base
          exact base
        · -- bound: pop entries < v[Fin.last n]
          intro i
          have h1 := hpop_get i
          have hilt : i.val < n + 1 := by have := i.isLt; omega
          have hi_lt_last :
              (⟨i.val, hilt⟩ : Fin (n + 1)).val < (Fin.last n).val := by
            have := i.isLt
            simp [Fin.last]
          have base := hsi (⟨i.val, hilt⟩ : Fin (n + 1)) (Fin.last n) hi_lt_last
          rw [← h1] at base
          exact base

/-- Public membership characterization: a column tuple lies in
`selectedColumnTuples n m` iff it is strictly increasing. -/
theorem mem_selectedColumnTuples_iff {n m : Nat} (cols : Vector (Fin m) n) :
    cols ∈ selectedColumnTuples n m ↔ IsStrictlyIncreasingColumnTuple cols := by
  refine ⟨?_, ?_⟩
  · intro hmem
    exact (mem_selectedColumnTuplesUpTo_imp n m cols hmem).1
  · intro hsi
    apply mem_selectedColumnTuplesUpTo_of_strictly_increasing n m cols hsi
    intro i
    exact cols[i].isLt

/-- Strictly increasing column tuples induce injective `Fin n → Fin m` selection
functions, so each enumerated tuple yields an injective `columnTupleVectorFn`. -/
theorem isStrictlyIncreasingColumnTuple_injective {n m : Nat}
    {cols : Vector (Fin m) n} (hsi : IsStrictlyIncreasingColumnTuple cols) :
    Function.Injective (columnTupleVectorFn cols) := by
  intro i j hij
  -- Either i.val < j.val, j.val < i.val, or i.val = j.val. Strict increase rules out the first two.
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · -- i.val < j.val ⇒ cols[i].val < cols[j].val ⇒ cols[i] ≠ cols[j], contradiction.
    have : cols[i].val < cols[j].val := hsi i j hlt
    exact absurd (congrArg Fin.val hij) (Nat.ne_of_lt this)
  · exact Fin.ext heq
  · have : cols[j].val < cols[i].val := hsi j i hgt
    exact absurd (congrArg Fin.val hij.symm) (Nat.ne_of_lt this)

/-- Convenience corollary: every column tuple enumerated by `selectedColumnTuples`
yields an injective column-selection function. -/
theorem mem_selectedColumnTuples_injective {n m : Nat}
    {cols : Vector (Fin m) n} (hmem : cols ∈ selectedColumnTuples n m) :
    Function.Injective (columnTupleVectorFn cols) :=
  isStrictlyIncreasingColumnTuple_injective ((mem_selectedColumnTuples_iff cols).mp hmem)

/-- The push map `pref ↦ pref.push c` is injective on prefixes for any fixed
last element `c`, since the popped vector recovers the prefix. -/
private theorem push_left_injective {α : Type u} {n : Nat} (c : α) :
    Function.Injective fun pref : Vector α n => pref.push c := by
  intro pref pref' h
  have := congrArg Vector.pop h
  simpa using this

/-- Outer-list version of `Nodup` for the `flatMap` body that builds
`selectedColumnTuplesUpTo` from a list of "last column" candidates. -/
private theorem selectedColumnTuplesUpTo_flatMap_nodup (m n : Nat) :
    ∀ (cs : List (Fin m)), cs.Nodup →
      (∀ c ∈ cs, (selectedColumnTuplesUpTo m n c.val).Nodup) →
      (cs.flatMap fun c =>
        (selectedColumnTuplesUpTo m n c.val).map fun pref => pref.push c).Nodup
  | [], _, _ => by simp
  | c :: cs, hnodup, hinner => by
      simp only [List.flatMap_cons]
      simp only [List.nodup_cons] at hnodup
      rw [List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · -- inner `(map ...)` for the head `c` is Nodup
        apply list_nodup_map_of_injective (push_left_injective c)
        exact hinner c (by simp)
      · -- suffix Nodup by IH
        exact selectedColumnTuplesUpTo_flatMap_nodup m n cs hnodup.2
          (fun c' hc' => hinner c' (List.mem_cons_of_mem c hc'))
      · -- disjointness: head produces last-element c, suffix produces last-element c' ∈ cs ⇒ c' ≠ c
        intro a hahead b hbsuffix hab
        rcases List.mem_map.mp hahead with ⟨pref, _, rfl⟩
        rcases List.mem_flatMap.mp hbsuffix with ⟨c', hc', hb⟩
        rcases List.mem_map.mp hb with ⟨pref', _, rfl⟩
        -- last entries match c and c' respectively, but c ≠ c'
        have hlast : (pref.push c)[Fin.last n] = (pref'.push c')[Fin.last n] := by
          rw [hab]
        rw [getElem_push_last_index, getElem_push_last_index] at hlast
        exact hnodup.1 (hlast ▸ hc')

private theorem selectedColumnTuplesUpTo_nodup (m : Nat) :
    ∀ (n bound : Nat), (selectedColumnTuplesUpTo m n bound).Nodup
  | 0, _ => by simp [selectedColumnTuplesUpTo]
  | n + 1, bound => by
      rw [selectedColumnTuplesUpTo]
      apply selectedColumnTuplesUpTo_flatMap_nodup
      · exact (List.nodup_finRange m).filter _
      · intro c _hc
        exact selectedColumnTuplesUpTo_nodup m n c.val

/-- The strictly-increasing column-tuple enumeration has no duplicates. -/
theorem selectedColumnTuples_nodup {n m : Nat} :
    (selectedColumnTuples n m).Nodup :=
  selectedColumnTuplesUpTo_nodup m n m

/-! ### Canonical sort and orbit factorization for injective column tuples

For the Cauchy-Binet orbit-grouping argument we need, for every injective
ordered column tuple `cols : Vector (Fin m) n`, a canonical factorization

```
cols[i] = (sortInjTuple cols)[(sortInjPerm cols)[i]]
```

where `sortInjTuple cols` is strictly increasing (i.e. lives in
`selectedColumnTuples n m`) and `sortInjPerm cols` is a permutation of
`Fin n` (i.e. lives in `permutationVectors n`). This gives a bijection
between injective `columnTupleVectors n m` entries and the product
`selectedColumnTuples n m × permutationVectors n`, which lets the orbit
sum group ordered minors by their canonical sorted column choice.

The implementation is rank-based: `sortInjPerm cols i` is the number of
columns in `cols` strictly smaller in value than `cols[i]`. For any
`cols`, this is `< n` because `cols[i]` is never strictly less than
itself; for *injective* `cols`, the rank is moreover a bijection on
`Fin n`. -/

/-- Count of indices whose `cols`-image has strictly smaller `Fin.val`
than that at `i`. This is the natural-number form of the rank. -/
private def columnRankNat {m n : Nat} (cols : Vector (Fin m) n) (i : Fin n) : Nat :=
  ((List.finRange n).filter fun j => decide (cols[j].val < cols[i].val)).length

/-- The rank is always strictly less than `n`: index `i` itself is never
in the filter, so the filter is a strict sublist of `finRange n`. -/
private theorem columnRankNat_lt {m n : Nat} (cols : Vector (Fin m) n) (i : Fin n) :
    columnRankNat cols i < n := by
  have hwit :
      ∃ x ∈ List.finRange n, ¬ (decide (cols[x].val < cols[i].val) = true) := by
    refine ⟨i, List.mem_finRange i, ?_⟩
    simp
  have hlt :=
    (List.length_filter_lt_length_iff_exists
      (p := fun j => decide (cols[j].val < cols[i].val))
      (l := List.finRange n)).mpr hwit
  simpa [columnRankNat, List.length_finRange] using hlt

/-- Canonical sorting permutation: for each index `i`, output the rank of
`cols[i]` (number of strictly smaller positions). For an injective `cols`
this is genuinely a permutation of `Fin n`; for a non-injective `cols` it
is still well-defined but may have repeated values. -/
def sortInjPerm {m n : Nat} (cols : Vector (Fin m) n) : Vector (Fin n) n :=
  Vector.ofFn fun i => ⟨columnRankNat cols i, columnRankNat_lt cols i⟩

/-- The `i`-th value of the sorting permutation is the rank `columnRankNat cols i`
of `cols[i]` (the number of strictly smaller positions). -/
@[grind =] theorem sortInjPerm_getElem_val {m n : Nat}
    (cols : Vector (Fin m) n) (i : Fin n) :
    (sortInjPerm cols)[i].val = columnRankNat cols i := by
  simp [sortInjPerm]

/-- The canonical sorted version of `cols`: read `cols` through the inverse
of `sortInjPerm`. For an injective `cols` this is strictly increasing; for
a non-injective `cols` the value is well-defined but not meaningful. -/
def sortInjTuple {m n : Nat} (cols : Vector (Fin m) n) : Vector (Fin m) n :=
  Vector.ofFn fun r => cols[(inversePermutationVector (sortInjPerm cols))[r]]

/-- Strict version of `List.countP_mono_left`: a single witness where
`q` holds but `p` doesn't forces strict inequality. -/
private theorem countP_lt_countP_of_witness {α : Type u}
    (p q : α → Bool)
    (hle_all : ∀ (xs : List α) (x : α), x ∈ xs → p x = true → q x = true) :
    ∀ (xs : List α) (k : α), k ∈ xs → q k = true → p k = false →
      xs.countP p < xs.countP q
  | [], _k, hkmem, _, _ => by exact absurd hkmem List.not_mem_nil
  | x :: xs, k, hkmem, hqk, hpk => by
      simp only [List.mem_cons] at hkmem
      rcases hkmem with heq | hk_in_xs
      · -- x = k: at the head, `p k = false` and `q k = true`.
        subst heq
        have hxs_le : xs.countP p ≤ xs.countP q :=
          List.countP_mono_left
            (fun y hy => hle_all _ y (List.mem_cons_of_mem k hy))
        simp [hqk, hpk]
        omega
      · -- k ∈ xs: recurse on the tail.
        have ih :=
          countP_lt_countP_of_witness p q hle_all xs k hk_in_xs hqk hpk
        by_cases hpx : p x = true
        · have hqx : q x = true := hle_all (x :: xs) x List.mem_cons_self hpx
          simp [hpx, hqx]; omega
        · have hpx' : p x = false := by
            cases hpe : p x with
            | true => exact absurd hpe hpx
            | false => rfl
          by_cases hqx : q x = true
          · simp [hpx', hqx]; omega
          · have hqx' : q x = false := by
              cases hqe : q x with
              | true => exact absurd hqe hqx
              | false => rfl
            simp [hpx', hqx']; exact ih

/-- Monotonicity of the rank: if `cols[i].val < cols[j].val` then the
rank strictly increases from `i` to `j`. Holds for any `cols`, no
injectivity assumption needed. -/
private theorem columnRankNat_strictMono {m n : Nat} (cols : Vector (Fin m) n)
    {i j : Fin n} (hij : cols[i].val < cols[j].val) :
    columnRankNat cols i < columnRankNat cols j := by
  -- Switch from `length filter` to `countP`.
  have hlen_eq_p :
      ((List.finRange n).filter fun k => decide (cols[k].val < cols[i].val)).length
        = (List.finRange n).countP (fun k => decide (cols[k].val < cols[i].val)) := by
    rw [List.countP_eq_length_filter]
  have hlen_eq_q :
      ((List.finRange n).filter fun k => decide (cols[k].val < cols[j].val)).length
        = (List.finRange n).countP (fun k => decide (cols[k].val < cols[j].val)) := by
    rw [List.countP_eq_length_filter]
  unfold columnRankNat
  rw [hlen_eq_p, hlen_eq_q]
  -- Strict comparison via element `i`.
  refine countP_lt_countP_of_witness
    (fun k => decide (cols[k].val < cols[i].val))
    (fun k => decide (cols[k].val < cols[j].val))
    ?_ (List.finRange n) i (List.mem_finRange i)
    (decide_eq_true hij) ?_
  · intro _ k _hkmem hpk
    have hkk : cols[k].val < cols[i].val := by simpa using hpk
    exact decide_eq_true (Nat.lt_trans hkk hij)
  · simp

/-- For an injective `cols`, the rank function is itself injective: two
positions with the same rank must agree as `Fin n`. -/
private theorem columnRankNat_injective_of_injective {m n : Nat}
    (cols : Vector (Fin m) n) (hinj : Function.Injective (columnTupleVectorFn cols)) :
    Function.Injective (columnRankNat cols) := by
  intro i j hrank
  rcases Nat.lt_trichotomy cols[i].val cols[j].val with hlt | heq | hgt
  · exact absurd (columnRankNat_strictMono cols hlt) (by omega)
  · -- cols[i].val = cols[j].val ⇒ cols[i] = cols[j] ⇒ i = j by injectivity.
    have hcol_eq : cols[i] = cols[j] := Fin.ext heq
    exact hinj hcol_eq
  · exact absurd (columnRankNat_strictMono cols hgt) (by omega)

/-- For an injective `cols`, `sortInjPerm cols` is a permutation as a list. -/
private theorem sortInjPerm_toList_nodup_of_injective {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) :
    (sortInjPerm cols).toList.Nodup := by
  rw [vector_toList_eq_finRange_map_get]
  apply list_nodup_map_of_injective ?_ (List.nodup_finRange n)
  intro i j hij
  have hval : columnRankNat cols i = columnRankNat cols j := by
    have := congrArg Fin.val hij
    simpa [sortInjPerm] using this
  exact columnRankNat_injective_of_injective cols hinj hval

/-- For an injective `cols`, `sortInjPerm cols ∈ permutationVectors n`. -/
theorem sortInjPerm_mem_permutationVectors {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) :
    sortInjPerm cols ∈ permutationVectors n :=
  permutationVectors_complete (sortInjPerm_toList_nodup_of_injective cols hinj)

/-- Converse of `columnRankNat_strictMono` for injective `cols`: a strict
rank comparison implies the underlying value comparison. -/
private theorem cols_val_lt_of_rank_lt_of_injective {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols))
    {i j : Fin n} (hij : columnRankNat cols i < columnRankNat cols j) :
    cols[i].val < cols[j].val := by
  rcases Nat.lt_trichotomy cols[i].val cols[j].val with hlt | heq | hgt
  · exact hlt
  · have hcol_eq : cols[i] = cols[j] := Fin.ext heq
    have hij' : i = j := hinj hcol_eq
    subst hij'
    omega
  · have := columnRankNat_strictMono cols hgt
    omega

/-- `Vector.ofFn`-indexed access at a `Fin n` argument, packaged so that
the result is the function applied to the original `Fin n` index rather
than to its repackaged Nat-value form. -/
private theorem vector_ofFn_getElem_fin {α : Type u} {n : Nat}
    (f : Fin n → α) (k : Fin n) :
    (Vector.ofFn f)[k] = f k := by
  rw [show ((Vector.ofFn f)[k] : α) = (Vector.ofFn f)[k.val]'(by simp [k.isLt]) from rfl]
  rw [Vector.getElem_ofFn]

/-- Every length-`n` tuple of column indices appears in
`columnTupleVectors n m`. -/
theorem mem_columnTupleVectors {n m : Nat} (cols : Vector (Fin m) n) :
    cols ∈ columnTupleVectors n m := by
  have hcols : cols = Vector.ofFn (fun i : Fin n => cols[i]) := by
    apply Vector.ext
    intro i hi
    let k : Fin n := ⟨i, hi⟩
    change cols[k] = (Vector.ofFn fun i : Fin n => cols[i])[k]
    rw [vector_ofFn_getElem_fin]
  rw [hcols]
  exact columnTupleVectors_mem_ofFn (fun i : Fin n => cols[i])

/-- Factorization equation: each entry of `cols` is recovered through the
canonical sort/permutation pair. Requires injectivity of `cols`. -/
theorem cols_getElem_eq_sortInjTuple_sortInjPerm {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols))
    (i : Fin n) :
    cols[i] = (sortInjTuple cols)[(sortInjPerm cols)[i]] := by
  have hnodup := sortInjPerm_toList_nodup_of_injective cols hinj
  have hidx :=
    inversePermutationValues_get_index (sortInjPerm cols) hnodup i
  have hinv_eq : inversePermutationVector (sortInjPerm cols)
                   = inversePermutationValues (sortInjPerm cols) hnodup :=
    inversePermutationVector_eq (sortInjPerm cols) hnodup
  have hstep :
      (inversePermutationVector (sortInjPerm cols))[(sortInjPerm cols)[i]]
        = (inversePermutationValues (sortInjPerm cols) hnodup)[(sortInjPerm cols)[i]] :=
    congrArg (fun v : Vector (Fin n) n => v[(sortInjPerm cols)[i]]) hinv_eq
  have hcompose :
      (inversePermutationVector (sortInjPerm cols))[(sortInjPerm cols)[i]] = i :=
    hstep.trans hidx
  rw [sortInjTuple, vector_ofFn_getElem_fin]
  exact (congrArg (fun k : Fin n => cols[k]) hcompose).symm

/-- For an injective `cols`, applying `sortInjPerm` after the inverse
returns the input rank. -/
private theorem sortInjPerm_inv_apply {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) (r : Fin n) :
    (sortInjPerm cols)[(inversePermutationVector (sortInjPerm cols))[r]] = r := by
  have hnodup := sortInjPerm_toList_nodup_of_injective cols hinj
  have hval := inversePermutationValues_get_value (sortInjPerm cols) hnodup r
  have hinv_eq : inversePermutationVector (sortInjPerm cols)
                   = inversePermutationValues (sortInjPerm cols) hnodup :=
    inversePermutationVector_eq (sortInjPerm cols) hnodup
  have hstep :
      (sortInjPerm cols)[(inversePermutationVector (sortInjPerm cols))[r]]
        = (sortInjPerm cols)[(inversePermutationValues (sortInjPerm cols) hnodup)[r]] :=
    congrArg (fun v : Vector (Fin n) n => (sortInjPerm cols)[v[r]]) hinv_eq
  exact hstep.trans hval

/-- For an injective `cols`, the column-rank at the inverse-perm image
of `r` is exactly `r.val`. -/
private theorem columnRankNat_inv_apply {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) (r : Fin n) :
    columnRankNat cols (inversePermutationVector (sortInjPerm cols))[r] = r.val := by
  have hval' := sortInjPerm_inv_apply cols hinj r
  have := congrArg Fin.val hval'
  simpa [sortInjPerm] using this

/-- For an injective `cols`, the canonical sorted tuple is strictly
increasing. -/
theorem isStrictlyIncreasingColumnTuple_sortInjTuple {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) :
    IsStrictlyIncreasingColumnTuple (sortInjTuple cols) := by
  intro r r' hrr'
  have hrank_r := columnRankNat_inv_apply cols hinj r
  have hrank_r' := columnRankNat_inv_apply cols hinj r'
  have hrank_lt :
      columnRankNat cols (inversePermutationVector (sortInjPerm cols))[r] <
        columnRankNat cols (inversePermutationVector (sortInjPerm cols))[r'] := by
    rw [hrank_r, hrank_r']; exact hrr'
  have hval_lt :
      cols[(inversePermutationVector (sortInjPerm cols))[r]].val <
        cols[(inversePermutationVector (sortInjPerm cols))[r']].val :=
    cols_val_lt_of_rank_lt_of_injective cols hinj hrank_lt
  show (sortInjTuple cols)[r].val < (sortInjTuple cols)[r'].val
  rw [sortInjTuple, vector_ofFn_getElem_fin, vector_ofFn_getElem_fin]
  exact hval_lt

/-- For an injective `cols`, the canonical sorted tuple is enumerated by
`selectedColumnTuples n m`. -/
theorem sortInjTuple_mem_selectedColumnTuples {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) :
    sortInjTuple cols ∈ selectedColumnTuples n m :=
  (mem_selectedColumnTuples_iff (sortInjTuple cols)).mpr
    (isStrictlyIncreasingColumnTuple_sortInjTuple cols hinj)

/-! ### Forward injectivity of the sort/permutation pair -/

/-- Pairwise distinctness: two injective column tuples that map to the
same `(sortInjTuple, sortInjPerm)` pair must be equal. -/
theorem sortInj_pair_injective {m n : Nat} {cols cols' : Vector (Fin m) n}
    (hinj : Function.Injective (columnTupleVectorFn cols))
    (hinj' : Function.Injective (columnTupleVectorFn cols'))
    (hsort : sortInjTuple cols = sortInjTuple cols')
    (hperm : sortInjPerm cols = sortInjPerm cols') :
    cols = cols' := by
  apply Vector.ext
  intro k hk
  let i : Fin n := ⟨k, hk⟩
  show cols[i] = cols'[i]
  rw [cols_getElem_eq_sortInjTuple_sortInjPerm cols hinj i,
      cols_getElem_eq_sortInjTuple_sortInjPerm cols' hinj' i]
  -- Use congrArg to swap `sortInjPerm cols` for `sortInjPerm cols'`.
  have hperm_apply :
      (sortInjPerm cols)[i] = (sortInjPerm cols')[i] :=
    congrArg (fun v : Vector (Fin n) n => v[i]) hperm
  -- And use hsort to swap `sortInjTuple cols` for `sortInjTuple cols'`.
  rw [hsort]
  exact congrArg (fun k : Fin n => (sortInjTuple cols')[k]) hperm_apply

/-! ### Reconstruction from `selectedColumnTuples × permutationVectors`

For a strictly-increasing `sel` and a permutation `perm`, the
"reconstruction" `Vector.ofFn (fun i => sel[perm[i]])` is itself
injective, and its canonical sort/permutation pair recovers
`(sel, perm)`. This is the inverse map of `sortInjTuple`/`sortInjPerm`. -/

/-- Reconstruction map: given a sorted choice and a permutation, build
an ordered column tuple. -/
def reconstructInjTuple {m n : Nat}
    (sel : Vector (Fin m) n) (perm : Vector (Fin n) n) : Vector (Fin m) n :=
  Vector.ofFn fun i => sel[perm[i]]

/-- The `i`-th entry of the reconstructed tuple is `sel[perm[i]]`: read the
sorted choice `sel` through the permutation `perm`. -/
@[grind =] theorem reconstructInjTuple_getElem {m n : Nat}
    (sel : Vector (Fin m) n) (perm : Vector (Fin n) n) (i : Fin n) :
    (reconstructInjTuple sel perm)[i] = sel[perm[i]] := by
  rw [reconstructInjTuple, vector_ofFn_getElem_fin]

/-- Selecting columns via the reconstructed tuple equals selecting via `sel`
with the column index permuted by `perm`: entry `(r, c)` agrees with entry
`(r, perm[c])` of the `sel`-selected minor. -/
@[grind =] theorem columnTupleMatrix_reconstructInjTuple_entry
    {R : Type u} {n m : Nat} (A : Matrix R n m)
    (sel : Vector (Fin m) n) (perm : Vector (Fin n) n)
    (r c : Fin n) :
    (columnTupleMatrix A (columnTupleVectorFn (reconstructInjTuple sel perm)))[r][c] =
      (columnTupleMatrix A (columnTupleVectorFn sel))[r][perm[c]] := by
  rw [columnTupleMatrix_entry, columnTupleMatrix_entry]
  exact congrArg (fun col : Fin m => A[r][col])
    (reconstructInjTuple_getElem sel perm c)

private theorem columnTupleMatrix_reconstructInjTuple_eq
    {R : Type u} {n m : Nat} (A : Matrix R n m)
    (sel : Vector (Fin m) n) (perm : Vector (Fin n) n) :
    columnTupleMatrix A (columnTupleVectorFn (reconstructInjTuple sel perm)) =
      columnTupleMatrix A (fun i => sel[perm[i]]) := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change
    (columnTupleMatrix A (columnTupleVectorFn (reconstructInjTuple sel perm)))[
        (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnTupleMatrix A (fun i => sel[perm[i]]))[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnTupleMatrix_entry, columnTupleMatrix_entry]
  exact congrArg (fun col : Fin m => A[(⟨r, hr⟩ : Fin n)][col])
    (reconstructInjTuple_getElem sel perm (⟨c, hc⟩ : Fin n))

/-- Reconstructing an injective tuple from a selected tuple and a permutation
turns the coefficient product into the corresponding determinant product. -/
theorem columnTupleCoeff_reconstructInjTuple
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (sel : Vector (Fin m) n) (perm : Vector (Fin n) n) :
    columnTupleCoeff A (reconstructInjTuple sel perm) =
      detProduct (columnTupleMatrix A (columnTupleVectorFn sel)) perm := by
  unfold columnTupleCoeff detProduct
  apply foldl_det_product_congr
  intro i _hmem
  rw [columnTupleMatrix_entry]
  exact congrArg (fun col : Fin m => A[i][col])
    (reconstructInjTuple_getElem sel perm i)

/-- Counting how many entries of `List.finRange n` have value `< k`. -/
private theorem countP_finRange_val_lt :
    ∀ (n k : Nat), (List.finRange n).countP (fun x : Fin n => decide (x.val < k)) = min n k
  | 0, k => by simp
  | n + 1, k => by
      rw [List.finRange_succ_last, List.countP_append, List.countP_map]
      -- The induction hypothesis applies to the `map Fin.castSucc` part.
      -- `(castSucc x).val = x.val`, so the composed predicate matches.
      have ih := countP_finRange_val_lt n k
      have hmap_eq :
          (List.finRange n).countP ((fun x : Fin (n + 1) => decide (x.val < k)) ∘ Fin.castSucc) =
            (List.finRange n).countP (fun x : Fin n => decide (x.val < k)) := rfl
      rw [hmap_eq, ih]
      -- Singleton contribution.
      simp only [List.countP_singleton, Fin.last]
      -- Goal: min n k + (if decide (n < k) then 1 else 0) = min (n+1) k.
      by_cases hnk : n < k
      · rw [if_pos (by simpa using hnk)]
        omega
      · rw [if_neg (by simpa using hnk)]
        omega

/-- A permutation as a `Vector` acts as an injective function on `Fin n`. -/
private theorem permutationVectors_getElem_injective {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    Function.Injective (fun i : Fin n => perm[i]) := by
  intro i j hij
  have hnodup := permutationVectors_nodup hmem
  -- Apply the inverse-permutation to both sides.
  have hstep :
      (inversePermutationValues perm hnodup)[perm[i]]
        = (inversePermutationValues perm hnodup)[perm[j]] :=
    congrArg (fun k : Fin n => (inversePermutationValues perm hnodup)[k]) hij
  have hi := inversePermutationValues_get_index perm hnodup i
  have hj := inversePermutationValues_get_index perm hnodup j
  exact hi.symm.trans (hstep.trans hj)

/-- The reconstructed column tuple is itself injective when `sel` is
strictly increasing and `perm` is a permutation. -/
theorem reconstructInjTuple_injective {m n : Nat}
    {sel : Vector (Fin m) n} {perm : Vector (Fin n) n}
    (hsel : IsStrictlyIncreasingColumnTuple sel)
    (hperm : perm ∈ permutationVectors n) :
    Function.Injective (columnTupleVectorFn (reconstructInjTuple sel perm)) := by
  intro i j hij
  have hsel_inj := isStrictlyIncreasingColumnTuple_injective hsel
  have hperm_inj := permutationVectors_getElem_injective hperm
  -- `hij` is equality of reconstructed entries; extract `sel[perm[i]] = sel[perm[j]]`.
  have hval : sel[perm[i]] = sel[perm[j]] := by
    have hi := reconstructInjTuple_getElem sel perm i
    have hj := reconstructInjTuple_getElem sel perm j
    have hij' :
        (reconstructInjTuple sel perm)[i] = (reconstructInjTuple sel perm)[j] := hij
    exact hi.symm.trans (hij'.trans hj)
  exact hperm_inj (hsel_inj hval)

/-- For a strictly-increasing `sel`, value comparison agrees with index
comparison. -/
private theorem isStrictlyIncreasingColumnTuple_val_lt_iff {m n : Nat}
    {sel : Vector (Fin m) n} (hsel : IsStrictlyIncreasingColumnTuple sel)
    (a b : Fin n) :
    sel[a].val < sel[b].val ↔ a.val < b.val := by
  refine ⟨?_, hsel a b⟩
  intro hlt
  rcases Nat.lt_trichotomy a.val b.val with hltab | heqab | hgtab
  · exact hltab
  · have : a = b := Fin.ext heqab
    subst this; omega
  · have := hsel b a hgtab; omega

/-- For a permutation `perm`, the `toList` is a `List.Perm` of `List.finRange n`. -/
private theorem permutationVectors_toList_perm_finRange {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    perm.toList.Perm (List.finRange n) := by
  have hnodup := permutationVectors_nodup hmem
  apply (List.perm_ext_iff_of_nodup hnodup (List.nodup_finRange n)).mpr
  intro x
  refine ⟨fun _ => List.mem_finRange x, fun _ => ?_⟩
  exact fin_mem_of_full_nodup x (by simp [Vector.length_toList]) hnodup

/-- Count of indices `j` for which `perm[j].val < k.val` is exactly `k.val`
when `perm` is a permutation. -/
private theorem permutationVectors_count_val_lt {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) (k : Fin n) :
    (List.finRange n).countP (fun j : Fin n => decide (perm[j].val < k.val)) = k.val := by
  -- Reduce to counting on perm.toList via `countP_map`.
  have hmap :
      (List.finRange n).countP (fun j : Fin n => decide (perm[j].val < k.val)) =
        ((List.finRange n).map fun j : Fin n => perm[j]).countP
          (fun x : Fin n => decide (x.val < k.val)) := by
    rw [List.countP_map]
    rfl
  have htoList : perm.toList = (List.finRange n).map (fun j : Fin n => perm[j]) :=
    vector_toList_eq_finRange_map_get perm
  rw [hmap, ← htoList]
  rw [List.Perm.countP_eq _ (permutationVectors_toList_perm_finRange hmem)]
  rw [countP_finRange_val_lt]
  exact Nat.min_eq_right (Nat.le_of_lt k.isLt)

/-- For a strictly-increasing `sel` and a permutation `perm`, the column
rank of the reconstruction at index `i` agrees with `perm[i].val`. -/
private theorem columnRankNat_reconstructInjTuple {m n : Nat}
    {sel : Vector (Fin m) n} {perm : Vector (Fin n) n}
    (hsel : IsStrictlyIncreasingColumnTuple sel)
    (hperm : perm ∈ permutationVectors n) (i : Fin n) :
    columnRankNat (reconstructInjTuple sel perm) i = (perm[i]).val := by
  unfold columnRankNat
  -- Convert filter to countP, replace predicate using strict monotonicity, then
  -- apply the permutation count lemma.
  rw [← List.countP_eq_length_filter]
  have hpred :
      (fun j : Fin n => decide ((reconstructInjTuple sel perm)[j].val
                                   < (reconstructInjTuple sel perm)[i].val)) =
        (fun j : Fin n => decide ((perm[j]).val < (perm[i]).val)) := by
    funext j
    rw [reconstructInjTuple_getElem, reconstructInjTuple_getElem]
    exact decide_eq_decide.mpr (isStrictlyIncreasingColumnTuple_val_lt_iff hsel _ _)
  rw [hpred]
  exact permutationVectors_count_val_lt hperm (perm[i])

/-- `sortInjPerm` of a reconstructed tuple recovers the original permutation. -/
theorem sortInjPerm_reconstructInjTuple {m n : Nat}
    {sel : Vector (Fin m) n} {perm : Vector (Fin n) n}
    (hsel : IsStrictlyIncreasingColumnTuple sel)
    (hperm : perm ∈ permutationVectors n) :
    sortInjPerm (reconstructInjTuple sel perm) = perm := by
  apply Vector.ext
  intro k hk
  let i : Fin n := ⟨k, hk⟩
  show (sortInjPerm (reconstructInjTuple sel perm))[i] = perm[i]
  apply Fin.ext
  rw [sortInjPerm_getElem_val]
  exact columnRankNat_reconstructInjTuple hsel hperm i

/-- `sortInjTuple` of a reconstructed tuple recovers the original selection. -/
theorem sortInjTuple_reconstructInjTuple {m n : Nat}
    {sel : Vector (Fin m) n} {perm : Vector (Fin n) n}
    (hsel : IsStrictlyIncreasingColumnTuple sel)
    (hperm : perm ∈ permutationVectors n) :
    sortInjTuple (reconstructInjTuple sel perm) = sel := by
  -- Use the factorization equation on the reconstructed tuple, which is injective.
  have hinj : Function.Injective (columnTupleVectorFn (reconstructInjTuple sel perm)) :=
    reconstructInjTuple_injective hsel hperm
  apply Vector.ext
  intro k hk
  let r : Fin n := ⟨k, hk⟩
  show (sortInjTuple (reconstructInjTuple sel perm))[r] = sel[r]
  -- The reconstruction at index `inv perm [r]` equals sel[perm[(inv perm) r]] = sel[r].
  -- And by the factorization equation, this equals sortInjTuple cols at sortInjPerm cols [(inv perm) r]
  -- which is just r by the permutation identity. Hmm, this is circular.
  -- Direct: sortInjTuple cols [r] = cols[inv (sortInjPerm cols) [r]]
  --                                = cols[inv perm [r]]                    -- by sortInjPerm_reconstructInjTuple
  --                                = sel[perm[(inv perm) r]]               -- by reconstruction defn
  --                                = sel[r]                                -- by perm ∘ inv perm = id
  have hsortPerm := sortInjPerm_reconstructInjTuple hsel hperm
  -- Substitute sortInjPerm with perm in the sortInjTuple definition.
  rw [sortInjTuple, vector_ofFn_getElem_fin]
  -- Goal: cols[inv (sortInjPerm cols) [r]] = sel[r]
  -- where cols := reconstructInjTuple sel perm.
  have hinv_eq : inversePermutationVector (sortInjPerm (reconstructInjTuple sel perm))
                   = inversePermutationVector perm :=
    congrArg inversePermutationVector hsortPerm
  have hstep :
      (reconstructInjTuple sel perm)[(inversePermutationVector
                                        (sortInjPerm (reconstructInjTuple sel perm)))[r]]
        = (reconstructInjTuple sel perm)[(inversePermutationVector perm)[r]] :=
    congrArg
      (fun v : Vector (Fin n) n => (reconstructInjTuple sel perm)[v[r]])
      hinv_eq
  rw [hstep]
  -- Now: reconstruction at (inv perm)[r] = sel[perm[(inv perm)[r]]] = sel[r].
  rw [reconstructInjTuple_getElem]
  -- Use that perm ∘ inv perm = id (i.e., perm[(inv perm)[r]] = r).
  have hnodup := permutationVectors_nodup hperm
  have hinv_perm : inversePermutationVector perm
                     = inversePermutationValues perm hnodup :=
    inversePermutationVector_eq perm hnodup
  have hval := inversePermutationValues_get_value perm hnodup r
  -- hval : perm[(inv perm) [r]] = r (where inv perm = inversePermutationValues perm hnodup)
  have hstep' :
      perm[(inversePermutationVector perm)[r]]
        = perm[(inversePermutationValues perm hnodup)[r]] :=
    congrArg (fun v : Vector (Fin n) n => perm[v[r]]) hinv_perm
  have hperm_apply : perm[(inversePermutationVector perm)[r]] = r := hstep'.trans hval
  -- Therefore: sel[perm[(inv perm)[r]]] = sel[r] via congrArg.
  exact congrArg (fun k : Fin n => sel[k]) hperm_apply

/-! ### Bijection wrappers -/

/-- Forward-then-backward identity: reconstruction inverts the canonical
sort/permutation pair on injective column tuples. -/
theorem reconstructInjTuple_sortInj {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) :
    reconstructInjTuple (sortInjTuple cols) (sortInjPerm cols) = cols := by
  apply Vector.ext
  intro k hk
  let i : Fin n := ⟨k, hk⟩
  show (reconstructInjTuple (sortInjTuple cols) (sortInjPerm cols))[i] = cols[i]
  rw [reconstructInjTuple_getElem]
  exact (cols_getElem_eq_sortInjTuple_sortInjPerm cols hinj i).symm

/-- For each fixed `sel`, the inner `map (reconstructInjTuple sel)` list
is `Nodup` over `permutationVectors n`. -/
private theorem permutationVectors_map_reconstruct_nodup {m n : Nat}
    {sel : Vector (Fin m) n} (hsel : IsStrictlyIncreasingColumnTuple sel) :
    ((permutationVectors n).map (reconstructInjTuple sel)).Nodup := by
  apply list_nodup_map_on permutationVectors_nodup_list
  intro a ha b hb hab
  -- Apply sortInjPerm to both sides to recover the permutation.
  have := congrArg sortInjPerm hab
  rw [sortInjPerm_reconstructInjTuple hsel ha,
      sortInjPerm_reconstructInjTuple hsel hb] at this
  exact this

/-- The flat list of reconstructed column tuples, indexed by
`selectedColumnTuples × permutationVectors`, has no duplicates. -/
theorem selPerm_reconstructed_list_nodup {m n : Nat} :
    ((selectedColumnTuples n m).flatMap fun sel =>
      (permutationVectors n).map (reconstructInjTuple sel)).Nodup := by
  -- Generalize so we can induct on the outer list (selectedColumnTuples).
  suffices h : ∀ (sels : List (Vector (Fin m) n)), sels.Nodup →
      (∀ sel ∈ sels, IsStrictlyIncreasingColumnTuple sel) →
      (sels.flatMap fun sel =>
        (permutationVectors n).map (reconstructInjTuple sel)).Nodup by
    exact h _ selectedColumnTuples_nodup
      (fun sel hmem => (mem_selectedColumnTuples_iff sel).mp hmem)
  intro sels hsels_nodup hsels_inc
  induction sels with
  | nil => simp
  | cons s ss ih =>
      simp only [List.flatMap_cons]
      rw [List.nodup_append]
      simp only [List.nodup_cons] at hsels_nodup
      refine ⟨?_, ?_, ?_⟩
      · -- Inner head list is Nodup.
        exact permutationVectors_map_reconstruct_nodup (hsels_inc s (by simp))
      · -- Tail Nodup by IH.
        exact ih hsels_nodup.2 (fun sel' hsel' => hsels_inc sel' (List.mem_cons_of_mem s hsel'))
      · -- Disjointness: a reconstruction with `sel = s` and a reconstruction
        -- with `sel = s' ∈ ss` agree only if `s = s'` by `sortInjTuple`.
        intro a ha_head b hb_suffix hab
        rcases List.mem_map.mp ha_head with ⟨perm, hperm_mem, rfl⟩
        rcases List.mem_flatMap.mp hb_suffix with ⟨s', hs'_mem, hb_in⟩
        rcases List.mem_map.mp hb_in with ⟨perm', hperm'_mem, hb_eq⟩
        -- hab : (reconstructInjTuple s perm) = b; hb_eq : reconstructInjTuple s' perm' = b
        have hrec_eq : reconstructInjTuple s perm = reconstructInjTuple s' perm' :=
          hab.trans hb_eq.symm
        have hs_inc := hsels_inc s (by simp)
        have hs'_inc := hsels_inc s' (List.mem_cons_of_mem s hs'_mem)
        have hsort := congrArg sortInjTuple hrec_eq
        rw [sortInjTuple_reconstructInjTuple hs_inc hperm_mem,
            sortInjTuple_reconstructInjTuple hs'_inc hperm'_mem] at hsort
        subst hsort
        exact hsels_nodup.1 hs'_mem

/-- A column tuple is injective iff it is enumerated by the
`selectedColumnTuples × permutationVectors` reconstruction. This is the
bijection statement in membership form. -/
theorem mem_selPerm_reconstructed_iff {m n : Nat} (cols : Vector (Fin m) n) :
    cols ∈ ((selectedColumnTuples n m).flatMap fun sel =>
      (permutationVectors n).map (reconstructInjTuple sel)) ↔
      Function.Injective (columnTupleVectorFn cols) := by
  refine ⟨?_, ?_⟩
  · -- Backward: every reconstruction is injective.
    intro hmem
    rcases List.mem_flatMap.mp hmem with ⟨sel, hsel_mem, hinner⟩
    rcases List.mem_map.mp hinner with ⟨perm, hperm_mem, rfl⟩
    have hsel_inc : IsStrictlyIncreasingColumnTuple sel :=
      (mem_selectedColumnTuples_iff sel).mp hsel_mem
    exact reconstructInjTuple_injective hsel_inc hperm_mem
  · -- Forward: every injective tuple is in the reconstruction list, via
    -- (sortInjTuple cols, sortInjPerm cols).
    intro hinj
    rw [List.mem_flatMap]
    refine ⟨sortInjTuple cols, sortInjTuple_mem_selectedColumnTuples cols hinj, ?_⟩
    rw [List.mem_map]
    refine ⟨sortInjPerm cols, sortInjPerm_mem_permutationVectors cols hinj, ?_⟩
    exact reconstructInjTuple_sortInj cols hinj

private theorem foldl_det_sum_filter_of_zero {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (p : β → Prop) [DecidablePred p]
    (f : β → R) (z : R)
    (hzero : ∀ x, x ∈ xs → ¬ p x → f x = 0) :
    xs.foldl (fun acc x => acc + f x) z =
      (xs.filter p).foldl (fun acc x => acc + f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : p x
      · simp [List.filter, hx]
        apply ih
        intro y hy hpy
        exact hzero y (List.mem_cons_of_mem x hy) hpy
      · simp [List.filter, hx]
        have hxzero : f x = 0 := hzero x (by simp) hx
        rw [hxzero]
        have hacc : z + (0 : R) = z := by grind
        rw [hacc]
        apply ih
        intro y hy hpy
        exact hzero y (List.mem_cons_of_mem x hy) hpy

/-- Refold the ordered column-tuple Gram expansion over the canonical
`selectedColumnTuples × permutationVectors` reconstruction list. Non-injective
ordered tuples contribute zero determinants, and the remaining injective tuples
are exactly the reconstructed selected/permutation tuples. -/
theorem columnTupleExpansion_refold_selectedPerm
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat} (A : Matrix R n m) :
    (columnTupleVectors n m).foldl
        (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 =
      (((selectedColumnTuples n m).flatMap fun sel =>
          (permutationVectors n).map (reconstructInjTuple sel))).foldl
        (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 := by
  classical
  let reconstructed :=
    (selectedColumnTuples n m).flatMap fun sel =>
      (permutationVectors n).map (reconstructInjTuple sel)
  let term := columnTupleExpansionTerm A
  have hfilter :
      (columnTupleVectors n m).foldl (fun acc cols => acc + term cols) 0 =
        ((columnTupleVectors n m).filter
          (fun cols => Function.Injective (columnTupleVectorFn cols))).foldl
            (fun acc cols => acc + term cols) 0 := by
    apply foldl_det_sum_filter_of_zero
    intro cols hmem hnot
    unfold term columnTupleExpansionTerm
    have hdet :
        det (columnTupleMatrix A (columnTupleVectorFn cols)) = 0 :=
      det_columnTupleMatrix_eq_zero_of_not_injective A (columnTupleVectorFn cols) hnot
    rw [hdet]
    grind
  have hperm :
      ((columnTupleVectors n m).filter
          (fun cols => Function.Injective (columnTupleVectorFn cols))).Perm
        reconstructed := by
    apply (List.perm_ext_iff_of_nodup
      ((columnTupleVectors_nodup (n := n) (m := m)).filter _)
      (by simpa [reconstructed] using (selPerm_reconstructed_list_nodup (m := m) (n := n)))).mpr
    intro cols
    constructor
    · intro hmem
      rw [List.mem_filter] at hmem
      exact (mem_selPerm_reconstructed_iff cols).mpr (of_decide_eq_true hmem.2)
    · intro hmem
      rw [List.mem_filter]
      exact ⟨mem_columnTupleVectors cols,
        decide_eq_true ((mem_selPerm_reconstructed_iff cols).mp hmem)⟩
  calc
    (columnTupleVectors n m).foldl (fun acc cols => acc + columnTupleExpansionTerm A cols) 0
        = (columnTupleVectors n m).foldl (fun acc cols => acc + term cols) 0 := rfl
    _ = ((columnTupleVectors n m).filter
          (fun cols => Function.Injective (columnTupleVectorFn cols))).foldl
            (fun acc cols => acc + term cols) 0 := hfilter
    _ = reconstructed.foldl (fun acc cols => acc + term cols) 0 := by
          exact foldl_det_sum_perm term hperm 0
    _ = (((selectedColumnTuples n m).flatMap fun sel =>
          (permutationVectors n).map (reconstructInjTuple sel))).foldl
        (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 := rfl

private theorem columnTupleExpansionTerm_reconstructInjTuple
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (sel : Vector (Fin m) n) (perm : Vector (Fin n) n)
    (hperm : perm ∈ permutationVectors n) :
    columnTupleExpansionTerm A (reconstructInjTuple sel perm) =
      detTerm (columnTupleMatrix A (columnTupleVectorFn sel)) perm *
        det (columnTupleMatrix A (columnTupleVectorFn sel)) := by
  unfold columnTupleExpansionTerm detTerm
  rw [columnTupleCoeff_reconstructInjTuple]
  rw [columnTupleMatrix_reconstructInjTuple_eq A sel perm]
  rw [det_columnTupleMatrix_compose_perm A sel perm hperm]
  grind

private theorem columnTupleExpansion_reconstruct_orbit_sum
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (sel : Vector (Fin m) n) :
    (permutationVectors n).foldl
        (fun acc perm => acc + columnTupleExpansionTerm A (reconstructInjTuple sel perm)) 0 =
      det (columnTupleMatrix A (columnTupleVectorFn sel)) ^ 2 := by
  let minor := columnTupleMatrix A (columnTupleVectorFn sel)
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + columnTupleExpansionTerm A (reconstructInjTuple sel perm)) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + detTerm minor perm * det minor) 0 := by
        apply foldl_det_sum_congr
        intro perm hperm
        exact columnTupleExpansionTerm_reconstructInjTuple A sel perm hperm
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm minor perm) 0 *
        det minor := by
        exact foldl_det_sum_mul_right_zero (permutationVectors n) (fun perm => detTerm minor perm)
          (det minor)
    _ = det minor ^ 2 := by
        unfold det
        grind

private theorem columnTupleExpansion_selectedPerm_collapse
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat} (A : Matrix R n m) :
    (((selectedColumnTuples n m).flatMap fun sel =>
        (permutationVectors n).map (reconstructInjTuple sel))).foldl
      (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 =
    (selectedColumnTuples n m).foldl
      (fun acc sel => acc + det (columnTupleMatrix A (columnTupleVectorFn sel)) ^ 2) 0 := by
  rw [foldl_det_sum_flatMap]
  apply foldl_acc_congr
  intro acc sel _hsel
  rw [foldl_det_sum_start]
  congr 1
  rw [foldl_det_sum_map]
  rw [columnTupleExpansion_reconstruct_orbit_sum A sel]

/-- Cauchy-Binet for the row Gram matrix: the Gram determinant is the finite
sum of squares of the selected column minors. -/
theorem det_gramMatrix_eq_sum_minors_sq
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat} (A : Matrix R n m) :
    det (gramMatrix A) =
      (selectedColumnTuples n m).foldl
        (fun acc cols => acc + det (columnTupleMatrix A (columnTupleVectorFn cols)) ^ 2) 0 := by
  calc
    det (gramMatrix A) =
      (columnTupleVectors n m).foldl
        (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 := by
        exact det_gramMatrix_eq_sum_columnTuples A
    _ =
      (((selectedColumnTuples n m).flatMap fun sel =>
          (permutationVectors n).map (reconstructInjTuple sel))).foldl
        (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 := by
        exact columnTupleExpansion_refold_selectedPerm A
    _ =
      (selectedColumnTuples n m).foldl
        (fun acc cols => acc + det (columnTupleMatrix A (columnTupleVectorFn cols)) ^ 2) 0 := by
        exact columnTupleExpansion_selectedPerm_collapse A

private theorem foldl_int_sum_sq_nonneg_start {β : Type v}
    (xs : List β) (f : β → Int) (acc : Int) (hacc : 0 ≤ acc) :
    0 ≤ xs.foldl (fun acc x => acc + f x ^ 2) acc := by
  induction xs generalizing acc with
  | nil => simpa using hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : 0 ≤ f x ^ 2 := by
        simpa [Lean.Grind.Semiring.pow_two] using
          (Lean.Grind.OrderedRing.sq_nonneg (a := f x))
      exact ih (acc + f x ^ 2) (Int.add_nonneg hacc hx)

private theorem foldl_int_sum_sq_nonneg {β : Type v} (xs : List β) (f : β → Int) :
    0 ≤ xs.foldl (fun acc x => acc + f x ^ 2) 0 :=
  foldl_int_sum_sq_nonneg_start xs f 0 (by simp)

private theorem foldl_int_sum_sq_pos_of_acc {β : Type v}
    (xs : List β) (f : β → Int) (acc : Int) (hacc : 0 < acc) :
    0 < xs.foldl (fun acc x => acc + f x ^ 2) acc := by
  induction xs generalizing acc with
  | nil => simpa using hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : 0 ≤ f x ^ 2 := by
        simpa [Lean.Grind.Semiring.pow_two] using
          (Lean.Grind.OrderedRing.sq_nonneg (a := f x))
      exact ih (acc + f x ^ 2) (Int.add_pos_of_pos_of_nonneg hacc hx)

private theorem foldl_int_sum_sq_pos_start {β : Type v}
    (xs : List β) (f : β → Int) (acc : Int) (hacc : 0 ≤ acc)
    (target : β) (hx : target ∈ xs) (hpos : 0 < f target ^ 2) :
    0 < xs.foldl (fun acc x => acc + f x ^ 2) acc := by
  induction xs generalizing acc with
  | nil => cases hx
  | cons y ys ih =>
      simp only [List.foldl_cons]
      simp only [List.mem_cons] at hx
      cases hx with
      | inl hxy =>
          subst hxy
          exact foldl_int_sum_sq_pos_of_acc ys f (acc + f target ^ 2)
            (Int.add_pos_of_nonneg_of_pos hacc hpos)
      | inr htail =>
          have hy : 0 ≤ f y ^ 2 := by
            simpa [Lean.Grind.Semiring.pow_two] using
              (Lean.Grind.OrderedRing.sq_nonneg (a := f y))
          exact ih (acc + f y ^ 2) (Int.add_nonneg hacc hy) htail

private theorem foldl_int_sum_sq_pos_of_mem {β : Type v}
    (xs : List β) (f : β → Int) (x : β) (hx : x ∈ xs) (hpos : 0 < f x ^ 2) :
    0 < xs.foldl (fun acc x => acc + f x ^ 2) 0 :=
  foldl_int_sum_sq_pos_start xs f 0 (by simp) x hx hpos

/-- Integer row Gram determinants are nonnegative, by Cauchy-Binet as a finite
sum of integer squares. -/
theorem det_gramMatrix_nonneg {n m : Nat} (A : Matrix Int n m) :
    0 ≤ det (gramMatrix A) := by
  rw [det_gramMatrix_eq_sum_minors_sq A]
  exact foldl_int_sum_sq_nonneg (selectedColumnTuples n m)
    (fun cols => det (columnTupleMatrix A (columnTupleVectorFn cols)))

/-- The identity selection of the first `k` columns of an `n`-column matrix. -/
def firstColumns (k n : Nat) (hk : k ≤ n) : Vector (Fin n) k :=
  Vector.ofFn fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

/-- The `i`-th entry of the first-`k`-columns selection is the index `i` itself,
embedded into `Fin n`. -/
@[grind =] theorem firstColumns_entry (k n : Nat) (hk : k ≤ n) (i : Fin k) :
    (firstColumns k n hk)[i] = (⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ : Fin n) := by
  simp [firstColumns]

/-- The first `k` columns form a strictly increasing selected column tuple. -/
theorem firstColumns_mem_selectedColumnTuples (k n : Nat) (hk : k ≤ n) :
    firstColumns k n hk ∈ selectedColumnTuples k n := by
  rw [mem_selectedColumnTuples_iff]
  intro i j hij
  simp [firstColumns]
  exact hij

/-- Selecting the first `k` columns from the leading `k` rows of a square
matrix gives exactly its leading `k × k` prefix. -/
theorem columnTupleMatrix_leadingRows_firstColumns_eq_leadingPrefix
    {R : Type u} {n : Nat} (M : Matrix R n n) (k : Nat) (hk : k ≤ n) :
    columnTupleMatrix (leadingRows M k hk) (columnTupleVectorFn (firstColumns k n hk)) =
      leadingPrefix M k hk := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  change
    (columnTupleMatrix (leadingRows M k hk) (columnTupleVectorFn (firstColumns k n hk)))[
        (⟨i, hi⟩ : Fin k)][(⟨j, hj⟩ : Fin k)] =
      (leadingPrefix M k hk)[(⟨i, hi⟩ : Fin k)][(⟨j, hj⟩ : Fin k)]
  simp [columnTupleMatrix, leadingRows, leadingPrefix, columnTupleVectorFn, firstColumns, ofFn]

/-- The Gram determinant of the first `k` rows of a positive-diagonal integer
upper-triangular matrix is strictly positive. The leading-principal minor
provides a positive square term in the Cauchy-Binet expansion. -/
theorem det_gramMatrix_leadingRows_pos_of_upperTriangular_pos_diag
    {n : Nat} (M : Matrix Int n n)
    (hzero : ∀ i j : Fin n, j.val < i.val → M[i][j] = 0)
    (hdiag : ∀ i : Fin n, 0 < M[i][i])
    (k : Nat) (hk : k ≤ n) :
    0 < det (gramMatrix (leadingRows M k hk)) := by
  rw [det_gramMatrix_eq_sum_minors_sq (leadingRows M k hk)]
  let cols := firstColumns k n hk
  have hmem : cols ∈ selectedColumnTuples k n :=
    firstColumns_mem_selectedColumnTuples k n hk
  have hminor_eq :
      det (columnTupleMatrix (leadingRows M k hk) (columnTupleVectorFn cols)) =
        det (leadingPrefix M k hk) := by
    dsimp [cols]
    rw [columnTupleMatrix_leadingRows_firstColumns_eq_leadingPrefix M k hk]
  have hprefixZero :
      ∀ i j : Fin k, j.val < i.val → (leadingPrefix M k hk)[i][j] = 0 := by
    intro i j hij
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
    have hentry : (leadingPrefix M k hk)[i][j] = M[ii][jj] := by
      simp [leadingPrefix, ofFn, ii, jj]
    rw [hentry]
    exact hzero ii jj hij
  have hprefixDiag :
      ∀ i : Fin k, 0 < (leadingPrefix M k hk)[i][i] := by
    intro i
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    have hentry : (leadingPrefix M k hk)[i][i] = M[ii][ii] := by
      simp [leadingPrefix, ofFn, ii]
    rw [hentry]
    exact hdiag ii
  have hminor_pos :
      0 < det (columnTupleMatrix (leadingRows M k hk) (columnTupleVectorFn cols)) := by
    rw [hminor_eq]
    exact det_upperTriangular_pos_diag (leadingPrefix M k hk) hprefixZero hprefixDiag
  have hminor_sq_pos :
      0 < det (columnTupleMatrix (leadingRows M k hk) (columnTupleVectorFn cols)) ^ 2 := by
    simpa [Lean.Grind.Semiring.pow_two] using Int.mul_pos hminor_pos hminor_pos
  exact foldl_int_sum_sq_pos_of_mem
    (xs := selectedColumnTuples k n)
    (f := fun cols => det (columnTupleMatrix (leadingRows M k hk) (columnTupleVectorFn cols)))
    (x := cols) hmem hminor_sq_pos

/-! ### Adjugate matrix and `M * adjugate M = det M • 1`

The local adjugate matrix is the transpose of the cofactor matrix. The
defining property is `(M * adjugate M)[i][j] = det M * δᵢⱼ`, which we
prove entrywise via Laplace expansion. The off-diagonal case uses the
"alien cofactor" identity: expanding row `i` against the cofactors of a
different row `j` collapses to the determinant of a matrix with two
equal rows. These are the Mathlib-free local analogues of Mathlib's
`Matrix.adjugate` and `Matrix.mul_adjugate` needed by the Desnanot-Jacobi
assembly. -/

/-- Replace row `dst` of `M` with the vector `v`. -/
def setRow {R : Type u} {n m : Nat}
    (M : Matrix R n m) (dst : Fin n) (v : Vector R m) : Matrix R n m :=
  M.set dst v

/-- Reading back the replaced row `dst` of `setRow M dst v` yields `v`. -/
@[grind =] theorem setRow_get_self {R : Type u} {n m : Nat}
    (M : Matrix R n m) (dst : Fin n) (v : Vector R m) :
    (setRow M dst v)[dst] = v := by
  simp [setRow]

/-- Replacing row `dst` leaves every other row unchanged. -/
theorem setRow_row_ne {R : Type u} {n m : Nat}
    (M : Matrix R n m) (dst r : Fin n) (v : Vector R m)
    (h : r ≠ dst) :
    (setRow M dst v)[r] = M[r] := by
  have hval : dst.val ≠ r.val := fun hval => h (Fin.ext hval.symm)
  exact Vector.getElem_set_ne (xs := M) (x := v) dst.isLt r.isLt hval

/-- Deleting the destination row of `setRow M dst v` gives the same minor
as deleting the destination row of `M`: the replaced row is removed
anyway, so the new entries are invisible. -/
theorem deleteRowCol_setRow_self {R : Type u} {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (dst col : Fin (n + 1))
    (v : Vector R (n + 1)) :
    deleteRowCol (setRow M dst v) dst col = deleteRowCol M dst col := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin n := ⟨j, hj⟩
  change (deleteRowCol (setRow M dst v) dst col)[ii][jj] =
    (deleteRowCol M dst col)[ii][jj]
  rw [deleteRowCol_entry, deleteRowCol_entry]
  have hne : skipIndex dst ii ≠ dst := skipIndex_ne dst ii
  have hrow := setRow_row_ne M dst (skipIndex dst ii) v hne
  exact congrArg (fun row => row[skipIndex col jj]) hrow

/-- The cofactor expansion of `setRow M dst v` along the replaced row
`dst` uses the same minors as the cofactor expansion of `M` along that
row, because the deleted row never contributes to the minor. -/
theorem cofactor_setRow_self {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (dst col : Fin (n + 1))
    (v : Vector R (n + 1)) :
    cofactor (setRow M dst v) dst col = cofactor M dst col := by
  unfold cofactor
  rw [deleteRowCol_setRow_self M dst col v]

/-- Pair a row vector with a cofactor row of `M`. This is the scalar that
appears in Laplace expansion after replacing the expanded row. -/
def cofactorRowPairing {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row : Fin (n + 1)) (v : Vector R (n + 1)) :
    R :=
  (List.finRange (n + 1)).foldl
    (fun acc col => acc + v[col] * cofactor M row col) 0

/-- Replacing row `row` by `v` makes the determinant the pairing of `v`
against the original cofactor row. -/
theorem det_setRow_eq_cofactorRowPairing
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row : Fin (n + 1)) (v : Vector R (n + 1)) :
    det (setRow M row v) = cofactorRowPairing M row v := by
  rw [det_eq_foldl_laplace_row (setRow M row v) row]
  unfold cofactorRowPairing
  apply foldl_acc_congr
  intro acc col _hmem
  rw [show (setRow M row v)[row][col] = v[col] by
    rw [setRow_get_self]]
  rw [cofactor_setRow_self M row col v]

/-- Pairing the original row against its own cofactor row recovers `det M`. -/
theorem cofactorRowPairing_self
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row : Fin (n + 1)) :
    cofactorRowPairing M row M[row] = det M := by
  exact (det_eq_foldl_laplace_row M row).symm

/-- The "alien cofactor" identity: expanding row `i` of `M` against the
cofactors of a different row `j` produces zero. This is the
characteristic vanishing identity that makes the adjugate work. -/
theorem foldl_alien_cofactor_eq_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i j : Fin (n + 1)) (hij : i ≠ j) :
    (List.finRange (n + 1)).foldl
        (fun acc k => acc + M[i][k] * cofactor M j k) 0 = 0 := by
  let N : Matrix R (n + 1) (n + 1) := setRow M j M[i]
  have hNi : N[i] = M[i] := setRow_row_ne M j i M[i] hij
  have hNj : N[j] = M[i] := setRow_get_self M j M[i]
  have hrows : N[i] = N[j] := hNi.trans hNj.symm
  have hdetN : det N = 0 := det_eq_zero_of_row_eq N i j hij hrows
  have hLaplace := det_eq_foldl_laplace_row N j
  have hcof :
      (List.finRange (n + 1)).foldl
          (fun acc k => acc + N[j][k] * cofactor N j k) 0 =
        (List.finRange (n + 1)).foldl
          (fun acc k => acc + M[i][k] * cofactor M j k) 0 := by
    apply foldl_acc_congr
    intro acc k _hmem
    have hentry : N[j][k] = M[i][k] := congrArg (fun row => row[k]) hNj
    have hcofk : cofactor N j k = cofactor M j k :=
      cofactor_setRow_self M j k M[i]
    rw [hentry, hcofk]
  rw [hcof] at hLaplace
  exact hLaplace.symm.trans hdetN

/-- Pairing an unreplaced row of `M` against a different cofactor row is zero. -/
theorem cofactorRowPairing_alien_eq_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i j : Fin (n + 1)) (hij : i ≠ j) :
    cofactorRowPairing M j M[i] = 0 := by
  exact foldl_alien_cofactor_eq_zero M i j hij

/-- The local adjugate matrix: entry `(i, j)` is the cofactor at row `j`,
column `i` of `M`. This is the transpose of the cofactor matrix. -/
def adjugate {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) : Matrix R (n + 1) (n + 1) :=
  ofFn fun i j => cofactor M j i

/-- Entry `(i, j)` of the adjugate is the cofactor of `M` at row `j`, column `i`
(the transpose of the cofactor matrix). -/
@[grind =] theorem adjugate_get {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i j : Fin (n + 1)) :
    (adjugate M)[i][j] = cofactor M j i := by
  simp [adjugate, ofFn]

/-- Entrywise version of `M * adjugate M = det M • 1`. On the diagonal
this is Laplace expansion of `det M`; off the diagonal it is the alien
cofactor identity. -/
theorem mul_adjugate_apply {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i j : Fin (n + 1)) :
    (M * adjugate M)[i][j] =
      if i = j then det M else 0 := by
  have hmul : (M * adjugate M)[i][j] = Matrix.dot (row M i) (col (adjugate M) j) := by
    change (Matrix.mul M (adjugate M))[i][j] = _
    unfold Matrix.mul
    show (ofFn fun i j => Matrix.dot (row M i) (col (adjugate M) j))[i][j] = _
    simp [ofFn]
  have hentry :
      (M * adjugate M)[i][j] =
        (List.finRange (n + 1)).foldl
          (fun acc k => acc + M[i][k] * cofactor M j k) 0 := by
    rw [hmul]
    unfold Matrix.dot Hex.Vector.dotProduct
    apply foldl_acc_congr
    intro acc k _hmem
    congr 1
    have hrow : (row M i)[k] = M[i][k] := rfl
    have hcol : (col (adjugate M) j)[k] = (adjugate M)[k][j] := by
      simp [col]
    rw [hrow, hcol, adjugate_get]
  by_cases hij : i = j
  · subst hij
    rw [hentry, if_pos rfl]
    exact (det_eq_foldl_laplace_row M i).symm
  · rw [hentry, if_neg hij]
    exact foldl_alien_cofactor_eq_zero M i j hij

/-- Entrywise version of `adjugate M * M = det M • 1`.

This is the transpose-side companion to `mul_adjugate_apply`; it is useful
when cofactor identities are consumed columnwise rather than rowwise. -/
theorem adjugate_mul_apply {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i j : Fin (n + 1)) :
    (adjugate M * M)[i][j] =
      if i = j then det M else 0 := by
  have hentry :
      (adjugate M * M)[i][j] =
        (M.transpose * adjugate M.transpose)[j][i] := by
    have hleft :
        (adjugate M * M)[i][j] =
          (List.finRange (n + 1)).foldl
            (fun acc k => acc + cofactor M k i * M[k][j]) 0 := by
      change (Matrix.mul (adjugate M) M)[i][j] = _
      unfold Matrix.mul
      rw [getElem_ofFn]
      unfold Matrix.dot Hex.Vector.dotProduct
      apply foldl_acc_congr
      intro acc k _hmem
      have hrow : (row (adjugate M) i)[k] = (adjugate M)[i][k] := rfl
      have hcol : (col M j)[k] = M[k][j] := by
        simp [col]
      rw [hrow, hcol, adjugate_get]
    have hright :
        (M.transpose * adjugate M.transpose)[j][i] =
          (List.finRange (n + 1)).foldl
            (fun acc k => acc + M[k][j] * cofactor M k i) 0 := by
      change (Matrix.mul M.transpose (adjugate M.transpose))[j][i] = _
      unfold Matrix.mul
      rw [getElem_ofFn]
      unfold Matrix.dot Hex.Vector.dotProduct
      apply foldl_acc_congr
      intro acc k _hmem
      have hrow : (row M.transpose j)[k] = M[k][j] := by
        simp [row, transpose, col]
      have hcol : (col (adjugate M.transpose) i)[k] =
          cofactor M k i := by
        have hcol' : (col (adjugate M.transpose) i)[k] =
            (adjugate M.transpose)[k][i] := by
          simp [col]
        rw [hcol', adjugate_get, cofactor_transpose]
      rw [hrow, hcol]
    rw [hleft, hright]
    apply foldl_acc_congr
    intro acc k _hmem
    rw [Lean.Grind.CommSemiring.mul_comm]
  rw [hentry]
  rw [mul_adjugate_apply M.transpose j i]
  rw [det_transpose M]
  by_cases hij : i = j
  · subst hij
    rfl
  · rw [if_neg hij]
    have hji : j ≠ i := fun h => hij h.symm
    rw [if_neg hji]

/-- Column-`0` view of `M * adjugate M`. -/
theorem mul_adjugate_apply_zero {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i : Fin (n + 1)) :
    (M * adjugate M)[i][(0 : Fin (n + 1))] =
      if i = 0 then det M else 0 :=
  mul_adjugate_apply M i 0

/-- Last-column view of `M * adjugate M`. -/
theorem mul_adjugate_apply_last {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i : Fin (n + 1)) :
    (M * adjugate M)[i][Fin.last n] =
      if i = Fin.last n then det M else 0 :=
  mul_adjugate_apply M i (Fin.last n)

/-- Cofactor-minor representation of an adjugate entry. -/
theorem adjugate_eq_cofactorSign_mul_deleteRowCol
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i j : Fin (n + 1)) :
    (adjugate M)[i][j] = cofactorSign j i * det (deleteRowCol M j i) := by
  rw [adjugate_get]
  rfl

/-- The `(0, 0)` adjugate entry equals the determinant of the minor
obtained by deleting row `0` and column `0`. -/
@[grind =] theorem adjugate_zero_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) :
    (adjugate M)[(0 : Fin (n + 1))][(0 : Fin (n + 1))] =
      det (deleteRowCol M 0 0) := by
  rw [adjugate_get]
  exact cofactor_of_even M 0 0 (by simp)

/-- The `(Fin.last, Fin.last)` adjugate entry equals the determinant of
the leading prefix minor obtained by deleting the last row and column. -/
@[grind =] theorem adjugate_last_last
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) :
    (adjugate M)[Fin.last n][Fin.last n] =
      det (leadingPrefix M n (Nat.le_succ n)) := by
  rw [adjugate_get]
  exact cofactor_last_last M

/-! ### Multiplicativity helpers

These private helpers prove determinant multiplicativity for Hex.det. -/

private theorem ofFn_toList_eq_map_finRange {α : Type v} {n : Nat}
    (f : Fin n → α) :
    (Vector.ofFn f).toList = (List.finRange n).map f := by
  rw [vector_toList_eq_finRange_map_get]
  apply List.map_congr_left
  intro i _
  exact vector_ofFn_getElem_fin f i

private theorem ofFn_mem_permutationVectors_of_injective {n : Nat}
    (cols : Fin n → Fin n) (hcols : Function.Injective cols) :
    Vector.ofFn cols ∈ permutationVectors n := by
  apply permutationVectors_complete
  rw [ofFn_toList_eq_map_finRange]
  apply list_nodup_map_on (List.nodup_finRange n)
  intro a _ha b _hb hab
  exact hcols hab

private theorem columnTupleMatrix_eq_ofFn_ofFn
    {R : Type u} {n : Nat} (M : Matrix R n n) (cols : Fin n → Fin n) :
    columnTupleMatrix M cols =
      (ofFn fun r c => M[r][(Vector.ofFn cols)[c]] : Matrix R n n) := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  show (columnTupleMatrix M cols)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
    (ofFn (fun r c => M[r][(Vector.ofFn cols)[c]]) : Matrix R n n)[
      (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnTupleMatrix_entry]
  unfold ofFn
  rw [vector_ofFn_getElem_fin, vector_ofFn_getElem_fin]
  exact congrArg (fun col : Fin n => M[(⟨r, hr⟩ : Fin n)][col])
    (vector_ofFn_getElem_fin cols (⟨c, hc⟩ : Fin n)).symm

private theorem det_columnTupleMatrix_of_injective
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (cols : Fin n → Fin n)
    (hcols : Function.Injective cols) :
    det (columnTupleMatrix M cols) =
      detSign (R := R) (Vector.ofFn cols) * det M := by
  have hmem : Vector.ofFn cols ∈ permutationVectors n :=
    ofFn_mem_permutationVectors_of_injective cols hcols
  rw [columnTupleMatrix_eq_ofFn_ofFn M cols]
  exact det_colPermute_vector M (Vector.ofFn cols) hmem

private theorem det_columnTupleMatrix_eq_det_mul_det_one
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (cols : Fin n → Fin n) :
    det (columnTupleMatrix M cols) =
      det M * det (columnTupleMatrix (1 : Matrix R n n) cols) := by
  by_cases hinj : Function.Injective cols
  · rw [det_columnTupleMatrix_of_injective M cols hinj,
        det_columnTupleMatrix_of_injective (1 : Matrix R n n) cols hinj]
    rw [det_one]
    grind
  · rw [det_columnTupleMatrix_eq_zero_of_not_injective M cols hinj,
        det_columnTupleMatrix_eq_zero_of_not_injective (1 : Matrix R n n) cols hinj]
    grind

private theorem mul_eq_columnSumMatrix_transpose
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M N : Matrix R n n) :
    M * N = columnSumMatrix M N.transpose := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  let rr : Fin n := ⟨r, hr⟩
  let cc : Fin n := ⟨c, hc⟩
  show (M * N)[rr][cc] = (columnSumMatrix M N.transpose)[rr][cc]
  rw [columnSumMatrix_entry]
  change (Matrix.mul M N)[rr][cc] = _
  unfold Matrix.mul ofFn
  rw [vector_ofFn_getElem_fin, vector_ofFn_getElem_fin]
  unfold Matrix.dot Hex.Vector.dotProduct
  apply foldl_det_sum_congr
  intro k _
  have hrow : (row M rr)[k] = M[rr][k] := by simp [row]
  have hcol : (col N cc)[k] = N[k][cc] := by
    show (Vector.ofFn (fun i : Fin n => N[i][cc]))[k] = N[k][cc]
    exact vector_ofFn_getElem_fin _ k
  have htrn : N.transpose[cc][k] = N[k][cc] := by
    show (Vector.ofFn (fun j : Fin n => col N j))[cc][k] = N[k][cc]
    rw [vector_ofFn_getElem_fin]
    exact hcol
  rw [hrow, hcol, htrn]
  exact Lean.Grind.CommSemiring.mul_comm _ _

private theorem eq_columnSumMatrix_one_transpose
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (N : Matrix R n n) :
    N = columnSumMatrix (1 : Matrix R n n) N.transpose := by
  rw [← mul_eq_columnSumMatrix_transpose (1 : Matrix R n n) N]
  exact (one_mul N).symm

/-- Determinant of a product of square matrices.

This is the Mathlib-free Cauchy-Binet specialization already used by the
Desnanot-Jacobi auxiliary proof. -/
theorem det_mul
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M N : Matrix R n n) :
    det (M * N) = det M * det N := by
  rw [mul_eq_columnSumMatrix_transpose M N]
  rw [det_columnSumMatrix_eq_sum_columnTuples M N.transpose]
  have hbody_eq :
      (columnTupleVectors n n).foldl
          (fun acc cols => acc +
            columnTupleCoeff N.transpose cols *
              det (columnTupleMatrix M (columnTupleVectorFn cols))) 0 =
        (columnTupleVectors n n).foldl
          (fun acc cols => acc + det M *
            (columnTupleCoeff N.transpose cols *
              det (columnTupleMatrix (1 : Matrix R n n)
                (columnTupleVectorFn cols)))) 0 := by
    apply foldl_det_sum_congr
    intro cols _
    rw [det_columnTupleMatrix_eq_det_mul_det_one M (columnTupleVectorFn cols)]
    exact Lean.Grind.CommSemiring.mul_left_comm _ _ _
  rw [hbody_eq]
  rw [foldl_det_sum_mul_left_zero
        (columnTupleVectors n n)
        (det M)
        (fun cols => columnTupleCoeff N.transpose cols *
            det (columnTupleMatrix (1 : Matrix R n n)
              (columnTupleVectorFn cols)))]
  rw [← det_columnSumMatrix_eq_sum_columnTuples
        (1 : Matrix R n n) N.transpose]
  rw [← eq_columnSumMatrix_one_transpose N]

/-! ### Plucker minor helpers

Encoding for the universal 3-term Plucker identity substrate. -/

/-- Embed `Fin n` into `Fin (n + 2)` while skipping two deleted indices
`p < q`. This indexes minors with two removed rows.

The ordering proof `_hpq` is a phantom argument: it documents and pins the
`p < q` precondition at call sites but is not consumed by the definition.
This intentionally triggers the `unusedArguments` linter; the binder is kept
deliberately (no `@[nolint]` exists in the Mathlib-free layer). -/
def skipIndex2 {n : Nat} (p q : Fin (n + 2)) (_hpq : p.val < q.val)
    (i : Fin n) : Fin (n + 2) :=
  if hi1 : i.val < p.val then
    ⟨i.val, by have hp := p.isLt; omega⟩
  else if hi2 : i.val + 1 < q.val then
    ⟨i.val + 1, by have hq := q.isLt; omega⟩
  else
    ⟨i.val + 2, by have hi := i.isLt; omega⟩

/-- Below the first deleted index `p`, `skipIndex2` is the identity: its value
at `i` is `i`. -/
@[simp, grind =] theorem skipIndex2_val_of_lt_p {n : Nat} (p q : Fin (n + 2))
    (hpq : p.val < q.val) (i : Fin n) (h : i.val < p.val) :
    (skipIndex2 p q hpq i).val = i.val := by
  simp [skipIndex2, h]

/-- Between the two deleted indices `p` and `q`, `skipIndex2` shifts up by one:
its value at `i` is `i + 1`. -/
@[simp, grind =] theorem skipIndex2_val_of_between {n : Nat} (p q : Fin (n + 2))
    (hpq : p.val < q.val) (i : Fin n) (h1 : ¬ i.val < p.val)
    (h2 : i.val + 1 < q.val) :
    (skipIndex2 p q hpq i).val = i.val + 1 := by
  simp [skipIndex2, h1, h2]

/-- At or beyond the second deleted index `q`, `skipIndex2` shifts up by two:
its value at `i` is `i + 2`. -/
@[simp, grind =] theorem skipIndex2_val_of_ge_q {n : Nat} (p q : Fin (n + 2))
    (hpq : p.val < q.val) (i : Fin n) (h1 : ¬ i.val < p.val)
    (h2 : ¬ i.val + 1 < q.val) :
    (skipIndex2 p q hpq i).val = i.val + 2 := by
  simp [skipIndex2, h1, h2]

/-- `skipIndex2 p q hpq` never lands on the first skipped index `p`. -/
theorem skipIndex2_ne_p {n : Nat} (p q : Fin (n + 2)) (hpq : p.val < q.val)
    (i : Fin n) : skipIndex2 p q hpq i ≠ p := by
  intro hsame
  have hval : (skipIndex2 p q hpq i).val = p.val := congrArg Fin.val hsame
  by_cases h1 : i.val < p.val
  · rw [skipIndex2_val_of_lt_p p q hpq i h1] at hval; omega
  · by_cases h2 : i.val + 1 < q.val
    · rw [skipIndex2_val_of_between p q hpq i h1 h2] at hval; omega
    · rw [skipIndex2_val_of_ge_q p q hpq i h1 h2] at hval; omega

/-- `skipIndex2 p q hpq` never lands on the second skipped index `q`. -/
theorem skipIndex2_ne_q {n : Nat} (p q : Fin (n + 2)) (hpq : p.val < q.val)
    (i : Fin n) : skipIndex2 p q hpq i ≠ q := by
  intro hsame
  have hval : (skipIndex2 p q hpq i).val = q.val := congrArg Fin.val hsame
  by_cases h1 : i.val < p.val
  · rw [skipIndex2_val_of_lt_p p q hpq i h1] at hval; omega
  · by_cases h2 : i.val + 1 < q.val
    · rw [skipIndex2_val_of_between p q hpq i h1 h2] at hval; omega
    · rw [skipIndex2_val_of_ge_q p q hpq i h1 h2] at hval; omega

/-- The `(n + 1) × (n + 1)` matrix obtained from `[B | v]` by deleting
row `p`. Columns `0..n-1` carry the corresponding columns of `B`
(restricted to rows other than `p`); the last column carries `v`
(restricted to rows other than `p`). -/
def mMatrix {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (v : Vector R (n + 2)) (p : Fin (n + 2)) :
    Matrix R (n + 1) (n + 1) :=
  ofFn fun i j =>
    if hj : j.val < n then
      B[skipIndex p i][(⟨j.val, hj⟩ : Fin n)]
    else
      v[skipIndex p i]

/-- In a non-last column, `mMatrix` reads the corresponding entry of `B`
through the row-deletion map. -/
theorem mMatrix_entry_lt {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (v : Vector R (n + 2)) (p : Fin (n + 2))
    (i : Fin (n + 1)) (j : Fin (n + 1)) (h : j.val < n) :
    (mMatrix B v p)[i][j] = B[skipIndex p i][(⟨j.val, h⟩ : Fin n)] := by
  unfold mMatrix
  rw [getElem_ofFn]
  exact dif_pos h

/-- The last column of `mMatrix B v p` is the vector `v` with row `p`
deleted. -/
theorem mMatrix_entry_last {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (v : Vector R (n + 2)) (p : Fin (n + 2))
    (i : Fin (n + 1)) :
    (mMatrix B v p)[i][Fin.last n] = v[skipIndex p i] := by
  have h : ¬ (Fin.last n : Fin (n + 1)).val < n := by
    simp [Fin.last]
  unfold mMatrix
  rw [getElem_ofFn]
  exact dif_neg h

/-- The determinant of `mMatrix B v p`: the `(n + 1)`-maximal minor of
`[B | v]` with row `p` deleted. -/
def mDet {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (v : Vector R (n + 2)) (p : Fin (n + 2)) : R :=
  det (mMatrix B v p)

/-- The `n × n` matrix obtained from `B` by deleting rows `p` and `q`
(in increasing-row order, with `p.val < q.val`). -/
def nMatrix {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (p q : Fin (n + 2)) (hpq : p.val < q.val) :
    Matrix R n n :=
  ofFn fun i j => B[skipIndex2 p q hpq i][j]

/-- Entry `(i, j)` of the two-row-deleted minor `nMatrix B p q hpq` is the source
entry `B[skipIndex2 p q hpq i][j]`. -/
@[grind =] theorem nMatrix_entry {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (p q : Fin (n + 2)) (hpq : p.val < q.val)
    (i : Fin n) (j : Fin n) :
    (nMatrix B p q hpq)[i][j] = B[skipIndex2 p q hpq i][j] := by
  simp [nMatrix, ofFn]

/-- The determinant of `nMatrix B p q hpq`: the `n × n` minor of `B`
with rows `p, q` deleted. -/
def nDet {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (p q : Fin (n + 2)) (hpq : p.val < q.val) : R :=
  det (nMatrix B p q hpq)

/-! ### Row-move infrastructure for ordered four-row transports

These helpers transport the determinant of a matrix whose rows are an
ordered `nMatrix` row sequence with one row displaced downward. Each
"row-move" is realised as a chain of adjacent `rowSwap`s; the determinant
picks up `(-1) ^ k` for a `k`-step move. The four row-content lemmas
identify the rows of the moved matrix so consumers can pair them with
`nMatrix_entry` / `skipIndex2` value lemmas. -/

/-- Move the row at position `src + k` of `M` to position `src` by `k`
adjacent row swaps. The rows previously at positions `src, …, src + k - 1`
shift right by one to positions `src + 1, …, src + k`. Rows outside the
interval `[src, src + k]` are unchanged. -/
private def rowMoveUp {R : Type u} {n m : Nat} (M : Matrix R n m) (src : Nat) :
    (k : Nat) → src + k < n → Matrix R n m
  | 0, _ => M
  | k + 1, h =>
    rowMoveUp
      (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩) src k (by omega)

@[simp, grind =] private theorem rowMoveUp_zero {R : Type u} {n m : Nat}
    (M : Matrix R n m) (src : Nat) (h : src + 0 < n) :
    rowMoveUp M src 0 h = M := rfl

private theorem rowMoveUp_succ {R : Type u} {n m : Nat}
    (M : Matrix R n m) (src k : Nat) (h : src + (k + 1) < n) :
    rowMoveUp M src (k + 1) h =
      rowMoveUp (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩) src k
        (by omega) := rfl

/-- Determinant contribution of `rowMoveUp`: each of the `k` adjacent
swaps negates the determinant. -/
private theorem det_rowMoveUp {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src k : Nat) (h : src + k < n) :
    det (rowMoveUp M src k h) = (-1 : R) ^ k * det M := by
  induction k generalizing M with
  | zero => simp; grind
  | succ k ih =>
      rw [rowMoveUp_succ]
      have hne : (⟨src + k, by omega⟩ : Fin n) ≠ ⟨src + k + 1, h⟩ := by
        intro heq
        have hv : (⟨src + k, by omega⟩ : Fin n).val =
            (⟨src + k + 1, h⟩ : Fin n).val := congrArg Fin.val heq
        simp at hv
      rw [ih]
      rw [det_rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩ hne]
      rw [Lean.Grind.Semiring.pow_succ]
      grind

/-- Rows of `M` strictly below the move interval are unchanged by
`rowMoveUp`. -/
private theorem rowMoveUp_row_of_lt {R : Type u} {n m : Nat}
    (M : Matrix R n m) (src k : Nat) (h : src + k < n) (i : Fin n)
    (hi : i.val < src) :
    (rowMoveUp M src k h)[i] = M[i] := by
  induction k generalizing M with
  | zero => rfl
  | succ k ih =>
      rw [rowMoveUp_succ]
      rw [ih (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩) (by omega)]
      apply Vector.ext
      intro j hj
      let jj : Fin m := ⟨j, hj⟩
      show (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩)[i][jj] = M[i][jj]
      rw [rowSwap_get]
      have h_ne_j : i ≠ ⟨src + k + 1, h⟩ := by
        intro heq; have := congrArg Fin.val heq; simp at this; omega
      have h_ne_i : i ≠ ⟨src + k, by omega⟩ := by
        intro heq; have := congrArg Fin.val heq; simp at this; omega
      rw [if_neg h_ne_j, if_neg h_ne_i]

/-- Rows of `M` strictly above the move interval are unchanged by
`rowMoveUp`. -/
private theorem rowMoveUp_row_of_gt {R : Type u} {n m : Nat}
    (M : Matrix R n m) (src k : Nat) (h : src + k < n) (i : Fin n)
    (hi : src + k < i.val) :
    (rowMoveUp M src k h)[i] = M[i] := by
  induction k generalizing M with
  | zero => rfl
  | succ k ih =>
      rw [rowMoveUp_succ]
      rw [ih (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩) (by omega)
        (by omega)]
      apply Vector.ext
      intro j hj
      let jj : Fin m := ⟨j, hj⟩
      show (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩)[i][jj] = M[i][jj]
      rw [rowSwap_get]
      have h_ne_j : i ≠ ⟨src + k + 1, h⟩ := by
        intro heq; have := congrArg Fin.val heq; simp at this; omega
      have h_ne_i : i ≠ ⟨src + k, by omega⟩ := by
        intro heq; have := congrArg Fin.val heq; simp at this; omega
      rw [if_neg h_ne_j, if_neg h_ne_i]

/-- The bottom of the move interval (`i.val = src`) receives the row
originally at the top of the interval (`src + k`). -/
private theorem rowMoveUp_row_eq_src {R : Type u} {n m : Nat}
    (M : Matrix R n m) (src k : Nat) (h : src + k < n) (i : Fin n)
    (hi : i.val = src) :
    (rowMoveUp M src k h)[i] = M[(⟨src + k, h⟩ : Fin n)] := by
  induction k generalizing M with
  | zero =>
      have hii : i = (⟨src + 0, h⟩ : Fin n) := Fin.ext (by simp [hi])
      rw [hii]; rfl
  | succ k ih =>
      rw [rowMoveUp_succ]
      rw [ih (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩) (by omega)]
      apply Vector.ext
      intro j hj
      let jj : Fin m := ⟨j, hj⟩
      show (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩)[
          (⟨src + k, by omega⟩ : Fin n)][jj]
          = M[(⟨src + (k + 1), h⟩ : Fin n)][jj]
      rw [rowSwap_get]
      have h_ne_j : (⟨src + k, by omega⟩ : Fin n) ≠ ⟨src + k + 1, h⟩ := by
        intro heq; have := congrArg Fin.val heq; simp at this
      rw [if_neg h_ne_j, if_pos rfl]
      have hii : (⟨src + k + 1, h⟩ : Fin n) = ⟨src + (k + 1), h⟩ := by
        apply Fin.ext; simp; omega
      rw [hii]

/-- Strictly inside the move interval (`src < i.val ≤ src + k`), the row
at position `i` of `rowMoveUp` is the row originally at position
`i.val - 1`: each row shifted right by one to make room for the inserted
row at `src`. -/
private theorem rowMoveUp_row_between {R : Type u} {n m : Nat}
    (M : Matrix R n m) (src k : Nat) (h : src + k < n) (i : Fin n)
    (hi_lt : src < i.val) (hi_le : i.val ≤ src + k) :
    (rowMoveUp M src k h)[i] =
      M[(⟨i.val - 1, by have := i.isLt; omega⟩ : Fin n)] := by
  induction k generalizing M with
  | zero =>
      -- src < i.val ≤ src + 0 = src is empty
      omega
  | succ k ih =>
      rw [rowMoveUp_succ]
      by_cases h_lt : i.val ≤ src + k
      · -- Inductive case: still in the move interval after one swap
        rw [ih (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩) (by omega)
          h_lt]
        apply Vector.ext
        intro j hj
        let jj : Fin m := ⟨j, hj⟩
        show (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩)[
            (⟨i.val - 1, by have := i.isLt; omega⟩ : Fin n)][jj] =
          M[(⟨i.val - 1, by have := i.isLt; omega⟩ : Fin n)][jj]
        rw [rowSwap_get]
        have h_ne_j :
            (⟨i.val - 1, by have := i.isLt; omega⟩ : Fin n)
              ≠ ⟨src + k + 1, h⟩ := by
          intro heq; have := congrArg Fin.val heq; simp at this; omega
        have h_ne_i :
            (⟨i.val - 1, by have := i.isLt; omega⟩ : Fin n)
              ≠ ⟨src + k, by omega⟩ := by
          intro heq; have := congrArg Fin.val heq; simp at this; omega
        rw [if_neg h_ne_j, if_neg h_ne_i]
      · -- Boundary case: i.val = src + k + 1
        have hi_eq : i.val = src + k + 1 := by omega
        have h_gt : src + k < i.val := by omega
        rw [rowMoveUp_row_of_gt
          (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩) src k
          (by omega) i h_gt]
        apply Vector.ext
        intro j hj
        let jj : Fin m := ⟨j, hj⟩
        show (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩)[i][jj] =
          M[(⟨i.val - 1, by have := i.isLt; omega⟩ : Fin n)][jj]
        rw [rowSwap_get]
        have h_eq_j : i = (⟨src + k + 1, h⟩ : Fin n) := by
          apply Fin.ext; simp [hi_eq]
        rw [if_pos h_eq_j]
        have hii : (⟨src + k, by omega⟩ : Fin n) =
            ⟨i.val - 1, by have := i.isLt; omega⟩ := by
          apply Fin.ext; simp; omega
        rw [hii]

/-! ### One-row `setRow` transports to ordered `nDet` minors

For `a < b < t` in `Fin (n + 2)`, the private helpers
`rowMoveUp_setRow_nMatrix_replace_first_eq_nMatrix` and
`_replace_second_eq_nMatrix` identify the result of replacing the
`(t.val - 2)`-th row of `nMatrix B a b hab` with `B[a]` (respectively
`B[b]`) as a `rowMoveUp` of the ordered minor `nMatrix B b t` (resp.
`nMatrix B a t`). The four ordered four-row transports
`det_setRow_nMatrix_r{2,3}_r{0,1}_eq_pow_mul_nDet_*` combine these row
equalities with `det_rowMoveUp` to give the signed `nDet` lemmas
required by the ordered four-row Plucker assembly. -/

/-- For `a < b < t`, replacing row `s` (with `s.val = t.val - 2`) of
`nMatrix B a b hab` by `B[a]` and then sliding that row up to position
`a.val` by `t.val - a.val - 2` adjacent swaps reproduces
`nMatrix B b t hbt`. -/
private theorem rowMoveUp_setRow_nMatrix_replace_first_eq_nMatrix
    {R : Type u} {n : Nat} (B : Matrix R (n + 2) n)
    (a b t : Fin (n + 2)) (hab : a.val < b.val) (hbt : b.val < t.val)
    (s : Fin n) (hs : s.val = t.val - 2)
    (hsk : a.val + (t.val - a.val - 2) < n) :
    rowMoveUp (setRow (nMatrix B a b hab) s B[a]) a.val
        (t.val - a.val - 2) hsk =
      nMatrix B b t hbt := by
  apply Vector.ext
  intro i hi
  let ii : Fin n := ⟨i, hi⟩
  show (rowMoveUp (setRow (nMatrix B a b hab) s B[a]) a.val
        (t.val - a.val - 2) hsk)[ii] = (nMatrix B b t hbt)[ii]
  by_cases h_below : ii.val < a.val
  · -- Below the move interval: both rowMoveUp and setRow leave the row alone.
    have hii_ne_s : ii ≠ s := by
      intro he
      have hv : ii.val = s.val := congrArg Fin.val he
      rw [hs] at hv
      have : a.val < t.val := Nat.lt_trans hab hbt
      omega
    rw [rowMoveUp_row_of_lt (setRow (nMatrix B a b hab) s B[a]) a.val
          (t.val - a.val - 2) hsk ii h_below,
        setRow_row_ne (nMatrix B a b hab) s ii B[a] hii_ne_s]
    apply Vector.ext
    intro j hj
    let jj : Fin n := ⟨j, hj⟩
    show (nMatrix B a b hab)[ii][jj] = (nMatrix B b t hbt)[ii][jj]
    rw [nMatrix_entry, nMatrix_entry]
    have hii_lt_b : ii.val < b.val := Nat.lt_trans h_below hab
    have hidx : skipIndex2 a b hab ii = skipIndex2 b t hbt ii := by
      apply Fin.ext
      rw [skipIndex2_val_of_lt_p a b hab ii h_below,
          skipIndex2_val_of_lt_p b t hbt ii hii_lt_b]
    exact congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx
  · by_cases h_eq : ii.val = a.val
    · -- At the source of the move: the inserted row B[a] surfaces here.
      have h_row_eq :
          (rowMoveUp (setRow (nMatrix B a b hab) s B[a]) a.val
              (t.val - a.val - 2) hsk)[ii] = B[a] := by
        rw [rowMoveUp_row_eq_src (setRow (nMatrix B a b hab) s B[a]) a.val
              (t.val - a.val - 2) hsk ii h_eq]
        have hidx_eq :
            (⟨a.val + (t.val - a.val - 2), hsk⟩ : Fin n) = s := by
          apply Fin.ext
          show a.val + (t.val - a.val - 2) = s.val
          rw [hs]; omega
        calc (setRow (nMatrix B a b hab) s B[a])[
              (⟨a.val + (t.val - a.val - 2), hsk⟩ : Fin n)]
            = (setRow (nMatrix B a b hab) s B[a])[s] :=
              congrArg
                (fun (i : Fin n) =>
                  (setRow (nMatrix B a b hab) s B[a])[i]) hidx_eq
          _ = B[a] := setRow_get_self _ _ _
      rw [h_row_eq]
      apply Vector.ext
      intro j hj
      let jj : Fin n := ⟨j, hj⟩
      show B[a][jj] = (nMatrix B b t hbt)[ii][jj]
      rw [nMatrix_entry]
      have hii_lt_b : ii.val < b.val := by rw [h_eq]; exact hab
      have hidx : skipIndex2 b t hbt ii = a := by
        apply Fin.ext
        rw [skipIndex2_val_of_lt_p b t hbt ii hii_lt_b]
        exact h_eq
      exact (congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx).symm
    · by_cases h_above : t.val - 2 < ii.val
      · -- Above the move interval: both rowMoveUp and setRow leave the row alone.
        have h_above' : a.val + (t.val - a.val - 2) < ii.val := by
          have : a.val + (t.val - a.val - 2) = t.val - 2 := by omega
          rw [this]; exact h_above
        rw [rowMoveUp_row_of_gt (setRow (nMatrix B a b hab) s B[a]) a.val
              (t.val - a.val - 2) hsk ii h_above']
        have hii_ne_s : ii ≠ s := by
          intro he
          have hv : ii.val = s.val := congrArg Fin.val he
          rw [hs] at hv; omega
        rw [setRow_row_ne (nMatrix B a b hab) s ii B[a] hii_ne_s]
        apply Vector.ext
        intro j hj
        let jj : Fin n := ⟨j, hj⟩
        show (nMatrix B a b hab)[ii][jj] = (nMatrix B b t hbt)[ii][jj]
        rw [nMatrix_entry, nMatrix_entry]
        have h_not_lt_a : ¬ ii.val < a.val := h_below
        have h_not_between_lhs : ¬ ii.val + 1 < b.val := by omega
        have h_not_lt_b_rhs : ¬ ii.val < b.val := by omega
        have h_not_between_rhs : ¬ ii.val + 1 < t.val := by omega
        have hidx : skipIndex2 a b hab ii = skipIndex2 b t hbt ii := by
          apply Fin.ext
          rw [skipIndex2_val_of_ge_q a b hab ii h_not_lt_a h_not_between_lhs,
              skipIndex2_val_of_ge_q b t hbt ii h_not_lt_b_rhs h_not_between_rhs]
        exact congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx
      · -- Inside the move interval (strictly): rows shift right by one.
        have h_lt_src : a.val < ii.val := by
          have h1 : ¬ ii.val < a.val := h_below
          have h2 : ii.val ≠ a.val := h_eq
          omega
        have h_le_top : ii.val ≤ a.val + (t.val - a.val - 2) := by
          have : a.val + (t.val - a.val - 2) = t.val - 2 := by omega
          rw [this]; omega
        rw [rowMoveUp_row_between (setRow (nMatrix B a b hab) s B[a]) a.val
              (t.val - a.val - 2) hsk ii h_lt_src h_le_top]
        let j_minus : Fin n := ⟨ii.val - 1, by have := ii.isLt; omega⟩
        have hj_ne_s : j_minus ≠ s := by
          intro he
          have hv : j_minus.val = s.val := congrArg Fin.val he
          rw [hs] at hv
          have : ii.val - 1 = t.val - 2 := hv
          omega
        rw [setRow_row_ne (nMatrix B a b hab) s j_minus B[a] hj_ne_s]
        apply Vector.ext
        intro j hj
        let jj : Fin n := ⟨j, hj⟩
        show (nMatrix B a b hab)[j_minus][jj] = (nMatrix B b t hbt)[ii][jj]
        rw [nMatrix_entry, nMatrix_entry]
        have h_not_lt_a : ¬ j_minus.val < a.val := by
          show ¬ ii.val - 1 < a.val; omega
        by_cases h_below_b : ii.val < b.val
        · have h_between_lhs : j_minus.val + 1 < b.val := by
            show ii.val - 1 + 1 < b.val; omega
          have h_lt_b_rhs : ii.val < b.val := h_below_b
          have hidx : skipIndex2 a b hab j_minus = skipIndex2 b t hbt ii := by
            apply Fin.ext
            rw [skipIndex2_val_of_between a b hab j_minus h_not_lt_a
                  h_between_lhs,
                skipIndex2_val_of_lt_p b t hbt ii h_lt_b_rhs]
            show ii.val - 1 + 1 = ii.val
            omega
          exact congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx
        · have h_not_between_lhs : ¬ j_minus.val + 1 < b.val := by
            show ¬ ii.val - 1 + 1 < b.val; omega
          have h_not_lt_b_rhs : ¬ ii.val < b.val := h_below_b
          have h_between_rhs : ii.val + 1 < t.val := by omega
          have hidx : skipIndex2 a b hab j_minus = skipIndex2 b t hbt ii := by
            apply Fin.ext
            rw [skipIndex2_val_of_ge_q a b hab j_minus h_not_lt_a
                  h_not_between_lhs,
                skipIndex2_val_of_between b t hbt ii h_not_lt_b_rhs
                  h_between_rhs]
            show ii.val - 1 + 2 = ii.val + 1
            omega
          exact congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx

/-- For `a < b < t`, replacing row `s` (with `s.val = t.val - 2`) of
`nMatrix B a b hab` by `B[b]` and then sliding that row up to position
`b.val - 1` by `t.val - b.val - 1` adjacent swaps reproduces
`nMatrix B a t (Nat.lt_trans hab hbt)`. -/
private theorem rowMoveUp_setRow_nMatrix_replace_second_eq_nMatrix
    {R : Type u} {n : Nat} (B : Matrix R (n + 2) n)
    (a b t : Fin (n + 2)) (hab : a.val < b.val) (hbt : b.val < t.val)
    (s : Fin n) (hs : s.val = t.val - 2)
    (hsk : b.val - 1 + (t.val - b.val - 1) < n) :
    rowMoveUp (setRow (nMatrix B a b hab) s B[b]) (b.val - 1)
        (t.val - b.val - 1) hsk =
      nMatrix B a t (Nat.lt_trans hab hbt) := by
  apply Vector.ext
  intro i hi
  let ii : Fin n := ⟨i, hi⟩
  have hat : a.val < t.val := Nat.lt_trans hab hbt
  show (rowMoveUp (setRow (nMatrix B a b hab) s B[b]) (b.val - 1)
        (t.val - b.val - 1) hsk)[ii] = (nMatrix B a t hat)[ii]
  by_cases h_below : ii.val < b.val - 1
  · -- Below the move interval.
    have hii_ne_s : ii ≠ s := by
      intro he
      have hv : ii.val = s.val := congrArg Fin.val he
      rw [hs] at hv; omega
    rw [rowMoveUp_row_of_lt (setRow (nMatrix B a b hab) s B[b]) (b.val - 1)
          (t.val - b.val - 1) hsk ii h_below,
        setRow_row_ne (nMatrix B a b hab) s ii B[b] hii_ne_s]
    apply Vector.ext
    intro j hj
    let jj : Fin n := ⟨j, hj⟩
    show (nMatrix B a b hab)[ii][jj] = (nMatrix B a t hat)[ii][jj]
    rw [nMatrix_entry, nMatrix_entry]
    by_cases h_lt_a : ii.val < a.val
    · have hidx : skipIndex2 a b hab ii = skipIndex2 a t hat ii := by
        apply Fin.ext
        rw [skipIndex2_val_of_lt_p a b hab ii h_lt_a,
            skipIndex2_val_of_lt_p a t hat ii h_lt_a]
      exact congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx
    · have h_between_lhs : ii.val + 1 < b.val := by omega
      have h_between_rhs : ii.val + 1 < t.val := by omega
      have hidx : skipIndex2 a b hab ii = skipIndex2 a t hat ii := by
        apply Fin.ext
        rw [skipIndex2_val_of_between a b hab ii h_lt_a h_between_lhs,
            skipIndex2_val_of_between a t hat ii h_lt_a h_between_rhs]
      exact congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx
  · by_cases h_eq : ii.val = b.val - 1
    · -- At the source of the move: the inserted row B[b] surfaces here.
      have h_row_eq :
          (rowMoveUp (setRow (nMatrix B a b hab) s B[b]) (b.val - 1)
              (t.val - b.val - 1) hsk)[ii] = B[b] := by
        rw [rowMoveUp_row_eq_src (setRow (nMatrix B a b hab) s B[b])
              (b.val - 1) (t.val - b.val - 1) hsk ii h_eq]
        have hidx_eq :
            (⟨b.val - 1 + (t.val - b.val - 1), hsk⟩ : Fin n) = s := by
          apply Fin.ext
          show b.val - 1 + (t.val - b.val - 1) = s.val
          rw [hs]; omega
        calc (setRow (nMatrix B a b hab) s B[b])[
              (⟨b.val - 1 + (t.val - b.val - 1), hsk⟩ : Fin n)]
            = (setRow (nMatrix B a b hab) s B[b])[s] :=
              congrArg
                (fun (i : Fin n) =>
                  (setRow (nMatrix B a b hab) s B[b])[i]) hidx_eq
          _ = B[b] := setRow_get_self _ _ _
      rw [h_row_eq]
      apply Vector.ext
      intro j hj
      let jj : Fin n := ⟨j, hj⟩
      show B[b][jj] = (nMatrix B a t hat)[ii][jj]
      rw [nMatrix_entry]
      have h_not_lt_a : ¬ ii.val < a.val := by
        have : a.val ≤ b.val - 1 := by omega
        rw [h_eq]; omega
      have h_between : ii.val + 1 < t.val := by rw [h_eq]; omega
      have hidx : skipIndex2 a t hat ii = b := by
        apply Fin.ext
        rw [skipIndex2_val_of_between a t hat ii h_not_lt_a h_between]
        show ii.val + 1 = b.val
        rw [h_eq]; omega
      exact (congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx).symm
    · by_cases h_above : t.val - 2 < ii.val
      · -- Above the move interval.
        have h_above' : b.val - 1 + (t.val - b.val - 1) < ii.val := by
          have : b.val - 1 + (t.val - b.val - 1) = t.val - 2 := by omega
          rw [this]; exact h_above
        rw [rowMoveUp_row_of_gt (setRow (nMatrix B a b hab) s B[b])
              (b.val - 1) (t.val - b.val - 1) hsk ii h_above']
        have hii_ne_s : ii ≠ s := by
          intro he
          have hv : ii.val = s.val := congrArg Fin.val he
          rw [hs] at hv; omega
        rw [setRow_row_ne (nMatrix B a b hab) s ii B[b] hii_ne_s]
        apply Vector.ext
        intro j hj
        let jj : Fin n := ⟨j, hj⟩
        show (nMatrix B a b hab)[ii][jj] = (nMatrix B a t hat)[ii][jj]
        rw [nMatrix_entry, nMatrix_entry]
        have h_not_lt_a : ¬ ii.val < a.val := by omega
        have h_not_between_lhs : ¬ ii.val + 1 < b.val := by omega
        have h_not_between_rhs : ¬ ii.val + 1 < t.val := by omega
        have hidx : skipIndex2 a b hab ii = skipIndex2 a t hat ii := by
          apply Fin.ext
          rw [skipIndex2_val_of_ge_q a b hab ii h_not_lt_a h_not_between_lhs,
              skipIndex2_val_of_ge_q a t hat ii h_not_lt_a h_not_between_rhs]
        exact congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx
      · -- Inside the move interval (strictly).
        have h_lt_src : b.val - 1 < ii.val := by
          have h1 : ¬ ii.val < b.val - 1 := h_below
          have h2 : ii.val ≠ b.val - 1 := h_eq
          omega
        have h_le_top : ii.val ≤ b.val - 1 + (t.val - b.val - 1) := by
          have : b.val - 1 + (t.val - b.val - 1) = t.val - 2 := by omega
          rw [this]; omega
        rw [rowMoveUp_row_between (setRow (nMatrix B a b hab) s B[b])
              (b.val - 1) (t.val - b.val - 1) hsk ii h_lt_src h_le_top]
        let j_minus : Fin n := ⟨ii.val - 1, by have := ii.isLt; omega⟩
        have hj_ne_s : j_minus ≠ s := by
          intro he
          have hv : j_minus.val = s.val := congrArg Fin.val he
          rw [hs] at hv
          have : ii.val - 1 = t.val - 2 := hv
          omega
        rw [setRow_row_ne (nMatrix B a b hab) s j_minus B[b] hj_ne_s]
        apply Vector.ext
        intro j hj
        let jj : Fin n := ⟨j, hj⟩
        show (nMatrix B a b hab)[j_minus][jj] = (nMatrix B a t hat)[ii][jj]
        rw [nMatrix_entry, nMatrix_entry]
        have h_not_lt_a_lhs : ¬ j_minus.val < a.val := by
          show ¬ ii.val - 1 < a.val
          have : a.val ≤ b.val - 1 := by omega
          omega
        have h_not_between_lhs : ¬ j_minus.val + 1 < b.val := by
          show ¬ ii.val - 1 + 1 < b.val
          omega
        have h_not_lt_a_rhs : ¬ ii.val < a.val := by omega
        have h_between_rhs : ii.val + 1 < t.val := by omega
        have hidx : skipIndex2 a b hab j_minus = skipIndex2 a t hat ii := by
          apply Fin.ext
          rw [skipIndex2_val_of_ge_q a b hab j_minus h_not_lt_a_lhs
                h_not_between_lhs,
              skipIndex2_val_of_between a t hat ii h_not_lt_a_rhs
                h_between_rhs]
          show ii.val - 1 + 2 = ii.val + 1
          omega
        exact congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx

/-- For ordered rows `r0 < r1 < r2 < r3` of `B : Matrix R (n + 2) n`,
replacing the `s2 = ⟨r2.val - 2, _⟩` row of `nMatrix B r0 r1 h01` by
`B[r0]` produces the signed `nDet B r1 r2 h12` minor with sign
`(-1) ^ (r2.val - r0.val - 2)`. -/
private theorem det_setRow_nMatrix_r2_r0_eq_pow_mul_nDet_r1_r2
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (r0 r1 r2 r3 : Fin (n + 2))
    (h01 : r0.val < r1.val) (h12 : r1.val < r2.val) (h23 : r2.val < r3.val) :
    let M := nMatrix B r0 r1 h01
    let s2 : Fin n := ⟨r2.val - 2, by have := r3.isLt; omega⟩
    det (setRow M s2 B[r0]) =
      (-1 : R) ^ (r2.val - r0.val - 2) * nDet B r1 r2 h12 := by
  intro M s2
  have hsk : r0.val + (r2.val - r0.val - 2) < n := by
    have _h13 : r1.val < r3.val := Nat.lt_trans h12 h23
    have := r3.isLt; omega
  have hrow := rowMoveUp_setRow_nMatrix_replace_first_eq_nMatrix
      B r0 r1 r2 h01 h12 s2 rfl hsk
  have hdet_rm :=
    det_rowMoveUp (setRow M s2 B[r0]) r0.val (r2.val - r0.val - 2) hsk
  rw [hrow] at hdet_rm
  show det (setRow M s2 B[r0]) =
    (-1 : R) ^ (r2.val - r0.val - 2) * nDet B r1 r2 h12
  have h_nDet : nDet B r1 r2 h12 = det (nMatrix B r1 r2 h12) := rfl
  rw [h_nDet, hdet_rm, ← Lean.Grind.Semiring.mul_assoc,
      neg_one_pow_mul_self, Lean.Grind.Semiring.one_mul]

/-- For ordered rows `r0 < r1 < r2 < r3`, replacing the
`s3 = ⟨r3.val - 2, _⟩` row of `nMatrix B r0 r1 h01` by `B[r0]` produces
the signed `nDet B r1 r3 _` minor with sign `(-1) ^ (r3.val - r0.val - 2)`. -/
private theorem det_setRow_nMatrix_r3_r0_eq_pow_mul_nDet_r1_r3
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (r0 r1 r2 r3 : Fin (n + 2))
    (h01 : r0.val < r1.val) (h12 : r1.val < r2.val) (h23 : r2.val < r3.val) :
    let M := nMatrix B r0 r1 h01
    let s3 : Fin n := ⟨r3.val - 2, by have := r3.isLt; omega⟩
    det (setRow M s3 B[r0]) =
      (-1 : R) ^ (r3.val - r0.val - 2) *
        nDet B r1 r3 (Nat.lt_trans h12 h23) := by
  intro M s3
  have h13 : r1.val < r3.val := Nat.lt_trans h12 h23
  have hsk : r0.val + (r3.val - r0.val - 2) < n := by
    have := r3.isLt; omega
  have hrow := rowMoveUp_setRow_nMatrix_replace_first_eq_nMatrix
      B r0 r1 r3 h01 h13 s3 rfl hsk
  have hdet_rm :=
    det_rowMoveUp (setRow M s3 B[r0]) r0.val (r3.val - r0.val - 2) hsk
  rw [hrow] at hdet_rm
  show det (setRow M s3 B[r0]) =
    (-1 : R) ^ (r3.val - r0.val - 2) * nDet B r1 r3 h13
  have h_nDet : nDet B r1 r3 h13 = det (nMatrix B r1 r3 h13) := rfl
  rw [h_nDet, hdet_rm, ← Lean.Grind.Semiring.mul_assoc,
      neg_one_pow_mul_self, Lean.Grind.Semiring.one_mul]

/-- For ordered rows `r0 < r1 < r2 < r3`, replacing the
`s2 = ⟨r2.val - 2, _⟩` row of `nMatrix B r0 r1 h01` by `B[r1]` produces
the signed `nDet B r0 r2 _` minor with sign `(-1) ^ (r2.val - r1.val - 1)`. -/
private theorem det_setRow_nMatrix_r2_r1_eq_pow_mul_nDet_r0_r2
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (r0 r1 r2 r3 : Fin (n + 2))
    (h01 : r0.val < r1.val) (h12 : r1.val < r2.val) (h23 : r2.val < r3.val) :
    let M := nMatrix B r0 r1 h01
    let s2 : Fin n := ⟨r2.val - 2, by have := r3.isLt; omega⟩
    det (setRow M s2 B[r1]) =
      (-1 : R) ^ (r2.val - r1.val - 1) *
        nDet B r0 r2 (Nat.lt_trans h01 h12) := by
  intro M s2
  have h02 : r0.val < r2.val := Nat.lt_trans h01 h12
  have hsk : r1.val - 1 + (r2.val - r1.val - 1) < n := by
    have := r3.isLt; omega
  have hrow := rowMoveUp_setRow_nMatrix_replace_second_eq_nMatrix
      B r0 r1 r2 h01 h12 s2 rfl hsk
  have hdet_rm :=
    det_rowMoveUp (setRow M s2 B[r1]) (r1.val - 1) (r2.val - r1.val - 1) hsk
  rw [hrow] at hdet_rm
  show det (setRow M s2 B[r1]) =
    (-1 : R) ^ (r2.val - r1.val - 1) * nDet B r0 r2 h02
  have h_nDet : nDet B r0 r2 h02 = det (nMatrix B r0 r2 h02) := rfl
  rw [h_nDet, hdet_rm, ← Lean.Grind.Semiring.mul_assoc,
      neg_one_pow_mul_self, Lean.Grind.Semiring.one_mul]

/-- For ordered rows `r0 < r1 < r2 < r3`, replacing the
`s3 = ⟨r3.val - 2, _⟩` row of `nMatrix B r0 r1 h01` by `B[r1]` produces
the signed `nDet B r0 r3 _` minor with sign `(-1) ^ (r3.val - r1.val - 1)`. -/
private theorem det_setRow_nMatrix_r3_r1_eq_pow_mul_nDet_r0_r3
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (r0 r1 r2 r3 : Fin (n + 2))
    (h01 : r0.val < r1.val) (h12 : r1.val < r2.val) (h23 : r2.val < r3.val) :
    let M := nMatrix B r0 r1 h01
    let s3 : Fin n := ⟨r3.val - 2, by have := r3.isLt; omega⟩
    det (setRow M s3 B[r1]) =
      (-1 : R) ^ (r3.val - r1.val - 1) *
        nDet B r0 r3 (Nat.lt_trans h01 (Nat.lt_trans h12 h23)) := by
  intro M s3
  have h13 : r1.val < r3.val := Nat.lt_trans h12 h23
  have h03 : r0.val < r3.val := Nat.lt_trans h01 h13
  have hsk : r1.val - 1 + (r3.val - r1.val - 1) < n := by
    have := r3.isLt; omega
  have hrow := rowMoveUp_setRow_nMatrix_replace_second_eq_nMatrix
      B r0 r1 r3 h01 h13 s3 rfl hsk
  have hdet_rm :=
    det_rowMoveUp (setRow M s3 B[r1]) (r1.val - 1) (r3.val - r1.val - 1) hsk
  rw [hrow] at hdet_rm
  show det (setRow M s3 B[r1]) =
    (-1 : R) ^ (r3.val - r1.val - 1) * nDet B r0 r3 h03
  have h_nDet : nDet B r0 r3 h03 = det (nMatrix B r0 r3 h03) := rfl
  rw [h_nDet, hdet_rm, ← Lean.Grind.Semiring.mul_assoc,
      neg_one_pow_mul_self, Lean.Grind.Semiring.one_mul]

/-! ### Double-row `setRow` transport to ordered `nDet` minors

For ordered rows `r0 < r1 < r2 < r3`, the double replacement
`setRow (setRow (nMatrix B r0 r1 h01) s2 B[r0]) s3 B[r1]` (with
`s2 = ⟨r2.val - 2, _⟩` and `s3 = ⟨r3.val - 2, _⟩`) realises the row
content of `nMatrix B r2 r3 h23` with the inserted rows `B[r0]` and
`B[r1]` displaced downward. Two `rowMoveUp` operations (first sliding
`B[r0]` up to position `r0.val`, then `B[r1]` up to position `r1.val - 1`
of the intermediate matrix) reorder the rows back, contributing the
combined sign `(-1)^((r2 - r0 - 2) + (r3 - r1 - 2))`. The intermediate
identification uses `rowMoveUp_setRow_of_gt` to slide the outer
`setRow s3 B[r1]` past the inner `rowMoveUp`, since `s3.val > r2.val - 2`
places it strictly above the inner move interval. -/

/-- `rowMoveUp` commutes with `setRow` when the `setRow` target index
sits strictly above the move interval. The destination row is untouched
by `rowMoveUp` on both sides, so the operations can be exchanged. -/
private theorem rowMoveUp_setRow_of_gt {R : Type u} {n m : Nat}
    (M : Matrix R n m) (src k : Nat) (h : src + k < n) (j : Fin n)
    (v : Vector R m) (hj : src + k < j.val) :
    rowMoveUp (setRow M j v) src k h = setRow (rowMoveUp M src k h) j v := by
  apply Vector.ext
  intro i hi
  let ii : Fin n := ⟨i, hi⟩
  show (rowMoveUp (setRow M j v) src k h)[ii] =
    (setRow (rowMoveUp M src k h) j v)[ii]
  by_cases h_eq_j : ii = j
  · -- ii = j: both sides evaluate to v
    have hii_gt : src + k < ii.val := by
      have := congrArg Fin.val h_eq_j; omega
    have hLHS_move :
        (rowMoveUp (setRow M j v) src k h)[ii] = (setRow M j v)[ii] :=
      rowMoveUp_row_of_gt (setRow M j v) src k h ii hii_gt
    have hLHS_idx :
        (setRow M j v)[ii] = (setRow M j v)[j] :=
      congrArg (fun (i : Fin n) => (setRow M j v)[i]) h_eq_j
    have hRHS_idx :
        (setRow (rowMoveUp M src k h) j v)[ii] =
          (setRow (rowMoveUp M src k h) j v)[j] :=
      congrArg (fun (i : Fin n) =>
        (setRow (rowMoveUp M src k h) j v)[i]) h_eq_j
    rw [hLHS_move, hLHS_idx, hRHS_idx, setRow_get_self, setRow_get_self]
  · -- ii ≠ j: the outer setRow on the RHS is a no-op at ii
    rw [setRow_row_ne (rowMoveUp M src k h) j ii v h_eq_j]
    by_cases h_below : ii.val < src
    · -- Below the move interval: both rowMoveUp ops are no-ops at ii
      rw [rowMoveUp_row_of_lt (setRow M j v) src k h ii h_below,
          rowMoveUp_row_of_lt M src k h ii h_below,
          setRow_row_ne M j ii v h_eq_j]
    · by_cases h_eq_src : ii.val = src
      · -- ii.val = src: rowMoveUp produces the row originally at src + k
        rw [rowMoveUp_row_eq_src (setRow M j v) src k h ii h_eq_src,
            rowMoveUp_row_eq_src M src k h ii h_eq_src]
        have hsk_ne_j : (⟨src + k, h⟩ : Fin n) ≠ j := by
          intro he
          have : src + k = j.val := congrArg Fin.val he
          omega
        rw [setRow_row_ne M j ⟨src + k, h⟩ v hsk_ne_j]
      · by_cases h_above : src + k < ii.val
        · -- Above the move interval: both rowMoveUp ops are no-ops at ii
          rw [rowMoveUp_row_of_gt (setRow M j v) src k h ii h_above,
              rowMoveUp_row_of_gt M src k h ii h_above,
              setRow_row_ne M j ii v h_eq_j]
        · -- Strictly inside: src < ii.val ≤ src + k; both rowMoveUp ops
          -- produce the row originally at ii.val - 1
          have h_lt_src : src < ii.val := by
            have h1 : ¬ ii.val < src := h_below
            have h2 : ii.val ≠ src := h_eq_src
            omega
          have h_le_top : ii.val ≤ src + k := by omega
          rw [rowMoveUp_row_between (setRow M j v) src k h ii h_lt_src h_le_top,
              rowMoveUp_row_between M src k h ii h_lt_src h_le_top]
          have h_iminus_ne_j :
              (⟨ii.val - 1, by have := ii.isLt; omega⟩ : Fin n) ≠ j := by
            intro he
            have : ii.val - 1 = j.val := congrArg Fin.val he
            omega
          rw [setRow_row_ne M j ⟨ii.val - 1, by have := ii.isLt; omega⟩
                v h_iminus_ne_j]

/-- For ordered rows `r0 < r1 < r2 < r3`, the doubly-replaced matrix
`setRow (setRow (nMatrix B r0 r1 h01) s2 B[r0]) s3 B[r1]` (with
`s2 = ⟨r2.val - 2, _⟩` and `s3 = ⟨r3.val - 2, _⟩`) has determinant
`(-1)^((r2 - r0 - 2) + (r3 - r1 - 2)) * nDet B r2 r3 h23`. -/
private theorem det_setRow_setRow_nMatrix_r2_r0_r3_r1_eq_pow_mul_nDet_r2_r3
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (r0 r1 r2 r3 : Fin (n + 2))
    (h01 : r0.val < r1.val) (h12 : r1.val < r2.val)
    (h23 : r2.val < r3.val) :
    let M := nMatrix B r0 r1 h01
    let s2 : Fin n := ⟨r2.val - 2, by have := r3.isLt; omega⟩
    let s3 : Fin n := ⟨r3.val - 2, by have := r3.isLt; omega⟩
    det (setRow (setRow M s2 B[r0]) s3 B[r1]) =
      (-1 : R) ^ ((r2.val - r0.val - 2) + (r3.val - r1.val - 2)) *
        nDet B r2 r3 h23 := by
  intro M s2 s3
  have hsk1 : r0.val + (r2.val - r0.val - 2) < n := by
    have := r3.isLt; omega
  have hsk2 : r1.val + (r3.val - r1.val - 2) < n := by
    have := r3.isLt; omega
  have hs3_gt : r0.val + (r2.val - r0.val - 2) < s3.val := by
    show r0.val + (r2.val - r0.val - 2) < r3.val - 2
    omega
  -- Step 1: slide the outer `setRow s3 B[r1]` past the first `rowMoveUp`.
  have hcommute :
      rowMoveUp (setRow (setRow M s2 B[r0]) s3 B[r1]) r0.val
          (r2.val - r0.val - 2) hsk1 =
        setRow
          (rowMoveUp (setRow M s2 B[r0]) r0.val (r2.val - r0.val - 2) hsk1)
          s3 B[r1] :=
    rowMoveUp_setRow_of_gt (setRow M s2 B[r0]) r0.val (r2.val - r0.val - 2)
      hsk1 s3 B[r1] hs3_gt
  -- Step 2: identify the inner `rowMoveUp` with `nMatrix B r1 r2 h12`.
  have hrow1 :
      rowMoveUp (setRow M s2 B[r0]) r0.val (r2.val - r0.val - 2) hsk1 =
        nMatrix B r1 r2 h12 :=
    rowMoveUp_setRow_nMatrix_replace_first_eq_nMatrix
      B r0 r1 r2 h01 h12 s2 rfl hsk1
  rw [hrow1] at hcommute
  -- Step 3: outer `det_rowMoveUp` peels off the first sign factor.
  have hdet_outer :=
    det_rowMoveUp (setRow (setRow M s2 B[r0]) s3 B[r1]) r0.val
      (r2.val - r0.val - 2) hsk1
  rw [hcommute] at hdet_outer
  -- hdet_outer : det (setRow (nMatrix B r1 r2 h12) s3 B[r1]) =
  --              (-1)^(r2 - r0 - 2) * det (setRow (setRow M s2 B[r0]) s3 B[r1])
  -- Step 4: identify the next `rowMoveUp` with `nMatrix B r2 r3 h23`.
  have hrow2 :
      rowMoveUp (setRow (nMatrix B r1 r2 h12) s3 B[r1]) r1.val
          (r3.val - r1.val - 2) hsk2 =
        nMatrix B r2 r3 h23 :=
    rowMoveUp_setRow_nMatrix_replace_first_eq_nMatrix
      B r1 r2 r3 h12 h23 s3 rfl hsk2
  -- Step 5: inner `det_rowMoveUp` peels off the second sign factor.
  have hdet_inner :=
    det_rowMoveUp (setRow (nMatrix B r1 r2 h12) s3 B[r1]) r1.val
      (r3.val - r1.val - 2) hsk2
  rw [hrow2] at hdet_inner
  -- hdet_inner : det (nMatrix B r2 r3 h23) =
  --              (-1)^(r3 - r1 - 2) * det (setRow (nMatrix B r1 r2 h12) s3 B[r1])
  -- Combine. Let a = r2 - r0 - 2, b = r3 - r1 - 2. After substitution we
  -- need D = (-1)^(a+b) * ((-1)^b * ((-1)^a * D)), which collapses by
  -- `pow_add` and `neg_one_pow_mul_self`.
  show det (setRow (setRow M s2 B[r0]) s3 B[r1]) =
    (-1 : R) ^ ((r2.val - r0.val - 2) + (r3.val - r1.val - 2)) *
      nDet B r2 r3 h23
  have h_nDet : nDet B r2 r3 h23 = det (nMatrix B r2 r3 h23) := rfl
  rw [h_nDet, hdet_inner, hdet_outer]
  have h_pow_add :
      (-1 : R) ^ ((r2.val - r0.val - 2) + (r3.val - r1.val - 2)) =
        (-1 : R) ^ (r2.val - r0.val - 2) *
          (-1 : R) ^ (r3.val - r1.val - 2) :=
    Lean.Grind.Semiring.pow_add (-1 : R) (r2.val - r0.val - 2)
      (r3.val - r1.val - 2)
  have h_self_a := neg_one_pow_mul_self (R := R) (r2.val - r0.val - 2)
  have h_self_b := neg_one_pow_mul_self (R := R) (r3.val - r1.val - 2)
  rw [h_pow_add]
  grind

/-- The square matrix `[B | u | v]` formed by appending two vector columns to
`B : Matrix R (n + 2) n`. The original `B` columns occupy positions
`0..n-1`; `u` occupies column `n`; `v` occupies the last column. -/
def twoColMatrix {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (u v : Vector R (n + 2)) :
    Matrix R (n + 2) (n + 2) :=
  ofFn fun i j =>
    if hj : j.val < n then
      B[i][(⟨j.val, hj⟩ : Fin n)]
    else if hju : j.val = n then
      u[i]
    else
      v[i]

/-- In one of the original `B` columns, `twoColMatrix` agrees entrywise with
`B`. -/
theorem twoColMatrix_entry_lt {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (u v : Vector R (n + 2))
    (i j : Fin (n + 2)) (h : j.val < n) :
    (twoColMatrix B u v)[i][j] = B[i][(⟨j.val, h⟩ : Fin n)] := by
  unfold twoColMatrix
  rw [getElem_ofFn]
  exact dif_pos h

/-- The penultimate column of `twoColMatrix B u v` is `u`. -/
theorem twoColMatrix_entry_penultimate {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (u v : Vector R (n + 2))
    (i : Fin (n + 2)) :
    (twoColMatrix B u v)[i][(⟨n, by omega⟩ : Fin (n + 2))] = u[i] := by
  unfold twoColMatrix
  rw [getElem_ofFn]
  have hnlt : ¬ (⟨n, by omega⟩ : Fin (n + 2)).val < n := by
    simp
  have hneq : (⟨n, by omega⟩ : Fin (n + 2)).val = n := by
    simp
  rw [dif_neg hnlt]
  rw [dif_pos hneq]

/-- The last column of `twoColMatrix B u v` is `v`. -/
theorem twoColMatrix_entry_last {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (u v : Vector R (n + 2))
    (i : Fin (n + 2)) :
    (twoColMatrix B u v)[i][Fin.last (n + 1)] = v[i] := by
  unfold twoColMatrix
  rw [getElem_ofFn]
  have hlast_lt : ¬ (Fin.last (n + 1) : Fin (n + 2)).val < n := by
    simp [Fin.last]
  have hlast_ne : ¬ (Fin.last (n + 1) : Fin (n + 2)).val = n := by
    simp [Fin.last]
  rw [dif_neg hlast_lt]
  rw [dif_neg hlast_ne]

/-- The determinant of `[B | u | v]`. -/
def twoColDet {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (u v : Vector R (n + 2)) : R :=
  det (twoColMatrix B u v)

/-- Deleting row `p` and the final `v` column from `[B | u | v]`
recovers the one-column augmented matrix `mMatrix B u p`. -/
theorem deleteRowCol_twoColMatrix_last_eq_mMatrix {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (u v : Vector R (n + 2)) (p : Fin (n + 2)) :
    deleteRowCol (twoColMatrix B u v) p (Fin.last (n + 1)) =
      mMatrix B u p := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin (n + 1) := ⟨i, hi⟩
  let jj : Fin (n + 1) := ⟨j, hj⟩
  change (deleteRowCol (twoColMatrix B u v) p (Fin.last (n + 1)))[ii][jj] =
    (mMatrix B u p)[ii][jj]
  rw [deleteRowCol_entry]
  have hcol :
      (skipIndex (Fin.last (n + 1)) jj).val = jj.val := by
    rw [skipIndex_last]
    simp
  by_cases hjlt : jj.val < n
  · have hskiplt : (skipIndex (Fin.last (n + 1)) jj).val < n := by
      rw [hcol]
      exact hjlt
    rw [twoColMatrix_entry_lt B u v (skipIndex p ii)
        (skipIndex (Fin.last (n + 1)) jj) hskiplt]
    rw [mMatrix_entry_lt B u p ii jj hjlt]
    have hcol_eq : (⟨(skipIndex (Fin.last (n + 1)) jj).val, hskiplt⟩ : Fin n) =
        (⟨jj.val, hjlt⟩ : Fin n) := by
      apply Fin.ext
      exact hcol
    simp only [hcol_eq]
  · have hjn : jj.val = n := by omega
    have hskip_eq :
        skipIndex (Fin.last (n + 1)) jj =
          (⟨n, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rw [hcol]
      exact hjn
    have hjj_last : jj = Fin.last n := by
      apply Fin.ext
      simp [Fin.last, hjn]
    calc
      (twoColMatrix B u v)[skipIndex p ii][skipIndex (Fin.last (n + 1)) jj] =
          (twoColMatrix B u v)[skipIndex p ii][(⟨n, by omega⟩ : Fin (n + 2))] := by
            exact congrArg (fun c => (twoColMatrix B u v)[skipIndex p ii][c]) hskip_eq
      _ = u[skipIndex p ii] := by
            exact twoColMatrix_entry_penultimate B u v (skipIndex p ii)
      _ = (mMatrix B u p)[ii][jj] := by
            calc
              u[skipIndex p ii] = (mMatrix B u p)[ii][Fin.last n] := by
                exact (mMatrix_entry_last B u p ii).symm
              _ = (mMatrix B u p)[ii][jj] := by
                exact (congrArg (fun c => (mMatrix B u p)[ii][c]) hjj_last).symm

/-- Laplace expansion of the two-column determinant along the final column,
with the remaining minor identified as `mDet B u p`. -/
theorem twoColDet_eq_sum_mDet {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (u v : Vector R (n + 2)) :
    twoColDet B u v =
      (List.finRange (n + 2)).foldl
        (fun acc p =>
          acc + v[p] * (cofactorSign (R := R) p (Fin.last (n + 1)) * mDet B u p)) 0 := by
  unfold twoColDet
  rw [det_eq_foldl_laplace_last (twoColMatrix B u v)]
  apply foldl_acc_congr
  intro acc p _hmem
  rw [twoColMatrix_entry_last]
  unfold cofactor mDet
  rw [deleteRowCol_twoColMatrix_last_eq_mMatrix B u v p]

/-- `mMatrix B v p` exposed as a `colReplace` on its last column: the
other columns come from `B` and are independent of `v`, while the last
column carries `fun i => v[skipIndex p i]`. -/
theorem mMatrix_eq_colReplace_last {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (v w : Vector R (n + 2)) (p : Fin (n + 2)) :
    mMatrix B v p =
      colReplace (mMatrix B w p) (Fin.last n)
        (fun i : Fin (n + 1) => v[skipIndex p i]) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  change (mMatrix B v p)[(⟨i, hi⟩ : Fin (n + 1))][(⟨j, hj⟩ : Fin (n + 1))] =
    (colReplace (mMatrix B w p) (Fin.last n)
        (fun i : Fin (n + 1) => v[skipIndex p i]))[(⟨i, hi⟩ : Fin (n + 1))][(⟨j, hj⟩ : Fin (n + 1))]
  rw [colReplace_get]
  by_cases hjlt : j < n
  · have hjne : (⟨j, hj⟩ : Fin (n + 1)) ≠ Fin.last n := by
      intro h
      have hval := congrArg Fin.val h
      simp [Fin.last] at hval
      omega
    rw [if_neg hjne]
    rw [mMatrix_entry_lt B v p (⟨i, hi⟩ : Fin (n + 1)) (⟨j, hj⟩ : Fin (n + 1)) hjlt]
    rw [mMatrix_entry_lt B w p (⟨i, hi⟩ : Fin (n + 1)) (⟨j, hj⟩ : Fin (n + 1)) hjlt]
  · have hjeq : j = n := by omega
    have hjlast : (⟨j, hj⟩ : Fin (n + 1)) = Fin.last n := by
      apply Fin.ext
      simp [Fin.last, hjeq]
    rw [if_pos hjlast]
    show (mMatrix B v p)[(⟨i, hi⟩ : Fin (n + 1))][(⟨j, hj⟩ : Fin (n + 1))] = v[skipIndex p (⟨i, hi⟩ : Fin (n + 1))]
    unfold mMatrix
    rw [getElem_ofFn]
    have hjnlt : ¬ (⟨j, hj⟩ : Fin (n + 1)).val < n := by
      show ¬ j < n; exact hjlt
    exact dif_neg hjnlt

/-- `mDet` is additive in the augmented vector column. -/
theorem mDet_add_v {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (v w : Vector R (n + 2)) (p : Fin (n + 2)) :
    mDet B (v + w) p = mDet B v p + mDet B w p := by
  unfold mDet
  rw [mMatrix_eq_colReplace_last B (v + w) v p]
  rw [show (fun i : Fin (n + 1) => (v + w)[skipIndex p i]) =
      fun i : Fin (n + 1) => v[skipIndex p i] + w[skipIndex p i] by
        funext i
        simp [Vector.getElem_add]]
  rw [det_colReplace_add]
  rw [← mMatrix_eq_colReplace_last B v v p]
  rw [← mMatrix_eq_colReplace_last B w v p]

/-- `mDet` is homogeneous in the augmented vector column. -/
theorem mDet_smul_v {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (c : R) (v : Vector R (n + 2)) (p : Fin (n + 2)) :
    mDet B (c • v) p = c * mDet B v p := by
  unfold mDet
  rw [mMatrix_eq_colReplace_last B (c • v) v p]
  rw [show (fun i : Fin (n + 1) => (c • v)[skipIndex p i]) =
      fun i : Fin (n + 1) => c * v[skipIndex p i] by
        funext i
        simp [Vector.getElem_smul]
        change c * v[skipIndex p i] = c * v[skipIndex p i]
        rfl]
  rw [det_colReplace_smul]
  rw [← mMatrix_eq_colReplace_last B v v p]

/-- The standard basis vector `e_q : Vector R (n + 2)` with value `1`
at position `q` and `0` elsewhere. -/
def basisVec {R : Type u} [Zero R] [One R] {n : Nat} (q : Fin (n + 2)) :
    Vector R (n + 2) :=
  Vector.ofFn fun i => if i = q then (1 : R) else (0 : R)

/-- Entry `i` of the standard basis vector `e_q` is `1` when `i = q` and `0`
otherwise. -/
@[grind =] theorem basisVec_getElem {R : Type u} [Zero R] [One R] {n : Nat}
    (q : Fin (n + 2)) (i : Fin (n + 2)) :
    (basisVec (R := R) q)[i] = if i = q then (1 : R) else (0 : R) := by
  simp [basisVec]

/-- For `p < q`, the unique row of `Fin (n + 1)` that maps to `q` under
`skipIndex p` is `⟨q.val - 1, _⟩`. -/
theorem skipIndex_at_q_minus_one_eq_q_of_lt {n : Nat}
    (p q : Fin (n + 2)) (hpq : p.val < q.val) :
    skipIndex p (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) = q := by
  apply Fin.ext
  show (skipIndex p (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1))).val = q.val
  have hnot : ¬ ((⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)).val < p.val) := by
    show ¬ q.val - 1 < p.val
    omega
  rw [skipIndex_val_of_not_lt p _ hnot]
  show q.val - 1 + 1 = q.val
  omega

/-- For `p < q`, the chained skip `skipIndex p ∘ skipIndex r_q`
(where `r_q = q.val - 1`) equals `skipIndex2 p q hpq`. This is the
row-reindexing identity used to recover the `n × n` minor of `B` from
the deleted-row-and-last-column minor of `mMatrix B (basisVec q) p`. -/
theorem skipIndex_skipIndex_eq_skipIndex2_of_lt {n : Nat}
    (p q : Fin (n + 2)) (hpq : p.val < q.val) (i : Fin n) :
    skipIndex p
        (skipIndex (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) i) =
      skipIndex2 p q hpq i := by
  apply Fin.ext
  by_cases h1 : i.val < p.val
  · have hrq : i.val < q.val - 1 := by omega
    rw [skipIndex2_val_of_lt_p p q hpq i h1]
    have hskip1 : skipIndex (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) i =
        ⟨i.val, by have := i.isLt; omega⟩ := by
      apply Fin.ext
      show (skipIndex _ i).val = i.val
      have : i.val < (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)).val := by
        show i.val < q.val - 1
        omega
      rw [skipIndex_val_of_lt _ _ this]
    rw [hskip1]
    show (skipIndex p (⟨i.val, _⟩ : Fin (n + 1))).val = i.val
    have hp : (⟨i.val, by have := i.isLt; omega⟩ : Fin (n + 1)).val < p.val := h1
    rw [skipIndex_val_of_lt p _ hp]
  · by_cases h2 : i.val + 1 < q.val
    · rw [skipIndex2_val_of_between p q hpq i h1 h2]
      have hrq_lt : i.val < q.val - 1 := by omega
      have hskip1 : skipIndex (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) i =
          ⟨i.val, by have := i.isLt; omega⟩ := by
        apply Fin.ext
        show (skipIndex _ i).val = i.val
        have : i.val < (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)).val := by
          show i.val < q.val - 1
          omega
        rw [skipIndex_val_of_lt _ _ this]
      rw [hskip1]
      show (skipIndex p (⟨i.val, _⟩ : Fin (n + 1))).val = i.val + 1
      have hp : ¬ (⟨i.val, by have := i.isLt; omega⟩ : Fin (n + 1)).val < p.val := h1
      rw [skipIndex_val_of_not_lt p _ hp]
    · rw [skipIndex2_val_of_ge_q p q hpq i h1 h2]
      have hrq_ge : ¬ i.val < q.val - 1 := by omega
      have hskip1 : skipIndex (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) i =
          ⟨i.val + 1, by have := i.isLt; omega⟩ := by
        apply Fin.ext
        show (skipIndex _ i).val = i.val + 1
        have : ¬ i.val < (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)).val := by
          show ¬ i.val < q.val - 1
          exact hrq_ge
        rw [skipIndex_val_of_not_lt _ _ this]
      rw [hskip1]
      show (skipIndex p (⟨i.val + 1, _⟩ : Fin (n + 1))).val = i.val + 2
      have hp : ¬ (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (n + 1)).val < p.val := by
        show ¬ i.val + 1 < p.val
        omega
      rw [skipIndex_val_of_not_lt p _ hp]

/-- Foldl over a list whose body is identically zero leaves the seed
unchanged. -/
private theorem foldl_add_zero_body {α : Type u} [Lean.Grind.CommRing α]
    {β : Type v} (xs : List β) (z : α) (f : β → α)
    (hall : ∀ y ∈ xs, f y = 0) :
    xs.foldl (fun acc y => acc + f y) z = z := by
  induction xs generalizing z with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.foldl_cons]
      have hy : f y = 0 := hall y List.mem_cons_self
      rw [hy]
      have hzero : z + (0 : α) = z := by grind
      rw [hzero]
      exact ih z (fun w hw => hall w (List.mem_cons_of_mem _ hw))

/-- Foldl over a `Nodup` list where the additive contribution is
nonzero at exactly one matching element. -/
private theorem foldl_add_with_unique_match {α : Type u}
    [Lean.Grind.CommRing α] {β : Type v} [DecidableEq β]
    (xs : List β) (z : α) (q : β) (f : β → α)
    (hmem : q ∈ xs) (hnodup : xs.Nodup) :
    xs.foldl (fun acc x => acc + (if x = q then f x else (0 : α))) z = z + f q := by
  induction xs generalizing z with
  | nil => simp at hmem
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hxq : x = q
      · -- x = q. By nodup, q ∉ xs, so the remaining foldl preserves z + f x.
        subst hxq
        rw [if_pos rfl]
        have hxs_nomem : x ∉ xs := (List.nodup_cons.mp hnodup).1
        apply foldl_add_zero_body xs (z + f x)
            (fun y => if y = x then f y else (0 : α))
        intro y hy
        have hyne : y ≠ x := fun heq => hxs_nomem (heq ▸ hy)
        exact if_neg hyne
      · -- x ≠ q. q still in xs; apply IH.
        rw [if_neg hxq]
        have hzero_step : z + (0 : α) = z := by grind
        rw [hzero_step]
        have hmem' : q ∈ xs := by
          cases List.mem_cons.mp hmem with
          | inl h => exact absurd h.symm hxq
          | inr h => exact h
        have hnodup' : xs.Nodup := (List.nodup_cons.mp hnodup).2
        exact ih z hmem' hnodup'

private theorem foldl_basisVec_weighted_single
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (q : Fin (n + 2)) (f : Fin (n + 2) → R) :
    (List.finRange (n + 2)).foldl
        (fun acc p => acc + (basisVec (R := R) q)[p] * f p) 0 =
      f q := by
  have hfold :=
    foldl_add_with_unique_match (α := R) (List.finRange (n + 2)) (0 : R) q
      (fun p => (basisVec (R := R) q)[p] * f p)
      (List.mem_finRange q) (List.nodup_finRange (n + 2))
  have hcongr :
      (List.finRange (n + 2)).foldl
          (fun acc p => acc + (basisVec (R := R) q)[p] * f p) 0 =
        (List.finRange (n + 2)).foldl
          (fun acc p =>
            acc + if p = q then (basisVec (R := R) q)[p] * f p else 0) 0 := by
    apply foldl_acc_congr
    intro acc p _hmem
    by_cases hp : p = q
    · rw [if_pos hp]
    · rw [if_neg hp]
      rw [basisVec_getElem]
      rw [if_neg hp]
      grind
  calc
    (List.finRange (n + 2)).foldl
        (fun acc p => acc + (basisVec (R := R) q)[p] * f p) 0 =
      (List.finRange (n + 2)).foldl
        (fun acc p =>
          acc + if p = q then (basisVec (R := R) q)[p] * f p else 0) 0 := hcongr
    _ = 0 + (basisVec (R := R) q)[q] * f q := hfold
    _ = f q := by
      rw [basisVec_getElem]
      rw [if_pos rfl]
      grind

/-- Expands the augmented vector column of `mDet` in the standard basis. -/
theorem mDet_eq_sum_basisVec
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (v : Vector R (n + 2)) (p : Fin (n + 2)) :
    mDet B v p =
      (List.finRange (n + 2)).foldl
        (fun acc q => acc + v[q] * mDet B (basisVec (R := R) q) p) 0 := by
  unfold mDet
  rw [mMatrix_eq_colReplace_last B v v p]
  have hcol :
      (fun i : Fin (n + 1) => v[skipIndex p i]) =
        fun i : Fin (n + 1) =>
          (List.finRange (n + 2)).foldl
            (fun acc q => acc + v[q] * (basisVec (R := R) q)[skipIndex p i]) 0 := by
    funext i
    have hfold :=
      foldl_add_with_unique_match (α := R) (List.finRange (n + 2)) (0 : R)
        (skipIndex p i)
        (fun q => v[q] * (basisVec (R := R) q)[skipIndex p i])
        (List.mem_finRange (skipIndex p i)) (List.nodup_finRange (n + 2))
    have hcongr :
        (List.finRange (n + 2)).foldl
            (fun acc q => acc + v[q] * (basisVec (R := R) q)[skipIndex p i]) 0 =
          (List.finRange (n + 2)).foldl
            (fun acc q =>
              acc + if q = skipIndex p i then
                v[q] * (basisVec (R := R) q)[skipIndex p i] else 0) 0 := by
      apply foldl_acc_congr
      intro acc q _hmem
      by_cases hq : q = skipIndex p i
      · rw [if_pos hq]
      · rw [if_neg hq]
        rw [basisVec_getElem]
        rw [if_neg (fun h => hq h.symm)]
        grind
    symm
    calc
      (List.finRange (n + 2)).foldl
          (fun acc q => acc + v[q] * (basisVec (R := R) q)[skipIndex p i]) 0 =
        (List.finRange (n + 2)).foldl
          (fun acc q =>
            acc + if q = skipIndex p i then
              v[q] * (basisVec (R := R) q)[skipIndex p i] else 0) 0 := hcongr
      _ = 0 + v[skipIndex p i] * (basisVec (R := R) (skipIndex p i))[skipIndex p i] := hfold
      _ = v[skipIndex p i] := by
        rw [basisVec_getElem]
        rw [if_pos rfl]
        grind
  rw [hcol]
  rw [det_colReplace_sum_finRange]
  apply foldl_acc_congr
  intro acc q _hmem
  rw [← mMatrix_eq_colReplace_last B (basisVec (R := R) q) v p]

/-- Laplace expansion specialized to a column equal to a standard basis
vector: if column `c` of `M` holds `1` at row `q` and `0` elsewhere, then
`det M` equals the signed minor `cofactorSign q c * det (deleteRowCol M q c)`. -/
theorem det_eq_signed_minor_of_col_basis
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (q c : Fin (n + 1))
    (hcol : ∀ r : Fin (n + 1), M[r][c] = if r = q then (1 : R) else (0 : R)) :
    det M = cofactorSign q c * det (deleteRowCol M q c) := by
  rw [det_eq_foldl_laplace_col M c]
  -- Rewrite the body using hcol; only the q-th term survives.
  have hbody : ∀ acc row,
      acc + M[row][c] * cofactor M row c =
        acc + (if row = q then cofactor M q c else (0 : R)) := by
    intro acc row
    rw [hcol row]
    by_cases h : row = q
    · subst h
      rw [if_pos rfl, if_pos rfl]
      grind
    · rw [if_neg h, if_neg h]
      grind
  have hfold :
      (List.finRange (n + 1)).foldl
          (fun acc row => acc + M[row][c] * cofactor M row c) 0 =
        (List.finRange (n + 1)).foldl
          (fun acc row =>
            acc + (if row = q then cofactor M q c else (0 : R))) 0 := by
    apply foldl_acc_congr
    intro acc row _hmem
    exact hbody acc row
  rw [hfold]
  have hmem : q ∈ List.finRange (n + 1) := List.mem_finRange q
  have hnodup : (List.finRange (n + 1)).Nodup := List.nodup_finRange (n + 1)
  rw [foldl_add_with_unique_match (List.finRange (n + 1)) (0 : R) q
        (fun _ => cofactor M q c) hmem hnodup]
  -- Now goal: 0 + cofactor M q c = cofactorSign q c * det (deleteRowCol M q c).
  rw [show (0 : R) + cofactor M q c = cofactor M q c by grind]
  rfl

/-- For `p < q`, deleting row `r_q = q.val - 1` and the last column of
`mMatrix B v p` recovers `nMatrix B p q hpq`, independent of `v`. -/
theorem deleteRowCol_mMatrix_at_q_minus_one_eq_nMatrix_of_lt
    {R : Type u} {n : Nat} (B : Matrix R (n + 2) n) (v : Vector R (n + 2))
    (p q : Fin (n + 2)) (hpq : p.val < q.val) :
    deleteRowCol (mMatrix B v p)
        (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) (Fin.last n) =
      nMatrix B p q hpq := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin n := ⟨j, hj⟩
  change (deleteRowCol (mMatrix B v p)
        (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) (Fin.last n))[ii][jj] =
    (nMatrix B p q hpq)[ii][jj]
  rw [deleteRowCol_entry]
  rw [nMatrix_entry]
  -- The column index: skipIndex (Fin.last n) jj = jj.castSucc; its val = jj.val < n.
  have hjj_castSucc : (skipIndex (Fin.last n) jj).val = jj.val := by
    show (skipIndex (Fin.last n) jj).val = jj.val
    rw [skipIndex_last]
    simp
  have hjjlt : (skipIndex (Fin.last n) jj).val < n := by
    rw [hjj_castSucc]; exact jj.isLt
  rw [mMatrix_entry_lt B v p (skipIndex (⟨q.val - 1, _⟩ : Fin (n + 1)) ii)
        (skipIndex (Fin.last n) jj) hjjlt]
  -- Both row and column indices match the nMatrix indexing.
  have hrow : skipIndex p
        (skipIndex (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) ii) =
      skipIndex2 p q hpq ii :=
    skipIndex_skipIndex_eq_skipIndex2_of_lt p q hpq ii
  have hcol : (⟨(skipIndex (Fin.last n) jj).val, hjjlt⟩ : Fin n) = jj := by
    apply Fin.ext
    show (skipIndex (Fin.last n) jj).val = jj.val
    exact hjj_castSucc
  -- Use simp to handle index-rewriting with proof-irrelevance.
  simp only [hrow, hcol]

/-- For `q < p`, the unique row of `Fin (n + 1)` that maps to `q` under
`skipIndex p` is `⟨q.val, _⟩`. -/
theorem skipIndex_at_q_eq_q_of_gt {n : Nat}
    (p q : Fin (n + 2)) (hqp : q.val < p.val) :
    skipIndex p (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) = q := by
  apply Fin.ext
  show (skipIndex p (⟨q.val, _⟩ : Fin (n + 1))).val = q.val
  have h : (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)).val < p.val := hqp
  rw [skipIndex_val_of_lt p _ h]

/-- For `q < p`, the chained skip `skipIndex p ∘ skipIndex r_q`
(where `r_q = ⟨q.val, _⟩`) equals `skipIndex2 q p hqp`. -/
theorem skipIndex_skipIndex_eq_skipIndex2_of_gt {n : Nat}
    (p q : Fin (n + 2)) (hqp : q.val < p.val) (i : Fin n) :
    skipIndex p
        (skipIndex (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) i) =
      skipIndex2 q p hqp i := by
  apply Fin.ext
  by_cases h1 : i.val < q.val
  · rw [skipIndex2_val_of_lt_p q p hqp i h1]
    have hskip1 : skipIndex (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) i =
        ⟨i.val, by have := i.isLt; omega⟩ := by
      apply Fin.ext
      show (skipIndex _ i).val = i.val
      have : i.val < (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)).val := h1
      rw [skipIndex_val_of_lt _ _ this]
    rw [hskip1]
    show (skipIndex p (⟨i.val, _⟩ : Fin (n + 1))).val = i.val
    have hp : (⟨i.val, by have := i.isLt; omega⟩ : Fin (n + 1)).val < p.val := by
      show i.val < p.val
      omega
    rw [skipIndex_val_of_lt p _ hp]
  · by_cases h2 : i.val + 1 < p.val
    · rw [skipIndex2_val_of_between q p hqp i h1 h2]
      have hskip1 : skipIndex (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) i =
          ⟨i.val + 1, by have := i.isLt; omega⟩ := by
        apply Fin.ext
        show (skipIndex _ i).val = i.val + 1
        have hne : ¬ i.val < (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)).val := h1
        rw [skipIndex_val_of_not_lt _ _ hne]
      rw [hskip1]
      show (skipIndex p (⟨i.val + 1, _⟩ : Fin (n + 1))).val = i.val + 1
      have hp : (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (n + 1)).val < p.val := h2
      rw [skipIndex_val_of_lt p _ hp]
    · rw [skipIndex2_val_of_ge_q q p hqp i h1 h2]
      have hskip1 : skipIndex (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) i =
          ⟨i.val + 1, by have := i.isLt; omega⟩ := by
        apply Fin.ext
        show (skipIndex _ i).val = i.val + 1
        have hne : ¬ i.val < (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)).val := h1
        rw [skipIndex_val_of_not_lt _ _ hne]
      rw [hskip1]
      show (skipIndex p (⟨i.val + 1, _⟩ : Fin (n + 1))).val = i.val + 2
      have hp : ¬ (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (n + 1)).val < p.val := h2
      rw [skipIndex_val_of_not_lt p _ hp]

/-- For `q < p`, deleting row `r_q = q.val` and the last column of
`mMatrix B v p` recovers `nMatrix B q p hqp`, independent of `v`. -/
theorem deleteRowCol_mMatrix_at_q_eq_nMatrix_of_gt
    {R : Type u} {n : Nat} (B : Matrix R (n + 2) n) (v : Vector R (n + 2))
    (p q : Fin (n + 2)) (hqp : q.val < p.val) :
    deleteRowCol (mMatrix B v p)
        (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) (Fin.last n) =
      nMatrix B q p hqp := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin n := ⟨j, hj⟩
  change (deleteRowCol (mMatrix B v p)
        (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) (Fin.last n))[ii][jj] =
    (nMatrix B q p hqp)[ii][jj]
  rw [deleteRowCol_entry]
  rw [nMatrix_entry]
  have hjj_castSucc : (skipIndex (Fin.last n) jj).val = jj.val := by
    show (skipIndex (Fin.last n) jj).val = jj.val
    rw [skipIndex_last]
    simp
  have hjjlt : (skipIndex (Fin.last n) jj).val < n := by
    rw [hjj_castSucc]; exact jj.isLt
  rw [mMatrix_entry_lt B v p (skipIndex (⟨q.val, _⟩ : Fin (n + 1)) ii)
        (skipIndex (Fin.last n) jj) hjjlt]
  have hrow : skipIndex p
        (skipIndex (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) ii) =
      skipIndex2 q p hqp ii :=
    skipIndex_skipIndex_eq_skipIndex2_of_gt p q hqp ii
  have hcol : (⟨(skipIndex (Fin.last n) jj).val, hjjlt⟩ : Fin n) = jj := by
    apply Fin.ext
    show (skipIndex (Fin.last n) jj).val = jj.val
    exact hjj_castSucc
  simp only [hrow, hcol]

/-- Basis-vector evaluation of `mDet` when `q < p`: the basis vector
`e_q` becomes the standard basis vector `e_{q.val}` in the last
column of `mMatrix B (basisVec q) p`, so Laplace along that column
recovers a signed `n × n` minor of `B`. -/
theorem mDet_basisVec_eq_signed_nDet_of_gt
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (p q : Fin (n + 2)) (hqp : q.val < p.val) :
    mDet B (basisVec (R := R) q) p =
      cofactorSign (R := R)
        (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) (Fin.last n) *
      nDet B q p hqp := by
  unfold mDet
  let r_q : Fin (n + 1) := ⟨q.val, by have := p.isLt; omega⟩
  show (mMatrix B (basisVec (R := R) q) p).det =
      cofactorSign (R := R) r_q (Fin.last n) * nDet B q p hqp
  have hcol : ∀ r : Fin (n + 1),
      (mMatrix B (basisVec (R := R) q) p)[r][Fin.last n] =
        if r = r_q then (1 : R) else (0 : R) := by
    intro r
    rw [mMatrix_entry_last]
    rw [basisVec_getElem]
    by_cases hreq : r = r_q
    · subst hreq
      rw [if_pos rfl]
      have : skipIndex p r_q = q :=
        skipIndex_at_q_eq_q_of_gt p q hqp
      rw [this]
      exact if_pos rfl
    · rw [if_neg hreq]
      have hne : skipIndex p r ≠ q := by
        intro heq
        have hq_eq : skipIndex p r_q = q :=
          skipIndex_at_q_eq_q_of_gt p q hqp
        have : skipIndex p r = skipIndex p r_q := heq.trans hq_eq.symm
        exact hreq (skipIndex_injective p this)
      exact if_neg hne
  rw [det_eq_signed_minor_of_col_basis (mMatrix B (basisVec (R := R) q) p) r_q
        (Fin.last n) hcol]
  congr 1
  unfold nDet
  exact congrArg det
    (deleteRowCol_mMatrix_at_q_eq_nMatrix_of_gt B
      (basisVec (R := R) q) p q hqp)

/-- Basis-vector evaluation of `mDet` when `q > p`: the basis vector
`e_q` becomes the standard basis vector `e_{q.val - 1}` in the last
column of `mMatrix B (basisVec q) p`, so Laplace along that column
recovers a signed `n × n` minor of `B`. -/
theorem mDet_basisVec_eq_signed_nDet_of_lt
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (p q : Fin (n + 2)) (hpq : p.val < q.val) :
    mDet B (basisVec (R := R) q) p =
      cofactorSign (R := R)
        (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) (Fin.last n) *
      nDet B p q hpq := by
  unfold mDet
  -- Last column of `mMatrix B (basisVec q) p` is e_{r_q} where r_q = q.val - 1.
  let r_q : Fin (n + 1) := ⟨q.val - 1, by have := q.isLt; omega⟩
  show (mMatrix B (basisVec (R := R) q) p).det =
      cofactorSign (R := R) r_q (Fin.last n) * nDet B p q hpq
  have hcol : ∀ r : Fin (n + 1),
      (mMatrix B (basisVec (R := R) q) p)[r][Fin.last n] =
        if r = r_q then (1 : R) else (0 : R) := by
    intro r
    rw [mMatrix_entry_last]
    rw [basisVec_getElem]
    by_cases hreq : r = r_q
    · subst hreq
      rw [if_pos rfl]
      have : skipIndex p r_q = q :=
        skipIndex_at_q_minus_one_eq_q_of_lt p q hpq
      rw [this]
      exact if_pos rfl
    · rw [if_neg hreq]
      -- Need: (if skipIndex p r = q then 1 else 0) = 0, i.e., skipIndex p r ≠ q.
      have hne : skipIndex p r ≠ q := by
        intro heq
        -- skipIndex p is injective, and skipIndex p r_q = q.
        have hq_eq : skipIndex p r_q = q :=
          skipIndex_at_q_minus_one_eq_q_of_lt p q hpq
        have : skipIndex p r = skipIndex p r_q := heq.trans hq_eq.symm
        exact hreq (skipIndex_injective p this)
      exact if_neg hne
  rw [det_eq_signed_minor_of_col_basis (mMatrix B (basisVec (R := R) q) p) r_q
        (Fin.last n) hcol]
  congr 1
  unfold nDet
  exact congrArg det
    (deleteRowCol_mMatrix_at_q_minus_one_eq_nMatrix_of_lt B
      (basisVec (R := R) q) p q hpq)

/-- `mDet B (basisVec p) p = 0`: the basis vector `e_p` becomes the zero
column inside `mMatrix B (basisVec p) p` after row `p` is deleted, so
the determinant vanishes. -/
theorem mDet_basisVec_eq_zero_of_eq {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (B : Matrix R (n + 2) n) (p : Fin (n + 2)) :
    mDet B (basisVec (R := R) p) p = 0 := by
  unfold mDet
  -- The last column of `mMatrix B (basisVec p) p` is identically zero.
  have hcol : (fun r : Fin (n + 1) =>
      (basisVec (R := R) p)[skipIndex p r]) = (fun _ => (0 : R)) := by
    funext r
    rw [basisVec_getElem]
    exact if_neg (skipIndex_ne p r)
  -- Express mMatrix as colReplace with that zero function on the last column.
  rw [mMatrix_eq_colReplace_last B (basisVec (R := R) p)
        (basisVec (R := R) p) p]
  rw [hcol]
  exact det_colReplace_zero _ _

/-- Ordered basis-pair evaluation for `twoColDet`: if `a < b`, the only
surviving ordered pair is the deleted-row pair `(a, b)`. -/
theorem twoColDet_basisVec_basisVec_of_lt
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (a b : Fin (n + 2)) (hab : a.val < b.val) :
    twoColDet B (basisVec (R := R) a) (basisVec (R := R) b) =
      cofactorSign (R := R) b (Fin.last (n + 1)) *
        (cofactorSign (R := R)
          (⟨a.val, by have := b.isLt; omega⟩ : Fin (n + 1)) (Fin.last n) *
          nDet B a b hab) := by
  rw [twoColDet_eq_sum_mDet]
  rw [foldl_basisVec_weighted_single (R := R) b
      (fun p => cofactorSign (R := R) p (Fin.last (n + 1)) *
        mDet B (basisVec (R := R) a) p)]
  rw [mDet_basisVec_eq_signed_nDet_of_gt B b a hab]

/-- Reverse ordered basis-pair evaluation for `twoColDet`: if `b < a`,
the determinant recovers the same deleted-row pair with the reversed
coefficient order. -/
theorem twoColDet_basisVec_basisVec_of_gt
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (a b : Fin (n + 2)) (hba : b.val < a.val) :
    twoColDet B (basisVec (R := R) a) (basisVec (R := R) b) =
      cofactorSign (R := R) b (Fin.last (n + 1)) *
        (cofactorSign (R := R)
          (⟨a.val - 1, by have := a.isLt; omega⟩ : Fin (n + 1)) (Fin.last n) *
          nDet B b a hba) := by
  rw [twoColDet_eq_sum_mDet]
  rw [foldl_basisVec_weighted_single (R := R) b
      (fun p => cofactorSign (R := R) p (Fin.last (n + 1)) *
        mDet B (basisVec (R := R) a) p)]
  rw [mDet_basisVec_eq_signed_nDet_of_lt B b a hba]

/-- A repeated basis vector in the two appended columns makes
`twoColDet` vanish. -/
theorem twoColDet_basisVec_basisVec_of_eq
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (a : Fin (n + 2)) :
    twoColDet B (basisVec (R := R) a) (basisVec (R := R) a) = 0 := by
  rw [twoColDet_eq_sum_mDet]
  rw [foldl_basisVec_weighted_single (R := R) a
      (fun p => cofactorSign (R := R) p (Fin.last (n + 1)) *
        mDet B (basisVec (R := R) a) p)]
  rw [mDet_basisVec_eq_zero_of_eq B a]
  grind

/-- Evaluation of `twoColDet` when the final appended column is a basis
vector. This is the one-column Laplace expansion with the remaining
`mDet` minor exposed directly. -/
theorem twoColDet_basisVec_right
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (u : Vector R (n + 2)) (b : Fin (n + 2)) :
    twoColDet B u (basisVec (R := R) b) =
      cofactorSign (R := R) b (Fin.last (n + 1)) * mDet B u b := by
  rw [twoColDet_eq_sum_mDet]
  rw [foldl_basisVec_weighted_single (R := R) b
      (fun p => cofactorSign (R := R) p (Fin.last (n + 1)) * mDet B u p)]

/-- Bilinear basis expansion of `twoColDet` over the two appended columns.
The basis-pair terms are reduced by
`twoColDet_basisVec_basisVec_of_lt`,
`twoColDet_basisVec_basisVec_of_gt`, and
`twoColDet_basisVec_basisVec_of_eq`. -/
theorem twoColDet_eq_sum_basisVec_pairs
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (u v : Vector R (n + 2)) :
    twoColDet B u v =
      (List.finRange (n + 2)).foldl
        (fun acc b =>
          acc + v[b] *
            (List.finRange (n + 2)).foldl
              (fun acc a =>
                acc + u[a] * twoColDet B (basisVec (R := R) a)
                  (basisVec (R := R) b)) 0) 0 := by
  rw [twoColDet_eq_sum_mDet]
  apply foldl_acc_congr
  intro acc b _hmem
  rw [mDet_eq_sum_basisVec B u b]
  congr 2
  calc
    cofactorSign (R := R) b (Fin.last (n + 1)) *
        (List.finRange (n + 2)).foldl
          (fun acc a => acc + u[a] * mDet B (basisVec (R := R) a) b) 0 =
      (List.finRange (n + 2)).foldl
        (fun acc a =>
          acc + cofactorSign (R := R) b (Fin.last (n + 1)) *
            (u[a] * mDet B (basisVec (R := R) a) b)) 0 := by
        rw [foldl_det_sum_mul_left_zero]
    _ =
      (List.finRange (n + 2)).foldl
        (fun acc a =>
          acc + u[a] * twoColDet B (basisVec (R := R) a)
            (basisVec (R := R) b)) 0 := by
        apply foldl_det_sum_congr
        intro a _ha
        rw [twoColDet_basisVec_right B (basisVec (R := R) a) b]
        grind

private theorem cofactorSign_consecutive_last_neg
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (a : Nat) (ha : a + 1 < n + 1) :
    cofactorSign (R := R) (⟨a + 1, ha⟩ : Fin (n + 1)) (Fin.last n) =
      -cofactorSign (R := R) (⟨a, by omega⟩ : Fin (n + 1)) (Fin.last n) := by
  unfold cofactorSign
  simp only [Fin.val_mk, Fin.last]
  by_cases h : (a + n) % 2 = 0
  · have hnext : (a + 1 + n) % 2 ≠ 0 := by omega
    rw [if_pos h, if_neg hnext]
  · have hnext : (a + 1 + n) % 2 = 0 := by omega
    rw [if_neg h, if_pos hnext]
    grind

private theorem det_plucker_three_term_basisVec_of_eq_p1
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (p1 p2 p3 : Fin (n + 2))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) :
    mDet B (basisVec (R := R) p1) p1 * nDet B p2 p3 h23 -
      mDet B (basisVec (R := R) p1) p2 *
        nDet B p1 p3 (Nat.lt_trans h12 h23) +
      mDet B (basisVec (R := R) p1) p3 * nDet B p1 p2 h12 = 0 := by
  rw [mDet_basisVec_eq_zero_of_eq B p1]
  rw [mDet_basisVec_eq_signed_nDet_of_gt B p2 p1 h12]
  rw [mDet_basisVec_eq_signed_nDet_of_gt B p3 p1 (Nat.lt_trans h12 h23)]
  grind

private theorem det_plucker_three_term_basisVec_of_eq_p2
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (p1 p2 p3 : Fin (n + 2))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) :
    mDet B (basisVec (R := R) p2) p1 * nDet B p2 p3 h23 -
      mDet B (basisVec (R := R) p2) p2 *
        nDet B p1 p3 (Nat.lt_trans h12 h23) +
      mDet B (basisVec (R := R) p2) p3 * nDet B p1 p2 h12 = 0 := by
  rw [mDet_basisVec_eq_signed_nDet_of_lt B p1 p2 h12]
  rw [mDet_basisVec_eq_zero_of_eq B p2]
  rw [mDet_basisVec_eq_signed_nDet_of_gt B p3 p2 h23]
  have hp2pos : 0 < p2.val := by omega
  have hrow :
      (⟨p2.val, by have := p3.isLt; omega⟩ : Fin (n + 1)) =
        (⟨p2.val - 1 + 1, by have := p3.isLt; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp
    omega
  rw [hrow]
  rw [cofactorSign_consecutive_last_neg (R := R) (p2.val - 1)
      (by have := p3.isLt; omega)]
  grind

private theorem det_plucker_three_term_basisVec_of_eq_p3
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (p1 p2 p3 : Fin (n + 2))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) :
    mDet B (basisVec (R := R) p3) p1 * nDet B p2 p3 h23 -
      mDet B (basisVec (R := R) p3) p2 *
        nDet B p1 p3 (Nat.lt_trans h12 h23) +
      mDet B (basisVec (R := R) p3) p3 * nDet B p1 p2 h12 = 0 := by
  rw [mDet_basisVec_eq_signed_nDet_of_lt B p1 p3 (Nat.lt_trans h12 h23)]
  rw [mDet_basisVec_eq_signed_nDet_of_lt B p2 p3 h23]
  rw [mDet_basisVec_eq_zero_of_eq B p3]
  grind

private theorem det_plucker_three_term_of_basisVec
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (v : Vector R (n + 2))
    (p1 p2 p3 : Fin (n + 2))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (hbasis : ∀ q : Fin (n + 2),
      mDet B (basisVec (R := R) q) p1 * nDet B p2 p3 h23 -
        mDet B (basisVec (R := R) q) p2 *
          nDet B p1 p3 (Nat.lt_trans h12 h23) +
        mDet B (basisVec (R := R) q) p3 * nDet B p1 p2 h12 = 0) :
    mDet B v p1 * nDet B p2 p3 h23 -
      mDet B v p2 * nDet B p1 p3 (Nat.lt_trans h12 h23) +
      mDet B v p3 * nDet B p1 p2 h12 = 0 := by
  rw [mDet_eq_sum_basisVec B v p1]
  rw [mDet_eq_sum_basisVec B v p2]
  rw [mDet_eq_sum_basisVec B v p3]
  rw [← foldl_det_sum_mul_right_zero (List.finRange (n + 2))
      (fun q => v[q] * mDet B (basisVec (R := R) q) p1)
      (nDet B p2 p3 h23)]
  rw [← foldl_det_sum_mul_right_zero (List.finRange (n + 2))
      (fun q => v[q] * mDet B (basisVec (R := R) q) p2)
      (nDet B p1 p3 (Nat.lt_trans h12 h23))]
  rw [← foldl_det_sum_mul_right_zero (List.finRange (n + 2))
      (fun q => v[q] * mDet B (basisVec (R := R) q) p3)
      (nDet B p1 p2 h12)]
  apply foldl_det_sum_sub_add_zero_of_body_zero
      (List.finRange (n + 2))
      (fun q => v[q] * mDet B (basisVec (R := R) q) p1 *
        nDet B p2 p3 h23)
      (fun q => v[q] * mDet B (basisVec (R := R) q) p2 *
        nDet B p1 p3 (Nat.lt_trans h12 h23))
      (fun q => v[q] * mDet B (basisVec (R := R) q) p3 *
        nDet B p1 p2 h12)
  · grind
  · intro q _hq
    have hq := hbasis q
    grind

/-! ### Two-row replacement determinant Plucker kernel

The square-matrix two-row determinant Plucker identity: replacing distinct
rows `a` and `b` of an `(n+1) × (n+1)` matrix `M` by vectors `u` and `v` is
controlled by the cofactor-row pairings of `u` and `v` against the original
cofactors of rows `a` and `b`. The proof routes through the single-column
adjugate identity, computed by expanding the `(c, s)` entry of
`adjugate (setRow M r u) * (setRow M r u * adjugate M)` in two ways. -/

/-- Entry formula for matrix multiplication: the `(i, j)` entry of `A * B`
is the `foldl`-sum of `A[i][l] * B[l][j]` over `l`. -/
private theorem mul_apply_foldl
    {R : Type u} [Lean.Grind.CommRing R] {n m k : Nat}
    (A : Matrix R n m) (B : Matrix R m k) (i : Fin n) (j : Fin k) :
    (A * B)[i][j] =
      (List.finRange m).foldl
        (fun acc l => acc + A[i][l] * B[l][j]) 0 := by
  change (Matrix.mul A B)[i][j] = _
  unfold Matrix.mul
  rw [getElem_ofFn]
  unfold Matrix.dot Hex.Vector.dotProduct
  apply foldl_acc_congr
  intro acc l _hmem
  rw [row_getElem, col_getElem]

/-- Row decomposition of `setRow M r u * adjugate M`: the `(i, s)` entry is
the `cofactor-row pairing` of `M`'s row `s` against the (possibly replaced)
row of `setRow M r u` at position `i`. -/
private theorem setRow_mul_adjugate_apply_row
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (r : Fin (n + 1)) (u : Vector R (n + 1))
    (i s : Fin (n + 1)) :
    (setRow M r u * adjugate M)[i][s] =
      cofactorRowPairing M s ((setRow M r u)[i]) := by
  rw [mul_apply_foldl]
  unfold cofactorRowPairing
  apply foldl_acc_congr
  intro acc l _hmem
  rw [adjugate_get]

/-- The replaced row contributes the cofactor-row pairing of `u` against the
`s`-row cofactors of the original matrix. -/
private theorem setRow_mul_adjugate_apply_self
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (r : Fin (n + 1)) (u : Vector R (n + 1))
    (s : Fin (n + 1)) :
    (setRow M r u * adjugate M)[r][s] = cofactorRowPairing M s u := by
  rw [setRow_mul_adjugate_apply_row, setRow_get_self]

/-- Non-replaced rows of `setRow M r u * adjugate M` reproduce the
`M * adjugate M` structure: `det M` on the diagonal, zero off-diagonal. -/
private theorem setRow_mul_adjugate_apply_ne
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (r : Fin (n + 1)) (u : Vector R (n + 1))
    (i s : Fin (n + 1)) (hir : i ≠ r) :
    (setRow M r u * adjugate M)[i][s] = if i = s then det M else 0 := by
  rw [setRow_mul_adjugate_apply_row, setRow_row_ne M r i u hir]
  by_cases his : i = s
  · subst his
    rw [if_pos rfl]
    exact cofactorRowPairing_self M i
  · rw [if_neg his]
    exact cofactorRowPairing_alien_eq_zero M i s his

/-- Lift a bilinear "`det · f = a · g - b · h`" pointwise identity over a
`foldl`-pairing against an arbitrary row weighting. This is the generic
column-summation lemma used to assemble the two-row Plucker identity from
the single-column adjugate identity. -/
private theorem foldl_pairing_mul_sub
    {R : Type u} [Lean.Grind.CommRing R] {β : Type v} (xs : List β)
    (det a b accF accG accH : R) (row f g h : β → R)
    (hacc : det * accF = a * accG - b * accH)
    (hpoint : ∀ x, det * f x = a * g x - b * h x) :
    det * xs.foldl (fun acc x => acc + row x * f x) accF =
      a * xs.foldl (fun acc x => acc + row x * g x) accG -
        b * xs.foldl (fun acc x => acc + row x * h x) accH := by
  induction xs generalizing accF accG accH with
  | nil => simpa using hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      have hx := hpoint x
      calc
        det * (accF + row x * f x) =
            det * accF + row x * (det * f x) := by grind
        _ = a * (accG + row x * g x) - b * (accH + row x * h x) := by
            rw [hacc, hx]; grind

/-- Single-column adjugate identity for a one-row replacement.

For matrix `M`, distinct rows `r` and `s`, replacement row `u`, and column
`c`, the determinant of `M` paired with the row-replaced cofactor at `(s, c)`
decomposes as a bilinear difference of cofactor-row pairings against the
original cofactors at rows `s` and `r`.

The proof computes the `(c, s)` entry of
`adjugate (setRow M r u) * (setRow M r u * adjugate M)` two ways: directly,
by isolating the `i = r` and `i = s` terms, and via `mul_assoc` plus
`adjugate_mul_apply`. -/
private theorem det_mul_cofactor_setRow_eq_cofactorRowPairing_mul_sub
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1))
    (r s c : Fin (n + 1)) (u : Vector R (n + 1)) (hrs : s ≠ r) :
    det M * cofactor (setRow M r u) s c =
      cofactorRowPairing M r u * cofactor M s c -
        cofactorRowPairing M s u * cofactor M r c := by
  -- Way 1: by `mul_assoc`, the `(c, s)` entry of
  -- `adjugate (setRow M r u) * (setRow M r u * adjugate M)` equals the entry of
  -- `(adjugate (setRow M r u) * setRow M r u) * adjugate M`. Then
  -- `adjugate_mul_apply` reduces the inner factor to `if c = l then det
  -- (setRow M r u) else 0`, and the remaining `foldl` extracts the `l = c` term.
  have hway1 :
      (adjugate (setRow M r u) * (setRow M r u * adjugate M))[c][s] =
        det (setRow M r u) * cofactor M s c := by
    rw [show adjugate (setRow M r u) * (setRow M r u * adjugate M) =
            (adjugate (setRow M r u) * setRow M r u) * adjugate M
            from (Hex.Matrix.mul_assoc (adjugate (setRow M r u)) (setRow M r u)
              (adjugate M)).symm]
    rw [mul_apply_foldl (adjugate (setRow M r u) * setRow M r u) (adjugate M) c s]
    have hcongr :
        (List.finRange (n + 1)).foldl
            (fun acc l =>
              acc + (adjugate (setRow M r u) * setRow M r u)[c][l] *
                (adjugate M)[l][s]) 0 =
          (List.finRange (n + 1)).foldl
            (fun acc l =>
              acc + if l = c then
                det (setRow M r u) * cofactor M s l else 0) 0 := by
      apply foldl_acc_congr
      intro acc l _hmem
      congr 1
      rw [adjugate_mul_apply, adjugate_get]
      by_cases hcl : c = l
      · subst hcl
        rw [if_pos rfl, if_pos rfl]
      · have hlc : l ≠ c := fun h => hcl h.symm
        rw [if_neg hcl, if_neg hlc]
        grind
    rw [hcongr]
    have hmatch :=
      foldl_add_with_unique_match (α := R) (List.finRange (n + 1)) (0 : R) c
        (fun l => det (setRow M r u) * cofactor M s l)
        (List.mem_finRange c) (List.nodup_finRange (n + 1))
    rw [hmatch]
    grind
  -- Way 2: compute the same entry by unfolding the matrix product into a sum
  -- over `i`. Decompose the body via `setRow_mul_adjugate_apply_self` / `_ne`
  -- into two single-extract terms.
  have hway2 :
      (adjugate (setRow M r u) * (setRow M r u * adjugate M))[c][s] =
        cofactor M r c * cofactorRowPairing M s u +
          det M * cofactor (setRow M r u) s c := by
    rw [mul_apply_foldl (adjugate (setRow M r u)) (setRow M r u * adjugate M) c s]
    have hbody :
        (List.finRange (n + 1)).foldl
            (fun acc i =>
              acc + (adjugate (setRow M r u))[c][i] *
                (setRow M r u * adjugate M)[i][s]) 0 =
          (List.finRange (n + 1)).foldl
            (fun acc i =>
              acc +
                ((if i = r then
                    (adjugate (setRow M r u))[c][i] *
                      cofactorRowPairing M s u
                  else 0) +
                 (if i = s then
                    (adjugate (setRow M r u))[c][i] * det M
                  else 0))) 0 := by
      apply foldl_acc_congr
      intro acc i _hmem
      congr 1
      by_cases hir : i = r
      · subst hir
        have his_ne : i ≠ s := fun h => hrs h.symm
        rw [setRow_mul_adjugate_apply_self M i u s, if_pos rfl, if_neg his_ne,
          Lean.Grind.AddCommMonoid.add_zero]
      · rw [setRow_mul_adjugate_apply_ne M r u i s hir, if_neg hir]
        by_cases his : i = s
        · subst his
          rw [if_pos rfl, if_pos rfl, Lean.Grind.AddCommMonoid.zero_add]
        · rw [if_neg his, if_neg his, Lean.Grind.Semiring.mul_zero,
            Lean.Grind.AddCommMonoid.add_zero]
    rw [hbody]
    rw [foldl_det_sum_add_zero]
    have hr_extract :=
      foldl_add_with_unique_match (α := R) (List.finRange (n + 1)) (0 : R) r
        (fun i => (adjugate (setRow M r u))[c][i] * cofactorRowPairing M s u)
        (List.mem_finRange r) (List.nodup_finRange (n + 1))
    have hs_extract :=
      foldl_add_with_unique_match (α := R) (List.finRange (n + 1)) (0 : R) s
        (fun i => (adjugate (setRow M r u))[c][i] * det M)
        (List.mem_finRange s) (List.nodup_finRange (n + 1))
    rw [hr_extract, hs_extract]
    -- Beta-reduce the extracted lambdas.
    show (0 : R) +
        (adjugate (setRow M r u))[c][r] * cofactorRowPairing M s u +
        ((0 : R) + (adjugate (setRow M r u))[c][s] * det M) =
        cofactor M r c * cofactorRowPairing M s u +
          det M * cofactor (setRow M r u) s c
    rw [adjugate_get (setRow M r u) c r, adjugate_get (setRow M r u) c s]
    have hcof_r : cofactor (setRow M r u) r c = cofactor M r c := by
      unfold cofactor
      rw [deleteRowCol_setRow_self M r c u]
    rw [hcof_r]
    rw [Lean.Grind.AddCommMonoid.zero_add, Lean.Grind.AddCommMonoid.zero_add,
        Lean.Grind.CommSemiring.mul_comm (cofactor (setRow M r u) s c) (det M)]
  -- Combine: hway1 = hway2 gives the desired identity after rearranging.
  have hcombined :
      det (setRow M r u) * cofactor M s c =
        cofactor M r c * cofactorRowPairing M s u +
          det M * cofactor (setRow M r u) s c :=
    hway1.symm.trans hway2
  rw [det_setRow_eq_cofactorRowPairing M r u] at hcombined
  -- Rearrange `hcombined` to extract `det M * cofactor (setRow M r u) s c`.
  -- From `Y = Z + X` derive `X = Y - Z`, where the subtracted term carries the
  -- expected `cofactorRowPairing M s u * cofactor M r c` ordering via mul_comm.
  rw [Lean.Grind.CommSemiring.mul_comm (cofactor M r c)
        (cofactorRowPairing M s u)] at hcombined
  -- hcombined: cofactorRowPairing M r u * cofactor M s c =
  --   cofactorRowPairing M s u * cofactor M r c + det M * cofactor (setRow M r u) s c
  rw [show
      cofactorRowPairing M r u * cofactor M s c -
        cofactorRowPairing M s u * cofactor M r c =
      det M * cofactor (setRow M r u) s c from ?_]
  rw [hcombined]
  rw [Lean.Grind.AddCommMonoid.add_comm (cofactorRowPairing M s u * cofactor M r c)
        (det M * cofactor (setRow M r u) s c)]
  exact Lean.Grind.AddCommGroup.add_sub_cancel

/-- Two-row replacement determinant Plucker kernel.

For matrix `M : Matrix R (n+1) (n+1)`, distinct rows `a` and `b`, and
replacement vectors `u`, `v`, the determinant of `M` paired with the
two-row-replaced cofactor-row pairing satisfies the quadratic Sylvester
relation against the four one-row cofactor-row pairings of `u` and `v`. -/
theorem cofactorRowPairing_setRow_plucker
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (a b : Fin (n + 1)) (hab : a ≠ b)
    (u v : Vector R (n + 1)) :
    det M * cofactorRowPairing (setRow M a u) b v =
      cofactorRowPairing M a u * cofactorRowPairing M b v -
        cofactorRowPairing M a v * cofactorRowPairing M b u := by
  -- The natural shape from `foldl_pairing_mul_sub` has `cofactorRowPairing M
  -- b u * cofactorRowPairing M a v` for the subtracted product; commute to the
  -- issue's stated form via `mul_comm` afterwards.
  have hpre :
      det M * cofactorRowPairing (setRow M a u) b v =
        cofactorRowPairing M a u * cofactorRowPairing M b v -
          cofactorRowPairing M b u * cofactorRowPairing M a v := by
    unfold cofactorRowPairing
    apply foldl_pairing_mul_sub
    · grind
    · intro c
      exact det_mul_cofactor_setRow_eq_cofactorRowPairing_mul_sub M a b c u
        (fun h => hab h.symm)
  rw [hpre]
  grind

/-- Two-row replacement determinant Plucker identity. -/
theorem det_setRow_setRow_mul_det
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (a b : Fin (n + 1)) (hab : a ≠ b)
    (u v : Vector R (n + 1)) :
    det M * det (setRow (setRow M a u) b v) =
      det (setRow M a u) * det (setRow M b v) -
        det (setRow M a v) * det (setRow M b u) := by
  rw [det_setRow_eq_cofactorRowPairing (setRow M a u) b v,
    det_setRow_eq_cofactorRowPairing M a u,
    det_setRow_eq_cofactorRowPairing M b v,
    det_setRow_eq_cofactorRowPairing M a v,
    det_setRow_eq_cofactorRowPairing M b u]
  exact cofactorRowPairing_setRow_plucker M a b hab u v

/-- Canonical ordered four-row Grassmann-Plucker identity for the raw `nDet`
minors of an `(n + 2) × n` matrix: for any four strictly increasing rows
`r0 < r1 < r2 < r3`, the three pairings of `nDet` two-row minors sum to zero
with the canonical Plucker signs.

The proof applies the square two-row replacement Plucker kernel
`det_setRow_setRow_mul_det` to `nMatrix B r0 r1 h01` at the two replacement
positions `s2 = ⟨r2.val - 2, _⟩` and `s3 = ⟨r3.val - 2, _⟩`, then transports
each of the five resulting determinants to a signed `nDet` minor via the
single-row and double-row `setRow ∘ setRow` row-replacement transports. The
sign exponents collapse against the common factor
`(-1) ^ ((r2 - r0 - 2) + (r3 - r1 - 2))`. -/
private theorem nDet_plucker_four_row_canonical
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (r0 r1 r2 r3 : Fin (n + 2))
    (h01 : r0.val < r1.val) (h12 : r1.val < r2.val)
    (h23 : r2.val < r3.val) :
    nDet B r2 r3 h23 * nDet B r0 r1 h01 -
      nDet B r1 r3 (Nat.lt_trans h12 h23) *
        nDet B r0 r2 (Nat.lt_trans h01 h12) +
      nDet B r1 r2 h12 *
        nDet B r0 r3 (Nat.lt_trans h01 (Nat.lt_trans h12 h23)) = 0 := by
  -- A strictly increasing four-tuple in `Fin (n + 2)` forces `n ≥ 2`. Reduce
  -- to `n = n' + 1` so the `(n+1) × (n+1)` square Plucker kernel applies to
  -- `nMatrix B r0 r1 h01`.
  cases n with
  | zero =>
      have := r3.isLt
      omega
  | succ n' =>
      have hsk2 : r2.val - 2 < n' + 1 := by have := r3.isLt; omega
      have hsk3 : r3.val - 2 < n' + 1 := by have := r3.isLt; omega
      have hs2s3 :
          (⟨r2.val - 2, hsk2⟩ : Fin (n' + 1)) ≠ ⟨r3.val - 2, hsk3⟩ := by
        intro heq
        have : r2.val - 2 = r3.val - 2 := congrArg Fin.val heq
        omega
      have hsq :=
        det_setRow_setRow_mul_det (nMatrix B r0 r1 h01)
          (⟨r2.val - 2, hsk2⟩ : Fin (n' + 1))
          (⟨r3.val - 2, hsk3⟩ : Fin (n' + 1)) hs2s3 B[r0] B[r1]
      have ho :=
        det_setRow_setRow_nMatrix_r2_r0_r3_r1_eq_pow_mul_nDet_r2_r3
          B r0 r1 r2 r3 h01 h12 h23
      have ha :=
        det_setRow_nMatrix_r2_r0_eq_pow_mul_nDet_r1_r2
          B r0 r1 r2 r3 h01 h12 h23
      have hb :=
        det_setRow_nMatrix_r3_r1_eq_pow_mul_nDet_r0_r3
          B r0 r1 r2 r3 h01 h12 h23
      have hc :=
        det_setRow_nMatrix_r2_r1_eq_pow_mul_nDet_r0_r2
          B r0 r1 r2 r3 h01 h12 h23
      have hd :=
        det_setRow_nMatrix_r3_r0_eq_pow_mul_nDet_r1_r3
          B r0 r1 r2 r3 h01 h12 h23
      simp only at ho ha hb hc hd
      rw [ho, ha, hb, hc, hd] at hsq
      change nDet B r0 r1 h01 * _ = _ at hsq
      -- Sign-cancellation facts: square cancellation of the common factor,
      -- the `pow_add` split of the outer exponent, the `pow_succ` shift for
      -- `r3 - r1 - 1`, and the parity identity
      -- `(r2 - r1 - 1) + (r3 - r0 - 2) = ((r2 - r0 - 2) + (r3 - r1 - 2)) + 1`
      -- that aligns the two off-diagonal sign products.
      have hself :=
        neg_one_pow_mul_self (R := R)
          ((r2.val - r0.val - 2) + (r3.val - r1.val - 2))
      have hpow_ab :=
        Lean.Grind.Semiring.pow_add (-1 : R)
          (r2.val - r0.val - 2) (r3.val - r1.val - 2)
      have hpow_b1 :
          (-1 : R) ^ (r3.val - r1.val - 1) =
            (-1 : R) ^ (r3.val - r1.val - 2) * (-1 : R) := by
        have heq : r3.val - r1.val - 1 = (r3.val - r1.val - 2) + 1 := by omega
        rw [heq, Lean.Grind.Semiring.pow_succ]
      have hpow_de :
          (-1 : R) ^ (r2.val - r1.val - 1) * (-1 : R) ^ (r3.val - r0.val - 2) =
            (-1 : R) ^ ((r2.val - r0.val - 2) + (r3.val - r1.val - 2)) *
              (-1 : R) := by
        rw [← Lean.Grind.Semiring.pow_add]
        have heq :
            (r2.val - r1.val - 1) + (r3.val - r0.val - 2) =
              ((r2.val - r0.val - 2) + (r3.val - r1.val - 2)) + 1 := by omega
        rw [heq, Lean.Grind.Semiring.pow_succ]
      grind

/-- Raw `nDet` three-term Plucker identity for the q-between case
`p1 < q < p2 < p3`: a direct specialization of the canonical four-row
identity at `(r0, r1, r2, r3) = (p1, q, p2, p3)`. The product order of the
two off-diagonal pairs is swapped relative to the canonical statement;
multiplication in a `CommRing` discharges the swap. -/
private theorem det_plucker_three_term_nDet_of_between_p1_p2
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (p1 q p2 p3 : Fin (n + 2))
    (h1q : p1.val < q.val) (hq2 : q.val < p2.val) (h23 : p2.val < p3.val) :
    nDet B p2 p3 h23 * nDet B p1 q h1q -
      nDet B p1 p2 (Nat.lt_trans h1q hq2) *
        nDet B q p3 (Nat.lt_trans hq2 h23) +
      nDet B p1 p3 (Nat.lt_trans h1q (Nat.lt_trans hq2 h23)) *
        nDet B q p2 hq2 = 0 := by
  have hraw := nDet_plucker_four_row_canonical B p1 q p2 p3 h1q hq2 h23
  grind

/-- Raw `nDet` three-term Grassmann-Plucker identity for the q-before case
`q < p1 < p2 < p3`: the canonical ordered four-row identity
`nDet_plucker_four_row_canonical` instantiated at `(r0, r1, r2, r3) := (q, p1, p2, p3)`.
This is the q-before kernel consumed by the downstream consecutive-top Gram
pattern. -/
private theorem det_plucker_three_term_nDet_of_lt_p1
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (q p1 p2 p3 : Fin (n + 2))
    (hq1 : q.val < p1.val) (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) :
    nDet B p2 p3 h23 * nDet B q p1 hq1 -
      nDet B p1 p3 (Nat.lt_trans h12 h23) *
        nDet B q p2 (Nat.lt_trans hq1 h12) +
      nDet B p1 p2 h12 *
        nDet B q p3 (Nat.lt_trans hq1 (Nat.lt_trans h12 h23)) = 0 :=
  nDet_plucker_four_row_canonical B q p1 p2 p3 hq1 h12 h23

/-- Basis-vector case `q < p1` of the three-term Plucker identity:
expanding `mDet B (basisVec q) p_i` via `mDet_basisVec_eq_signed_nDet_of_gt`
(each `q < p_i`) reduces the goal to the raw q-before `nDet` kernel. -/
private theorem det_plucker_three_term_basisVec_of_lt_p1_of_nDet
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (q p1 p2 p3 : Fin (n + 2))
    (hq1 : q.val < p1.val) (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) :
    mDet B (basisVec (R := R) q) p1 * nDet B p2 p3 h23 -
      mDet B (basisVec (R := R) q) p2 *
        nDet B p1 p3 (Nat.lt_trans h12 h23) +
      mDet B (basisVec (R := R) q) p3 * nDet B p1 p2 h12 = 0 := by
  have hraw := det_plucker_three_term_nDet_of_lt_p1 B q p1 p2 p3 hq1 h12 h23
  rw [mDet_basisVec_eq_signed_nDet_of_gt B p1 q hq1]
  rw [mDet_basisVec_eq_signed_nDet_of_gt B p2 q (Nat.lt_trans hq1 h12)]
  rw [mDet_basisVec_eq_signed_nDet_of_gt B p3 q
      (Nat.lt_trans hq1 (Nat.lt_trans h12 h23))]
  grind

/-- Basis-vector case `p1 < q < p2` of the three-term Plucker identity.
The first expansion uses `mDet_basisVec_eq_signed_nDet_of_lt`; the latter two
use `mDet_basisVec_eq_signed_nDet_of_gt`. The consecutive cofactor signs differ
by a minus sign, leaving the raw q-between `nDet` kernel. -/
private theorem det_plucker_three_term_basisVec_of_between_p1_p2_of_nDet
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (p1 q p2 p3 : Fin (n + 2))
    (h1q : p1.val < q.val) (hq2 : q.val < p2.val) (h23 : p2.val < p3.val) :
    mDet B (basisVec (R := R) q) p1 * nDet B p2 p3 h23 -
      mDet B (basisVec (R := R) q) p2 *
        nDet B p1 p3 (Nat.lt_trans (Nat.lt_trans h1q hq2) h23) +
      mDet B (basisVec (R := R) q) p3 *
        nDet B p1 p2 (Nat.lt_trans h1q hq2) = 0 := by
  have hraw :=
    det_plucker_three_term_nDet_of_between_p1_p2 B p1 q p2 p3 h1q hq2 h23
  rw [mDet_basisVec_eq_signed_nDet_of_lt B p1 q h1q]
  rw [mDet_basisVec_eq_signed_nDet_of_gt B p2 q hq2]
  rw [mDet_basisVec_eq_signed_nDet_of_gt B p3 q (Nat.lt_trans hq2 h23)]
  have hrow :
      (⟨q.val, by have := p3.isLt; omega⟩ : Fin (n + 1)) =
        (⟨q.val - 1 + 1, by have := p3.isLt; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp
    omega
  rw [hrow]
  rw [cofactorSign_consecutive_last_neg (R := R) (q.val - 1)
      (by have := p3.isLt; omega)]
  grind

/-- Consecutive-top vector-column Plücker identity.

This is the Mathlib-free specialization used by the Gram/Bareiss trajectory:
the three distinguished rows are `alpha`, `k`, and `k+1` inside
`Fin (k + 2)`, so the top row is the last possible row and there is no
`q > p3` basis-vector case. -/
theorem det_plucker_three_term_consecutive_top
    {R : Type u} [Lean.Grind.CommRing R] {k : Nat}
    (B : Matrix R (k + 2) k) (v : Vector R (k + 2))
    (alpha : Fin (k + 2)) (halpha : alpha.val < k) :
    let pk : Fin (k + 2) := ⟨k, by omega⟩
    let plast : Fin (k + 2) := Fin.last (k + 1)
    mDet B v alpha * nDet B pk plast (by dsimp [pk, plast]; omega) -
      mDet B v pk * nDet B alpha plast (by dsimp [plast]; omega) +
      mDet B v plast * nDet B alpha pk (by dsimp [pk]; exact halpha) = 0 := by
  let pk : Fin (k + 2) := ⟨k, by omega⟩
  let plast : Fin (k + 2) := Fin.last (k + 1)
  have h12 : alpha.val < pk.val := by
    dsimp [pk]
    exact halpha
  have h23 : pk.val < plast.val := by
    dsimp [pk, plast]
    omega
  dsimp only
  refine det_plucker_three_term_of_basisVec B v alpha pk plast h12 h23 ?_
  intro q
  by_cases hq_alpha : q = alpha
  · subst q
    exact det_plucker_three_term_basisVec_of_eq_p1 B alpha pk plast h12 h23
  by_cases hq_pk : q = pk
  · subst hq_pk
    exact det_plucker_three_term_basisVec_of_eq_p2 B alpha pk plast h12 h23
  by_cases hq_plast : q = plast
  · subst hq_plast
    exact det_plucker_three_term_basisVec_of_eq_p3 B alpha pk plast h12 h23
  by_cases hq_lt_alpha : q.val < alpha.val
  · exact det_plucker_three_term_basisVec_of_lt_p1_of_nDet
      B q alpha pk plast hq_lt_alpha h12 h23
  have halpha_lt_q : alpha.val < q.val := by
    omega
  have hq_lt_pk : q.val < pk.val := by
    have hq_ne_pk_val : q.val ≠ k := by
      intro hv
      apply hq_pk
      apply Fin.ext
      dsimp [pk]
      exact hv
    have hq_ne_plast_val : q.val ≠ k + 1 := by
      intro hv
      apply hq_plast
      apply Fin.ext
      dsimp [plast]
      exact hv
    have hq_bound : q.val < k + 2 := q.isLt
    dsimp [pk]
    omega
  exact det_plucker_three_term_basisVec_of_between_p1_p2_of_nDet
    B alpha q pk plast halpha_lt_q hq_lt_pk h23

end Matrix
end Hex
