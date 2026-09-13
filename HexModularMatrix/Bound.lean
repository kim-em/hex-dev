/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.Nat.Sqrt
public import HexDeterminant.Laplace

public section

/-! Integer determinant bounds, with a Mathlib-free proof of the row-norm bound. -/

namespace Hex.Matrix

namespace DetBound

/-- Sum over finite indices without allocating an index list at runtime. -/
@[expose]
def sum {R : Type u} [Lean.Grind.Semiring R] (f : Fin n → R) : R :=
  Fin.foldl n (fun a i => a + f i) 0

/-- Product over finite indices without allocating an index list at runtime. -/
@[expose]
def prod {R : Type u} [Lean.Grind.Semiring R] (f : Fin n → R) : R :=
  Fin.foldl n (fun a i => a * f i) 1

/-- Split off the first summand. -/
theorem sum_succ {R : Type u} [Lean.Grind.Semiring R] (f : Fin (n + 1) → R) :
    sum f = f 0 + sum (fun i => f i.succ) := by
  rw [sum, Fin.foldl_succ]
  simp only [Lean.Grind.AddCommMonoid.zero_add, sum, Fin.foldl_eq_finRange_foldl]
  exact List.foldl_add_eq_add_foldl _ _ _

/-- Split off the first factor. -/
theorem prod_succ (f : Fin (n + 1) → Nat) :
    prod f = f 0 * prod (fun i => f i.succ) := by
  rw [prod, Fin.foldl_succ]
  simp only [Lean.Grind.Semiring.one_mul, prod, Fin.foldl_eq_finRange_foldl]
  exact List.foldl_mul_eq_mul_foldl _ _ _

/-- Finite sums preserve pointwise inequalities. -/
theorem sum_le {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) : sum f ≤ sum g := by
  have go (xs : List (Fin n)) (a b : Nat) (hab : a ≤ b) :
      xs.foldl (fun a i => a + f i) a ≤ xs.foldl (fun b i => b + g i) b := by
    induction xs generalizing a b with
    | nil => exact hab
    | cons i xs ih => exact ih _ _ (Nat.add_le_add hab (h i))
  simpa only [sum, Fin.foldl_eq_finRange_foldl] using
    go (List.finRange n) 0 0 (Nat.le_refl 0)

/-- Finite products of natural numbers preserve pointwise inequalities. -/
theorem prod_le {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) : prod f ≤ prod g := by
  have go (xs : List (Fin n)) (a b : Nat) (hab : a ≤ b) :
      xs.foldl (fun a i => a * f i) a ≤ xs.foldl (fun b i => b * g i) b := by
    induction xs generalizing a b with
    | nil => exact hab
    | cons i xs ih => exact ih _ _ (Nat.mul_le_mul hab (h i))
  simpa only [prod, Fin.foldl_eq_finRange_foldl] using go (List.finRange n) 1 1 (Nat.le_refl 1)

/-- The absolute value of an integer sum is bounded by the sum of absolute values. -/
theorem natAbs_sum (f : Fin n → Int) : (sum f).natAbs ≤ sum (fun i => (f i).natAbs) := by
  have go (xs : List (Fin n)) (a : Int) (b : Nat) (hab : a.natAbs ≤ b) :
      (xs.foldl (fun a i => a + f i) a).natAbs ≤
        xs.foldl (fun b i => b + (f i).natAbs) b := by
    induction xs generalizing a b with
    | nil => exact hab
    | cons i xs ih =>
      exact ih _ _ (Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_right hab _))
  simpa only [sum, Fin.foldl_eq_finRange_foldl] using go (List.finRange n) 0 0 (by decide)

private theorem skip_zero (i : Fin n) : skipIndex (0 : Fin (n + 1)) i = i.succ := by
  apply Fin.ext
  simp [skipIndex]

private theorem skip_succ_zero (j : Fin (n + 1)) :
    skipIndex j.succ (0 : Fin (n + 1)) = 0 := by
  simp [skipIndex]

private theorem skip_succ (j : Fin (n + 1)) (i : Fin n) :
    skipIndex j.succ i.succ = (skipIndex j i).succ := by
  simp only [skipIndex, Fin.val_succ]
  split <;> split <;> simp_all <;> omega

/-- Deleting one nonnegative summand can only decrease a sum. -/
theorem sum_skip_le (f : Fin (n + 1) → Nat) (j : Fin (n + 1)) :
    sum (fun i => f (skipIndex j i)) ≤ sum f := by
  induction n with
  | zero => simp [sum]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [skip_zero]
      rw [sum_succ f]
      omega
    · rw [sum_succ, sum_succ f]
      simp only [skip_succ_zero, skip_succ]
      exact Nat.add_le_add_left (ih (fun i => f i.succ) j) _

/-- A common factor can be taken out of a finite sum. -/
theorem sum_mul (f : Fin n → Nat) (b : Nat) :
    sum (fun i => f i * b) = sum f * b := by
  simp only [sum, Fin.foldl_eq_finRange_foldl]
  exact List.foldl_add_mul_right_zero _ _ _

/-- The sum of squares of nonnegative entries is at most their sum squared. -/
theorem sum_sq_le (f : Fin n → Nat) : sum (fun i => f i ^ 2) ≤ sum f ^ 2 := by
  induction n with
  | zero => simp [sum]
  | succ n ih =>
    rw [sum_succ, sum_succ f]
    have h := ih (fun i => f i.succ)
    simp only [Nat.pow_two, Nat.add_mul, Nat.mul_add] at h ⊢
    omega

end DetBound

/-- Product of the sums of absolute values in each row. -/
@[expose]
def rowNormBound (A : Matrix Int n n) : Nat :=
  DetBound.prod fun i : Fin n => DetBound.sum fun j : Fin n => A[(i, j)].natAbs

/-- The row-norm bound dominates the absolute value of the determinant,
proved by Laplace expansion and induction on the matrix dimension. -/
theorem natAbs_det_le_rowNormBound (A : Matrix Int n n) :
    (det A).natAbs ≤ rowNormBound A := by
  induction n with
  | zero =>
    simp [det, permutationVectors, detTerm, detSign, detProduct, inversionCount,
      rowNormBound, DetBound.prod]
  | succ n ih =>
    let tail : Nat := DetBound.prod fun i : Fin n =>
      DetBound.sum fun j : Fin (n + 1) => A[(i.succ, j)].natAbs
    have hminor (j : Fin (n + 1)) :
        (det (A.deleteRowCol 0 j)).natAbs ≤ tail := by
      apply Nat.le_trans (ih (A.deleteRowCol 0 j))
      apply DetBound.prod_le
      intro i
      simp only [getElem_pair_eq_nested, getElem_deleteRowCol]
      simpa only [DetBound.skip_zero, getElem_pair_eq_nested] using
        DetBound.sum_skip_le (fun k : Fin (n + 1) => A[(i.succ, k)].natAbs) j
    have hcofactor (j : Fin (n + 1)) :
        (cofactor A 0 j).natAbs = (det (A.deleteRowCol 0 j)).natAbs := by
      simp only [cofactor, cofactorSign]
      split <;> simp
    rw [det_eq_finFoldl_laplace_row A 0]
    change (DetBound.sum (fun j : Fin (n + 1) => A[(0 : Fin (n + 1))][j] * cofactor A 0 j)).natAbs ≤ _
    apply Nat.le_trans (DetBound.natAbs_sum _)
    calc
      DetBound.sum (fun j : Fin (n + 1) => (A[(0 : Fin (n + 1))][j] * cofactor A 0 j).natAbs)
          ≤ DetBound.sum (fun j : Fin (n + 1) => A[(0 : Fin (n + 1))][j].natAbs * tail) := by
        apply DetBound.sum_le
        intro j
        rw [Int.natAbs_mul, hcofactor]
        exact Nat.mul_le_mul_left _ (hminor j)
      _ = rowNormBound A := by
        rw [DetBound.sum_mul, rowNormBound, DetBound.prod_succ]
        simp only [tail, getElem_pair_eq_nested]

/-- The smaller of the row and column Hadamard bounds, using integer ceiling
square roots for each Euclidean norm. -/
@[expose]
def hadamardBound (A : Matrix Int n n) : Nat :=
  min (DetBound.prod fun j : Fin n => HexArith.Nat.ceilSqrt
        (DetBound.sum fun i : Fin n => A[(i, j)].natAbs ^ 2))
      (DetBound.prod fun i : Fin n => HexArith.Nat.ceilSqrt
        (DetBound.sum fun j : Fin n => A[(i, j)].natAbs ^ 2))

/-- Taking both row and column Hadamard bounds is never worse than the
row-norm bound. -/
theorem hadamardBound_le_rowNormBound (A : Matrix Int n n) :
    hadamardBound A ≤ rowNormBound A := by
  apply Nat.le_trans (Nat.min_le_right _ _)
  apply DetBound.prod_le
  intro i
  exact HexArith.Nat.ceilSqrt_le (DetBound.sum_sq_le (fun j : Fin n => A[(i, j)].natAbs))

/-- Hadamard's determinant inequality, supplied by the Mathlib companion. -/
class LawfulDetBound : Prop where
  natAbs_det_le : ∀ {n} (A : Matrix Int n n), (det A).natAbs ≤ hadamardBound A

end Hex.Matrix
