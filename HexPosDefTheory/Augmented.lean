/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexBareissTheory.Bareiss
public import HexPosDefTheory.Gaussian
import Mathlib.Tactic.Ring

public section

/-! Bordered-minor exactness and transform equations for augmented elimination. -/

open Matrix

namespace Hex.PosDefTheory

open HexMatrixTheory

variable {R : Type*} [CommRing R] {n : Nat}

/-- Place two blocks above zero rows so the existing square bordered-minor
invariant applies to every column of the augmented system. -/
def augment (B C : Hex.Matrix R n n) : Hex.Matrix R (n + n) (n + n) :=
  Hex.Matrix.ofFn fun i j =>
    if hi : i.val < n then
      if hj : j.val < n then B[((⟨i.val, hi⟩ : Fin n), (⟨j.val, hj⟩ : Fin n))]
      else C[((⟨i.val, hi⟩ : Fin n), (⟨j.val - n, by omega⟩ : Fin n))]
    else 0

theorem augment_left (B C : Hex.Matrix R n n) (i j : Fin n) :
    (augment B C)[i.castAdd n][j.castAdd n] = B[i][j] := by
  rw [augment, Hex.Matrix.getElem_ofFn]
  simp only [Fin.val_castAdd, dite_eq_left i.isLt, dite_eq_left j.isLt]
  simp only [Hex.Matrix.getElem_pair_eq_nested, Fin.eta]

theorem augment_right (B C : Hex.Matrix R n n) (i j : Fin n) :
    (augment B C)[i.castAdd n][j.natAdd n] = C[i][j] := by
  rw [augment, Hex.Matrix.getElem_ofFn]
  simp only [Fin.val_castAdd, Fin.val_natAdd, dite_eq_left i.isLt,
    dite_eq_right (show ¬ n + j.val < n by omega), Nat.add_sub_cancel_left]
  simp only [Hex.Matrix.getElem_pair_eq_nested, Fin.eta]

/-- The local bordered-minor identity supplies the exact numerator at every
trailing position of a regular Bareiss state. -/
theorem trailing_divisible [DecidableEq R] (source : Hex.Matrix R m m)
    (state : Hex.Matrix.BareissState R m) (h : BareissNoPivotInvariant source state)
    (i j : Fin m) (hi : state.step < i.val) (hj : state.step < j.val) :
    ∃ q : R,
      state.matrix[(⟨state.step, by omega⟩ : Fin m)][(⟨state.step, by omega⟩ : Fin m)] *
          state.matrix[i][j] -
        state.matrix[i][(⟨state.step, by omega⟩ : Fin m)] *
          state.matrix[(⟨state.step, by omega⟩ : Fin m)][j] = q * state.prevPivot := by
  have hk : state.step < m := by omega
  have hnext : state.step + 1 < m := by omega
  let kk : Fin m := ⟨state.step, hk⟩
  refine ⟨Hex.Matrix.det (Hex.Matrix.borderedMinor source (state.step + 1) hnext i j), ?_⟩
  have he := desnanot_jacobi_borderedMinor source state.step hk hnext i j hi hj
  rw [← h.prevPivot_eq, ← h.trailing_eq hk kk kk (by simp [kk]) (by simp [kk]),
    ← h.trailing_eq hk i j (Nat.le_of_lt hi) (Nat.le_of_lt hj),
    ← h.trailing_eq hk i kk (Nat.le_of_lt hi) (by simp [kk]),
    ← h.trailing_eq hk kk j (by simp [kk]) (Nat.le_of_lt hj)] at he
  exact he.symm

/-- Desnanot–Jacobi supplies exact division for the augmented right block,
including columns which were not part of the original coefficient matrix. -/
theorem right_divisible [DecidableEq R] (B C : Hex.Matrix R n n)
    (state : Hex.Matrix.BareissState R (n + n))
    (h : BareissNoPivotInvariant (augment B C) state)
    (i j : Fin n) (hi : state.step < i.val) :
    ∃ q : R,
      state.matrix[(⟨state.step, by omega⟩ : Fin (n + n))][
          (⟨state.step, by omega⟩ : Fin (n + n))] *
          state.matrix[(⟨i.val, by omega⟩ : Fin (n + n))][
            (⟨n + j.val, by omega⟩ : Fin (n + n))] -
        state.matrix[(⟨i.val, by omega⟩ : Fin (n + n))][
          (⟨state.step, by omega⟩ : Fin (n + n))] *
          state.matrix[(⟨state.step, by omega⟩ : Fin (n + n))][
            (⟨n + j.val, by omega⟩ : Fin (n + n))] = q * state.prevPivot := by
  have hk : state.step < n + n := by omega
  have hnext : state.step + 1 < n + n := by omega
  let ii : Fin (n + n) := ⟨i.val, by omega⟩
  let jj : Fin (n + n) := ⟨n + j.val, by omega⟩
  let kk : Fin (n + n) := ⟨state.step, hk⟩
  refine ⟨Hex.Matrix.det (Hex.Matrix.borderedMinor (augment B C)
    (state.step + 1) hnext ii jj), ?_⟩
  have he := desnanot_jacobi_borderedMinor (augment B C) state.step hk hnext
    ii jj (by exact hi) (by dsimp [jj]; omega)
  rw [← h.prevPivot_eq, ← h.trailing_eq hk kk kk (by simp [kk]) (by simp [kk]),
    ← h.trailing_eq hk ii jj (by exact Nat.le_of_lt hi) (by dsimp [jj]; omega),
    ← h.trailing_eq hk ii kk (by exact Nat.le_of_lt hi) (by simp [kk]),
    ← h.trailing_eq hk kk jj (by simp [kk]) (by dsimp [jj]; omega)] at he
  exact he.symm

/-- Every leading prefix of the augmented system lies in the original
Hermitian block, so its determinant is self-adjoint. -/
theorem prefix_selfAdjoint [StarRing R] (B C : Hex.Matrix R n n)
    (hB : (matrixEquiv B).IsHermitian) (k : Nat) (hk : k ≤ n) :
    star (Hex.Matrix.det (Hex.Matrix.principalSubmatrix (augment B C) k (by omega))) =
      Hex.Matrix.det (Hex.Matrix.principalSubmatrix (augment B C) k (by omega)) := by
  let P := Hex.Matrix.principalSubmatrix (augment B C) k (by omega)
  have he (i j : Fin k) : matrixEquiv P i j =
      B[((⟨i.val, by omega⟩ : Fin n), (⟨j.val, by omega⟩ : Fin n))] := by
    rw [matrixEquiv_apply]
    change P[i][j] = _
    rw [Hex.Matrix.getElem_principalSubmatrix, augment, Hex.Matrix.getElem_ofFn]
    simp only [dite_eq_left (i.isLt.trans_le hk), dite_eq_left (j.isLt.trans_le hk)]
  have hP : (matrixEquiv P).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, he]
    have h := congrFun (congrFun hB (⟨i.val, by omega⟩ : Fin n))
      (⟨j.val, by omega⟩ : Fin n)
    simpa only [Matrix.conjTranspose_apply, matrixEquiv_apply,
      Hex.Matrix.getElem_pair_eq_nested] using h
  change star (Hex.Matrix.det P) = Hex.Matrix.det P
  rw [det_eq, ← Matrix.det_conjTranspose, hP]

/-- The no-swap invariant establishes reality of diagonal pivots; no
imaginary component is discarded by this argument. -/
theorem pivot_selfAdjoint [StarRing R] [DecidableEq R] (B C : Hex.Matrix R n n)
    (state : Hex.Matrix.BareissState R (n + n))
    (h : BareissNoPivotInvariant (augment B C) state)
    (hB : (matrixEquiv B).IsHermitian) (hk : state.step < n) :
    star state.matrix[(⟨state.step, by omega⟩ : Fin (n + n))][
      (⟨state.step, by omega⟩ : Fin (n + n))] =
      state.matrix[(⟨state.step, by omega⟩ : Fin (n + n))][
        (⟨state.step, by omega⟩ : Fin (n + n))] := by
  have he := h.trailing_eq (by omega)
    (⟨state.step, by omega⟩ : Fin (n + n))
    (⟨state.step, by omega⟩ : Fin (n + n)) (by simp) (by simp)
  rw [borderedMinor_corner_eq_principalSubmatrix] at he
  rw [he]
  exact prefix_selfAdjoint B C hB (state.step + 1) (by omega)

/-- Exact row updates in both blocks preserve the transform relation. -/
theorem transform_step [NoZeroDivisors R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B L T L' T' : _root_.Matrix ι ι R) (k : ι) (p d : R) (hd : d ≠ 0)
    (old : L = T * B) (changed : ι → Prop) [DecidablePred changed]
    (left : ∀ i j, changed i → L' i j * d = p * L i j - L i k * L k j)
    (right : ∀ i j, changed i → T' i j * d = p * T i j - L i k * T k j)
    (left_fixed : ∀ i j, ¬ changed i → L' i j = L i j)
    (right_fixed : ∀ i j, ¬ changed i → T' i j = T i j) : L' = T' * B := by
  ext i j
  by_cases hi : changed i
  · apply mul_right_cancel₀ hd
    rw [left i j hi, Matrix.mul_apply, Finset.sum_mul]
    calc
      p * L i j - L i k * L k j =
          ∑ a, (p * T i a - L i k * T k a) * B a j := by
        have hiL := congrFun (congrFun old i) j
        have hkL := congrFun (congrFun old k) j
        rw [hiL, hkL]
        simp only [Matrix.mul_apply, Finset.mul_sum, sub_mul,
          Finset.sum_sub_distrib, mul_assoc]
      _ = ∑ a, T' i a * B a j * d := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← right i a hi]
        ring
  · rw [left_fixed i j hi, old, Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [right_fixed i a hi]

end Hex.PosDefTheory
