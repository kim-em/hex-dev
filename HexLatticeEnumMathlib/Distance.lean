/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnumMathlib.GramSchmidt
public import HexMatrixMathlib.Algebra
import Mathlib.Tactic

public section

namespace HexLatticeEnumMathlib

open Hex.LatticeEnum
open HexMatrixMathlib

variable {n m : Nat}

/-- A row combination pairs with a vector by pairing each row separately. -/
theorem dot_vecMul (a : Vector Rat n) (rows : Hex.Matrix Rat n m) (v : Vector Rat m) :
    (Hex.Matrix.vecMul a rows).dotProduct v =
      ∑ i : Fin n, a[i] * (rows.getRow i).dotProduct v := by
  simp only [HexMatrixMathlib.dotProduct_eq, _root_.dotProduct, vectorEquiv_apply]
  simp only [Hex.Matrix.vecMul, Hex.Matrix.getElem_mulVec,
    Hex.Matrix.row_transpose, HexMatrixMathlib.dotProduct_eq, _root_.dotProduct, vectorEquiv_apply,
    Hex.Matrix.getElem_col]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp only [Hex.Matrix.getElem_eq_getRow]
  ring

/-- Valid projection data leave a residual orthogonal to every orthogonal row. -/
theorem residual_orthogonal (p : Data n m) (rows : Hex.Matrix Int n m)
    (t : Vector Rat m) (hp : p.Valid rows t) (i : Fin n) :
    p.residual.dotProduct (p.orthogonal.getRow i) = 0 := by
  rw [hp.2.2.2.2, Vector.dotProduct_sub_left, dot_vecMul]
  have hs : (∑ j : Fin n, p.projection[j] *
      (p.orthogonal.getRow j).dotProduct (p.orthogonal.getRow i)) =
      p.projection[i] * p.norms[i] := by
    rw [Finset.sum_eq_single i]
    · rw [hp.1 i |>.2]
      rfl
    · intro j _ hji
      rw [hp.2.1 j i |>.2.2 hji, mul_zero]
    · simp
  rw [hs, hp.2.2.2.1 i, div_mul_cancel₀ _ (ne_of_gt (hp.1 i).1), sub_self]

private theorem vecMul_sub (a c : Vector Rat n) (rows : Hex.Matrix Rat n m) :
    Hex.Matrix.vecMul (a - c) rows = Hex.Matrix.vecMul a rows - Hex.Matrix.vecMul c rows := by
  apply Vector.ext
  intro j hj
  simp only [Hex.Matrix.vecMul, Vector.getElem_sub]
  change (rows.transpose * (a - c))[(⟨j, hj⟩ : Fin m)] =
    (rows.transpose * a)[(⟨j, hj⟩ : Fin m)] - (rows.transpose * c)[(⟨j, hj⟩ : Fin m)]
  rw [Hex.Matrix.getElem_mulVec, Hex.Matrix.getElem_mulVec,
    Hex.Matrix.getElem_mulVec, Vector.dotProduct_sub_right]

/-- The residual is also orthogonal to each original basis row. -/
theorem residual_basis (p : Data n m) (rows : Hex.Matrix Int n m)
    (t : Vector Rat m) (hp : p.Valid rows t) (i : Fin n) :
    p.residual.dotProduct (castVector (rows.getRow i)) = 0 := by
  have hr : castVector (rows.getRow i) = Hex.Matrix.vecMul (p.mu.getRow i) p.orthogonal := by
    apply Vector.ext
    intro j hj
    have he := congrArg (fun M : Hex.Matrix Rat n m => M[i][(⟨j, hj⟩ : Fin m)]) hp.2.2.1
    rw [Hex.Matrix.getElem_mul] at he
    simp only [castVector, Hex.Vector.getElem_ofFn']
    change ((rows.getRow i)[j] : Rat) = (p.orthogonal.transpose * p.mu.getRow i)[(⟨j, hj⟩ : Fin m)]
    rw [Hex.Matrix.getElem_mulVec, Hex.Matrix.row_transpose]
    simpa [Hex.GramSchmidt.castIntMatrix, Hex.Matrix.row, Vector.dotProduct_comm] using he.symm
  rw [hr, Vector.dotProduct_comm, dot_vecMul]
  apply Finset.sum_eq_zero
  intro j _
  rw [Vector.dotProduct_comm, residual_orthogonal p rows t hp j, mul_zero]

/-- Pythagoras retains the target's residual outside the row span. -/
theorem norm_difference (p : Data n m) (rows : Hex.Matrix Int n m)
    (t : Vector Rat m) (hp : p.Valid rows t) (a : Vector Rat n) :
    (Hex.Matrix.vecMul a p.orthogonal - t).normSq = p.residual.normSq +
      ∑ i : Fin n, (a[i] - p.projection[i]) ^ 2 * p.norms[i] := by
  have heq : Hex.Matrix.vecMul a p.orthogonal - t =
      Hex.Matrix.vecMul (a - p.projection) p.orthogonal - p.residual := by
    rw [vecMul_sub, hp.2.2.2.2]
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_sub]
    ring
  rw [heq]
  have horth : (Hex.Matrix.vecMul (a - p.projection) p.orthogonal).dotProduct
      p.residual = 0 := by
    rw [dot_vecMul]
    apply Finset.sum_eq_zero
    intro i _
    rw [Vector.dotProduct_comm, residual_orthogonal p rows t hp i, mul_zero]
  have hnorm := Hex.GramSchmidt.normSq_vecMul_of_orthogonal p.orthogonal
    (a - p.projection) (fun i j hij => hp.2.1 i j |>.2.2 hij)
  rw [Fin.foldl_eq_finRange_foldl, foldl_finRange_eq_sum] at hnorm
  change (Hex.Matrix.vecMul (a - p.projection) p.orthogonal - p.residual).dotProduct
      (Hex.Matrix.vecMul (a - p.projection) p.orthogonal - p.residual) = _
  rw [Vector.dotProduct_sub_left, Vector.dotProduct_sub_right,
    Vector.dotProduct_sub_right, horth, Vector.dotProduct_comm p.residual,
    horth, sub_zero, zero_sub, sub_neg_eq_add]
  change (Hex.Matrix.vecMul (a - p.projection) p.orthogonal).normSq + p.residual.normSq = _
  rw [hnorm, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hp.1 i |>.2]
  simp only [Fin.getElem_fin, Vector.getElem_sub, Hex.Matrix.row, pow_two]

/-- Integer row combinations commute with the exact rational coordinate cast. -/
theorem cast_vector (rows : Hex.Matrix Int n m) (z : Vector Int n) :
    (Hex.Matrix.vecMul z rows).map (fun x : Int => (x : Rat)) =
      Hex.Matrix.vecMul (z.map fun x : Int => (x : Rat)) (Hex.GramSchmidt.castIntMatrix rows) := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_map]
  change (((z * rows)[(⟨j, hj⟩ : Fin m)] : Int) : Rat) =
    ((z.map fun x : Int => (x : Rat)) * Hex.GramSchmidt.castIntMatrix rows)[(⟨j, hj⟩ : Fin m)]
  rw [Hex.Matrix.getElem_vecMul, Hex.Matrix.getElem_vecMul]
  simp only [HexMatrixMathlib.dotProduct_eq, _root_.dotProduct, vectorEquiv_apply]
  simp only [Hex.Matrix.getElem_col]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simp [Hex.GramSchmidt.castIntMatrix]

/-- The unit triangular change of coordinates gives the centre used by traversal. -/
theorem centre_eq (p : Data n m) (rows : Hex.Matrix Int n m)
    (t : Vector Rat m) (hp : p.Valid rows t) (z : Vector Int n) (i : Fin n) :
    (Hex.Matrix.vecMul (z.map fun x : Int => (x : Rat)) p.mu)[i] - p.projection[i] =
      (z[i] : Rat) - p.centre z i := by
  have hf : (fun (acc : Rat) (j : Fin n) =>
      if i < j then acc + p.mu[(j, i)] * (z[j] : Rat) else acc) =
      (fun acc j => acc + (if i < j then p.mu[(j, i)] * (z[j] : Rat) else 0)) := by
    funext acc j
    split_ifs <;> simp
  unfold Data.centre
  rw [hf, foldl_finRange_eq_sum]
  change ((z.map fun x : Int => (x : Rat)) * p.mu)[i] - _ = _
  rw [Hex.Matrix.getElem_vecMul, HexMatrixMathlib.dotProduct_eq]
  simp only [_root_.dotProduct, vectorEquiv_apply]
  simp only [Hex.Matrix.getElem_col]
  simp only [Fin.getElem_fin, Vector.getElem_map]
  have hs : (∑ j : Fin n, p.mu[j][i] * (z[j] : Rat)) =
      (z[i] : Rat) + ∑ j : Fin n, if i < j then p.mu[(j, i)] * (z[j] : Rat) else 0 := by
    calc
      _ = (∑ j : Fin n, if j = i then (z[i] : Rat) else 0) +
          ∑ j : Fin n, if i < j then p.mu[(j, i)] * (z[j] : Rat) else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Hex.Matrix.getElem_pair_eq_nested]
        by_cases hji : j = i
        · subst j
          simp [hp.2.1 i i |>.2.1 rfl]
        · by_cases hij : i < j
          · simp [hji, hij]
          · have hlt : j < i := lt_of_le_of_ne (le_of_not_gt hij) hji
            simp [hji, hij, hp.2.1 j i |>.1 hlt]
      _ = _ := by simp
  simp only [Fin.getElem_fin] at hs
  rw [hs]
  ring

/-- Exact squared distance decomposes into the residual and all search-level costs. -/
theorem distance_decomposition (p : Data n m) (rows : Hex.Matrix Int n m)
    (t : Vector Rat m) (hp : p.Valid rows t) (z : Vector Int n) :
    distance (Hex.Matrix.vecMul z rows) t = p.residual.normSq +
      ∑ i : Fin n, p.norms[i] * ((z[i] : Rat) - p.centre z i) ^ 2 := by
  simp only [distance, subtract_eq, castVector_eq]
  rw [cast_vector, ← hp.2.2.1, ← Hex.Matrix.vecMul_mul, norm_difference p rows t hp]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [centre_eq p rows t hp z i, mul_comm]

/-- Positive orthogonal rows have unique rational coordinates. -/
theorem orthogonal_injective (p : Data n m) (rows : Hex.Matrix Int n m)
    (t : Vector Rat m) (hp : p.Valid rows t) :
    Function.Injective (fun a : Vector Rat n => Hex.Matrix.vecMul a p.orthogonal) := by
  have hdot (a : Vector Rat n) (i : Fin n) :
      (Hex.Matrix.vecMul a p.orthogonal).dotProduct (p.orthogonal.getRow i) =
        a[i] * p.norms[i] := by
    rw [dot_vecMul, Finset.sum_eq_single i]
    · rw [(hp.1 i).2]
      rfl
    · intro j _ hji
      rw [(hp.2.1 j i).2.2 hji, mul_zero]
    · simp
  intro a c hac
  apply Vector.ext
  intro j hj
  have h := congrArg (fun v => v.dotProduct (p.orthogonal.getRow ⟨j, hj⟩)) hac
  rw [hdot, hdot] at h
  exact mul_right_cancel₀ (ne_of_gt (hp.1 ⟨j, hj⟩).1) h

/-- Suffix centres depend only on strictly later coefficients. -/
theorem centre_congr (p : Data n m) (z w : Vector Int n) (i : Fin n)
    (h : ∀ j : Fin n, i < j → z[j] = w[j]) : p.centre z i = p.centre w i := by
  unfold Data.centre
  congr 1
  apply congrArg (fun f => (List.finRange n).foldl f 0)
  funext acc j
  split_ifs with hij
  · rw [h j hij]
  · rfl

/-- Valid positive orthogonal data prove uniqueness of integer row coordinates. -/
theorem data_injective (p : Data n m) (rows : Hex.Matrix Int n m) (t : Vector Rat m)
    (hp : p.Valid rows t) : Function.Injective (fun z : Vector Int n => Hex.Matrix.vecMul z rows) := by
  intro z w hzw
  have heq : Hex.Matrix.vecMul (z.map fun x : Int => (x : Rat)) p.mu =
      Hex.Matrix.vecMul (w.map fun x : Int => (x : Rat)) p.mu := by
    apply orthogonal_injective p rows t hp
    dsimp only
    rw [Hex.Matrix.vecMul_mul, Hex.Matrix.vecMul_mul, hp.2.2.1,
      ← cast_vector, ← cast_vector]
    exact congrArg (fun v : Vector Int m => v.map fun x : Int => (x : Rat)) hzw
  have hall : ∀ k : Nat, k ≤ n → ∀ i : Fin n, k ≤ i.val → z[i] = w[i] := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self => intro i hi; omega
    | of_succ k hk ih =>
      intro i hi
      by_cases hki : k = i.val
      · have hc : p.centre z i = p.centre w i :=
          centre_congr p z w i (fun j hij => ih j (by omega))
        have he := congrArg (fun a : Vector Rat n => a[i] - p.projection[i]) heq
        rw [centre_eq p rows t hp z i, centre_eq p rows t hp w i, hc] at he
        have he' : (z[i] : Rat) = (w[i] : Rat) := by linarith
        exact_mod_cast he'
      · exact ih i (by omega)
  apply Vector.ext
  intro i hi
  exact hall 0 (Nat.zero_le n) ⟨i, hi⟩ (Nat.zero_le i)

/-- Independent integer rows give unique original-basis coefficients. -/
theorem vector_injective (b : Basis n m) : Function.Injective (vector b) :=
  data_injective (prepare b 0).toData b.rows 0 (prepare_valid b 0)

/-- Squared distances are nonnegative, independently of preparation. -/
theorem distance_nonneg (v : Vector Int m) (t : Vector Rat m) : 0 ≤ distance v t := by
  simp only [distance, subtract_eq, castVector_eq, Vector.normSq]
  rw [HexMatrixMathlib.dotProduct_eq]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

end HexLatticeEnumMathlib
