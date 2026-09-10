/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnum.GramSchmidt
public import HexGramSchmidtMathlib.Int
import Mathlib.Tactic

public section

namespace HexLatticeEnumMathlib

open Hex.LatticeEnum

variable {n m : Nat} (b : Basis n m) (t : Vector Rat m)

/-- Executable preparation recovers the squared norms of the semantic basis. -/
theorem prepare_norms (i : Fin n) :
    (prepare b t).norms[i] = ((Hex.GramSchmidt.Int.basis b.rows).row i).normSq := by
  simp only [prepare, Fin.getElem_fin, Vector.getElem_ofFn]
  change ((Hex.GramSchmidt.Int.gramDetVec b.rows).get ⟨i.val + 1, _⟩ : Rat) /
      ((Hex.GramSchmidt.Int.gramDetVec b.rows).get ⟨i.val, _⟩ : Rat) = _
  rw [Hex.GramSchmidt.Int.gramDetVec_eq_gramDet b.rows
      (Hex.GramSchmidt.Int.StepWitness.ofGram b.rows),
    Hex.GramSchmidt.Int.gramDetVec_eq_gramDet b.rows
      (Hex.GramSchmidt.Int.StepWitness.ofGram b.rows)]
  exact (Hex.GramSchmidt.Int.basis_normSq b.rows b.independent i.val i.isLt).symm

/-- Every orthogonalized direction of an accepted input has positive weight. -/
theorem prepare_norms_pos (i : Fin n) : 0 < (prepare b t).norms[i] := by
  rw [prepare_norms, Hex.GramSchmidt.Int.basis_normSq b.rows b.independent i.val i.isLt]
  apply div_pos
  · exact_mod_cast b.independent i
  · by_cases hi : i.val = 0
    · simp [hi]
    · exact_mod_cast Hex.GramSchmidt.Int.gramDet_pos b.rows b.independent
        i.val (Nat.le_of_lt i.isLt) (Nat.pos_of_ne_zero hi)

/-- The integer pass recovers the complete unit triangular coefficient matrix. -/
theorem coefficients_eq :
    coefficientsOfData (Hex.GramSchmidt.Int.data b.rows) = Hex.GramSchmidt.Int.coeffs b.rows := by
  apply Hex.Matrix.ext_getElem
  intro i j
  simp only [coefficientsOfData, Hex.Matrix.getElem_ofFn]
  split_ifs with hji hij
  · rw [Hex.Matrix.getElem_pair_eq_nested]
    change (((Hex.GramSchmidt.Int.scaledCoeffs b.rows)[i][j] : Int) : Rat) /
        ((Hex.GramSchmidt.Int.gramDetVec b.rows).get
          ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ : Rat) = _
    rw [Hex.GramSchmidt.Int.gramDetVec_eq_gramDet b.rows
      (Hex.GramSchmidt.Int.StepWitness.ofGram b.rows) (j.val + 1)
      (Nat.succ_le_of_lt j.isLt)]
    apply (div_eq_iff ?_).mpr
    · simpa [Hex.GramSchmidt.entry, Hex.Matrix.row, mul_comm] using
        Hex.GramSchmidt.Int.scaledCoeffs_eq b.rows i.val j.val i.isLt hji
    · exact_mod_cast Nat.ne_of_gt (b.independent j)
  · subst j
    exact (Hex.GramSchmidt.Int.coeffs_diag b.rows i.val i.isLt).symm
  · have hij' : i.val < j.val := by
      have : i.val ≠ j.val := fun h => hij (Fin.ext h)
      omega
    exact (Hex.GramSchmidt.Int.coeffs_upper b.rows i.val j.val i.isLt j.isLt hij').symm

/-- Prepared coefficients agree with semantic Gram–Schmidt coefficients. -/
theorem prepare_mu : (prepare b t).mu = Hex.GramSchmidt.Int.coeffs b.rows :=
  coefficients_eq b

/-- Forward substitution computes each semantic orthogonal row exactly once. -/
theorem orthogonalRows_eq (k : Nat) (hk : k ≤ n) :
    orthogonalRows b.rows (Hex.GramSchmidt.Int.coeffs b.rows) k hk =
      Vector.ofFn (fun i : Fin k =>
        (Hex.GramSchmidt.Int.basis b.rows).getRow ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) := by
  induction k with
  | zero =>
    apply Vector.ext
    intro i hi
    omega
  | succ k ih =>
    rw [orthogonalRows, ih (by omega)]
    apply Vector.ext
    intro j hj
    rw [Vector.getElem_ofFn]
    by_cases hjk : j < k
    · rw [Vector.getElem_push_lt hjk, Vector.getElem_ofFn]
    · have hjk : j = k := by omega
      subst j
      rw [Vector.getElem_push_eq]
      simp only [Fin.getElem_fin, Vector.getElem_ofFn, Hex.Matrix.getElem_pair_eq_nested]
      change (b.rows.row ⟨k, by omega⟩).map (fun x : Int => (x : Rat)) -
          Hex.GramSchmidt.prefixCombination (Hex.GramSchmidt.Int.coeffs b.rows)
            (Hex.GramSchmidt.Int.basis b.rows) k (by omega) = _
      rw [Hex.GramSchmidt.Int.basis_decomposition b.rows k (by omega)]
      apply Vector.ext
      intro a ha
      simp [Hex.Matrix.row]

/-- Prepared orthogonal rows agree with the semantic Gram–Schmidt basis. -/
theorem prepare_orthogonal :
    (prepare b t).orthogonal = Hex.GramSchmidt.Int.basis b.rows := by
  simp only [prepare, coefficients_eq, orthogonalRows_eq]
  apply Hex.Matrix.ext_getElem
  intro i j
  simp

/-- Native preparation satisfies every rational identity used by certificate replay. -/
theorem prepare_valid : (prepare b t).Valid := by
  unfold Prepared.Valid Data.Valid
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨prepare_norms_pos b t i, ?_⟩
    change (prepare b t).norms[i] = ((prepare b t).orthogonal.getRow i).normSq
    rw [prepare_norms, prepare_orthogonal]
    rfl
  · intro i j
    change (i < j → (prepare b t).mu[(i, j)] = 0) ∧
      (i = j → (prepare b t).mu[(i, j)] = 1) ∧
      (i ≠ j → ((prepare b t).orthogonal.getRow i).dotProduct
        ((prepare b t).orthogonal.getRow j) = 0)
    rw [prepare_mu, prepare_orthogonal, Hex.Matrix.getElem_pair_eq_nested]
    refine ⟨fun h => Hex.GramSchmidt.Int.coeffs_upper b.rows i.val j.val i.isLt j.isLt h,
      ?_, ?_⟩
    · intro h
      subst j
      exact Hex.GramSchmidt.Int.coeffs_diag b.rows i.val i.isLt
    · intro h
      exact Hex.GramSchmidt.Int.basis_orthogonal b.rows i.val j.val i.isLt j.isLt
        (fun heq => h (Fin.ext heq))
  · rw [prepare_mu, prepare_orthogonal]
    exact Hex.GramSchmidt.Int.coeffs_mul_basis_eq_castIntMatrix b.rows
  · intro i
    simp only [prepare, Fin.getElem_fin, Vector.getElem_ofFn]
  · rfl

/-- Replay accepts preparation from every independent input, including rank zero. -/
theorem prepare_check : (prepare b t).check = true := by
  simpa [Prepared.check, Data.check_iff, Prepared.Valid] using prepare_valid b t

end HexLatticeEnumMathlib
