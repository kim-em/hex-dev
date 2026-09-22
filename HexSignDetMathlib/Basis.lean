/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Support
public import HexRankMathlib.Cert
public import Mathlib.Order.Preorder.Finite

public section

/-! Full column rank after pruning and acceptance of the existing integer
rank producer. These facts depend only on the checked finite system. -/
namespace Hex.SignDet

open HexMatrixMathlib

/-- Selecting distinct columns of a matrix with a nonzero scaled left inverse
retains full column rank, over the integers themselves. -/
theorem rank_selectCols {r k : Nat} (m inv : Matrix Int r r) (d : Int)
    (hd : d ≠ 0) (hi : inv * m = Matrix.scale d (Matrix.identity r))
    (cols : Vector (Fin r) k) (hc : Function.Injective cols.get) :
    (matrixEquiv (Matrix.selectCols m cols)).rank = k := by
  have he : matrixEquiv inv * matrixEquiv m = d • (1 : _root_.Matrix (Fin r) (Fin r) Int) := by
    rw [← matrixEquiv_mul, hi, Matrix.scale_eq_smul, matrixEquiv_smul, matrixEquiv_identity]
  have hsub : (matrixEquiv inv).submatrix cols.get id *
      (matrixEquiv m).submatrix id cols.get = d • (1 : _root_.Matrix (Fin k) (Fin k) Int) := by
    rw [← _root_.Matrix.submatrix_mul _ _ cols.get id cols.get Function.bijective_id, he]
    ext i j
    simp only [_root_.Matrix.submatrix_apply, _root_.Matrix.smul_apply,
      smul_eq_mul, _root_.Matrix.one_apply, hc.eq_iff]
  rw [matrixEquiv_selectCols]
  apply le_antisymm
  · simpa using _root_.Matrix.rank_le_card_width ((matrixEquiv m).submatrix id cols.get)
  · have hl := _root_.Matrix.rank_mul_le_right
      ((matrixEquiv inv).submatrix cols.get id) ((matrixEquiv m).submatrix id cols.get)
    rw [hsub, _root_.Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero hd), _root_.Matrix.rank_one, Fintype.card_fin] at hl
    exact hl

/-- Zero-count pruning keeps a square row basis available even if every
count is zero. No semantic root-count premise is needed for this rank fact. -/
theorem System.retained_rank {r arity : Nat} (s : System r) (h : s.check arity = true) :
    (matrixEquiv s.retainedMatrix).rank = s.positive.length := by
  obtain ⟨hd, hi, _⟩ := s.identities h
  apply rank_selectCols _ s.inverse s.denominator hd hi
  have hn : s.positive.Nodup := List.Nodup.filter _ (List.nodup_finRange r)
  intro i j hij
  apply hn.injective_get
  simpa only [Vector.get, Vector.getElem_mk, List.getElem_toArray, List.get_eq_getElem,
    Fin.val_cast] using hij

/-- The existing integer rank producer supplies checked evidence for the
pruned matrix; its exact quotient law is discharged over `Int`. -/
theorem System.basis_checks {r : Nat} (s : System r) :
    Matrix.checkRank s.retainedMatrix (Matrix.rankCert s.retainedMatrix) = true :=
  rankCertWith_check (fun a b hb => Int.mul_ediv_cancel a hb) (by decide) s.retainedMatrix

/-- The produced retained basis has exactly one row per positive column. -/
theorem System.basis_rank {r arity : Nat} (s : System r) (h : s.check arity = true) :
    (Matrix.rankCert s.retainedMatrix).rank = s.positive.length :=
  (checkRank_sound s.basis_checks).symm.trans (s.retained_rank h)

private theorem ordered_cols {r k : Nat} (cols : Vector (Fin k) r)
    (hr : r = k) (hm : StrictMono cols.get) : cols.toList.map Fin.val = List.range k := by
  subst r
  have he : cols = Vector.ofFn (fun i : Fin k => i) := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_ofFn]
    exact congrFun hm.eq_id (⟨i, hi⟩ : Fin k)
  rw [he]
  simp [Vector.toList_ofFn, List.ofFn_eq_map]

/-- Since all retained columns are independent, the rank producer's increasing
pivot columns are exactly their original order. -/
theorem System.basis_columns {r arity : Nat} (s : System r) (h : s.check arity = true) :
    (Matrix.rankCert s.retainedMatrix).cols.toList.map Fin.val = List.range s.positive.length := by
  apply ordered_cols _ (s.basis_rank h)
  exact rowReduceWith_cols_strictMono (fun a b hb => Int.mul_ediv_cancel a hb)
    (by decide) s.retainedMatrix

private theorem reverse_inverse {k : Nat} (a b : _root_.Matrix (Fin k) (Fin k) Int)
    (d : Int) (hd : d ≠ 0) (h : a * b = d • 1) : b * a = d • 1 := by
  have hdet : a.det ≠ 0 := by
    intro hz
    have he := congrArg _root_.Matrix.det h
    simp only [_root_.Matrix.det_mul, _root_.Matrix.det_smul, _root_.Matrix.det_one,
      mul_one, hz, zero_mul, Fintype.card_fin] at he
    exact pow_ne_zero k hd he.symm
  have hc : IsLeftRegular a.det := fun _ _ he => mul_left_cancel₀ hdet he
  apply (_root_.Matrix.isRegular_of_isLeftRegular_det hc).left
  change a * (b * a) = a * (d • 1)
  rw [← mul_assoc, h, _root_.Matrix.smul_mul, _root_.Matrix.mul_smul, one_mul, mul_one]

/-- The rank producer's right-inverse certificate also supplies the left
inverse checked by BKR, with the same integer denominator and literal order. -/
theorem System.basis_inverse {r : Nat} (s : System r) :
    let c := Matrix.rankCert s.retainedMatrix
    c.adj * Matrix.selectedSubmatrix s.retainedMatrix c.rows c.cols =
      Matrix.scale c.denom (Matrix.identity c.rank) := by
  dsimp only
  obtain ⟨hd, hi, _⟩ := (checkRank_iff_matrixEquiv _ _).mp s.basis_checks
  apply matrixEquiv.injective
  rw [matrixEquiv_mul, matrixEquiv_selectedSubmatrix, Matrix.scale_eq_smul,
    matrixEquiv_smul, matrixEquiv_identity]
  exact reverse_inverse _ _ _ hd hi

end Hex.SignDet
