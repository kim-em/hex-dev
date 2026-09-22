/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Replay
public import HexSignDetMathlib.Basis
public import HexSignDetMathlib.Tensor

public section

namespace Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]

/-- Dimension-indexed form of the actual retained exponent rows. -/
def Node.basisRows (n : Node E Ctx) : Vector (List Nat) n.basis.rank :=
  n.basis.rows.map fun i => n.system.rows[i]

/-- The rank witness's column order in the original sign conditions. -/
def Node.basisCols (n : Node E Ctx) : Vector (List Int) n.basis.rank :=
  n.basis.cols.map fun j => n.system.columns[n.system.positive[j]]

theorem Node.basisRows_list (n : Node E Ctx) : n.basisRows.toList = n.rows := by
  simp only [basisRows, rows, Vector.toList_map]

/-- The selected minor is the moment matrix of the actual retained rows
and columns, before using the rank producer's column-order theorem. -/
theorem Node.basis_matrix (n : Node E Ctx) :
    Matrix.selectedSubmatrix n.system.retainedMatrix n.basis.rows n.basis.cols =
      momentMatrix n.basisRows n.basisCols := by
  apply Matrix.ext_getElem
  intro i j
  rw [Matrix.getElem_selectedSubmatrix]
  simp only [System.retainedMatrix, Matrix.getElem_selectCols,
    momentMatrix, Matrix.getElem_ofFn, basisRows, basisCols]
  simp only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray]

/-- Exact rank-column order identifies the selected sign columns with all
positive columns, including the empty support. -/
theorem Node.basis_support (n : Node E Ctx)
    (hc : n.basis.cols.toList.map Fin.val = List.range n.system.positive.length) :
    n.basisCols.toList = n.system.support := by
  have he : n.basis.cols.toList = List.finRange n.system.positive.length := by
    apply List.map_injective_iff.mpr Fin.val_injective
    simpa using hc
  simp only [basisCols, Vector.toList_map, he, System.support]
  rw [← List.ofFn_eq_map]
  simpa only [Fin.getElem_fin] using
    List.ofFn_getElem_eq_map n.system.positive (fun i => n.system.columns[i])

/-- System shape validation supplies the width premise for multiplying
retained moment matrices, without a polynomial or root hypothesis. -/
theorem Node.basis_width (n : Node E Ctx) {arity : Nat}
    (hs : n.system.check arity = true) (i j : Fin n.basis.rank) :
    n.basisRows[i].length = n.basisCols[j].length := by
  simp only [System.check, Bool.and_eq_true] at hs
  have hr := List.all_eq_true.mp hs.1.1.1.1.1
    n.system.rows[n.basis.rows[i]] (List.getElem_mem (by simp))
  have hc := List.all_eq_true.mp hs.1.1.1.1.2
    n.system.columns[n.system.positive[n.basis.cols[j]]] (List.getElem_mem (by simp))
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr hc
  simpa only [basisRows, basisCols, Fin.getElem_fin, Vector.getElem_map] using hr.1.trans hc.1.symm

/-- The actual producer's retained witness inverts its retained moment matrix. -/
theorem Node.basis_inverse (n : Node E Ctx)
    (hb : n.basis = Matrix.rankCert n.system.retainedMatrix) :
    n.basis.adj * momentMatrix n.basisRows n.basisCols =
      Matrix.scale n.basis.denom (Matrix.identity n.basis.rank) := by
  rw [← n.basis_matrix, hb]
  exact n.system.basis_inverse

/-- The parent witness used by `buildTreeFrom` inverts the moment matrix
on precisely its concatenated retained row and support lists. These are the
actual child rank certificates; no accepted parent or root semantics is assumed. -/
theorem Node.product_inverse (l r : Node E Ctx) {a b : Nat}
    (hl : l.system.check a = true) (hr : r.system.check b = true)
    (hbl : l.basis = Matrix.rankCert l.system.retainedMatrix)
    (hbr : r.basis = Matrix.rankCert r.system.retainedMatrix) :
    let rows := productVector l.basisRows r.basisRows
    let cols := productVector l.basisCols r.basisCols
    rows.toList = product l.rows r.rows ∧
    cols.toList = product l.system.support r.system.support ∧
    tensor l.basis.adj r.basis.adj * momentMatrix rows cols =
      Matrix.scale (l.basis.denom * r.basis.denom)
        (Matrix.identity (l.basis.rank * r.basis.rank)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [productVector_toList, l.basisRows_list, r.basisRows_list]
  · rw [productVector_toList, l.basis_support, r.basis_support]
    · rw [hbr]; exact r.system.basis_columns hr
    · rw [hbl]; exact l.system.basis_columns hl
  · rw [momentMatrix_product _ _ _ _ (l.basis_width hl)]
    exact tensor_inverse _ _ _ _ _ _ (l.basis_inverse hbl) (r.basis_inverse hbr)

end Hex.SignDet
