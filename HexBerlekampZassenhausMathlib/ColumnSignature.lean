/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMatrixMathlib.RankSpanNullspace

/-!
Column-agreement equivalence for the BHKS RREF signature step.

This module isolates the linear-algebra core of BHKS Lemma 3.3: two columns
of the computed RREF echelon matrix agree exactly when every vector in the
original row span has equal coordinates at those columns.
-/

namespace HexBerlekampZassenhausMathlib

namespace BHKS

private theorem rowCombination_eq_on_columns_of_rows_eq
    {n m : Nat} (M : Hex.Matrix ℚ n m) (j k : Fin m)
    (hrows : ∀ i : Fin n, M[i][j] = M[i][k]) (c : Vector ℚ n) :
    (Hex.Matrix.rowCombination M c)[j] = (Hex.Matrix.rowCombination M c)[k] := by
  unfold Hex.Matrix.rowCombination
  change (Hex.Matrix.mulVec (Hex.Matrix.transpose M) c)[j] =
    (Hex.Matrix.mulVec (Hex.Matrix.transpose M) c)[k]
  unfold Hex.Matrix.mulVec Hex.Matrix.row Hex.Vector.dotProduct
    Hex.Matrix.transpose Hex.Matrix.col
  change
      (Vector.ofFn fun j : Fin m =>
        (List.finRange n).foldl
          (fun acc i =>
            acc + (Vector.ofFn fun j : Fin m => Vector.ofFn fun i : Fin n => M[i][j])[j][i] *
              c[i]) 0).get j =
      (Vector.ofFn fun j : Fin m =>
        (List.finRange n).foldl
          (fun acc i =>
            acc + (Vector.ofFn fun j : Fin m => Vector.ofFn fun i : Fin n => M[i][j])[j][i] *
              c[i]) 0).get k
  rw [Vector.get_ofFn, Vector.get_ofFn]
  suffices
      (List.finRange n).foldl
          (fun acc i => acc + M[i][j] * c[i]) 0 =
        (List.finRange n).foldl
          (fun acc i => acc + M[i][k] * c[i]) 0 by
    simpa using this
  suffices
      ∀ acc : ℚ,
        (List.finRange n).foldl
            (fun acc i => acc + M[i][j] * c[i]) acc =
          (List.finRange n).foldl
            (fun acc i => acc + M[i][k] * c[i]) acc by
    exact this 0
  intro acc
  induction List.finRange n generalizing acc with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.foldl_cons]
      have hi : M[i][j] * c[i] = M[i][k] * c[i] := by
        rw [hrows i]
      rw [hi]
      exact ih _

/--
Two columns of the RREF echelon matrix agree iff every vector in the original
row span has equal entries at those columns.

This is the abstract row-span version of the executable
`bhksColumnSignature` comparison: equality of column slices of the echelon rows
is represented here by pointwise equality over the `Fin n` row index.
-/
theorem rref_columnAgreement_iff_forall_mem_span_coord_eq
    {n r : Nat} (M : Hex.Matrix ℚ n r) (j k : Fin r) :
    (∀ i : Fin n, (Hex.Matrix.rref M).echelon[i][j] = (Hex.Matrix.rref M).echelon[i][k]) ↔
      ∀ v : Fin r → ℚ,
        v ∈ Submodule.span ℚ
          (Set.range (_root_.Matrix.row (HexMatrixMathlib.matrixEquiv M))) →
        v j = v k := by
  constructor
  · intro hcols v hv
    rcases HexMatrixMathlib.rref_mem_span_echelon_of_mem_span
        (Hex.Matrix.rref_isRREF M) hv with ⟨c, hc⟩
    have hcoord := rowCombination_eq_on_columns_of_rows_eq
      (M := (Hex.Matrix.rref M).echelon) j k hcols c
    rw [hc] at hcoord
    simpa [HexMatrixMathlib.vectorEquiv] using hcoord
  · intro hspan i
    have hmem := HexMatrixMathlib.rref_echelon_row_mem_span
      (Hex.Matrix.rref_isRREF M) i
    have hcoord := hspan
      (HexMatrixMathlib.vectorEquiv (Hex.Matrix.row (Hex.Matrix.rref M).echelon i)) hmem
    simpa [HexMatrixMathlib.vectorEquiv, Hex.Matrix.row] using hcoord

end BHKS

end HexBerlekampZassenhausMathlib
