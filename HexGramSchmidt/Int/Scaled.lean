/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGramSchmidt.Int.Core
import all HexGramSchmidt.Int.Core

public section

/-!
Scaled-coefficient and Gram-determinant surface for `hex-gram-schmidt`.

This module packages the executable scaled Gram-Schmidt output: the `Data`
record bundling the leading Gram determinant vector `d` with the scaled
coefficient matrix `ν`, produced by `data` from a single
`scaledCoeffRowsSchur` pass, and exposed as the public `gramDetVec` and
`scaledCoeffs`. It proves the per-row Schur kernel agrees with the reference
`scaledCoeffRows` formulation (`schurSigma_congr` and the column/boundary
frame lemmas), and develops the Bareiss commutation infrastructure the
determinant correspondence rests on: a `Matrix.stepMatrix` step commutes with
taking a `principalSubmatrix` and with taking a trailing `borderedMinor`
(`principalSubmatrix_stepMatrix_eq`, `borderedMinor_stepMatrix_eq`), the no-pivot
loop stays synchronized across a matrix and its bordered minor
(`noPivotLoop_full_eq_borderedMinor_at_trailing`), it preserves trailing-block
symmetry, and its `step`/`singularStep` bookkeeping is monotone and stable
under prefixing.
-/
namespace Hex
namespace GramSchmidt.Int
/-- σ-chain dependency frame lemma. The value of `schurSigma rows i j`
depends only on the diagonal cells `rows[k][k]` for `k < j`, the
row-`i` cells `rows[i][p]` for `p < j`, and the row-`j` cells `rows[j][p]`
for `p < j`. The hypothesis `0 < j` makes both initial reads `rows[i][0]`
and `rows[j][0]` fall under `h_i` and `h_j` at `p = 0`. -/
private theorem schurSigma_congr
    {rows rows' : Array (Array Int)} {i j : Nat} (hj : 0 < j)
    (h_diag : ∀ k, k < j → getArrayEntry rows k k = getArrayEntry rows' k k)
    (h_i : ∀ p, p < j → getArrayEntry rows i p = getArrayEntry rows' i p)
    (h_j : ∀ p, p < j → getArrayEntry rows j p = getArrayEntry rows' j p) :
    schurSigma rows i j = schurSigma rows' i j := by
  -- Generic foldl congruence under pointwise body equality.
  have foldl_congr :
      ∀ (L : List Nat) (init init' : Int),
        init = init' →
        (∀ p ∈ L, ∀ s : Int,
          Matrix.exactDiv
            (getArrayEntry rows p p * s +
              getArrayEntry rows i p * getArrayEntry rows j p)
            (getArrayEntry rows (p - 1) (p - 1)) =
          Matrix.exactDiv
            (getArrayEntry rows' p p * s +
              getArrayEntry rows' i p * getArrayEntry rows' j p)
            (getArrayEntry rows' (p - 1) (p - 1))) →
        L.foldl
            (fun sigma p =>
              Matrix.exactDiv
                (getArrayEntry rows p p * sigma +
                  getArrayEntry rows i p * getArrayEntry rows j p)
                (getArrayEntry rows (p - 1) (p - 1)))
            init =
          L.foldl
            (fun sigma p =>
              Matrix.exactDiv
                (getArrayEntry rows' p p * sigma +
                  getArrayEntry rows' i p * getArrayEntry rows' j p)
                (getArrayEntry rows' (p - 1) (p - 1)))
            init' := by
    intro L
    induction L with
    | nil => intro init init' hinit _; simpa using hinit
    | cons p L ih =>
        intro init init' hinit hstep
        simp only [List.foldl_cons]
        apply ih
        · rw [hinit, hstep p (List.mem_cons_self) init']
        · intro q hq s
          exact hstep q (List.mem_cons_of_mem _ hq) s
  -- Initial accumulator equality at `p = 0`.
  have h_init : getArrayEntry rows i 0 * getArrayEntry rows j 0 =
      getArrayEntry rows' i 0 * getArrayEntry rows' j 0 := by
    rw [h_i 0 hj, h_j 0 hj]
  -- Per-step equality, using `p < j` for every `p` in `[1, j)`.
  have h_step :
      ∀ p ∈ List.range' 1 (j - 1), ∀ s : Int,
        Matrix.exactDiv
          (getArrayEntry rows p p * s +
            getArrayEntry rows i p * getArrayEntry rows j p)
          (getArrayEntry rows (p - 1) (p - 1)) =
        Matrix.exactDiv
          (getArrayEntry rows' p p * s +
            getArrayEntry rows' i p * getArrayEntry rows' j p)
          (getArrayEntry rows' (p - 1) (p - 1)) := by
    intro p hp s
    rw [List.mem_range'] at hp
    have hp_lt : p < j := by omega
    have hp_pred_lt : p - 1 < j := by omega
    rw [h_diag p hp_lt, h_i p hp_lt, h_j p hp_lt, h_diag (p - 1) hp_pred_lt]
  -- Reduce `schurSigma` to a foldl on each side.
  show
    (Id.run do
      let mut sigma := getArrayEntry rows i 0 * getArrayEntry rows j 0
      for p in [1:j] do
        sigma :=
          Matrix.exactDiv
            (getArrayEntry rows p p * sigma +
              getArrayEntry rows i p * getArrayEntry rows j p)
            (getArrayEntry rows (p - 1) (p - 1))
      return sigma) =
    (Id.run do
      let mut sigma := getArrayEntry rows' i 0 * getArrayEntry rows' j 0
      for p in [1:j] do
        sigma :=
          Matrix.exactDiv
            (getArrayEntry rows' p p * sigma +
              getArrayEntry rows' i p * getArrayEntry rows' j p)
            (getArrayEntry rows' (p - 1) (p - 1))
      return sigma)
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  exact foldl_congr _ _ _ h_init h_step

/-- `j = 0` boundary frame lemma. After the full Schur kernel runs, the
`(i, 0)` cell holds the gram entry `gram[i][0]`. This is used by the σ-chain
recurrence (`σ₀ = rows[i][0] · rows[j][0]`) when filling in cells at column
`j > 0`. -/
private theorem getArrayEntry_scaledCoeffRowsSchur_col_zero
    (b : Matrix Int n m) (i : Nat) :
    getArrayEntry (scaledCoeffRowsSchur b) i 0 =
      getArrayEntry (gramRows b) i 0 := by
  by_cases hin : i < n
  · -- In bounds. The outer row loop hits row `i`, the inner column loop
    -- writes `gram[i][0]` at `(i, 0)`, and later row iterations leave it
    -- alone.
    have h_mem : i ∈ List.range' 0 n := by
      rw [List.mem_range']
      exact ⟨i, by simpa using hin, by simp⟩
    have h_row : i < (zeroRows n).size := by
      rw [zeroRows_size]; exact hin
    have h_col : 0 < (zeroRows n)[i]!.size := by
      rw [zeroRows_row_size n i hin]
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) hin
    simp [scaledCoeffRowsSchur]
    exact getArrayEntry_schurRowLoop_col_zero (List.range' 0 n) (zeroRows n)
      (gramRows b) i h_mem h_row h_col
  · -- Out of bounds. The row loop never visits row `i`, so `(i, 0)` stays at
    -- its zero initial value, which matches `gramRows b` out of bounds.
    have hin' : n ≤ i := Nat.le_of_not_lt hin
    have h_not_mem : i ∉ List.range' 0 n := by
      rw [List.mem_range']
      rintro ⟨k, hk, hki⟩
      simp at hki
      omega
    have h_gram_zero : getArrayEntry (gramRows b) i 0 = 0 := by
      have h_gram_size : (gramRows b).size = n := gramRows_size b
      have h_size_le : (gramRows b).size ≤ i := h_gram_size.symm ▸ hin'
      have h_entry_default : (gramRows b)[i]! = (default : Array Int) := by
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none h_size_le, Option.getD_none]
      unfold getArrayEntry
      rw [h_entry_default]
      exact getArrayEntry_default_row 0
    rw [h_gram_zero]
    simp [scaledCoeffRowsSchur]
    rw [getArrayEntry_schurRowLoop_row_not_mem (List.range' 0 n) (zeroRows n)
      (gramRows b) i 0 h_not_mem]
    exact getArrayEntry_zeroRows n i 0

private theorem getArrayEntry_scaledCoeffRowsSchur_eq_schurScaledCoeffEntry
    {n m : Nat} (b : Matrix Int n m) (a c : Nat)
    (h_c_le_a : c ≤ a) (han : a < n) :
    getArrayEntry (scaledCoeffRowsSchur b) a c =
      schurScaledCoeffEntry (scaledCoeffRowsSchur b) (gramRows b) a c := by
  let gram := gramRows b
  let rowPrefix := List.range' 0 a
  let rowSuffix := List.range' (a + 1) (n - (a + 1))
  let rowsBeforeA :=
    rowPrefix.foldl
      (fun next row =>
        (List.range' 0 (row + 1)).foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
          next) (zeroRows n)
  let colPrefix := List.range' 0 c
  let colSuffix := List.range' (c + 1) (a - c)
  let rowsBeforeC :=
    colPrefix.foldl
      (fun next col =>
        setArrayEntry next a col (schurScaledCoeffEntry next gram a col)) rowsBeforeA
  let rowsAfterC :=
    setArrayEntry rowsBeforeC a c (schurScaledCoeffEntry rowsBeforeC gram a c)
  have h_rows_split :
      List.range' 0 n = rowPrefix ++ a :: rowSuffix := by
    dsimp [rowPrefix, rowSuffix]
    have hn_split : n = a + (n - a) := by omega
    have hn_tail : n - a = (n - (a + 1)) + 1 := by omega
    calc
      List.range' 0 n = List.range' 0 (a + (n - a)) := by
        exact congrArg (List.range' 0) hn_split
      _ = List.range' 0 a ++ List.range' a (n - a) := by
        simpa using (List.range'_append_1 (s := 0) (m := a) (n := n - a)).symm
      _ = List.range' 0 a ++ List.range' a ((n - (a + 1)) + 1) := by
        rw [hn_tail]
      _ = List.range' 0 a ++ a :: List.range' (a + 1) (n - (a + 1)) := by
        rw [List.range'_succ]
  have h_cols_split :
      List.range' 0 (a + 1) = colPrefix ++ c :: colSuffix := by
    dsimp [colPrefix, colSuffix]
    have hc_split : a + 1 = c + ((a + 1) - c) := by omega
    have hc_tail : (a + 1) - c = (a - c) + 1 := by omega
    calc
      List.range' 0 (a + 1) = List.range' 0 (c + ((a + 1) - c)) := by
        exact congrArg (List.range' 0) hc_split
      _ = List.range' 0 c ++ List.range' c ((a + 1) - c) := by
        simpa using (List.range'_append_1 (s := 0) (m := c) (n := (a + 1) - c)).symm
      _ = List.range' 0 c ++ List.range' c ((a - c) + 1) := by
        rw [hc_tail]
      _ = List.range' 0 c ++ c :: List.range' (c + 1) (a - c) := by
        rw [List.range'_succ]
  have h_a_not_suffix : a ∉ rowSuffix := by
    dsimp [rowSuffix]
    intro hmem
    rw [List.mem_range'] at hmem
    omega
  have h_c_not_colSuffix : c ∉ colSuffix := by
    dsimp [colSuffix]
    intro hmem
    rw [List.mem_range'] at hmem
    omega
  have hrow_beforeC : a < rowsBeforeC.size := by
    dsimp [rowsBeforeC, rowsBeforeA]
    rw [schurColumnLoop_size, schurRowLoop_size, zeroRows_size]
    exact han
  have hcol_beforeC : c < rowsBeforeC[a]!.size := by
    dsimp [rowsBeforeC, rowsBeforeA]
    rw [schurColumnLoop_rows_size, schurRowLoop_rows_size, zeroRows_row_size n a han]
    exact Nat.lt_of_le_of_lt h_c_le_a han
  have h_write :
      getArrayEntry (scaledCoeffRowsSchur b) a c =
        schurScaledCoeffEntry rowsBeforeC gram a c := by
    simp [scaledCoeffRowsSchur, gram, h_rows_split, h_cols_split, rowsBeforeA,
      rowsBeforeC]
    rw [getArrayEntry_schurRowLoop_row_not_mem _ _ _ _ _ h_a_not_suffix,
      getArrayEntry_schurColumnLoop_col_not_mem _ _ _ _ _ h_c_not_colSuffix]
    exact getArrayEntry_setArrayEntry_self rowsBeforeC a c
      (schurScaledCoeffEntry rowsBeforeC gram a c) hrow_beforeC hcol_beforeC
  rw [h_write]
  by_cases hc0 : c = 0
  · simp [schurScaledCoeffEntry, hc0, gram]
  · have hcp : 0 < c := Nat.pos_of_ne_zero hc0
    have h_entry_congr :
        schurScaledCoeffEntry rowsBeforeC gram a c =
          schurScaledCoeffEntry (scaledCoeffRowsSchur b) gram a c := by
      simp [schurScaledCoeffEntry, hc0]
      have h_diag_cells :
          ∀ k, k < c →
            getArrayEntry rowsBeforeC k k =
              getArrayEntry (scaledCoeffRowsSchur b) k k := by
        intro k hk
        have hka : k < a := by omega
        have hk_not_a : k ≠ a := by omega
        have hk_not_suffix : k ∉ rowSuffix := by
          dsimp [rowSuffix]
          intro hmem
          rw [List.mem_range'] at hmem
          omega
        calc
          getArrayEntry rowsBeforeC k k =
              getArrayEntry rowsBeforeA k k := by
            dsimp [rowsBeforeC]
            exact getArrayEntry_schurColumnLoop_row_ne _ _ _ _ _ _ hk_not_a
          _ = getArrayEntry
              ((List.range' 0 n).foldl
                (fun next row =>
                  (List.range' 0 (row + 1)).foldl
                    (fun next col =>
                      setArrayEntry next row col
                        (schurScaledCoeffEntry next (gramRows b) row col))
                    next) (zeroRows n)) k k := by
            rw [h_rows_split]
            simp [rowsBeforeA, gram]
            rw [getArrayEntry_schurRowLoop_row_not_mem _ _ _ _ _ hk_not_suffix,
              getArrayEntry_schurColumnLoop_row_ne _ _ _ _ _ _ hk_not_a]
          _ = getArrayEntry (scaledCoeffRowsSchur b) k k := by
            simp [scaledCoeffRowsSchur]
      have h_row_a_cells :
          ∀ p, p < c →
            getArrayEntry rowsBeforeC a p =
              getArrayEntry (scaledCoeffRowsSchur b) a p := by
        intro p hp
        have hp_not_c : p ∉ colSuffix := by
          dsimp [colSuffix]
          intro hmem
          rw [List.mem_range'] at hmem
          omega
        calc
          getArrayEntry rowsBeforeC a p =
              getArrayEntry rowsAfterC a p := by
            dsimp [rowsAfterC]
            rw [getArrayEntry_setArrayEntry_of_col_ne]
            omega
          _ = getArrayEntry
              ((colPrefix ++ c :: colSuffix).foldl
                (fun next col =>
                  setArrayEntry next a col (schurScaledCoeffEntry next gram a col))
                rowsBeforeA) a p := by
            simp [colPrefix, rowsBeforeC, rowsAfterC]
            rw [getArrayEntry_schurColumnLoop_col_not_mem _ _ _ _ _ hp_not_c]
          _ = getArrayEntry (scaledCoeffRowsSchur b) a p := by
            simp [scaledCoeffRowsSchur, gram, h_rows_split, h_cols_split, rowsBeforeA]
            rw [getArrayEntry_schurRowLoop_row_not_mem _ _ _ _ _ h_a_not_suffix]
      have h_row_c_cells :
          ∀ p, p < c →
            getArrayEntry rowsBeforeC c p =
              getArrayEntry (scaledCoeffRowsSchur b) c p := by
        intro p hp
        by_cases hca : c = a
        · subst a
          have hp_not_c : p ∉ colSuffix := by
            dsimp [colSuffix]
            intro hmem
            rw [List.mem_range'] at hmem
            omega
          calc
            getArrayEntry rowsBeforeC c p =
                getArrayEntry rowsAfterC c p := by
              dsimp [rowsAfterC]
              rw [getArrayEntry_setArrayEntry_of_col_ne]
              omega
            _ = getArrayEntry
                ((colPrefix ++ c :: colSuffix).foldl
                  (fun next col =>
                    setArrayEntry next c col (schurScaledCoeffEntry next gram c col))
                  rowsBeforeA) c p := by
              simp [colPrefix, rowsBeforeC, rowsAfterC]
              rw [getArrayEntry_schurColumnLoop_col_not_mem _ _ _ _ _ hp_not_c]
            _ = getArrayEntry (scaledCoeffRowsSchur b) c p := by
              simp [scaledCoeffRowsSchur, gram, h_rows_split, h_cols_split, rowsBeforeA]
              rw [getArrayEntry_schurRowLoop_row_not_mem _ _ _ _ _ h_a_not_suffix]
        · have hca_lt : c < a := by omega
          have hca_ne : c ≠ a := by omega
          have hc_not_suffix : c ∉ rowSuffix := by
            dsimp [rowSuffix]
            intro hmem
            rw [List.mem_range'] at hmem
            omega
          calc
            getArrayEntry rowsBeforeC c p =
                getArrayEntry rowsBeforeA c p := by
              dsimp [rowsBeforeC]
              exact getArrayEntry_schurColumnLoop_row_ne _ _ _ _ _ _ hca_ne
            _ = getArrayEntry
                ((List.range' 0 n).foldl
                  (fun next row =>
                    (List.range' 0 (row + 1)).foldl
                      (fun next col =>
                        setArrayEntry next row col
                          (schurScaledCoeffEntry next (gramRows b) row col))
                      next) (zeroRows n)) c p := by
              rw [h_rows_split]
              simp [rowsBeforeA, gram]
              rw [getArrayEntry_schurRowLoop_row_not_mem _ _ _ _ _ hc_not_suffix,
                getArrayEntry_schurColumnLoop_row_ne _ _ _ _ _ _ hca_ne]
            _ = getArrayEntry (scaledCoeffRowsSchur b) c p := by
              simp [scaledCoeffRowsSchur]
      have h_diag_prev :
          getArrayEntry rowsBeforeC (c - 1) (c - 1) =
            getArrayEntry (scaledCoeffRowsSchur b) (c - 1) (c - 1) := by
        exact h_diag_cells (c - 1) (by omega)
      have h_sigma :
          schurSigma rowsBeforeC a c =
            schurSigma (scaledCoeffRowsSchur b) a c :=
        schurSigma_congr hcp h_diag_cells h_row_a_cells h_row_c_cells
      rw [h_diag_prev, h_sigma]
    exact h_entry_congr

/-- Integral scaled Gram-Schmidt coefficients. For `j < i`, the entry is the
determinant formula corresponding to `d_{j+1} * μ_{i,j}`; on the diagonal we
store `d_{j+1}`, and entries above the diagonal are zero. -/
structure Data (n : Nat) where
  d : Vector Nat (n + 1)
  ν : Matrix Int n n

@[expose]
def gramDetVecFromScaledCoeffRows (rows : Array (Array Int)) :
    Vector Nat (n + 1) :=
  Vector.ofFn fun k =>
    match hk : k.val with
    | 0 => 1
    | r + 1 =>
        have hrSucc : r + 1 < n + 1 := by
          simpa [hk] using k.isLt
        have _hr : r < n := Nat.succ_lt_succ_iff.mp hrSucc
        (getArrayEntry rows r r).toNat

/-- Run the per-row Schur scaled-coefficient kernel once and package both the
leading Gram determinant vector and the scaled Gram-Schmidt coefficient matrix. -/
@[expose]
def data (b : Matrix Int n m) : Data n :=
  let rows := scaledCoeffRowsSchur b
  { d := gramDetVecFromScaledCoeffRows rows
    ν := rowsToMatrix rows n }

/-- All leading Gram determinants, starting with the empty-prefix value
`d₀ = 1`. -/
@[expose]
def gramDetVec (b : Matrix Int n m) : Vector Nat (n + 1) :=
  (data b).d

/-- Integral scaled Gram-Schmidt coefficients. For `j < i`, the entry is the
determinant formula corresponding to `d_{j+1} * μ_{i,j}`; on the diagonal we
store `d_{j+1}`, and entries above the diagonal are zero. -/
@[expose]
def scaledCoeffs (b : Matrix Int n m) : Matrix Int n n :=
  (data b).ν

/-- Entry-level packaging equation from the public scaled-coefficient matrix
back to the shared array pass that computes it. -/
theorem scaledCoeffs_entry_eq_getArrayEntry
    (b : Matrix Int n m) (i j : Fin n) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      getArrayEntry (scaledCoeffRowsSchur b) i.val j.val := by
  simp [scaledCoeffs, data, rowsToMatrix, GramSchmidt.entry, Matrix.row, Matrix.ofFn]

/-- One Bareiss update step commutes with taking the leading `K × K`
prefix: the leading prefix of the updated full matrix equals the result
of running the same step on the leading prefix. The pivot/`prevPivot`
scalars are passed through unchanged. -/
private theorem principalSubmatrix_stepMatrix_eq
    {n K : Nat} (M : Matrix Int n n) (hK : K ≤ n)
    (k : Nat) (pivot prevPivot : Int) :
    Matrix.principalSubmatrix (Matrix.stepMatrix M k pivot prevPivot) K hK =
      Matrix.stepMatrix (Matrix.principalSubmatrix M K hK) k pivot prevPivot := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let iK : Fin K := ⟨i, hi⟩
  let jK : Fin K := ⟨j, hj⟩
  let iN : Fin n := ⟨i, Nat.lt_of_lt_of_le hi hK⟩
  let jN : Fin n := ⟨j, Nat.lt_of_lt_of_le hj hK⟩
  show (Matrix.principalSubmatrix (Matrix.stepMatrix M k pivot prevPivot) K hK)[iK][jK] =
      (Matrix.stepMatrix (Matrix.principalSubmatrix M K hK) k pivot prevPivot)[iK][jK]
  simp only [Matrix.getElem_principalSubmatrix]
  show (Matrix.stepMatrix M k pivot prevPivot)[iN][jN] =
      (Matrix.stepMatrix (Matrix.principalSubmatrix M K hK) k pivot prevPivot)[iK][jK]
  by_cases htrail : k < i ∧ k < j
  · have hki_n : k < iN.val := htrail.1
    have hkj_n : k < jN.val := htrail.2
    have hki_K : k < iK.val := htrail.1
    have hkj_K : k < jK.val := htrail.2
    rw [Matrix.stepMatrix_update_eq M k pivot prevPivot iN jN hki_n hkj_n]
    rw [Matrix.stepMatrix_update_eq (Matrix.principalSubmatrix M K hK) k pivot prevPivot
      iK jK hki_K hkj_K]
    simp only [Matrix.getElem_principalSubmatrix]
    rfl
  · by_cases hbelow : k < i ∧ j = k
    · have hki_n : k < iN.val := hbelow.1
      have hjk_n : jN.val = k := hbelow.2
      have hki_K : k < iK.val := hbelow.1
      have hjk_K : jK.val = k := hbelow.2
      rw [Matrix.stepMatrix_pivot_col_below M k pivot prevPivot iN jN hki_n hjk_n]
      rw [Matrix.stepMatrix_pivot_col_below (Matrix.principalSubmatrix M K hK) k
        pivot prevPivot iK jK hki_K hjk_K]
    · have hnot_n : ¬ (k < iN.val ∧ k < jN.val) := htrail
      have hnot_n' : ¬ (k < iN.val ∧ jN.val = k) := hbelow
      have hnot_K : ¬ (k < iK.val ∧ k < jK.val) := htrail
      have hnot_K' : ¬ (k < iK.val ∧ jK.val = k) := hbelow
      rw [Matrix.stepMatrix_eq_of_not_update M k pivot prevPivot iN jN hnot_n hnot_n']
      rw [Matrix.stepMatrix_eq_of_not_update (Matrix.principalSubmatrix M K hK) k
        pivot prevPivot iK jK hnot_K hnot_K']
      simp only [Matrix.getElem_principalSubmatrix]
      rfl

/-- A bordered-minor entry equals the source matrix at the lifted index.
The lifted index for a row/column of the bordered minor is the bordered
"row"/"col" anchor when the bordered-minor coordinate hits the last
position (val = k) and the natural inclusion otherwise. -/
private theorem borderedMinor_entry_eq_source
    {n : Nat} (M : Matrix Int n n) (k : Nat) (hk : k < n) (row col : Fin n)
    (i_bm j_bm : Fin (k + 1)) :
    (Matrix.borderedMinor M k hk row col)[i_bm][j_bm] =
      M[(if h : i_bm.val < k then ⟨i_bm.val, Nat.lt_trans h hk⟩ else row)][
        (if h : j_bm.val < k then ⟨j_bm.val, Nat.lt_trans h hk⟩ else col)] := by
  by_cases hi_lt : i_bm.val < k
  · by_cases hj_lt : j_bm.val < k
    · have h := Matrix.borderedMinor_entry_lt_lt M k hk row col i_bm j_bm hi_lt hj_lt
      simp [hi_lt, hj_lt] at h ⊢
      exact h
    · have hj_eq : j_bm.val = k := by
        have := j_bm.isLt
        omega
      have hjFin : j_bm = Fin.last k := Fin.ext (by simp [hj_eq])
      have h := Matrix.borderedMinor_entry_lt_last M k hk row col i_bm hi_lt
      rw [hjFin]
      simp [hi_lt] at h ⊢
      exact h
  · have hi_eq : i_bm.val = k := by
      have := i_bm.isLt
      omega
    have hiFin : i_bm = Fin.last k := Fin.ext (by simp [hi_eq])
    by_cases hj_lt : j_bm.val < k
    · have h := Matrix.borderedMinor_entry_last_lt M k hk row col j_bm hj_lt
      rw [hiFin]
      simp [hj_lt] at h ⊢
      exact h
    · have hj_eq : j_bm.val = k := by
        have := j_bm.isLt
        omega
      have hjFin : j_bm = Fin.last k := Fin.ext (by simp [hj_eq])
      have h := Matrix.borderedMinor_entry_last_last M k hk row col
      rw [hiFin, hjFin]
      simp at h ⊢
      exact h

/-- Promote a bordered-minor coordinate to its lifted index in `Fin n`. -/
private def liftBorderedIdx {n k : Nat} (hk : k < n) (anchor : Fin n) (x : Fin (k + 1)) :
    Fin n :=
  if h : x.val < k then ⟨x.val, Nat.lt_trans h hk⟩ else anchor

private theorem liftBorderedIdx_val_lt {n k : Nat} (hk : k < n) (anchor : Fin n)
    (x : Fin (k + 1)) (h : x.val < k) :
    liftBorderedIdx hk anchor x = ⟨x.val, Nat.lt_trans h hk⟩ := by
  simp [liftBorderedIdx, h]

private theorem liftBorderedIdx_val_eq_k {n k : Nat} (hk : k < n) (anchor : Fin n)
    (x : Fin (k + 1)) (h : x.val = k) :
    liftBorderedIdx hk anchor x = anchor := by
  have : ¬ x.val < k := fun h' => Nat.lt_irrefl _ (h ▸ h')
  simp [liftBorderedIdx, this]

private theorem liftBorderedIdx_at_kStep {n k : Nat} (hk : k < n) (anchor : Fin n)
    {k_step : Nat} (hkstep : k_step < k) (hkstep_lt_n : k_step < n)
    (hkstep_lt_k1 : k_step < k + 1) :
    liftBorderedIdx hk anchor ⟨k_step, hkstep_lt_k1⟩ = ⟨k_step, hkstep_lt_n⟩ := by
  show (if h : k_step < k then (⟨k_step, Nat.lt_trans h hk⟩ : Fin n) else anchor) =
    ⟨k_step, hkstep_lt_n⟩
  simp [hkstep]

private theorem borderedMinor_entry_eq_lift
    {n : Nat} (M : Matrix Int n n) (k : Nat) (hk : k < n) (row col : Fin n)
    (i_bm j_bm : Fin (k + 1)) :
    (Matrix.borderedMinor M k hk row col)[i_bm][j_bm] =
      M[liftBorderedIdx hk row i_bm][liftBorderedIdx hk col j_bm] := by
  rw [borderedMinor_entry_eq_source M k hk row col i_bm j_bm]
  rfl

/-- One Bareiss update step commutes with taking a bordered minor whose
border row/column indices `row`, `col` lie in the trailing block: the
bordered minor of the updated full matrix equals the result of running
the same step on the bordered minor. The pivot/`prevPivot` scalars are
passed through unchanged. -/
private theorem borderedMinor_stepMatrix_eq
    {n : Nat} (M : Matrix Int n n) (k : Nat) (hk : k < n) (row col : Fin n)
    (hrow : k ≤ row.val) (hcol : k ≤ col.val)
    (k_step : Nat) (hkstep : k_step < k) (pivot prevPivot : Int) :
    Matrix.borderedMinor (Matrix.stepMatrix M k_step pivot prevPivot) k hk row col =
      Matrix.stepMatrix (Matrix.borderedMinor M k hk row col) k_step pivot prevPivot := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let i_bm : Fin (k + 1) := ⟨i, hi⟩
  let j_bm : Fin (k + 1) := ⟨j, hj⟩
  let iN : Fin n := liftBorderedIdx hk row i_bm
  let jN : Fin n := liftBorderedIdx hk col j_bm
  -- Equivalence of "in update zone" between bordered minor and source.
  have hi_iff : k_step < i_bm.val ↔ k_step < iN.val := by
    by_cases hi_lt : i_bm.val < k
    · have : iN = ⟨i_bm.val, Nat.lt_trans hi_lt hk⟩ :=
        liftBorderedIdx_val_lt hk row i_bm hi_lt
      rw [show iN.val = i_bm.val from congrArg Fin.val this]
    · have hi_eq : i_bm.val = k := by have := i_bm.isLt; omega
      have : iN = row := liftBorderedIdx_val_eq_k hk row i_bm hi_eq
      rw [show iN.val = row.val from congrArg Fin.val this, hi_eq]
      constructor
      · intro _; exact Nat.lt_of_lt_of_le hkstep hrow
      · intro _; exact hkstep
  have hj_iff : k_step < j_bm.val ↔ k_step < jN.val := by
    by_cases hj_lt : j_bm.val < k
    · have : jN = ⟨j_bm.val, Nat.lt_trans hj_lt hk⟩ :=
        liftBorderedIdx_val_lt hk col j_bm hj_lt
      rw [show jN.val = j_bm.val from congrArg Fin.val this]
    · have hj_eq : j_bm.val = k := by have := j_bm.isLt; omega
      have : jN = col := liftBorderedIdx_val_eq_k hk col j_bm hj_eq
      rw [show jN.val = col.val from congrArg Fin.val this, hj_eq]
      constructor
      · intro _; exact Nat.lt_of_lt_of_le hkstep hcol
      · intro _; exact hkstep
  have hj_eq_iff : j_bm.val = k_step ↔ jN.val = k_step := by
    by_cases hj_lt : j_bm.val < k
    · have : jN = ⟨j_bm.val, Nat.lt_trans hj_lt hk⟩ :=
        liftBorderedIdx_val_lt hk col j_bm hj_lt
      rw [show jN.val = j_bm.val from congrArg Fin.val this]
    · have hj_eq : j_bm.val = k := by have := j_bm.isLt; omega
      have : jN = col := liftBorderedIdx_val_eq_k hk col j_bm hj_eq
      rw [show jN.val = col.val from congrArg Fin.val this, hj_eq]
      constructor
      · intro h; omega
      · intro h; exact absurd h (Nat.ne_of_gt (Nat.lt_of_lt_of_le hkstep hcol))
  -- Identify: borderedMinor entry at (i_bm, j_bm) equals M entry at (iN, jN).
  have h_entry : ∀ (M' : Matrix Int n n) (r : Fin (k + 1)) (c : Fin (k + 1)),
      (Matrix.borderedMinor M' k hk row col)[r][c] =
        M'[liftBorderedIdx hk row r][liftBorderedIdx hk col c] :=
    fun M' r c => borderedMinor_entry_eq_lift M' k hk row col r c
  show (Matrix.borderedMinor (Matrix.stepMatrix M k_step pivot prevPivot) k hk row col)[i_bm][j_bm] =
       (Matrix.stepMatrix (Matrix.borderedMinor M k hk row col) k_step pivot prevPivot)[i_bm][j_bm]
  rw [h_entry (Matrix.stepMatrix M k_step pivot prevPivot) i_bm j_bm]
  -- LHS = (stepMatrix M k_step pivot prevPivot)[iN][jN].
  by_cases htrail_bm : k_step < i_bm.val ∧ k_step < j_bm.val
  · have htrail_N : k_step < iN.val ∧ k_step < jN.val :=
      ⟨hi_iff.mp htrail_bm.1, hj_iff.mp htrail_bm.2⟩
    -- Pivot column / pivot row indices in `Fin (k+1)` have val = k_step < k.
    have hkstep_lt_k1 : k_step < k + 1 := Nat.lt_succ_of_lt hkstep
    have hkstep_lt_n : k_step < n := Nat.lt_trans hkstep hk
    let colK_bm : Fin (k + 1) := ⟨k_step, hkstep_lt_k1⟩
    let colK_N : Fin n := ⟨k_step, hkstep_lt_n⟩
    have hcolK_row : liftBorderedIdx hk row colK_bm = colK_N :=
      liftBorderedIdx_at_kStep hk row hkstep hkstep_lt_n hkstep_lt_k1
    have hcolK_col : liftBorderedIdx hk col colK_bm = colK_N :=
      liftBorderedIdx_at_kStep hk col hkstep hkstep_lt_n hkstep_lt_k1
    have h_iK : (Matrix.borderedMinor M k hk row col)[i_bm][colK_bm] = M[iN][colK_N] := by
      rw [h_entry M i_bm colK_bm]
      show M[iN][liftBorderedIdx hk col colK_bm] = M[iN][colK_N]
      exact congrArg (fun (x : Fin n) => M[iN][x]) hcolK_col
    have h_Kj : (Matrix.borderedMinor M k hk row col)[colK_bm][j_bm] = M[colK_N][jN] := by
      rw [h_entry M colK_bm j_bm]
      show M[liftBorderedIdx hk row colK_bm][jN] = M[colK_N][jN]
      exact congrArg (fun (x : Fin n) => M[x][jN]) hcolK_row
    -- Compute LHS directly.
    have hLHS :
        (Matrix.stepMatrix M k_step pivot prevPivot)[iN][jN] =
          Matrix.exactDiv (pivot * M[iN][jN] -
            M[iN][colK_N] * M[colK_N][jN]) prevPivot := by
      rw [Matrix.stepMatrix_update_eq M k_step pivot prevPivot iN jN htrail_N.1 htrail_N.2]
    have hRHS :
        (Matrix.stepMatrix (Matrix.borderedMinor M k hk row col) k_step pivot prevPivot)[i_bm][j_bm] =
          Matrix.exactDiv (pivot * (Matrix.borderedMinor M k hk row col)[i_bm][j_bm] -
            (Matrix.borderedMinor M k hk row col)[i_bm][colK_bm] *
            (Matrix.borderedMinor M k hk row col)[colK_bm][j_bm]) prevPivot := by
      rw [Matrix.stepMatrix_update_eq (Matrix.borderedMinor M k hk row col) k_step pivot prevPivot
        i_bm j_bm htrail_bm.1 htrail_bm.2]
    rw [hLHS, hRHS, h_entry M i_bm j_bm, h_iK, h_Kj]
  · by_cases hbelow_bm : k_step < i_bm.val ∧ j_bm.val = k_step
    · have hi_N : k_step < iN.val := hi_iff.mp hbelow_bm.1
      have hj_N : jN.val = k_step := hj_eq_iff.mp hbelow_bm.2
      rw [Matrix.stepMatrix_pivot_col_below M k_step pivot prevPivot iN jN hi_N hj_N]
      rw [Matrix.stepMatrix_pivot_col_below (Matrix.borderedMinor M k hk row col) k_step
        pivot prevPivot i_bm j_bm hbelow_bm.1 hbelow_bm.2]
    · -- Outside the update zone on both sides.
      have hnot_trail_N : ¬ (k_step < iN.val ∧ k_step < jN.val) := by
        intro h
        exact htrail_bm ⟨hi_iff.mpr h.1, hj_iff.mpr h.2⟩
      have hnot_below_N : ¬ (k_step < iN.val ∧ jN.val = k_step) := by
        intro h
        exact hbelow_bm ⟨hi_iff.mpr h.1, hj_eq_iff.mpr h.2⟩
      rw [Matrix.stepMatrix_eq_of_not_update M k_step pivot prevPivot iN jN
        hnot_trail_N hnot_below_N]
      rw [Matrix.stepMatrix_eq_of_not_update (Matrix.borderedMinor M k hk row col) k_step
        pivot prevPivot i_bm j_bm htrail_bm hbelow_bm]
      exact (h_entry M i_bm j_bm).symm

/-- Run `noPivotLoop` on a full `n × n` matrix and on its `(k + 1) × (k + 1)`
bordered minor (whose border row/column indices `row`, `col` lie in the
trailing block) from two BareissStates that agree under the bordered
minor. While both runs are still synchronized (`fuel + state.step < k + 1`),
their bookkeeping fields agree and the full state's matrix, restricted
to the bordered minor, matches the bordered-minor state's matrix. -/
private theorem noPivotLoop_sync_borderedMinor_aux
    {n : Nat} (k : Nat) (hk : k < n) (row col : Fin n)
    (hrow : k ≤ row.val) (hcol : k ≤ col.val) (fuel : Nat) :
    ∀ (state_full : Matrix.BareissState n) (state_bm : Matrix.BareissState (k + 1)),
      state_full.step = state_bm.step →
      state_full.prevPivot = state_bm.prevPivot →
      state_full.rowSwaps = state_bm.rowSwaps →
      state_full.singularStep = state_bm.singularStep →
      Matrix.borderedMinor state_full.matrix k hk row col = state_bm.matrix →
      fuel + state_full.step < k + 1 →
      (Matrix.noPivotLoop fuel state_full).step =
          (Matrix.noPivotLoop fuel state_bm).step ∧
      (Matrix.noPivotLoop fuel state_full).prevPivot =
          (Matrix.noPivotLoop fuel state_bm).prevPivot ∧
      (Matrix.noPivotLoop fuel state_full).rowSwaps =
          (Matrix.noPivotLoop fuel state_bm).rowSwaps ∧
      (Matrix.noPivotLoop fuel state_full).singularStep =
          (Matrix.noPivotLoop fuel state_bm).singularStep ∧
      Matrix.borderedMinor (Matrix.noPivotLoop fuel state_full).matrix k hk row col =
          (Matrix.noPivotLoop fuel state_bm).matrix := by
  induction fuel with
  | zero =>
      intros state_full state_bm h_step h_prev h_rows h_sing h_mat _hfuel
      simp only [Matrix.noPivotLoop]
      exact ⟨h_step, h_prev, h_rows, h_sing, h_mat⟩
  | succ f ih =>
      intros state_full state_bm h_step h_prev h_rows h_sing h_mat hfuel
      have h_step_lt_k1 : state_full.step + 1 < k + 1 := by omega
      have h_step_lt_k : state_full.step < k := by omega
      have h_step_lt_n : state_full.step < n := Nat.lt_trans h_step_lt_k hk
      have h_full_done : state_full.step + 1 < n := by
        have hk_le : k + 1 ≤ n := Nat.succ_le_of_lt hk
        omega
      have h_bm_done : state_bm.step + 1 < k + 1 := h_step ▸ h_step_lt_k1
      have h_bm_step_lt_k : state_bm.step < k := h_step ▸ h_step_lt_k
      let k_full : Fin n := ⟨state_full.step, h_step_lt_n⟩
      let k_bm : Fin (k + 1) := ⟨state_bm.step, Nat.lt_succ_of_lt h_bm_step_lt_k⟩
      have h_k_bm_lt : k_bm.val < k := h_bm_step_lt_k
      -- Pivot entries agree because borderedMinor of full state's matrix equals bm state's matrix.
      have h_pivot_eq :
          state_full.matrix[k_full][k_full] = state_bm.matrix[k_bm][k_bm] := by
        have hcongr :
            (Matrix.borderedMinor state_full.matrix k hk row col)[k_bm][k_bm] =
              state_bm.matrix[k_bm][k_bm] := by rw [h_mat]
        have h_bm_entry :=
          Matrix.borderedMinor_entry_lt_lt state_full.matrix k hk row col k_bm k_bm
            h_k_bm_lt h_k_bm_lt
        simp only at h_bm_entry
        rw [h_bm_entry] at hcongr
        have h_idx : k_full = (⟨k_bm.val, Nat.lt_trans h_k_bm_lt hk⟩ : Fin n) :=
          Fin.ext h_step
        calc state_full.matrix[k_full][k_full]
            = state_full.matrix[(⟨k_bm.val, Nat.lt_trans h_k_bm_lt hk⟩ : Fin n)][
                (⟨k_bm.val, Nat.lt_trans h_k_bm_lt hk⟩ : Fin n)] :=
              congrArg (fun (i : Fin n) => state_full.matrix[i][i]) h_idx
          _ = state_bm.matrix[k_bm][k_bm] := hcongr
      by_cases hp_full : state_full.matrix[k_full][k_full] = 0
      · -- Singular branch on both sides.
        have hp_bm : state_bm.matrix[k_bm][k_bm] = 0 := by
          rw [← h_pivot_eq]; exact hp_full
        rw [Matrix.noPivotLoop_singular_branch f state_full h_full_done hp_full,
          Matrix.noPivotLoop_singular_branch f state_bm h_bm_done hp_bm]
        refine ⟨h_step, h_prev, h_rows, ?_, h_mat⟩
        simp [h_step]
      · -- Regular branch on both sides; apply IH to the updated states.
        have hp_bm : state_bm.matrix[k_bm][k_bm] ≠ 0 := by
          rw [← h_pivot_eq]; exact hp_full
        rw [Matrix.noPivotLoop_regular_branch f state_full h_full_done hp_full,
          Matrix.noPivotLoop_regular_branch f state_bm h_bm_done hp_bm]
        have h_new_mat :
            Matrix.borderedMinor
              (Matrix.stepMatrix state_full.matrix state_full.step
                state_full.matrix[k_full][k_full] state_full.prevPivot) k hk row col =
              Matrix.stepMatrix state_bm.matrix state_bm.step
                state_bm.matrix[k_bm][k_bm] state_bm.prevPivot := by
          rw [borderedMinor_stepMatrix_eq state_full.matrix k hk row col hrow hcol
              state_full.step h_step_lt_k state_full.matrix[k_full][k_full]
              state_full.prevPivot, h_mat, h_step, h_prev, h_pivot_eq]
        apply ih
        · -- step
          simp [h_step]
        · -- prevPivot
          exact h_pivot_eq
        · -- rowSwaps
          exact h_rows
        · -- singularStep
          rfl
        · -- matrix
          exact h_new_mat
        · -- fuel
          simp; omega

/-- The `(row, col)` entry of the noPivot Bareiss state after `k` iterations on
the full `n × n` matrix agrees with the `(Fin.last k, Fin.last k)` entry of the
noPivot Bareiss state after `k` iterations on the `(k + 1) × (k + 1)` bordered
minor at `row, col`. The `singularStep` bookkeeping also agrees, mirroring the
leading-prefix sync corollary. Requires `row, col` to lie in the trailing block. -/
theorem noPivotLoop_full_eq_borderedMinor_at_trailing
    {n : Nat} (M : Matrix Int n n) (k : Nat) (hk : k < n) (row col : Fin n)
    (hrow : k ≤ row.val) (hcol : k ≤ col.val) :
    let BM := Matrix.borderedMinor M k hk row col
    let s_full := Matrix.noPivotLoop k (Matrix.noPivotInitialState M)
    let s_bm := Matrix.noPivotLoop k (Matrix.noPivotInitialState BM)
    s_full.matrix[row][col] = s_bm.matrix[Fin.last k][Fin.last k] ∧
      s_full.singularStep = s_bm.singularStep := by
  intro BM s_full s_bm
  have h_sync :=
    noPivotLoop_sync_borderedMinor_aux k hk row col hrow hcol k
      (Matrix.noPivotInitialState M) (Matrix.noPivotInitialState BM)
      rfl rfl rfl rfl rfl
      (show k + (Matrix.noPivotInitialState M).step < k + 1 by
        simp [Matrix.noPivotInitialState])
  obtain ⟨_, _, _, h_sing, h_mat⟩ := h_sync
  refine ⟨?_, h_sing⟩
  -- The (row, col) entry of s_full.matrix is the (Fin.last k, Fin.last k) entry of
  -- (borderedMinor s_full.matrix k hk row col), which equals s_bm.matrix by `h_mat`.
  have hcongr :
      (Matrix.borderedMinor s_full.matrix k hk row col)[Fin.last k][Fin.last k] =
        s_bm.matrix[Fin.last k][Fin.last k] := by rw [h_mat]
  rw [Matrix.borderedMinor_entry_last_last] at hcongr
  exact hcongr

/-- The step field of a no-pivot Bareiss state advances by at most `fuel` after
`fuel` loop iterations. Combined with `noPivotLoop_step_monotone`, this brackets
the resulting step between the starting step and the starting step plus the
fuel. -/
private theorem noPivotLoop_step_le_add
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n) :
    (Matrix.noPivotLoop fuel state).step ≤ state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      show state.step ≤ state.step + 0
      omega
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
          show state.step ≤ state.step + (f + 1)
          omega
        · rw [Matrix.noPivotLoop_regular_branch f state hDone hp]
          calc (Matrix.noPivotLoop f
              { step := state.step + 1
                matrix := Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none }).step
              ≤ state.step + 1 + f := ih _
            _ = state.step + (f + 1) := by omega
      · rw [Matrix.noPivotLoop_done f state hDone]
        show state.step ≤ state.step + (f + 1)
        omega

/-- Trailing-block symmetry is preserved by the no-pivot Bareiss loop: if the
input state's matrix is symmetric at indices at or beyond `state.step`, then the
resulting state's matrix is symmetric at indices at or beyond its `step`. The
abstract version takes only the input symmetry hypothesis; the diagonal Bareiss
update commutes through symmetry because the trailing block remains symmetric
after each `stepMatrix` application. -/
private theorem noPivotLoop_matrix_symm_preserve
    {n : Nat} (fuel : Nat) :
    ∀ (state : Matrix.BareissState n),
      (∀ a b : Fin n, state.step ≤ a.val → state.step ≤ b.val →
        state.matrix[a][b] = state.matrix[b][a]) →
      ∀ (a b : Fin n),
        (Matrix.noPivotLoop fuel state).step ≤ a.val →
        (Matrix.noPivotLoop fuel state).step ≤ b.val →
        (Matrix.noPivotLoop fuel state).matrix[a][b] =
          (Matrix.noPivotLoop fuel state).matrix[b][a] := by
  induction fuel with
  | zero =>
      intros state h_sym a b ha hb
      change state.matrix[a][b] = state.matrix[b][a]
      change state.step ≤ a.val at ha
      change state.step ≤ b.val at hb
      exact h_sym a b ha hb
  | succ f ih =>
      intros state h_sym a b ha hb
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · -- Singular branch: result is `{state with singularStep := some state.step}`.
          rw [Matrix.noPivotLoop_singular_branch f state hDone hp] at ha hb ⊢
          change state.matrix[a][b] = state.matrix[b][a]
          change state.step ≤ a.val at ha
          change state.step ≤ b.val at hb
          exact h_sym a b ha hb
        · -- Regular branch: recurse on the updated state with step + 1.
          rw [Matrix.noPivotLoop_regular_branch f state hDone hp] at ha hb ⊢
          let kFin : Fin n := ⟨state.step, Nat.lt_of_succ_lt hDone⟩
          have h_sym_new : ∀ (a' b' : Fin n),
              state.step + 1 ≤ a'.val → state.step + 1 ≤ b'.val →
              (Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot)[a'][b']
                = (Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot)[b'][a'] := by
            intros a' b' ha' hb'
            have ha'_lt : state.step < a'.val := ha'
            have hb'_lt : state.step < b'.val := hb'
            rw [Matrix.stepMatrix_update_eq state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot a' b' ha'_lt hb'_lt]
            rw [Matrix.stepMatrix_update_eq state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot b' a' hb'_lt ha'_lt]
            -- Both sides reduce to `exactDiv` of similar expressions. Identify
            -- the two `Fin n` indices at value `state.step` and use the
            -- trailing-block symmetry of `state.matrix`.
            have h_ab : state.matrix[a'][b'] = state.matrix[b'][a'] :=
              h_sym a' b' (Nat.le_of_lt ha'_lt) (Nat.le_of_lt hb'_lt)
            have h_ak : state.matrix[a'][kFin] = state.matrix[kFin][a'] :=
              h_sym a' kFin (Nat.le_of_lt ha'_lt) (Nat.le_refl _)
            have h_bk : state.matrix[b'][kFin] = state.matrix[kFin][b'] :=
              h_sym b' kFin (Nat.le_of_lt hb'_lt) (Nat.le_refl _)
            -- The two `Fin n` indices in the unfolded `stepMatrix_update_eq`
            -- have value `state.step` and so equal `kFin` definitionally.
            change Matrix.exactDiv (_ * state.matrix[a'][b']
                - state.matrix[a'][kFin] * state.matrix[kFin][b']) _
              = Matrix.exactDiv (_ * state.matrix[b'][a']
                - state.matrix[b'][kFin] * state.matrix[kFin][a']) _
            rw [h_ab, h_ak, h_bk]
            congr 1
            grind
          exact ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
            (by
              intros a' b' ha' hb'
              exact h_sym_new a' b' ha' hb')
            a b ha hb
      · -- Boundary case: `noPivotLoop` returns the input state unchanged.
        rw [Matrix.noPivotLoop_done f state hDone] at ha hb ⊢
        change state.matrix[a][b] = state.matrix[b][a]
        change state.step ≤ a.val at ha
        change state.step ≤ b.val at hb
        exact h_sym a b ha hb

/-- Identification of Bareiss-style trailing values across two bordered minors
of a symmetric matrix obtained by swapping the border row and column. Composed from
`noPivotLoop_full_eq_borderedMinor_at_trailing` (applied at both swapped
positions) and `noPivotLoop_matrix_symm_preserve` (which transports the
trailing-block symmetry of the input through the loop). -/
private theorem noPivotLoop_borderedMinor_swap_at_trailing
    {n : Nat} (M : Matrix Int n n)
    (h_sym : ∀ a b : Fin n, M[a][b] = M[b][a])
    (k : Nat) (hk : k < n) (i j : Fin n)
    (hki : k ≤ i.val) (hkj : k ≤ j.val) :
    (Matrix.noPivotLoop k (Matrix.noPivotInitialState
        (Matrix.borderedMinor M k hk i j))).matrix[Fin.last k][Fin.last k] =
    (Matrix.noPivotLoop k (Matrix.noPivotInitialState
        (Matrix.borderedMinor M k hk j i))).matrix[Fin.last k][Fin.last k] := by
  -- Reduce both sides through the full-matrix sync at swapped border positions.
  have h_ij :=
    (noPivotLoop_full_eq_borderedMinor_at_trailing M k hk i j hki hkj).1
  have h_ji :=
    (noPivotLoop_full_eq_borderedMinor_at_trailing M k hk j i hkj hki).1
  rw [← h_ij, ← h_ji]
  -- Reduce to symmetry of the full-matrix noPivotLoop at `(i, j)` vs `(j, i)`.
  -- Both indices are bounded below by `k`, and the loop's resulting step is at
  -- most `0 + k = k`, hence at most each of `i.val`, `j.val`.
  have h_step_le := noPivotLoop_step_le_add k (Matrix.noPivotInitialState M)
  have h_step0 : (Matrix.noPivotInitialState M).step = 0 := rfl
  have h_step_bound :
      (Matrix.noPivotLoop k (Matrix.noPivotInitialState M)).step ≤ k := by
    rw [h_step0] at h_step_le
    simpa using h_step_le
  have h_init_sym :
      ∀ a b : Fin n, (Matrix.noPivotInitialState M).step ≤ a.val →
        (Matrix.noPivotInitialState M).step ≤ b.val →
        (Matrix.noPivotInitialState M).matrix[a][b] =
          (Matrix.noPivotInitialState M).matrix[b][a] := by
    intros a b _ _
    exact h_sym a b
  exact noPivotLoop_matrix_symm_preserve k
    (Matrix.noPivotInitialState M) h_init_sym i j
    (Nat.le_trans h_step_bound hki) (Nat.le_trans h_step_bound hkj)

/-- Run `noPivotLoop` on a full `n × n` matrix and on its `K × K` leading
prefix from two BareissStates that agree on the leading prefix. While
both runs are still synchronized (fuel fits within `K - state.step`),
their bookkeeping fields agree and the full state's matrix, restricted
to the leading prefix, matches the prefix state's matrix. -/
private theorem noPivotLoop_sync_principalSubmatrix_aux
    {n K : Nat} (hK : K ≤ n) (fuel : Nat) :
    ∀ (state_full : Matrix.BareissState n) (state_pref : Matrix.BareissState K),
      state_full.step = state_pref.step →
      state_full.prevPivot = state_pref.prevPivot →
      state_full.rowSwaps = state_pref.rowSwaps →
      state_full.singularStep = state_pref.singularStep →
      Matrix.principalSubmatrix state_full.matrix K hK = state_pref.matrix →
      fuel + state_full.step < K →
      (Matrix.noPivotLoop fuel state_full).step =
          (Matrix.noPivotLoop fuel state_pref).step ∧
      (Matrix.noPivotLoop fuel state_full).prevPivot =
          (Matrix.noPivotLoop fuel state_pref).prevPivot ∧
      (Matrix.noPivotLoop fuel state_full).rowSwaps =
          (Matrix.noPivotLoop fuel state_pref).rowSwaps ∧
      (Matrix.noPivotLoop fuel state_full).singularStep =
          (Matrix.noPivotLoop fuel state_pref).singularStep ∧
      Matrix.principalSubmatrix (Matrix.noPivotLoop fuel state_full).matrix K hK =
          (Matrix.noPivotLoop fuel state_pref).matrix := by
  induction fuel with
  | zero =>
      intros state_full state_pref h_step h_prev h_rows h_sing h_mat _hfuel
      simp only [Matrix.noPivotLoop]
      exact ⟨h_step, h_prev, h_rows, h_sing, h_mat⟩
  | succ f ih =>
      intros state_full state_pref h_step h_prev h_rows h_sing h_mat hfuel
      have h_step_lt_K : state_full.step + 1 < K := by omega
      have h_full_done : state_full.step + 1 < n :=
        Nat.lt_of_lt_of_le h_step_lt_K hK
      have h_pref_done : state_pref.step + 1 < K := h_step ▸ h_step_lt_K
      have h_step_lt_n : state_full.step < n := Nat.lt_of_succ_lt h_full_done
      have h_step_lt_K_strict : state_full.step < K :=
        Nat.lt_of_succ_lt h_step_lt_K
      have h_pref_step_lt_K : state_pref.step < K := h_step ▸ h_step_lt_K_strict
      let k_full : Fin n := ⟨state_full.step, h_step_lt_n⟩
      let k_pref : Fin K := ⟨state_pref.step, h_pref_step_lt_K⟩
      let k_full' : Fin K := ⟨state_full.step, h_step_lt_K_strict⟩
      -- The pivot entries agree on both sides because the full state's
      -- matrix, restricted to the leading prefix, equals the prefix state's
      -- matrix.
      have h_k_eq : k_full' = k_pref := Fin.ext h_step
      have h_pivot_eq : state_full.matrix[k_full][k_full] =
          state_pref.matrix[k_pref][k_pref] := by
        have hcongr := congrArg (fun (M : Matrix Int K K) => M[k_pref][k_pref]) h_mat
        simp only [Matrix.getElem_principalSubmatrix] at hcongr
        -- hcongr : state_full.matrix[⟨k_pref.val, _⟩][⟨k_pref.val, _⟩] =
        --          state_pref.matrix[k_pref][k_pref]
        -- k_full.val = state_full.step = state_pref.step = k_pref.val (by h_step),
        -- so as Fin n elements they coincide. Use congrArg on the diagonal
        -- entry as a function of Fin n to close the gap.
        have h_idx :
            k_full = (⟨k_pref.val, Nat.lt_of_lt_of_le k_pref.isLt hK⟩ : Fin n) :=
          Fin.ext h_step
        have h_diag :
            state_full.matrix[k_full][k_full] =
              state_full.matrix[(⟨k_pref.val, Nat.lt_of_lt_of_le k_pref.isLt hK⟩ : Fin n)][(⟨k_pref.val, Nat.lt_of_lt_of_le k_pref.isLt hK⟩ : Fin n)] :=
          congrArg (fun (i : Fin n) => state_full.matrix[i][i]) h_idx
        exact h_diag.trans hcongr
      by_cases hp_full : state_full.matrix[k_full][k_full] = 0
      · -- Singular branch on both sides.
        have hp_pref : state_pref.matrix[k_pref][k_pref] = 0 := by
          rw [← h_pivot_eq]; exact hp_full
        rw [Matrix.noPivotLoop_singular_branch f state_full h_full_done hp_full,
          Matrix.noPivotLoop_singular_branch f state_pref h_pref_done hp_pref]
        refine ⟨h_step, h_prev, h_rows, ?_, h_mat⟩
        simp [h_step]
      · -- Regular branch on both sides; apply IH to the updated states.
        have hp_pref : state_pref.matrix[k_pref][k_pref] ≠ 0 := by
          rw [← h_pivot_eq]; exact hp_full
        rw [Matrix.noPivotLoop_regular_branch f state_full h_full_done hp_full,
          Matrix.noPivotLoop_regular_branch f state_pref h_pref_done hp_pref]
        -- After one step, the new states are still linked.
        have h_new_mat :
            Matrix.principalSubmatrix
              (Matrix.stepMatrix state_full.matrix state_full.step
                state_full.matrix[k_full][k_full] state_full.prevPivot) K hK =
              Matrix.stepMatrix state_pref.matrix state_pref.step
                state_pref.matrix[k_pref][k_pref] state_pref.prevPivot := by
          rw [principalSubmatrix_stepMatrix_eq, h_mat, h_step, h_prev, h_pivot_eq]
        apply ih
        · -- step
          simp [h_step]
        · -- prevPivot
          exact h_pivot_eq
        · -- rowSwaps
          exact h_rows
        · -- singularStep
          rfl
        · -- matrix
          exact h_new_mat
        · -- fuel
          simp; omega

/-- Once the no-pivot Bareiss loop has reached the boundary
(`state.step + 1 ≥ n`), any further fuel is a no-op. -/
private theorem noPivotLoop_id_at_done
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (hDone : ¬ state.step + 1 < n) :
    Matrix.noPivotLoop fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ f _ih => exact Matrix.noPivotLoop_done f state hDone

/-- Once the no-pivot Bareiss loop has marked the current step singular
(`state.singularStep = some state.step` with a zero pivot at that step),
any further fuel is a no-op. -/
theorem noPivotLoop_id_at_singular_fixedpoint
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0)
    (hsing : state.singularStep = some state.step) :
    Matrix.noPivotLoop fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ f _ih =>
      rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
      -- Goal: {state with singularStep := some state.step} = state.
      cases state with
      | mk step matrix prevPivot rowSwaps singularStep =>
        simp only at hsing
        subst hsing
        rfl

/-- Fuel composition for the no-pivot Bareiss loop: running `a + b` units of
fuel from `state` equals running `b` more units after `a` initial units. -/
theorem noPivotLoop_add
    {n : Nat} (a b : Nat) (state : Matrix.BareissState n) :
    Matrix.noPivotLoop (a + b) state =
      Matrix.noPivotLoop b (Matrix.noPivotLoop a state) := by
  induction a generalizing state with
  | zero =>
      show Matrix.noPivotLoop (0 + b) state = Matrix.noPivotLoop b state
      simp
  | succ a' ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · -- Singular: both sides collapse to `{state with singularStep := some state.step}`.
          have h_lhs :
              Matrix.noPivotLoop (a' + 1 + b) state =
                {state with singularStep := some state.step} := by
            have : a' + 1 + b = (a' + b) + 1 := by omega
            rw [this]
            exact Matrix.noPivotLoop_singular_branch (a' + b) state hDone hp
          have h_rhs_inner :
              Matrix.noPivotLoop (a' + 1) state =
                {state with singularStep := some state.step} :=
            Matrix.noPivotLoop_singular_branch a' state hDone hp
          rw [h_lhs, h_rhs_inner]
          symm
          -- Now show: noPivotLoop b {state with singularStep := some state.step} = that.
          let s' : Matrix.BareissState n :=
            {state with singularStep := some state.step}
          have hDone_s' : s'.step + 1 < n := hDone
          have hp_s' : s'.matrix[(⟨s'.step, Nat.lt_of_succ_lt hDone_s'⟩ : Fin n)][(⟨s'.step, Nat.lt_of_succ_lt hDone_s'⟩ : Fin n)] = 0 := hp
          have hsing_s' : s'.singularStep = some s'.step := rfl
          exact noPivotLoop_id_at_singular_fixedpoint b s' hDone_s' hp_s' hsing_s'
        · -- Regular: both sides do one step then recurse on `next`.
          have h_lhs :
              Matrix.noPivotLoop (a' + 1 + b) state =
                Matrix.noPivotLoop (a' + b)
                  { step := state.step + 1
                    matrix := Matrix.stepMatrix state.matrix state.step
                      state.matrix[k][k] state.prevPivot
                    prevPivot := state.matrix[k][k]
                    rowSwaps := state.rowSwaps
                    singularStep := none } := by
            have : a' + 1 + b = (a' + b) + 1 := by omega
            rw [this]
            exact Matrix.noPivotLoop_regular_branch (a' + b) state hDone hp
          have h_rhs_inner :
              Matrix.noPivotLoop (a' + 1) state =
                Matrix.noPivotLoop a'
                  { step := state.step + 1
                    matrix := Matrix.stepMatrix state.matrix state.step
                      state.matrix[k][k] state.prevPivot
                    prevPivot := state.matrix[k][k]
                    rowSwaps := state.rowSwaps
                    singularStep := none } :=
            Matrix.noPivotLoop_regular_branch a' state hDone hp
          rw [h_lhs, h_rhs_inner]
          exact ih _
      · -- Boundary: both sides return `state` unchanged.
        rw [noPivotLoop_id_at_done (a' + 1 + b) state hDone,
          noPivotLoop_id_at_done (a' + 1) state hDone]
        exact (noPivotLoop_id_at_done b state hDone).symm

/-- After running `noPivotLoop` from a state without a recorded singular
step, the result has either no singular step, or it has a singular step
that matches the current `step` field together with a zero pivot at that
position. -/
theorem noPivotLoop_singular_inv
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none) :
    (Matrix.noPivotLoop fuel state).singularStep = none ∨
    ∃ k : Fin n,
      (Matrix.noPivotLoop fuel state).singularStep = some k.val ∧
      (Matrix.noPivotLoop fuel state).step = k.val ∧
      (Matrix.noPivotLoop fuel state).matrix[k][k] = 0 ∧
      k.val + 1 < n := by
  induction fuel generalizing state with
  | zero =>
      left
      change state.singularStep = none
      exact h_init
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n := ⟨state.step, Nat.lt_of_succ_lt hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · -- Singular branch: result = {state with singularStep := some state.step}.
          right
          refine ⟨k, ?_, ?_, ?_, hDone⟩
          · rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
          · rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
          · rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
            exact hp
        · -- Regular branch
          rw [Matrix.noPivotLoop_regular_branch f state hDone hp]
          exact ih _ rfl
      · -- Boundary
        rw [Matrix.noPivotLoop_done f state hDone]
        left; exact h_init

/-- When the no-pivot Bareiss loop starts from a non-singular state and records
a singular step within `fuel` iterations, the recorded singular index is
strictly bounded by the initial step plus the fuel. The singular branch sets
`singularStep := some state.step` at the trigger iteration, and `state.step`
advances by at most one per regular iteration; with `fuel` iterations available
and at least one used for the singular trigger, the recorded index is `< start
+ fuel`. -/
theorem noPivotLoop_singularStep_lt
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none)
    (s : Nat)
    (h_sing : (Matrix.noPivotLoop fuel state).singularStep = some s) :
    s < state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      rw [Matrix.noPivotLoop_zero_fuel, h_init] at h_sing
      nomatch h_sing
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_singular_branch f state hDone hp] at h_sing
          simp at h_sing
          omega
        · rw [Matrix.noPivotLoop_regular_branch f state hDone hp] at h_sing
          have h_ih := ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
            rfl h_sing
          change s < state.step + 1 + f at h_ih
          show s < state.step + (f + 1)
          omega
      · rw [Matrix.noPivotLoop_done f state hDone] at h_sing
        rw [h_init] at h_sing
        nomatch h_sing

/-- After running `fuel` iterations of `Matrix.noPivotLoop` from a state with
no recorded singular step, if the result also has no recorded singular step
and the loop had at least `fuel + 1` steps of room from its starting step,
then the result's step is the starting step plus `fuel`. -/
private theorem noPivotLoop_step_eq_add_of_singularStep_none
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none)
    (h_room : state.step + fuel + 1 ≤ n)
    (h_no_sing : (Matrix.noPivotLoop fuel state).singularStep = none) :
    (Matrix.noPivotLoop fuel state).step = state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      show state.step = state.step + 0
      omega
  | succ f ih =>
      have hDone : state.step + 1 < n := by omega
      by_cases hp : state.matrix[state.step][state.step] = 0
      · rw [Matrix.noPivotLoop_singular_branch f state hDone hp] at h_no_sing
        simp at h_no_sing
      · rw [Matrix.noPivotLoop_regular_branch f state hDone hp] at h_no_sing
        rw [Matrix.noPivotLoop_regular_branch f state hDone hp]
        have h_next_room : state.step + 1 + f + 1 ≤ n := by omega
        have h_next_step := ih
          { step := state.step + 1
            matrix := Matrix.stepMatrix state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot
            prevPivot := state.matrix[state.step][state.step]
            rowSwaps := state.rowSwaps
            singularStep := none }
          rfl h_next_room h_no_sing
        rw [h_next_step]
        show state.step + 1 + f = state.step + (f + 1)
        omega

/-- A no-pivot Bareiss pass that never records a singular step preserves the
nonzero status of the previous pivot. Regular branches replace `prevPivot` by
the current nonzero pivot; singular branches contradict the final
`singularStep = none` hypothesis. -/
private theorem noPivotLoop_prevPivot_ne_zero
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (hprev : state.prevPivot ≠ 0)
    (h_no_sing : (Matrix.noPivotLoop fuel state).singularStep = none) :
    (Matrix.noPivotLoop fuel state).prevPivot ≠ 0 := by
  induction fuel generalizing state with
  | zero =>
      simpa [Matrix.noPivotLoop_zero_fuel] using hprev
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_singular_branch f state hDone hp] at h_no_sing
          simp at h_no_sing
        · rw [Matrix.noPivotLoop_regular_branch f state hDone hp] at h_no_sing
          rw [Matrix.noPivotLoop_regular_branch f state hDone hp]
          exact ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
            hp h_no_sing
      · rw [Matrix.noPivotLoop_done f state hDone] at h_no_sing ⊢
        exact hprev

/-- The `step` field of a no-pivot Bareiss state never decreases under further
loop iterations. -/
theorem noPivotLoop_step_monotone
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n) :
    state.step ≤ (Matrix.noPivotLoop fuel state).step := by
  induction fuel generalizing state with
  | zero =>
      show state.step ≤ state.step
      omega
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · have hStepLt : state.step < n := Nat.lt_of_succ_lt hDone
        by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
          show state.step ≤ state.step
          omega
        · rw [Matrix.noPivotLoop_regular_branch f state hDone hp]
          have h_ih := ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
          -- h_ih says state.step + 1 ≤ (noPivotLoop f next).step
          -- Want: state.step ≤ (noPivotLoop f next).step
          exact Nat.le_trans (Nat.le_succ _) h_ih
      · rw [Matrix.noPivotLoop_done f state hDone]
        show state.step ≤ state.step
        omega

/-- A singular step recorded by an initial no-pivot prefix remains the recorded
singular step after any further no-pivot iterations. -/
private theorem noPivotLoop_singularStep
    {n : Nat} (a b : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none) {s : Nat}
    (h_prefix : (Matrix.noPivotLoop a state).singularStep = some s) :
    (Matrix.noPivotLoop (a + b) state).singularStep = some s := by
  rw [noPivotLoop_add a b state]
  rcases noPivotLoop_singular_inv (n := n) a state h_init with h_none |
      ⟨k, h_sing, h_step, h_zero, h_bound⟩
  · rw [h_none] at h_prefix
    nomatch h_prefix
  · have hs : s = k.val := by
      rw [h_sing] at h_prefix
      injection h_prefix with h
      exact h.symm
    have hDone :
        (Matrix.noPivotLoop a state).step + 1 < n := by
      rw [h_step]
      exact h_bound
    have hidx :
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n) = k :=
      Fin.ext h_step
    have hp :
        (Matrix.noPivotLoop a state).matrix[
            (⟨(Matrix.noPivotLoop a state).step,
              Nat.lt_of_succ_lt hDone⟩ : Fin n)][
            (⟨(Matrix.noPivotLoop a state).step,
              Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0 := by
      have h_lift := congrArg
        (fun (idx : Fin n) => (Matrix.noPivotLoop a state).matrix[idx][idx])
        hidx
      exact h_lift.trans h_zero
    have hsing_state :
        (Matrix.noPivotLoop a state).singularStep =
          some (Matrix.noPivotLoop a state).step := by
      rw [h_sing, h_step]
    rw [noPivotLoop_id_at_singular_fixedpoint b _ hDone hp hsing_state, hs]
    exact h_sing

/-- If a full no-pivot run has no singular step, every initial prefix run also
has no singular step. -/
private theorem noPivotLoop_prefix_none_of_final_none
    {n : Nat} (a b : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none)
    (h_final : (Matrix.noPivotLoop (a + b) state).singularStep = none) :
    (Matrix.noPivotLoop a state).singularStep = none := by
  rcases noPivotLoop_singular_inv (n := n) a state h_init with h_none |
      ⟨k, h_sing, _h_step, _h_zero, _h_bound⟩
  · exact h_none
  · have h_persist :=
      noPivotLoop_singularStep a b state h_init h_sing
    rw [h_final] at h_persist
    nomatch h_persist

/-- If the full run records its first singular step after `a`, then the prefix
of length `a` is non-singular. -/
private theorem noPivotLoop_prefix_none_of_final_singular_after
    {n : Nat} (a b : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none) {s : Nat}
    (h_final : (Matrix.noPivotLoop (a + b) state).singularStep = some s)
    (hs_after : state.step + a ≤ s) :
    (Matrix.noPivotLoop a state).singularStep = none := by
  rcases noPivotLoop_singular_inv (n := n) a state h_init with h_none |
      ⟨k, h_sing, _h_step, _h_zero, _h_bound⟩
  · exact h_none
  · have h_persist :=
      noPivotLoop_singularStep a b state h_init h_sing
    rw [h_final] at h_persist
    injection h_persist with hks
    have hk_lt : k.val < state.step + a :=
      noPivotLoop_singularStep_lt a state h_init k.val h_sing
    omega

/-- No-pivot Bareiss projection at the `gramDetVecEntry` diagonal slot:
running `Matrix.noPivotLoop r` from the initial state on the full Gram
matrix and on its `(r+1)`-leading prefix yields states whose `(r, r)`
diagonal entry agrees (after the leading-prefix identification) and
whose `singularStep` field agrees. This is the executable-loop
projection needed by the parent assembly of
`gramDetVecEntry_eq_principalSubmatrix_bareiss`. -/
private theorem noPivotLoop_full_eq
    (b : Matrix Int n m) (r : Nat) (hr : r < n) :
    let GM := Matrix.gramMatrix b
    let hK : r + 1 ≤ n := Nat.succ_le_of_lt hr
    let LP := Matrix.principalSubmatrix GM (r + 1) hK
    let s_full := Matrix.noPivotLoop r (Matrix.noPivotInitialState GM)
    let s_pref := Matrix.noPivotLoop r (Matrix.noPivotInitialState LP)
    s_full.matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
        s_pref.matrix[(⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))][(⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))]
      ∧ s_full.singularStep = s_pref.singularStep := by
  intro GM hK LP s_full s_pref
  have h_sync := noPivotLoop_sync_principalSubmatrix_aux hK r
    (Matrix.noPivotInitialState GM) (Matrix.noPivotInitialState LP)
    rfl rfl rfl rfl rfl
    (show r + (Matrix.noPivotInitialState GM).step < r + 1 by
      simp [Matrix.noPivotInitialState])
  obtain ⟨_, _, _, h_sing, h_mat⟩ := h_sync
  refine ⟨?_, h_sing⟩
  -- Diagonal: the (r, r) entry of s_full agrees with the (r, r) entry of s_pref via the
  -- leading-prefix identification.
  have hcongr := congrArg
    (fun (M : Matrix Int (r + 1) (r + 1)) =>
      M[(⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))][(⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))])
    h_mat
  simp only [Matrix.getElem_principalSubmatrix] at hcongr
  -- hcongr's LHS index in Fin n has val = r; same as the goal's LHS index.
  exact hcongr

/-- Signed diagonal projection for a non-singular target prefix: the final
no-pivot full-Gram diagonal at `r` is the public Bareiss determinant of the
`(r + 1)` leading prefix. -/
theorem bareissNoPivotData_diag_eq_principalSubmatrix_bareiss_of_prefix_nonsingular
    (b : Matrix Int n m) (r : Nat) (hr : r < n)
    (h_nonsing :
      (Matrix.noPivotLoop r
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[
        (⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
      Matrix.bareiss
        (Matrix.principalSubmatrix (Matrix.gramMatrix b) (r + 1)
          (Nat.succ_le_of_lt hr)) := by
  let GM := Matrix.gramMatrix b
  let init := Matrix.noPivotInitialState GM
  let fullAtR := Matrix.noPivotLoop r init
  let LP := Matrix.principalSubmatrix GM (r + 1) (Nat.succ_le_of_lt hr)
  have h_step_r : fullAtR.step = r := by
    have h_room : init.step + r + 1 ≤ n := by
      simp [init, Matrix.noPivotInitialState]
      omega
    have h := noPivotLoop_step_eq_add_of_singularStep_none r init rfl h_room h_nonsing
    simpa [fullAtR, init, Matrix.noPivotInitialState] using h
  have h_factor :
      Matrix.noPivotLoop n init = Matrix.noPivotLoop (n - r) fullAtR := by
    have h_add := noPivotLoop_add r (n - r) init
    have h_split : r + (n - r) = n := by omega
    simpa [fullAtR, h_split] using h_add
  have h_final_diag :
      (Matrix.noPivotLoop n init).matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
        fullAtR.matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] := by
    rw [h_factor]
    have h_le : (⟨r, hr⟩ : Fin n).val ≤ fullAtR.step := by
      change r ≤ fullAtR.step
      rw [h_step_r]
      exact Nat.le_refl r
    exact Matrix.noPivotLoop_diag_of_le_step (n - r) fullAtR (⟨r, hr⟩ : Fin n) h_le
  obtain ⟨h_diag, h_sing⟩ :=
    noPivotLoop_full_eq (b := b) r hr
  have h_pref_nonsing :
      (Matrix.noPivotLoop r (Matrix.noPivotInitialState LP)).singularStep = none := by
    rw [← h_sing]
    exact h_nonsing
  have h_bareiss :=
    Matrix.bareiss_eq_noPivotLoop_last_of_no_singular (M := LP) h_pref_nonsing
  calc
    (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[
        (⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
        fullAtR.matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] := by
          simpa [Matrix.bareissNoPivotData, Matrix.finish, GM, init, fullAtR] using
            h_final_diag
    _ =
        (Matrix.noPivotLoop r (Matrix.noPivotInitialState LP)).matrix[
          (⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))][
          (⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))] := by
          exact h_diag
    _ = Matrix.bareiss LP := by
          simpa [LP, Fin.last] using h_bareiss.symm

end GramSchmidt.Int
end Hex
