import HexGramSchmidtMathlib.Int
import HexGramSchmidt.Update

/-!
Bridge-bound row-operation update theorems for `hex-gram-schmidt`.

The theorems in this module relate `gramDet` / `scaledCoeffs` under the
size-reduce (earlier-row-add) and adjacent-swap row operations. Their
statements are Hex-local, but their proofs cross the Mathlib boundary by
composing `HexMatrixMathlib.bareiss_eq_mathlib_det` with
`HexMatrixMathlib.det_eq.symm` through `gramDet_rowAdd_earlier` and the
matrix-side `gramDet_adjacentSwap_of_ne` bridge respectively, so they live
in the bridge layer per [SPEC/Libraries/hex-gram-schmidt.md "Proof path
governs placement, not just statement"]. The size-reduce theorems are thin
wrappers around `scaledCoeffs_rowAdd_pivot/lower/other_row/above_pivot` and
`gramDet_rowAdd_earlier`, which live in `HexGramSchmidtMathlib/Int.lean`.
-/

namespace Hex

namespace GramSchmidt.Int

/-! ### Size-reduce updates

`GramSchmidt.Int.sizeReduce b j k r` is `Matrix.rowAdd b j k (-r)` (definitional),
so the theorems below specialise the earlier-row-add updates in
`HexGramSchmidt/Int.lean` to the LLL size-reduce row operation. They are kept
in this bridge module because their proof path composes
`HexMatrixMathlib.bareiss_eq_mathlib_det` with
`HexMatrixMathlib.det_eq.symm`. -/

theorem gramDet_sizeReduce (b : Matrix Int n m) (j k : Fin n) (hjk : j.val < k.val)
    (r : Int) (t : Nat) (ht : t ≤ n) :
    gramDet (sizeReduce b j k r) t ht = gramDet b t ht := by
  unfold sizeReduce
  exact gramDet_rowAdd_earlier b j k (-r) t ht hjk

theorem scaledCoeffs_sizeReduce_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (r : Int) :
    GramSchmidt.entry (scaledCoeffs (sizeReduce b j k r)) k j =
      GramSchmidt.entry (scaledCoeffs b) k j -
        r * Int.ofNat (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
  rw [sizeReduce]
  rw [scaledCoeffs_rowAdd_pivot (b := b) (j := j) (k := k) hjk (-r)]
  rw [Int.neg_mul, Lean.Grind.Ring.sub_eq_add_neg]

theorem scaledCoeffs_sizeReduce_lower (b : Matrix Int n m) (l j k : Fin n)
    (hlj : l.val < j.val) (hjk : j.val < k.val) (r : Int) :
    GramSchmidt.entry (scaledCoeffs (sizeReduce b j k r)) k l =
      GramSchmidt.entry (scaledCoeffs b) k l -
        r * GramSchmidt.entry (scaledCoeffs b) j l := by
  rw [sizeReduce]
  rw [scaledCoeffs_rowAdd_lower (b := b) (l := l) (j := j) (k := k) hlj hjk (-r)]
  rw [Int.neg_mul, Lean.Grind.Ring.sub_eq_add_neg]

theorem scaledCoeffs_sizeReduce_other_row (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (r : Int) (i : Fin n) (hik : i ≠ k) :
    (scaledCoeffs (sizeReduce b j k r)).row i = (scaledCoeffs b).row i := by
  rw [sizeReduce]
  exact scaledCoeffs_rowAdd_other_row (b := b) (j := j) (k := k) hjk (-r) i hik

theorem scaledCoeffs_sizeReduce_above_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (r : Int) (l : Fin n)
    (hjl : j.val < l.val) (hlk : l.val < k.val) :
    GramSchmidt.entry (scaledCoeffs (sizeReduce b j k r)) k l =
      GramSchmidt.entry (scaledCoeffs b) k l := by
  rw [sizeReduce]
  exact scaledCoeffs_rowAdd_above_pivot (b := b) (j := j) (k := k) hjk (-r) l hjl hlk

/-! ### Adjacent-swap updates -/

private theorem rowSwap_row_eq_of_ne_int {n' m' : Nat}
    (b : Matrix Int n' m') (i j r : Fin n') (hri : r ≠ i) (hrj : r ≠ j) :
    (Matrix.rowSwap b i j)[r] = b[r] := by
  apply Vector.ext
  intro idx hidx
  let c : Fin m' := ⟨idx, hidx⟩
  change (Matrix.rowSwap b i j)[r][c] = b[r][c]
  rw [Matrix.rowSwap_getElem]
  by_cases hrj' : r = j
  · exact absurd hrj' hrj
  · by_cases hri' : r = i
    · exact absurd hri' hri
    · simp [hri', hrj']

private theorem rowSwap_row_left_int {n' m' : Nat}
    (b : Matrix Int n' m') (i j : Fin n') :
    (Matrix.rowSwap b i j)[i] = b[j] := by
  apply Vector.ext
  intro idx hidx
  let c : Fin m' := ⟨idx, hidx⟩
  change (Matrix.rowSwap b i j)[i][c] = b[j][c]
  rw [Matrix.rowSwap_getElem]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

private theorem rowSwap_row_right_int {n' m' : Nat}
    (b : Matrix Int n' m') (i j : Fin n') :
    (Matrix.rowSwap b i j)[j] = b[i] := by
  apply Vector.ext
  intro idx hidx
  let c : Fin m' := ⟨idx, hidx⟩
  change (Matrix.rowSwap b i j)[j][c] = b[i][c]
  rw [Matrix.rowSwap_getElem]
  simp

/-- When the swap indices `km1, k` both lie outside the leading `t`-prefix
(`t ≤ km1.val`), the leading Gram matrix is unchanged by the row swap. -/
private theorem leadingGramMatrixInt_rowSwap_outside
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1k : km1.val < k.val)
    (t : Nat) (ht : t ≤ n) (htkm1 : t ≤ km1.val) :
    GramSchmidt.leadingGramMatrixInt (Matrix.rowSwap b km1 k) t ht =
      GramSchmidt.leadingGramMatrixInt b t ht := by
  rw [GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram,
      GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram]
  apply Vector.ext
  intro p hp
  apply Vector.ext
  intro q hq
  let pp : Fin t := ⟨p, hp⟩
  let qq : Fin t := ⟨q, hq⟩
  let pn : Fin n := ⟨p, Nat.lt_of_lt_of_le hp ht⟩
  let qn : Fin n := ⟨q, Nat.lt_of_lt_of_le hq ht⟩
  have hp_ne_km1 : pn ≠ km1 := by
    intro h
    have hv : p = km1.val := by simpa [pn] using congrArg Fin.val h
    omega
  have hp_ne_k : pn ≠ k := by
    intro h
    have hv : p = k.val := by simpa [pn] using congrArg Fin.val h
    omega
  have hq_ne_km1 : qn ≠ km1 := by
    intro h
    have hv : q = km1.val := by simpa [qn] using congrArg Fin.val h
    omega
  have hq_ne_k : qn ≠ k := by
    intro h
    have hv : q = k.val := by simpa [qn] using congrArg Fin.val h
    omega
  have hp_eq : (Matrix.rowSwap b km1 k)[pn] = b[pn] :=
    rowSwap_row_eq_of_ne_int b km1 k pn hp_ne_km1 hp_ne_k
  have hq_eq : (Matrix.rowSwap b km1 k)[qn] = b[qn] :=
    rowSwap_row_eq_of_ne_int b km1 k qn hq_ne_km1 hq_ne_k
  show (Matrix.leadingPrefix (Matrix.gramMatrix (Matrix.rowSwap b km1 k)) t ht)[pp][qq] =
       (Matrix.leadingPrefix (Matrix.gramMatrix b) t ht)[pp][qq]
  simp only [Matrix.leadingPrefix_entry]
  show (Matrix.gramMatrix (Matrix.rowSwap b km1 k))[pn][qn] =
       (Matrix.gramMatrix b)[pn][qn]
  have hentry_swap :
      (Matrix.gramMatrix (Matrix.rowSwap b km1 k))[pn][qn] =
        Hex.Vector.dotProduct ((Matrix.rowSwap b km1 k)[pn]) ((Matrix.rowSwap b km1 k)[qn]) := by
    simp [Matrix.gramMatrix, Matrix.row, Matrix.ofFn]
  have hentry_b :
      (Matrix.gramMatrix b)[pn][qn] =
        Hex.Vector.dotProduct (b[pn]) (b[qn]) := by
    simp [Matrix.gramMatrix, Matrix.row, Matrix.ofFn]
  rw [hentry_swap, hentry_b, hp_eq, hq_eq]

/-- When the swap indices `km1, k` both lie inside the leading `t`-prefix
(`k.val < t`), the leading Gram matrix of the row-swapped basis equals the
"row-and-column swap" of the original leading Gram matrix at the lifted
indices `km1', k'`. The row-and-column swap is expressed via two transposes:
swap rows, transpose, swap rows again, transpose back. -/
private theorem leadingGramMatrixInt_rowSwap_inside
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1k : km1.val < k.val)
    (t : Nat) (ht : t ≤ n) (hkt : k.val < t) :
    let km1' : Fin t := ⟨km1.val, Nat.lt_trans hkm1k hkt⟩
    let k' : Fin t := ⟨k.val, hkt⟩
    GramSchmidt.leadingGramMatrixInt (Matrix.rowSwap b km1 k) t ht =
      (Matrix.rowSwap
        ((Matrix.rowSwap (GramSchmidt.leadingGramMatrixInt b t ht) km1' k').transpose)
        km1' k').transpose := by
  intro km1' k'
  rw [GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram
        (b := Matrix.rowSwap b km1 k) (k := t) (hk := ht),
      GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram
        (b := b) (k := t) (hk := ht)]
  let M : Matrix Int t t := Matrix.leadingPrefix (Matrix.gramMatrix b) t ht
  show Matrix.leadingPrefix (Matrix.gramMatrix (Matrix.rowSwap b km1 k)) t ht =
       (Matrix.rowSwap ((Matrix.rowSwap M km1' k').transpose) km1' k').transpose
  apply Vector.ext
  intro p hp
  apply Vector.ext
  intro q hq
  let pp : Fin t := ⟨p, hp⟩
  let qq : Fin t := ⟨q, hq⟩
  let pn : Fin n := ⟨p, Nat.lt_of_lt_of_le hp ht⟩
  let qn : Fin n := ⟨q, Nat.lt_of_lt_of_le hq ht⟩
  change (Matrix.leadingPrefix (Matrix.gramMatrix (Matrix.rowSwap b km1 k)) t ht)[pp][qq] =
         ((Matrix.rowSwap ((Matrix.rowSwap M km1' k').transpose) km1' k').transpose)[pp][qq]
  have hLHS :
      (Matrix.leadingPrefix (Matrix.gramMatrix (Matrix.rowSwap b km1 k)) t ht)[pp][qq] =
        Hex.Vector.dotProduct ((Matrix.rowSwap b km1 k)[pn]) ((Matrix.rowSwap b km1 k)[qn]) := by
    simp [Matrix.leadingPrefix, Matrix.gramMatrix, Matrix.row, Matrix.ofFn,
      pp, qq, pn, qn]
  have hM_entry : ∀ (a b' : Fin t),
      M[a][b'] =
        Hex.Vector.dotProduct (b[(⟨a.val, Nat.lt_of_lt_of_le a.isLt ht⟩ : Fin n)])
          (b[(⟨b'.val, Nat.lt_of_lt_of_le b'.isLt ht⟩ : Fin n)]) := by
    intro a b'
    simp [M, Matrix.leadingPrefix, Matrix.gramMatrix, Matrix.row, Matrix.ofFn]
  have hRHS_T :
      ((Matrix.rowSwap ((Matrix.rowSwap M km1' k').transpose) km1' k').transpose)[pp][qq] =
        (Matrix.rowSwap ((Matrix.rowSwap M km1' k').transpose) km1' k')[qq][pp] := by
    simp [Matrix.transpose, Matrix.col]
  rw [hLHS, hRHS_T]
  rw [Matrix.rowSwap_getElem (M := (Matrix.rowSwap M km1' k').transpose)
    (i := km1') (j := k') (r := qq) (k := pp)]
  have hkm1'_ne_k' : (km1' : Fin t) ≠ k' := by
    intro h
    have : km1'.val = k'.val := congrArg Fin.val h
    change km1.val = k.val at this
    omega
  have entry_after_outer_swap :
      ∀ (idx : Fin t),
        (Matrix.rowSwap M km1' k').transpose[idx][pp] =
          M[if pp = k' then km1' else if pp = km1' then k' else pp][idx] := by
    intro idx
    have hT : (Matrix.rowSwap M km1' k').transpose[idx][pp] =
        (Matrix.rowSwap M km1' k')[pp][idx] := by
      simp [Matrix.transpose, Matrix.col]
    rw [hT]
    rw [Matrix.rowSwap_getElem (M := M) (i := km1') (j := k') (r := pp) (k := idx)]
    by_cases hpk : pp = k'
    · simp [hpk]
    · by_cases hpkm1 : pp = km1'
      · simp [hpkm1, hkm1'_ne_k']
      · simp [hpk, hpkm1]
  have heq_get_swap : ∀ (r r' : Fin n), r = r' →
      (Matrix.rowSwap b km1 k)[r] = (Matrix.rowSwap b km1 k)[r'] := by
    intros r r' h; exact congrArg (Matrix.rowSwap b km1 k).get h
  by_cases hqk : qq = k'
  · simp only [if_pos hqk]
    rw [entry_after_outer_swap km1']
    have hqn_k : qn = k := by
      apply Fin.ext
      have hv : qq.val = k'.val := congrArg Fin.val hqk
      change q = k.val
      exact hv
    have hqn_eq : (Matrix.rowSwap b km1 k)[qn] = b[km1] :=
      (heq_get_swap qn k hqn_k).trans (rowSwap_row_right_int b km1 k)
    rw [hqn_eq]
    by_cases hpk : pp = k'
    · simp only [if_pos hpk]
      have hpn_k : pn = k := by
        apply Fin.ext
        have hv : pp.val = k'.val := congrArg Fin.val hpk
        change p = k.val
        exact hv
      have hpn_eq : (Matrix.rowSwap b km1 k)[pn] = b[km1] :=
        (heq_get_swap pn k hpn_k).trans (rowSwap_row_right_int b km1 k)
      rw [hpn_eq, hM_entry]
    · by_cases hpkm1 : pp = km1'
      · simp only [if_neg hpk, if_pos hpkm1]
        have hpn_km1 : pn = km1 := by
          apply Fin.ext
          have hv : pp.val = km1'.val := congrArg Fin.val hpkm1
          change p = km1.val
          exact hv
        have hpn_eq : (Matrix.rowSwap b km1 k)[pn] = b[k] :=
          (heq_get_swap pn km1 hpn_km1).trans (rowSwap_row_left_int b km1 k)
        rw [hpn_eq, hM_entry]
      · simp only [if_neg hpk, if_neg hpkm1]
        have hpn_ne_km1 : pn ≠ km1 := by
          intro h
          apply hpkm1
          apply Fin.ext
          have hv : pn.val = km1.val := congrArg Fin.val h
          change p = km1.val
          exact hv
        have hpn_ne_k : pn ≠ k := by
          intro h
          apply hpk
          apply Fin.ext
          have hv : pn.val = k.val := congrArg Fin.val h
          change p = k.val
          exact hv
        have hp_swap : (Matrix.rowSwap b km1 k)[pn] = b[pn] :=
          rowSwap_row_eq_of_ne_int b km1 k pn hpn_ne_km1 hpn_ne_k
        rw [hp_swap, hM_entry]
  · by_cases hqkm1 : qq = km1'
    · simp only [if_neg hqk, if_pos hqkm1]
      rw [entry_after_outer_swap k']
      have hqn_km1 : qn = km1 := by
        apply Fin.ext
        have hv : qq.val = km1'.val := congrArg Fin.val hqkm1
        change q = km1.val
        exact hv
      have hqn_eq : (Matrix.rowSwap b km1 k)[qn] = b[k] :=
        (heq_get_swap qn km1 hqn_km1).trans (rowSwap_row_left_int b km1 k)
      rw [hqn_eq]
      by_cases hpk : pp = k'
      · simp only [if_pos hpk]
        have hpn_k : pn = k := by
          apply Fin.ext
          have hv : pp.val = k'.val := congrArg Fin.val hpk
          change p = k.val
          exact hv
        have hpn_eq : (Matrix.rowSwap b km1 k)[pn] = b[km1] :=
          (heq_get_swap pn k hpn_k).trans (rowSwap_row_right_int b km1 k)
        rw [hpn_eq, hM_entry]
      · by_cases hpkm1 : pp = km1'
        · simp only [if_neg hpk, if_pos hpkm1]
          have hpn_km1 : pn = km1 := by
            apply Fin.ext
            have hv : pp.val = km1'.val := congrArg Fin.val hpkm1
            change p = km1.val
            exact hv
          have hpn_eq : (Matrix.rowSwap b km1 k)[pn] = b[k] :=
            (heq_get_swap pn km1 hpn_km1).trans (rowSwap_row_left_int b km1 k)
          rw [hpn_eq, hM_entry]
        · simp only [if_neg hpk, if_neg hpkm1]
          have hpn_ne_km1 : pn ≠ km1 := by
            intro h
            apply hpkm1
            apply Fin.ext
            have hv : pn.val = km1.val := congrArg Fin.val h
            change p = km1.val
            exact hv
          have hpn_ne_k : pn ≠ k := by
            intro h
            apply hpk
            apply Fin.ext
            have hv : pn.val = k.val := congrArg Fin.val h
            change p = k.val
            exact hv
          have hp_swap : (Matrix.rowSwap b km1 k)[pn] = b[pn] :=
            rowSwap_row_eq_of_ne_int b km1 k pn hpn_ne_km1 hpn_ne_k
          rw [hp_swap, hM_entry]
    · simp only [if_neg hqk, if_neg hqkm1]
      rw [entry_after_outer_swap qq]
      have hqn_ne_km1 : qn ≠ km1 := by
        intro h
        apply hqkm1
        apply Fin.ext
        have hv : qn.val = km1.val := congrArg Fin.val h
        change q = km1.val
        exact hv
      have hqn_ne_k : qn ≠ k := by
        intro h
        apply hqk
        apply Fin.ext
        have hv : qn.val = k.val := congrArg Fin.val h
        change q = k.val
        exact hv
      have hq_swap : (Matrix.rowSwap b km1 k)[qn] = b[qn] :=
        rowSwap_row_eq_of_ne_int b km1 k qn hqn_ne_km1 hqn_ne_k
      rw [hq_swap]
      by_cases hpk : pp = k'
      · simp only [if_pos hpk]
        have hpn_k : pn = k := by
          apply Fin.ext
          have hv : pp.val = k'.val := congrArg Fin.val hpk
          change p = k.val
          exact hv
        have hpn_eq : (Matrix.rowSwap b km1 k)[pn] = b[km1] :=
          (heq_get_swap pn k hpn_k).trans (rowSwap_row_right_int b km1 k)
        rw [hpn_eq, hM_entry]
      · by_cases hpkm1 : pp = km1'
        · simp only [if_neg hpk, if_pos hpkm1]
          have hpn_km1 : pn = km1 := by
            apply Fin.ext
            have hv : pp.val = km1'.val := congrArg Fin.val hpkm1
            change p = km1.val
            exact hv
          have hpn_eq : (Matrix.rowSwap b km1 k)[pn] = b[k] :=
            (heq_get_swap pn km1 hpn_km1).trans (rowSwap_row_left_int b km1 k)
          rw [hpn_eq, hM_entry]
        · simp only [if_neg hpk, if_neg hpkm1]
          have hpn_ne_km1 : pn ≠ km1 := by
            intro h
            apply hpkm1
            apply Fin.ext
            have hv : pn.val = km1.val := congrArg Fin.val h
            change p = km1.val
            exact hv
          have hpn_ne_k : pn ≠ k := by
            intro h
            apply hpk
            apply Fin.ext
            have hv : pn.val = k.val := congrArg Fin.val h
            change p = k.val
            exact hv
          have hp_swap : (Matrix.rowSwap b km1 k)[pn] = b[pn] :=
            rowSwap_row_eq_of_ne_int b km1 k pn hpn_ne_km1 hpn_ne_k
          rw [hp_swap, hM_entry]

/-- A "row-and-column swap" of a square matrix has the same determinant as the
original: the two row swaps each contribute a factor of -1, multiplying to 1. -/
private theorem det_rowSwap_transpose_rowSwap_transpose
    {R : Type u} [Lean.Grind.CommRing R] {n' : Nat}
    (M : Matrix R n' n') (i j : Fin n') (h : i ≠ j) :
    Matrix.det
        ((Matrix.rowSwap ((Matrix.rowSwap M i j).transpose) i j).transpose) =
      Matrix.det M := by
  rw [Matrix.det_transpose, Matrix.det_rowSwap _ _ _ h,
      Matrix.det_transpose, Matrix.det_rowSwap _ _ _ h]
  grind

theorem gramDet_adjacentSwap_of_ne (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (t : Nat) (ht : t ≤ n) (htk : t ≠ k.val) :
    gramDet (adjacentSwap b k hk) t ht = gramDet b t ht := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1k : km1.val < k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  unfold adjacentSwap gramDet
  congr 1
  by_cases hkt : k.val < t
  · rw [leadingGramMatrixInt_rowSwap_inside (b := b) (km1 := km1) (k := k) hkm1k t ht hkt]
    -- Bridge `bareiss = det` via Mathlib's `Matrix.det ∘ matrixEquiv`, composing
    -- `bareiss_eq_mathlib_det` with `det_eq.symm` to keep the executable
    -- determinant surface visible to `det_rowSwap_transpose_rowSwap_transpose`.
    have hbareiss_det : ∀ (M : Hex.Matrix Int t t),
        Hex.Matrix.bareiss M = Hex.Matrix.det M := fun M =>
      (HexMatrixMathlib.bareiss_eq_mathlib_det M).trans
        (HexMatrixMathlib.det_eq M).symm
    rw [hbareiss_det, hbareiss_det]
    apply det_rowSwap_transpose_rowSwap_transpose
    intro h
    have : km1.val = k.val := by
      have := congrArg Fin.val h
      simpa using this
    omega
  · have htlt : t ≤ km1.val := by
      have ht_le : t ≤ k.val := Nat.le_of_not_lt hkt
      have htlt_k : t < k.val := Nat.lt_of_le_of_ne ht_le htk
      dsimp [km1, GramSchmidt.prevRow]
      omega
    rw [leadingGramMatrixInt_rowSwap_outside (b := b) (km1 := km1) (k := k) hkm1k t ht htlt]

private theorem intCast_rat_injective_local {a b : Int} (h : (a : Rat) = (b : Rat)) :
    a = b := by
  have hz : ((a - b : Int) : Rat) = 0 := by simp [h]
  have hsub : a - b = 0 := Rat.intCast_eq_zero_iff.mp hz
  omega

theorem scaledCoeffs_adjacentSwap_lower_prev (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (j : Fin n) (hj : j.val + 1 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) km1 j =
      GramSchmidt.entry (scaledCoeffs b) k j := by
  intro km1
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hjkm1 : j.val < km1.val := by omega
  have hjk : j.val < k.val := by omega
  have hjsucc_ne : j.val + 1 ≠ k.val := by omega
  apply intCast_rat_injective_local
  have hLHS := scaledCoeffs_eq (b := adjacentSwap b k hk) km1.val j.val km1.isLt hjkm1
  have hRHS := scaledCoeffs_eq (b := b) k.val j.val k.isLt hjk
  have hdet :
      gramDet (adjacentSwap b k hk) (j.val + 1)
          (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) =
        gramDet b (j.val + 1) (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) := by
    apply gramDet_adjacentSwap_of_ne
    exact hjsucc_ne
  have hcoeff : GramSchmidt.entry (coeffs (adjacentSwap b k hk)) km1 j =
      GramSchmidt.entry (coeffs b) k j :=
    coeffs_adjacentSwap_lower_prev (b := b) k hk j hj
  calc ((GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) km1 j : Int) : Rat)
      = (gramDet (adjacentSwap b k hk) (j.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) : Rat) *
          GramSchmidt.entry (coeffs (adjacentSwap b k hk)) km1 j := hLHS
    _ = (gramDet b (j.val + 1) (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) : Rat) *
          GramSchmidt.entry (coeffs b) k j := by
          rw [hdet, hcoeff]
    _ = ((GramSchmidt.entry (scaledCoeffs b) k j : Int) : Rat) := hRHS.symm

theorem scaledCoeffs_adjacentSwap_lower_curr (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (j : Fin n) (hj : j.val + 1 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) k j =
      GramSchmidt.entry (scaledCoeffs b) km1 j := by
  intro km1
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hjkm1 : j.val < km1.val := by omega
  have hjk : j.val < k.val := by omega
  have hjsucc_ne : j.val + 1 ≠ k.val := by omega
  apply intCast_rat_injective_local
  have hLHS := scaledCoeffs_eq (b := adjacentSwap b k hk) k.val j.val k.isLt hjk
  have hRHS := scaledCoeffs_eq (b := b) km1.val j.val km1.isLt hjkm1
  have hdet :
      gramDet (adjacentSwap b k hk) (j.val + 1)
          (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) =
        gramDet b (j.val + 1) (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) := by
    apply gramDet_adjacentSwap_of_ne
    exact hjsucc_ne
  have hcoeff : GramSchmidt.entry (coeffs (adjacentSwap b k hk)) k j =
      GramSchmidt.entry (coeffs b) km1 j :=
    coeffs_adjacentSwap_lower_curr (b := b) k hk j hj
  calc ((GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) k j : Int) : Rat)
      = (gramDet (adjacentSwap b k hk) (j.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) : Rat) *
          GramSchmidt.entry (coeffs (adjacentSwap b k hk)) k j := hLHS
    _ = (gramDet b (j.val + 1) (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) : Rat) *
          GramSchmidt.entry (coeffs b) km1 j := by
          rw [hdet, hcoeff]
    _ = ((GramSchmidt.entry (scaledCoeffs b) km1 j : Int) : Rat) := hRHS.symm

theorem scaledCoeffs_adjacentSwap_pivot (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) k km1 =
      GramSchmidt.entry (scaledCoeffs b) k km1 := by
  intro km1
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hkm1k : km1.val < k.val := by omega
  calc
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) k km1
        = Matrix.det
            (GramSchmidt.scaledCoeffMatrix (Matrix.rowSwap b km1 k) k km1 hkm1k) := by
          rw [scaledCoeffs_eq_scaledCoeffMatrix_det]
          rfl
    _ = Matrix.det ((GramSchmidt.scaledCoeffMatrix b k km1 hkm1k).transpose) := by
          rw [GramSchmidt.Int.scaledCoeffMatrix_rowSwap_adjacent_pivot_transpose
            (b := b) (km1 := km1) (k := k) hkm1 hkm1k]
    _ = Matrix.det (GramSchmidt.scaledCoeffMatrix b k km1 hkm1k) := by
          rw [Matrix.det_transpose]
    _ = GramSchmidt.entry (scaledCoeffs b) k km1 := by
          rw [← scaledCoeffs_eq_scaledCoeffMatrix_det]


theorem gramDet_adjacentSwap_pivot (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    let km1 := GramSchmidt.prevRow k hk
    let B : Int := GramSchmidt.entry (scaledCoeffs b) k km1
    ((gramDet (adjacentSwap b k hk) k.val (Nat.le_of_lt k.isLt) : Nat) : Int) =
      (((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
          ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) + B ^ 2) /
        ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) := by
  let km1 := GramSchmidt.prevRow k hk
  let B : Int := GramSchmidt.entry (scaledCoeffs b) k km1
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]; omega
  have hprod :=
    GramSchmidt.Int.gramDet_rowSwap_adjacent_pivot_product
      (b := b) (km1 := km1) (k := k) hkm1
  -- `hprod` is in terms of `Matrix.rowSwap`; `adjacentSwap` is exactly that.
  have hdk_pos :
      ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) ≠ 0 := by
    intro h
    apply hdet
    exact Int.ofNat.inj h
  -- From dprime_int * dk_int = (rhs) and dk_int ≠ 0, deduce dprime_int = rhs / dk_int.
  -- Goal: ((gramDet (adjacentSwap b k hk) k.val ...) : Int) = (rhs) / dk_int.
  show ((gramDet (Matrix.rowSwap b km1 k) k.val (Nat.le_of_lt k.isLt) : Nat) : Int) =
      (((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
          ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) + B ^ 2) /
        ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int)
  rw [← hprod]
  exact (Int.mul_ediv_cancel _ hdk_pos).symm

theorem adjacentSwap_gramDetNumerator_dvd (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val)
    (hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    adjacentSwapDenom b k ∣ adjacentSwapGramDetNumerator b k hk := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]; omega
  have hprod :=
    GramSchmidt.Int.gramDet_rowSwap_adjacent_pivot_product
      (b := b) (km1 := km1) (k := k) hkm1
  -- The numerator equals dprime_int * dk_int, hence dk_int divides it.
  show ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) ∣
      adjacentSwapGramDetNumerator b k hk
  show ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) ∣
      ((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
          ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) +
        (GramSchmidt.entry (scaledCoeffs b) k km1) ^ 2
  rw [← hprod]
  exact ⟨((gramDet (Matrix.rowSwap b km1 k) k.val (Nat.le_of_lt k.isLt) : Nat) : Int),
    Int.mul_comm _ _⟩

/-! ### Adjacent-swap scaled-coefficient identity for rows above the pivot

For `i > k`, after swapping adjacent rows `km1, k` (with `km1.val + 1 = k.val`),
the executable Bareiss determinant of the scaled-coefficient Cramer minor
`scaledCoeffMatrix (rowSwap b km1 k) i km1` times the pivot Gram determinant
`d_k = gramDet b k.val` equals the integer numerator

  `d_{km1} * nu[i][k] + B * nu[i][km1]`

where `B = nu[k][km1]`. The proof linearises `nu'[i][km1]` (as a `Rat`) through
the basis identity `basis (rowSwap b km1 k) [km1] = basis b [k] + μ * basis b [km1]`
(via `basis_rowSwap_adjacent_prev`), bridges `bareiss → nu'` via
`scaledCoeffs_eq_scaledCoeffMatrix_bareiss`, and discharges with `ring`. -/
theorem bareiss_scaledCoeffMatrix_rowSwap_above_prev
    (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (i : Fin n) (hki : k.val < i.val)
    (hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    let km1 := GramSchmidt.prevRow k hk
    let hkm1i : km1.val < i.val := by
      dsimp [km1, GramSchmidt.prevRow]; omega
    Hex.Matrix.bareiss (GramSchmidt.scaledCoeffMatrix
        (Matrix.rowSwap b km1 k) i km1 hkm1i) *
      ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) =
      adjacentSwapScaledCoeffAbovePrevNumerator b k hk i := by
  intro km1 hkm1i
  -- Bridge bareiss → scaledCoeffs via the Mathlib-side identification.
  rw [← scaledCoeffs_eq_scaledCoeffMatrix_bareiss
      (Matrix.rowSwap b km1 k) i km1 hkm1i]
  -- The remaining Int goal: `scaledCoeffs b' i km1 * d_k = numerator`.
  -- Reduce to a rational identity.
  apply intCast_rat_injective_local
  -- Local abbreviations on the rational side.
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]; omega
  have hkm1k : km1.val < k.val := by omega
  have hkm1_lt_i : km1.val < i.val := hkm1i
  have hk_le_n : k.val ≤ n := Nat.le_of_lt k.isLt
  have hkm1_le_n : km1.val ≤ n := Nat.le_of_lt km1.isLt
  have hk1_le_n : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
  have hkm1_succ_le : km1.val + 1 ≤ n := Nat.succ_le_of_lt km1.isLt
  -- Rational shorthand: G, Nkm1, Nk, μ on the original basis.
  set μ : Rat := GramSchmidt.entry (coeffs b) k km1 with hμ_def
  set prev : Vector Rat m := (basis b).row km1 with hprev_def
  set curr : Vector Rat m := (basis b).row k with hcurr_def
  set G : Rat := gramSchmidtNormProduct b km1.val hkm1_le_n with hG_def
  set Nkm1 : Rat := Vector.normSq prev with hNkm1_def
  set Nk : Rat := Vector.normSq curr with hNk_def
  -- Rational expressions for the Gram determinants.
  have hdkm1_rat : (gramDet b km1.val hkm1_le_n : Rat) = G :=
    gramDet_eq_prod_normSq_uncond b km1.val hkm1_le_n
  have hdk_rat : (gramDet b k.val hk_le_n : Rat) = G * Nkm1 := by
    have h_succ := gramDet_succ_rat b km1.val hkm1_succ_le
    have hgd_eq :
        gramDet b (km1.val + 1) hkm1_succ_le = gramDet b k.val hk_le_n :=
      gramDet_subst_val b _ _ _ _ hkm1
    rw [← hgd_eq, h_succ]
  have hdkp1_rat : (gramDet b (k.val + 1) hk1_le_n : Rat) = G * Nkm1 * Nk := by
    have h_succ := gramDet_succ_rat b k.val hk1_le_n
    have hgnp_k_eq :
        gramSchmidtNormProduct b k.val hk_le_n =
          gramSchmidtNormProduct b (km1.val + 1) hkm1_succ_le :=
      gramSchmidtNormProduct_subst_val b _ _ _ _ hkm1.symm
    rw [h_succ, hgnp_k_eq,
        gramSchmidtNormProduct_succ b km1.val hkm1_succ_le]
  -- Basis orthogonality between curr and prev.
  have horth : Matrix.dot curr prev = 0 :=
    basis_orthogonal b k.val km1.val k.isLt km1.isLt (by omega)
  -- New basis row at km1 of the swapped matrix.
  have hbasis_swap :
      (basis (Matrix.rowSwap b km1 k)).row km1 = curr + μ • prev :=
    basis_rowSwap_adjacent_prev b km1 k hkm1
  -- normSq of the new basis row at km1.
  have hN'_eq : Vector.normSq ((basis (Matrix.rowSwap b km1 k)).row km1) =
      Nk + μ ^ 2 * Nkm1 := by
    rw [hbasis_swap]
    exact normSq_add_smul_orthogonal_rat curr prev μ horth
  -- gramDet (rowSwap b km1 k) k.val = G * (Nk + μ^2 * Nkm1).
  have hdprime_rat :
      (gramDet (Matrix.rowSwap b km1 k) k.val hk_le_n : Rat) =
        G * (Nk + μ ^ 2 * Nkm1) := by
    have h_succ :=
      gramDet_succ_rat (Matrix.rowSwap b km1 k) km1.val hkm1_succ_le
    have hgd_eq :
        gramDet (Matrix.rowSwap b km1 k) (km1.val + 1) hkm1_succ_le =
          gramDet (Matrix.rowSwap b km1 k) k.val hk_le_n :=
      gramDet_subst_val (Matrix.rowSwap b km1 k) _ _ _ _ hkm1
    rw [← hgd_eq, h_succ,
        gramSchmidtNormProduct_rowSwap_below b km1 k hkm1k]
    show G * Vector.normSq ((basis (Matrix.rowSwap b km1 k)).row
        ⟨km1.val, km1.isLt⟩) = G * (Nk + μ ^ 2 * Nkm1)
    rw [hN'_eq]
  -- B = d_k * μ.
  have hB_rat :
      ((GramSchmidt.entry (scaledCoeffs b) k km1 : Int) : Rat) = G * Nkm1 * μ := by
    rw [scaledCoeffs_eq b k.val km1.val k.isLt hkm1k]
    have hgd_eq :
        gramDet b (km1.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hkm1k k.isLt)) =
          gramDet b k.val hk_le_n :=
      gramDet_subst_val b _ _ _ _ hkm1
    show (gramDet b (km1.val + 1) _ : Rat) *
        GramSchmidt.entry (coeffs b) ⟨k.val, k.isLt⟩
          ⟨km1.val, Nat.lt_trans hkm1k k.isLt⟩ = G * Nkm1 * μ
    rw [hgd_eq, hdk_rat]
  -- nu[i][k] = d_{k+1} * c[i][k] = G * Nkm1 * Nk * c[i][k]
  have hnuik_rat :
      ((GramSchmidt.entry (scaledCoeffs b) i k : Int) : Rat) =
        G * Nkm1 * Nk * GramSchmidt.entry (coeffs b) i k := by
    have heq := scaledCoeffs_eq b i.val k.val i.isLt hki
    show ((GramSchmidt.entry (scaledCoeffs b) ⟨i.val, i.isLt⟩
        ⟨k.val, Nat.lt_trans hki i.isLt⟩ : Int) : Rat) = _
    rw [heq, hdkp1_rat]
  -- nu[i][km1] = d_k * c[i][km1] = G * Nkm1 * c[i][km1]
  have hnuikm1_rat :
      ((GramSchmidt.entry (scaledCoeffs b) i km1 : Int) : Rat) =
        G * Nkm1 * GramSchmidt.entry (coeffs b) i km1 := by
    have heq := scaledCoeffs_eq b i.val km1.val i.isLt hkm1_lt_i
    have hgd_eq :
        gramDet b (km1.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hkm1_lt_i i.isLt)) =
          gramDet b k.val hk_le_n :=
      gramDet_subst_val b _ _ _ _ hkm1
    show ((GramSchmidt.entry (scaledCoeffs b) ⟨i.val, i.isLt⟩
        ⟨km1.val, Nat.lt_trans hkm1_lt_i i.isLt⟩ : Int) : Rat) = _
    rw [heq, hgd_eq, hdk_rat]
  -- For i > k, the i-th row of b' = rowSwap b km1 k equals the i-th row of b.
  have hrow_b'_i : (Matrix.rowSwap b km1 k)[i] = b[i] := by
    have hi_ne_km1 : (i : Fin n) ≠ km1 := fun h => by
      have : i.val = km1.val := congrArg Fin.val h
      omega
    have hi_ne_k : (i : Fin n) ≠ k := fun h => by
      have : i.val = k.val := congrArg Fin.val h
      omega
    exact rowSwap_row_eq_of_ne_int b km1 k i hi_ne_km1 hi_ne_k
  have hcastRow_b'i :
      Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k).row i) =
        Vector.map (fun x : Int => (x : Rat)) (b.row i) := by
    show Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k)[i]) = _
    rw [hrow_b'_i]
    rfl
  -- Inner products of basis(b)[k] and basis(b)[km1] with cast(b.row i).
  have hdotk : Matrix.dot curr
        (Vector.map (fun x : Int => (x : Rat)) (b.row i)) =
      GramSchmidt.entry (coeffs b) i k * Nk := by
    have h := dot_basis_castRow_eq_coeffs_mul_normSq b i.val k.val i.isLt hki
    show Matrix.dot ((basis b).row ⟨k.val, k.isLt⟩) _ = _
    rw [h]
  have hdotkm1 : Matrix.dot prev
        (Vector.map (fun x : Int => (x : Rat)) (b.row i)) =
      GramSchmidt.entry (coeffs b) i km1 * Nkm1 := by
    have h := dot_basis_castRow_eq_coeffs_mul_normSq b i.val km1.val i.isLt hkm1_lt_i
    show Matrix.dot ((basis b).row ⟨km1.val, km1.isLt⟩) _ = _
    rw [h]
  -- Inner product of basis(b')[km1] with cast(b'.row i) = c[i][k] * Nk + μ * c[i][km1] * Nkm1.
  have hdot_b'_km1 :
      Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row km1)
          (Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k).row i)) =
        GramSchmidt.entry (coeffs b) i k * Nk +
          μ * (GramSchmidt.entry (coeffs b) i km1 * Nkm1) := by
    rw [hcastRow_b'i, hbasis_swap]
    -- dot (curr + μ • prev) (cast b.row i)
    --   = dot curr (cast b.row i) + μ * dot prev (cast b.row i)
    rw [dot_add_left_rat, dot_smul_left_rat]
    rw [hdotk, hdotkm1]
  -- Key Rat identity: nu'[i][km1] = G * <basis(b')[km1], cast(b'.row i)>.
  -- The proof uses scaledCoeffs_eq for b', plus dot_basis_castRow on b', plus
  -- the fact that d_k(b') = G * |basis(b')[km1]|^2 so the cancellation is clean.
  have hnu'_rat :
      ((GramSchmidt.entry (scaledCoeffs (Matrix.rowSwap b km1 k)) i km1 : Int) : Rat) =
        G * (GramSchmidt.entry (coeffs b) i k * Nk +
            μ * (GramSchmidt.entry (coeffs b) i km1 * Nkm1)) := by
    -- nu'[i][km1] = d_k(b') * c'[i][km1] = G * |basis(b')[km1]|^2 * c'[i][km1]
    -- And c'[i][km1] * |basis(b')[km1]|^2 = dot basis(b')[km1] (cast b'.row i)
    have hcoeff_normSq :
        GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i km1 *
          Vector.normSq ((basis (Matrix.rowSwap b km1 k)).row km1) =
        Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row km1)
          (Vector.map (fun x : Int => (x : Rat))
            ((Matrix.rowSwap b km1 k).row i)) := by
      have h := dot_basis_castRow_eq_coeffs_mul_normSq
        (Matrix.rowSwap b km1 k) i.val km1.val i.isLt hkm1_lt_i
      show GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) ⟨i.val, i.isLt⟩
            ⟨km1.val, Nat.lt_trans hkm1_lt_i i.isLt⟩ *
          Vector.normSq ((basis (Matrix.rowSwap b km1 k)).row
            ⟨km1.val, km1.isLt⟩) = _
      exact h.symm
    -- Apply scaledCoeffs_eq for b'.
    have heq := scaledCoeffs_eq (Matrix.rowSwap b km1 k) i.val km1.val i.isLt hkm1_lt_i
    show ((GramSchmidt.entry (scaledCoeffs (Matrix.rowSwap b km1 k)) ⟨i.val, i.isLt⟩
            ⟨km1.val, Nat.lt_trans hkm1_lt_i i.isLt⟩ : Int) : Rat) = _
    rw [heq]
    -- The exponent km1.val + 1 in scaledCoeffs_eq matches k.val via hkm1.
    have hgd_eq :
        gramDet (Matrix.rowSwap b km1 k) (km1.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hkm1_lt_i i.isLt)) =
          gramDet (Matrix.rowSwap b km1 k) k.val hk_le_n :=
      gramDet_subst_val (Matrix.rowSwap b km1 k) _ _ _ _ hkm1
    rw [hgd_eq, hdprime_rat]
    -- Now goal: G * (Nk + μ^2 * Nkm1) * c'[i][km1] = G * inner
    -- Use: c'[i][km1] * (Nk + μ^2 * Nkm1) = inner  (via hcoeff_normSq + hN'_eq).
    have hcoeff_inner :
        GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k))
            ⟨i.val, i.isLt⟩
            ⟨km1.val, Nat.lt_trans hkm1_lt_i i.isLt⟩ *
          (Nk + μ ^ 2 * Nkm1) =
        GramSchmidt.entry (coeffs b) i k * Nk +
          μ * (GramSchmidt.entry (coeffs b) i km1 * Nkm1) := by
      rw [← hN'_eq]
      rw [hcoeff_normSq]
      exact hdot_b'_km1
    linear_combination G * hcoeff_inner
  -- Combine all rational identities and discharge by ring.
  -- Goal: ↑(nu'[i][km1] * d_k) = ↑(numerator)
  -- numerator = d_{km1} * nu[i][k] + B * nu[i][km1]
  unfold adjacentSwapScaledCoeffAbovePrevNumerator adjacentSwapPivotCoeff
  push_cast
  rw [hnu'_rat, hdk_rat, hdkm1_rat, hnuik_rat, hnuikm1_rat, hB_rat]
  ring

end GramSchmidt.Int

end Hex
