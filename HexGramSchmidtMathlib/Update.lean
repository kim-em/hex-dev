import HexGramSchmidt.Update

/-!
Bridge-bound row-operation update theorems for `hex-gram-schmidt`.

The theorems in this module relate `gramDet` / `scaledCoeffs` under the
adjacent-swap row operation. Their statements are Hex-local, but their
proofs cross the Mathlib boundary by reaching `Matrix.bareiss_eq_det`,
so they live in the bridge layer per
[SPEC/Libraries/hex-gram-schmidt.md "Proof path governs placement,
not just statement"].

HO-43 Round 2 scope: this module currently holds only the
`adjacentSwap`-side relocations. The five size-reduce theorems
(`gramDet_sizeReduce`, `scaledCoeffs_sizeReduce_pivot/lower/
other_row/above_pivot`) remain in `HexGramSchmidt/Update.lean`
pending a consumer-side refactor of `LLLState.sizeReduceColumn`
in `HexLLL/Basic.lean` (cf. #3916); relocating them now would
break the Mathlib-free `HexLLL.Basic` build, which would either
force a `sorry` in `LLLState`'s structure field discharges
(cascading `sorry` into `sizeReduce_independent`) or smuggle a
bridge import into the Mathlib-free file.
-/

namespace Hex

namespace GramSchmidt.Int

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
    rw [Matrix.bareiss_eq_det, Matrix.bareiss_eq_det]
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
  have hz : ((a - b : Int) : Rat) = 0 := by
    simp [h]
    grind
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

end GramSchmidt.Int

end Hex
