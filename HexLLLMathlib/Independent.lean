import HexLLL.Basic
import HexGramSchmidtMathlib.Int
import HexGramSchmidtMathlib.Update

/-!
Mathlib-side independence theorems for `HexLLL`.

This module hosts the determinant-backed independence helpers whose proofs
factor through `GramSchmidt.Int.independent_of_det_positive` and therefore
ultimately depend on the Bareiss/`Matrix.det` correspondence. They are kept
out of the Mathlib-free `HexLLL/Basic.lean` so that the executable LLL core
does not expose a proof-only surface tied to the Mathlib-side layer.
-/

namespace Hex

namespace Matrix

/-- The identity matrix is independent: every executable leading Gram
determinant is positive. Used by Phase 4 benchmarks of
`lll.firstShortVector`, where the identity basis is the degenerate BZ-style
recombination input with all-zero lift coefficients. -/
theorem identity_independent {n : Nat} : (1 : Matrix Int n n).independent := by
  exact GramSchmidt.Int.independent_one

theorem gramMatrix_leadingRows_eq_submatrix {n : Nat} (M : Matrix Int n n) (k : Fin n) :
    gramMatrix (leadingRows M (k.val + 1) (Nat.succ_le_of_lt k.isLt)) =
      submatrix (gramMatrix M) k := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let iFin : Fin (k.val + 1) := ⟨i, hi⟩
  let jFin : Fin (k.val + 1) := ⟨j, hj⟩
  let ii : Fin n := ⟨i, Nat.lt_of_lt_of_le hi (Nat.succ_le_of_lt k.isLt)⟩
  let jj : Fin n := ⟨j, Nat.lt_of_lt_of_le hj (Nat.succ_le_of_lt k.isLt)⟩
  have hrow_i :
      row (leadingRows M (k.val + 1) (Nat.succ_le_of_lt k.isLt)) iFin = row M ii := by
    apply Vector.ext
    intro c hc
    simp [row, leadingRows, ofFn, iFin, ii]
  have hrow_j :
      row (leadingRows M (k.val + 1) (Nat.succ_le_of_lt k.isLt)) jFin = row M jj := by
    apply Vector.ext
    intro c hc
    simp [row, leadingRows, ofFn, jFin, jj]
  have hdot :
      Hex.Vector.dotProduct
          (row (leadingRows M (k.val + 1) (Nat.succ_le_of_lt k.isLt)) iFin)
          (row (leadingRows M (k.val + 1) (Nat.succ_le_of_lt k.isLt)) jFin) =
        Hex.Vector.dotProduct (row M ii) (row M jj) := by
    rw [hrow_i, hrow_j]
  simpa [gramMatrix, submatrix, ofFn, iFin, jFin, ii, jj] using
    hdot

theorem independent_of_upperTriangular_pos_diag {n : Nat}
    (M : Matrix Int n n)
    (hzero : ∀ i j : Fin n, j.val < i.val -> M[i][j] = 0)
    (hdiag : ∀ i : Fin n, 0 < M[i][i]) : M.independent := by
  exact GramSchmidt.Int.independent_of_det_positive M (by
    intro k
    have hpos :=
      det_gramMatrix_leadingRows_pos_of_upperTriangular_pos_diag M hzero hdiag
        (k.val + 1) (Nat.succ_le_of_lt k.isLt)
    rwa [gramMatrix_leadingRows_eq_submatrix M k] at hpos)

end Matrix

namespace LLLState

/-- Size reduction preserves the executable Gram-determinant independence
predicate.  This public theorem lives in the Mathlib-side library so the
Mathlib-free LLL core does not expose determinant-bound preservation surfaces. -/
theorem sizeReduce_independent (s : LLLState n m) (k : Nat)
    (hind : s.b.independent) (hvalid : s.Valid) (hvalid' : (s.sizeReduce k).Valid) :
    (s.sizeReduce k).b.independent := by
  intro i
  have hd_vec :
      (s.sizeReduce k).d.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ =
        s.d.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
    simpa using congrArg
      (fun d : Vector Nat (n + 1) => d.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (sizeReduce_d s k)
  have hgram :
      GramSchmidt.Int.gramDet (s.sizeReduce k).b (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) =
        GramSchmidt.Int.gramDet s.b (i.val + 1) (Nat.succ_le_of_lt i.isLt) := by
    rw [← hvalid'.d_eq (i.val + 1) (Nat.succ_lt_succ i.isLt)]
    rw [hd_vec]
    rw [hvalid.d_eq (i.val + 1) (Nat.succ_lt_succ i.isLt)]
  rw [hgram]
  exact hind i

private theorem vector_modify_get_self {α : Type*} {n : Nat}
    (v : Vector α n) (i : Fin n) (f : α → α) :
    (v.modify i.val f).get i = f (v.get i) := by
  unfold Vector.modify
  simp [Vector.get, Array.getElem_modify]

private theorem vector_modify_get_ne {α : Type*} {n : Nat}
    (v : Vector α n) (i : Nat) (f : α → α) (j : Fin n) (h : i ≠ j.val) :
    (v.modify i f).get j = v.get j := by
  unfold Vector.modify
  simp [Vector.get, Array.getElem_modify, h]

/-- Inner foldl in `swapStep`'s `setPrefixFrom`: setting positions `0..km1-1` of a
row to `source[·]`. -/
private def setPrefix (source row : Vector Int n) (km1 : Fin n) : Vector Int n :=
  (List.finRange km1.val).foldl
    (fun row j =>
      let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt km1.isLt⟩
      row.set jFin (source.get jFin))
    row

private theorem foldl_set_source_get_eq
    (xs : List (Fin n)) (base source : Vector Int n) (l : Fin n) :
    (xs.foldl (fun row i => row.set i (source.get i)) base).get l =
      if (∃ i ∈ xs, i.val = l.val) then source.get l else base.get l := by
  induction xs generalizing base with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    by_cases h_xs : ∃ i ∈ xs, i.val = l.val
    · simp [h_xs]
    · by_cases h_xl : x.val = l.val
      · have h_cons : ∃ i ∈ x :: xs, i.val = l.val :=
          ⟨x, List.mem_cons.mpr (Or.inl rfl), h_xl⟩
        have h_xeq : x = l := Fin.eq_of_val_eq h_xl
        subst h_xeq
        simp only [h_xs, ↓reduceIte, h_cons]
        change (base.set x.val (source.get x) x.isLt)[x.val] = _
        exact Vector.getElem_set_self x.isLt
      · have h_cons : ¬ ∃ i ∈ x :: xs, i.val = l.val := by
          rintro ⟨i, hi, hi_l⟩
          rcases List.mem_cons.mp hi with rfl | hxs
          · exact h_xl hi_l
          · exact h_xs ⟨i, hxs, hi_l⟩
        simp only [h_xs, ↓reduceIte, h_cons]
        change (base.set x.val (source.get x) x.isLt)[l.val] = base[l.val]
        exact Vector.getElem_set_ne x.isLt l.isLt h_xl

private theorem foldl_setSource_get_eq
    {kmVal : Nat} (hkm : kmVal ≤ n)
    (source base : Vector Int n) (l : Fin n) :
    ((List.finRange kmVal).foldl
        (fun (row : Vector Int n) (j : Fin kmVal) =>
          let jFin : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hkm⟩
          row.set jFin (source.get jFin))
        base).get l =
      if l.val < kmVal then source.get l else base.get l := by
  let cast : Fin kmVal → Fin n :=
    fun j => ⟨j.val, Nat.lt_of_lt_of_le j.isLt hkm⟩
  show ((List.finRange kmVal).foldl
        (fun (row : Vector Int n) (j : Fin kmVal) =>
          row.set (cast j) (source.get (cast j)))
        base).get l = _
  rw [show ((List.finRange kmVal).foldl
        (fun (row : Vector Int n) (j : Fin kmVal) =>
          row.set (cast j) (source.get (cast j)))
        base) =
      ((List.finRange kmVal).map cast).foldl
        (fun (row : Vector Int n) (i : Fin n) =>
          row.set i (source.get i))
        base from
      (@List.foldl_map (Fin kmVal) (Fin n) (Vector Int n) cast
        (fun row i => row.set i (source.get i))
        (List.finRange kmVal) base).symm]
  rw [foldl_set_source_get_eq]
  by_cases hlj : l.val < kmVal
  · have hex : ∃ i ∈ (List.finRange kmVal).map cast, i.val = l.val := by
      refine ⟨⟨l.val, Nat.lt_of_lt_of_le hlj hkm⟩, ?_, rfl⟩
      rw [List.mem_map]
      exact ⟨⟨l.val, hlj⟩, List.mem_finRange _, rfl⟩
    rw [if_pos hex, if_pos hlj]
  · have hno : ¬ ∃ i ∈ (List.finRange kmVal).map cast, i.val = l.val := by
      rintro ⟨i, hi_mem, hi_eq⟩
      rw [List.mem_map] at hi_mem
      obtain ⟨l', _, hl'⟩ := hi_mem
      have hcast : (cast l').val = l'.val := rfl
      have : l.val < kmVal := by
        rw [← hi_eq, ← hl', hcast]
        exact l'.isLt
      exact hlj this
    rw [if_neg hno, if_neg hlj]

private theorem setPrefix_get_lt {source row : Vector Int n} {km1 : Fin n}
    (l : Fin n) (hl : l.val < km1.val) :
    (setPrefix source row km1).get l = source.get l := by
  unfold setPrefix
  rw [foldl_setSource_get_eq (Nat.le_of_lt km1.isLt) source row l]
  simp [hl]

private theorem setPrefix_get_ge {source row : Vector Int n} {km1 : Fin n}
    (l : Fin n) (hl : km1.val ≤ l.val) :
    (setPrefix source row km1).get l = row.get l := by
  unfold setPrefix
  rw [foldl_setSource_get_eq (Nat.le_of_lt km1.isLt) source row l]
  simp [Nat.not_lt.mpr hl]

/-- Outer foldl in `swapStep` over rows above `k`. The update applied to row `i`
depends only on the original `source` (`s.ν`), not on the accumulator. -/
private theorem foldl_modify_rows_get
    {α : Type*} (k : Nat) (xs : List (Fin n)) (hnd : xs.Nodup)
    (base : Vector α n) (upd : Fin n → α → α) (l : Fin n) :
    (xs.foldl
        (fun (acc : Vector α n) (i : Fin n) =>
          if k < i.val then acc.modify i.val (upd i) else acc) base).get l =
      if (l ∈ xs ∧ k < l.val) then upd l (base.get l) else base.get l := by
  induction xs generalizing base with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have hxnd : x ∉ xs := (List.nodup_cons.mp hnd).1
    have hxs_nd : xs.Nodup := (List.nodup_cons.mp hnd).2
    by_cases hkx : k < x.val
    · rw [if_pos hkx]
      rw [ih hxs_nd (base.modify x.val (upd x))]
      by_cases hlx : x.val = l.val
      · have hxeq : x = l := Fin.eq_of_val_eq hlx
        subst hxeq
        have h1 : (x ∈ x :: xs) := List.mem_cons_self
        have h2 : ¬(x ∈ xs) := hxnd
        simp [h1, h2, hkx, vector_modify_get_self]
      · have hl_ne : l ≠ x := fun h => hlx (h ▸ rfl)
        have hxv_ne : x.val ≠ l.val := hlx
        rw [vector_modify_get_ne base x.val (upd x) l hxv_ne]
        have hl_cons_iff : (l ∈ x :: xs) ↔ (l ∈ xs) := by
          constructor
          · intro h
            rcases List.mem_cons.mp h with rfl | h'
            · exact (hl_ne rfl).elim
            · exact h'
          · exact fun h => List.mem_cons.mpr (Or.inr h)
        simp only [hl_cons_iff]
    · rw [if_neg hkx]
      rw [ih hxs_nd base]
      by_cases hxl : x = l
      · subst hxl
        simp [hkx]
      · have hl_cons_iff : (l ∈ x :: xs) ↔ (l ∈ xs) := by
          constructor
          · intro h
            rcases List.mem_cons.mp h with rfl | h'
            · exact (hxl rfl).elim
            · exact h'
          · exact fun h => List.mem_cons.mpr (Or.inr h)
        simp only [hl_cons_iff]

/-- Field projections through `swapStep`'s `0 < k < n` branch. -/
private theorem swapStep_b_eq (s : LLLState n m) (k : Nat) (hk : k < n) (hk0 : 0 < k) :
    (s.swapStep k).b = GramSchmidt.Int.adjacentSwap s.b ⟨k, hk⟩ hk0 := by
  unfold swapStep
  rw [dif_pos hk]
  rw [dif_pos hk0]

theorem swapStep_valid (s : LLLState n m) (k : Nat)
    (hind : s.b.independent) (hvalid : s.Valid) :
    (s.swapStep k).Valid := by
  unfold swapStep
  by_cases hk : k < n
  · rw [dif_pos hk]
    by_cases hk0 : 0 < k
    · rw [dif_pos hk0]
      sorry
    · rw [dif_neg hk0]
      exact hvalid
  · rw [dif_neg hk]
    exact hvalid

end LLLState

end Hex
