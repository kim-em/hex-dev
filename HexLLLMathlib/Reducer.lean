/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLL.Basic
public import HexLLLMathlib.State
public import HexLLLMathlib.Checker
public import HexGramSchmidtMathlib.Int
public import HexGramSchmidtMathlib.Update

public section

/-!
Mathlib-side correctness of the executable LLL reducers. The per-step
`Valid`/independence preservation, the potential strict-decrease and fuel
sufficiency, and the loop-invariant induction culminate in the reducedness,
lattice, and rational short-vector capstones for `Hex.lllNative` and
`Hex.lll`.
-/

/-- `Vector.get` is definitionally `getElem` at the index value, so this is `rfl`.
A local restatement avoids depending on a Mathlib lemma name that is not present
in the pinned Mathlib (`vector_get_eq_getElem` post-dates `v4.32.0-rc1-patch1`). -/
private theorem vector_get_eq_getElem {α : Type*} {n : ℕ} (v : Vector α n) (i : Fin n) :
    v.get i = v[i.1] := rfl

namespace Hex

open Hex.Internal

namespace Matrix

/-- The identity matrix is independent: every executable leading Gram
determinant is positive. Used by Phase 4 benchmarks of
`lll.firstShortVector`, where the identity basis is the degenerate BZ-style
recombination input with all-zero lift coefficients. -/
theorem identity_independent {n : Nat} : (Matrix.identity (R := Int) n).independent := by
  exact GramSchmidt.Int.independent_identity

private theorem gramMatrix_takeRows_eq_principalSubmatrix {n : Nat} (M : Matrix Int n n) (k : Nat)
    (hk : k ≤ n) :
    gramMatrix (takeRows M k hk) = principalSubmatrix (gramMatrix M) k hk := by
  apply Hex.Matrix.ext
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let iFin : Fin k := ⟨i, hi⟩
  let jFin : Fin k := ⟨j, hj⟩
  let ii : Fin n := ⟨i, Nat.lt_of_lt_of_le hi hk⟩
  let jj : Fin n := ⟨j, Nat.lt_of_lt_of_le hj hk⟩
  have hrow_i : row (takeRows M k hk) iFin = row M ii := by
    apply Vector.ext
    intro c hc
    simp [row, takeRows, ofFn, iFin, ii]
  have hrow_j : row (takeRows M k hk) jFin = row M jj := by
    apply Vector.ext
    intro c hc
    simp [row, takeRows, ofFn, jFin, jj]
  have hdot :
      (row (takeRows M k hk) iFin).dotProduct (row (takeRows M k hk) jFin) =
        (row M ii).dotProduct (row M jj) := by
    rw [hrow_i, hrow_j]
  simpa [gramMatrix, principalSubmatrix, ofFn, iFin, jFin, ii, jj] using
    hdot

private theorem independent_of_upperTriangular_pos_diag {n : Nat}
    (M : Matrix Int n n)
    (hzero : ∀ i j : Fin n, j.val < i.val -> M[i][j] = 0)
    (hdiag : ∀ i : Fin n, 0 < M[i][i]) : M.independent := by
  exact GramSchmidt.Int.independent_of_det_positive M (by
    intro k hk _
    have hpos :=
      det_gramMatrix_takeRows_pos_of_upperTriangular_pos_diag M hzero hdiag k hk
    rwa [gramMatrix_takeRows_eq_principalSubmatrix M k hk] at hpos)

end Matrix

namespace Internal.LLLState

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
    rw [← hvalid'.d_eq (i.val + 1) (Nat.succ_lt_succ i.isLt), hd_vec,
      hvalid.d_eq (i.val + 1) (Nat.succ_lt_succ i.isLt)]
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

/-- Matrix-row version of `foldl_modify_rows_get`: folding row-`modify`s over a
matrix and reading row `l` is the same as the single conditional update. -/
private theorem foldl_modify_matrix_getRow
    (k : Nat) (xs : List (Fin n)) (hnd : xs.Nodup)
    (base : Hex.Matrix Int n n) (upd : Fin n → Vector Int n → Vector Int n) (l : Fin n) :
    (xs.foldl
        (fun (ν : Hex.Matrix Int n n) (i : Fin n) =>
          if k < i.val then ν.modifyRow i.val (upd i) else ν) base).getRow l =
      if (l ∈ xs ∧ k < l.val) then upd l (base.getRow l) else base.getRow l := by
  have key : ∀ (acc : Hex.Matrix Int n n),
      (xs.foldl
          (fun (ν : Hex.Matrix Int n n) (i : Fin n) =>
            if k < i.val then ν.modifyRow i.val (upd i) else ν) acc).rows =
        xs.foldl
          (fun (a : Vector (Vector Int n) n) (i : Fin n) =>
            if k < i.val then a.modify i.val (upd i) else a) acc.rows := by
    intro acc
    clear hnd
    induction xs generalizing acc with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hkx : k < x.val
      · rw [if_pos hkx, if_pos hkx, ih (acc.modifyRow x.val (upd x)), Hex.Matrix.rows_modifyRow]
      · rw [if_neg hkx, if_neg hkx, ih acc]
  unfold Hex.Matrix.getRow
  rw [key base]
  simpa [Vector.get, Fin.getElem_fin] using
    foldl_modify_rows_get k xs hnd base.rows upd l

/-- Field projections through `swapStep`'s `0 < k < n` branch. -/
private theorem swapStep_b_eq (s : LLLState n m) (k : Nat) (hk : k < n) (hk0 : 0 < k) :
    (s.swapStep k).b = GramSchmidt.Int.adjacentSwap s.b ⟨k, hk⟩ hk0 := by
  unfold swapStep
  rw [dif_pos hk, dif_pos hk0]

private theorem swapStep_valid (s : LLLState n m) (k : Nat)
    (hind : s.b.independent) (hvalid : s.Valid) :
    (s.swapStep k).Valid := by
  unfold swapStep
  by_cases hk : k < n
  · rw [dif_pos hk]
    by_cases hk0 : 0 < k
    · rw [dif_pos hk0]
      set kFin : Fin n := ⟨k, hk⟩ with hkFin_def
      set km1 : Fin n := GramSchmidt.prevRow kFin hk0 with hkm1_def
      have hkFinVal : kFin.val = k := rfl
      have hkm1Val : km1.val = k - 1 := by
        simp [hkm1_def, GramSchmidt.prevRow, hkFinVal]
      have hkm1 : km1.val + 1 = k := by omega
      have hkm1_lt_k : km1.val < k := by omega
      have hdk_pos : 0 < GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) := by
        have := hind ⟨km1.val, Nat.lt_trans hkm1_lt_k hk⟩
        simpa [hkm1] using this
      have hdk_ne_zero :
          GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) ≠ 0 := Nat.pos_iff_ne_zero.mp hdk_pos
      -- Common shorthand for the per-state quantities.
      set B : Int := (s.ν.getRow kFin).get km1 with hB_def
      set dkPrev : Nat := s.d.get ⟨km1.val, Nat.lt_succ_of_lt km1.isLt⟩ with hdkPrev_def
      set dk : Nat := s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩ with hdk_def
      set dkNext : Nat := s.d.get ⟨k + 1, Nat.succ_lt_succ hk⟩ with hdkNext_def
      -- Bridge the let-bound `dk_*` quantities to gramDet via `hvalid`.
      have hdkPrev_eq :
          dkPrev = GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) := by
        simpa using hvalid.d_eq km1.val (Nat.lt_succ_of_lt km1.isLt)
      have hdk_eq :
          dk = GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) := by
        simpa using hvalid.d_eq k (Nat.lt_succ_of_lt hk)
      have hdkNext_eq :
          dkNext = GramSchmidt.Int.gramDet s.b (k + 1) (Nat.succ_le_of_lt hk) := by
        simpa using hvalid.d_eq (k + 1) (Nat.succ_lt_succ hk)
      have hB_eq :
          B = GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 := by
        rw [hB_def]
        simpa [GramSchmidt.entry, Matrix.row, vector_get_eq_getElem] using
          hvalid.ν_eq kFin.val km1.val kFin.isLt km1.isLt (by omega)
      have hdk_kFin_ne_zero :
          GramSchmidt.Int.gramDet s.b kFin.val (Nat.le_of_lt kFin.isLt) ≠ 0 := by
        change GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) ≠ 0
        exact hdk_ne_zero
      -- Cache the adjacent-swap pivot identity to use in d_eq + ν_eq.
      have hgramPivot :=
        GramSchmidt.Int.gramDet_adjacentSwap_pivot s.b kFin hk0 hdk_kFin_ne_zero
      have hkm1_lt_n : km1.val < n := km1.isLt
      have hkm1_le_n : km1.val ≤ n := Nat.le_of_lt km1.isLt
      -- Pre-compute the "upd" function used in the outer foldl, so we can apply
      -- `foldl_modify_rows_get`. The body matches the foldl in `swapStep`,
      -- which destructures `pairs.get i = ((s.ν.getRow i).get kFin, (s.ν.getRow i).get km1)`
      -- in the `k < i.val` branch (see `hpairs_at` below).
      let pairs : Vector (Int × Int) n :=
        Vector.ofFn fun i =>
          if _ : k < i.val then ((s.ν.getRow i).get kFin, (s.ν.getRow i).get km1)
          else (0, 0)
      let upd : Fin n → Vector Int n → Vector Int n :=
        fun i row =>
          let prev :=
            (Int.ofNat dkPrev * (pairs.get i).1 + B * (pairs.get i).2) / Int.ofNat dk
          let curr :=
            (Int.ofNat dkNext * (pairs.get i).2 - B * (pairs.get i).1) / Int.ofNat dk
          (row.set km1 prev).set kFin curr
      have hpairs_at : ∀ (i : Fin n), k < i.val →
          pairs.get i = ((s.ν.getRow i).get kFin, (s.ν.getRow i).get km1) := by
        intro i hi
        show (Vector.ofFn _)[i.1] = _
        rw [Vector.getElem_ofFn]
        exact dif_pos hi
      have hkm1_ne_kFin : km1 ≠ kFin := by
        intro h; rw [h] at hkm1_lt_k; omega
      have hkm1_val_ne_kFin : km1.val ≠ kFin.val := fun h =>
        hkm1_ne_kFin (Fin.eq_of_val_eq h)
      refine ⟨?_, ?_⟩
      · -- ν_eq: case-split on (i, j) relative to km1 and k.
        intro i j hi hj hji
        set b' : Hex.Matrix Int n m := GramSchmidt.Int.adjacentSwap s.b kFin hk0 with hb'_def
        set iFin : Fin n := ⟨i, hi⟩ with hiFin_def
        set jFin : Fin n := ⟨j, hj⟩ with hjFin_def
        have hjiFin : jFin.val < iFin.val := hji
        -- Define the abbreviations for the inner foldl base, so we can use
        -- per-row characterization lemmas without copying expressions.
        set νRowsSwapped : Hex.Matrix Int n n :=
          (s.ν.modifyRow km1.val (setPrefix (s.ν.getRow kFin) · km1)).modifyRow kFin.val
            (setPrefix (s.ν.getRow km1) · km1) with hνRows_def
        set νPivot : Hex.Matrix Int n n := νRowsSwapped.modifyRow kFin.val (·.set km1 B)
          with hνPivot_def
        -- Unfold the goal to expose the ν' foldl, then apply
        -- `foldl_modify_rows_get`.
        simp only [Fin.foldl_eq_finRange_foldl]
        change
          (((List.finRange n).foldl
              (fun (ν : Hex.Matrix Int n n) (i : Fin n) =>
                if _ : k < i.val then
                  ν.modifyRow i.val (upd i)
                else ν)
              νPivot).getRow iFin).get jFin =
            ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin
        have hν'_get :
            ((List.finRange n).foldl
                (fun (ν : Hex.Matrix Int n n) (i : Fin n) =>
                  if k < i.val then ν.modifyRow i.val (upd i) else ν)
                νPivot).getRow iFin =
              if k < iFin.val then upd iFin (νPivot.getRow iFin) else νPivot.getRow iFin := by
          have := foldl_modify_matrix_getRow (n := n) k
            (List.finRange n) (List.nodup_finRange n) νPivot upd iFin
          simp [List.mem_finRange] at this
          exact this
        -- Bridge `if _ : ...` (`dite`) to `if ...` (`ite`).
        have hbody_eq :
            (fun (ν : Hex.Matrix Int n n) (i : Fin n) =>
                if _ : k < i.val then ν.modifyRow i.val (upd i) else ν) =
              (fun (ν : Hex.Matrix Int n n) (i : Fin n) =>
                if k < i.val then ν.modifyRow i.val (upd i) else ν) := by
          funext ν i
          split <;> rfl
        rw [hbody_eq, hν'_get]
        -- Helper: evaluate νRowsSwapped.getRow at a given row.
        have hνRows_get_ne :
            ∀ (l : Fin n), l.val ≠ km1.val → l.val ≠ kFin.val →
              νRowsSwapped.getRow l = s.ν.getRow l := by
          intro l hl_km1 hl_kFin
          rw [hνRows_def, Hex.Matrix.getRow_modifyRow_ne _ kFin.val _ l (fun h => hl_kFin h.symm),
            Hex.Matrix.getRow_modifyRow_ne _ km1.val _ l (fun h => hl_km1 h.symm)]
        have hνRows_get_km1 : νRowsSwapped.getRow km1 = setPrefix (s.ν.getRow kFin) (s.ν.getRow km1) km1 := by
          rw [hνRows_def, Hex.Matrix.getRow_modifyRow_ne _ kFin.val _ km1 (fun h => hkm1_val_ne_kFin h.symm)]
          exact Hex.Matrix.getRow_modifyRow_self _ km1 _
        have hνRows_get_kFin :
            νRowsSwapped.getRow kFin = setPrefix (s.ν.getRow km1) (s.ν.getRow kFin) km1 := by
          rw [hνRows_def, Hex.Matrix.getRow_modifyRow_self _ kFin _,
            Hex.Matrix.getRow_modifyRow_ne _ km1.val _ kFin hkm1_val_ne_kFin]
        -- Evaluate νPivot.get.
        have hνPivot_get_ne :
            ∀ (l : Fin n), l.val ≠ kFin.val → νPivot.getRow l = νRowsSwapped.getRow l := by
          intro l hl_kFin
          rw [hνPivot_def]
          exact Hex.Matrix.getRow_modifyRow_ne _ kFin.val _ l (fun h => hl_kFin h.symm)
        have hνPivot_get_kFin :
            νPivot.getRow kFin = (νRowsSwapped.getRow kFin).set km1.val B hkm1_lt_n := by
          rw [hνPivot_def]
          exact Hex.Matrix.getRow_modifyRow_self _ kFin _
        -- Cache the `Valid` bridge from ν entries to scaledCoeffs.
        have hν_eq := hvalid.ν_eq
        -- Now case analysis on iFin's position.
        by_cases hki : k < iFin.val
        · -- Case D: k < iFin.val. ν' = upd iFin (νPivot.getRow iFin) and iFin ≠ km1, ≠ kFin.
          rw [if_pos hki]
          have hi_ne_km1 : iFin.val ≠ km1.val := by
            have : iFin.val > km1.val := by omega
            omega
          have hi_ne_kFin : iFin.val ≠ kFin.val := by
            have : iFin.val > kFin.val := hki
            omega
          rw [hνPivot_get_ne iFin hi_ne_kFin, hνRows_get_ne iFin hi_ne_km1 hi_ne_kFin]
          -- Now LHS = (upd iFin (s.ν.getRow iFin)).get jFin. Unfold `upd` to expose
          -- the `pairs.get iFin` reference, then substitute it with its explicit
          -- value (valid since `k < iFin.val` in this branch).
          show ((let prev := (Int.ofNat dkPrev * (pairs.get iFin).1 +
                              B * (pairs.get iFin).2) / Int.ofNat dk
                 let curr := (Int.ofNat dkNext * (pairs.get iFin).2 -
                              B * (pairs.get iFin).1) / Int.ofNat dk
                 ((s.ν.getRow iFin).set km1 prev).set kFin curr).get jFin) =
            ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin
          rw [show pairs.get iFin = ((s.ν.getRow iFin).get kFin, (s.ν.getRow iFin).get km1)
              from hpairs_at iFin hki]
          show ((((s.ν.getRow iFin).set km1.val
                ((Int.ofNat dkPrev * (s.ν.getRow iFin).get kFin +
                    B * (s.ν.getRow iFin).get km1) /
                  Int.ofNat dk) hkm1_lt_n).set kFin.val
              ((Int.ofNat dkNext * (s.ν.getRow iFin).get km1 -
                  B * (s.ν.getRow iFin).get kFin) /
                Int.ofNat dk) hk).get jFin) =
            ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin
          -- Bridge `s.ν.getRow iFin .get k(Fin/m1)` to `scaledCoeffs s.b ...` for the
          -- two pivot columns used by the formulas.
          have hν_at_kFin :
              (s.ν.getRow iFin).get kFin =
                GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) iFin kFin := by
            have := hν_eq iFin.val kFin.val iFin.isLt kFin.isLt
              (by rw [hkFinVal]; exact hki)
            simpa [GramSchmidt.entry, Matrix.row, vector_get_eq_getElem] using this
          have hν_at_km1 :
              (s.ν.getRow iFin).get km1 =
                GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) iFin km1 := by
            have hkm1_lt_i : km1.val < iFin.val := by omega
            have := hν_eq iFin.val km1.val iFin.isLt km1.isLt hkm1_lt_i
            simpa [GramSchmidt.entry, Matrix.row, vector_get_eq_getElem] using this
          by_cases hjk : jFin.val = kFin.val
          · -- D2: jFin = kFin. Outer .set kFin curr_i applies.
            rw [show jFin = kFin from Fin.eq_of_val_eq hjk]
            show ((((s.ν.getRow iFin).set km1.val _ hkm1_lt_n).set kFin.val _ hk).get kFin) = _
            rw [show ∀ (xs : Vector Int n) (x : Int),
                      (xs.set kFin.val x hk).get kFin = x from
                  fun xs x => Vector.getElem_set_self hk]
            rw [hdkNext_eq, hdk_eq, hB_eq, hν_at_kFin, hν_at_km1]
            have hsc := GramSchmidt.Int.scaledCoeffs_adjacentSwap_above_curr s.b kFin hk0
              iFin hki hdk_kFin_ne_zero
            change _ = GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs b') iFin kFin
            rw [hsc]
            unfold GramSchmidt.Int.adjacentSwapScaledCoeffAboveCurrNumerator
                  GramSchmidt.Int.adjacentSwapDenom
                  GramSchmidt.Int.adjacentSwapPivotCoeff
            rfl
          · by_cases hjkm1 : jFin.val = km1.val
            · -- D1: jFin = km1. Outer .set kFin doesn't affect km1; inner .set km1 prev_i applies.
              rw [show jFin = km1 from Fin.eq_of_val_eq hjkm1]
              have hkFin_ne_km1 : kFin.val ≠ km1.val := fun h => hkm1_val_ne_kFin h.symm
              show ((((s.ν.getRow iFin).set km1.val _ hkm1_lt_n).set kFin.val _ hk).get km1) = _
              rw [show ((((s.ν.getRow iFin).set km1.val _ hkm1_lt_n).set kFin.val _ hk).get km1) =
                    (((s.ν.getRow iFin).set km1.val _ hkm1_lt_n).get km1) from
                  Vector.getElem_set_ne (h := hkFin_ne_km1) _ km1.isLt]
              rw [show (((s.ν.getRow iFin).set km1.val _ hkm1_lt_n).get km1) = _ from
                  Vector.getElem_set_self hkm1_lt_n]
              rw [hdkPrev_eq, hdk_eq, hB_eq, hν_at_kFin, hν_at_km1]
              have hsc := GramSchmidt.Int.scaledCoeffs_adjacentSwap_above_prev s.b kFin hk0
                iFin hki hdk_kFin_ne_zero
              change _ = GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs b') iFin
                (GramSchmidt.prevRow kFin hk0)
              rw [hsc]
              unfold GramSchmidt.Int.adjacentSwapScaledCoeffAbovePrevNumerator
                    GramSchmidt.Int.adjacentSwapDenom
                    GramSchmidt.Int.adjacentSwapPivotCoeff
              rfl
            · -- D3: jFin ≠ km1, ≠ kFin. Both .sets miss jFin.
              have hkFin_ne_jFin : kFin.val ≠ jFin.val := fun h => hjk h.symm
              have hkm1_ne_jFin : km1.val ≠ jFin.val := fun h => hjkm1 h.symm
              show ((((s.ν.getRow iFin).set km1.val _ hkm1_lt_n).set kFin.val _ hk).get jFin) = _
              rw [show ((((s.ν.getRow iFin).set km1.val _ hkm1_lt_n).set kFin.val _ hk).get jFin) =
                    (((s.ν.getRow iFin).set km1.val _ hkm1_lt_n).get jFin) from
                  Vector.getElem_set_ne (h := hkFin_ne_jFin) _ jFin.isLt]
              rw [show (((s.ν.getRow iFin).set km1.val _ hkm1_lt_n).get jFin) = _ from
                  Vector.getElem_set_ne (h := hkm1_ne_jFin) _ jFin.isLt]
              have hν := hν_eq iFin.val jFin.val iFin.isLt jFin.isLt hjiFin
              by_cases hj_lt_km1 : jFin.val < km1.val
              · -- jFin below km1.
                have hsc :=
                  GramSchmidt.Int.scaledCoeffs_adjacentSwap_above_low s.b kFin hk0 iFin jFin
                    hki (by rw [hkFinVal]; omega)
                show (s.ν.getRow iFin)[jFin.val] = _
                calc (s.ν.getRow iFin)[jFin.val]
                    = ((GramSchmidt.Int.scaledCoeffs s.b).getRow iFin).get jFin := hν
                  _ = ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin := by
                        simpa [GramSchmidt.entry, Matrix.row, vector_get_eq_getElem] using hsc.symm
              · -- jFin above kFin.
                have hj_gt_k : kFin.val < jFin.val := by
                  rw [hkFinVal]; rw [hkm1Val] at hj_lt_km1; omega
                have hsc :=
                  GramSchmidt.Int.scaledCoeffs_adjacentSwap_above_high s.b kFin hk0 iFin jFin
                    hki hj_gt_k hjiFin
                show (s.ν.getRow iFin)[jFin.val] = _
                calc (s.ν.getRow iFin)[jFin.val]
                    = ((GramSchmidt.Int.scaledCoeffs s.b).getRow iFin).get jFin := hν
                  _ = ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin := by
                        simpa [GramSchmidt.entry, Matrix.row, vector_get_eq_getElem] using hsc.symm
        · -- Cases A/B/C: iFin.val ≤ k.
          rw [if_neg hki]
          have hki : iFin.val ≤ k := Nat.le_of_not_lt hki
          by_cases hi_eq_k : iFin.val = kFin.val
          · -- Case C: iFin = kFin.
            have hi_eq : iFin = kFin := Fin.eq_of_val_eq hi_eq_k
            rw [hi_eq, hνPivot_get_kFin]
            -- Subcase: jFin = km1 or not.
            by_cases hj_eq_km1 : jFin.val = km1.val
            · -- C1: jFin = km1. The .set km1 B applies.
              have hj_eq : jFin = km1 := Fin.eq_of_val_eq hj_eq_km1
              rw [hj_eq,
                show ((νRowsSwapped.getRow kFin).set km1.val B hkm1_lt_n).get km1 = B from
                    Vector.getElem_set_self km1.isLt]
              -- B = scaledCoeffs b' kFin km1 via hB_eq + scaledCoeffs_adjacentSwap_pivot.
              have hsc := GramSchmidt.Int.scaledCoeffs_adjacentSwap_pivot s.b kFin hk0
              show B = ((GramSchmidt.Int.scaledCoeffs b').getRow kFin).get km1
              calc B = GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 := hB_eq
                _ = ((GramSchmidt.Int.scaledCoeffs s.b).getRow kFin).get km1 := rfl
                _ = ((GramSchmidt.Int.scaledCoeffs b').getRow kFin).get km1 := by
                      have := hsc
                      simp [GramSchmidt.entry, Matrix.row] at this
                      exact this.symm
            · -- C2: jFin.val ≠ km1.val ⇒ jFin.val < km1.val (since jFin.val < k = kFin.val).
              have hj_lt_kFin : jFin.val < kFin.val := by
                rw [← hi_eq_k]; exact hjiFin
              have hj_lt_km1 : jFin.val < km1.val := by
                have : jFin.val < k := by rw [hkFinVal] at hj_lt_kFin; exact hj_lt_kFin
                omega
              have hj_succ_lt_k : jFin.val + 1 < k := by omega
              have hj_ne_km1 : km1.val ≠ jFin.val := fun h => hj_eq_km1 h.symm
              rw [show ((νRowsSwapped.getRow kFin).set km1.val B hkm1_lt_n).get jFin = _ from
                    Vector.getElem_set_ne (h := hj_ne_km1) _ jFin.isLt]
              rw [hνRows_get_kFin]
              change (setPrefix (s.ν.getRow km1) (s.ν.getRow kFin) km1).get jFin = _
              rw [setPrefix_get_lt jFin hj_lt_km1]
              have hν := hν_eq km1.val jFin.val km1.isLt jFin.isLt hj_lt_km1
              have hsc :=
                GramSchmidt.Int.scaledCoeffs_adjacentSwap_lower_curr s.b kFin hk0 jFin
                  (by rw [hkFinVal]; exact hj_succ_lt_k)
              show (s.ν.getRow km1).get jFin =
                ((GramSchmidt.Int.scaledCoeffs b').getRow kFin).get jFin
              calc (s.ν.getRow km1).get jFin
                  = ((GramSchmidt.Int.scaledCoeffs s.b).getRow km1).get jFin := hν
                _ = ((GramSchmidt.Int.scaledCoeffs b').getRow kFin).get jFin := by
                      simpa [GramSchmidt.entry, Matrix.row, vector_get_eq_getElem] using hsc.symm
          · -- iFin.val < k.
            have hi_lt_k : iFin.val < kFin.val := lt_of_le_of_ne hki hi_eq_k
            by_cases hi_eq_km1 : iFin.val = km1.val
            · -- Case B: iFin = km1.
              have hi_eq : iFin = km1 := Fin.eq_of_val_eq hi_eq_km1
              have hi_ne_kFin : iFin.val ≠ kFin.val := by
                rw [hi_eq_km1, hkFinVal]; omega
              have hj_lt_km1 : jFin.val < km1.val := by
                have : jFin.val < iFin.val := hjiFin
                omega
              have hj_succ_lt_k : jFin.val + 1 < k := by omega
              have hj_lt_kFin : jFin.val < kFin.val := by rw [hkFinVal]; omega
              rw [hνPivot_get_ne iFin hi_ne_kFin, hi_eq, hνRows_get_km1,
                  setPrefix_get_lt (km1 := km1) jFin hj_lt_km1]
              have hν := hν_eq kFin.val jFin.val kFin.isLt jFin.isLt hj_lt_kFin
              have hsc :=
                GramSchmidt.Int.scaledCoeffs_adjacentSwap_lower_prev s.b kFin hk0 jFin
                  (by rw [hkFinVal]; exact hj_succ_lt_k)
              -- The lemma uses `GramSchmidt.entry`, which is `(M.row _)[_]`;
              -- our goal uses `(M.getRow _).get _`. Bridge via simp.
              show (s.ν.getRow kFin).get jFin =
                ((GramSchmidt.Int.scaledCoeffs b').getRow km1).get jFin
              calc (s.ν.getRow kFin).get jFin
                  = ((GramSchmidt.Int.scaledCoeffs s.b).getRow kFin).get jFin := hν
                _ = ((GramSchmidt.Int.scaledCoeffs b').getRow km1).get jFin := by
                      simpa [GramSchmidt.entry, Matrix.row, vector_get_eq_getElem] using hsc.symm
            · -- Case A: iFin.val < km1.val.
              have hi_lt_km1 : iFin.val < km1.val := by omega
              have hi_ne_km1 : iFin.val ≠ km1.val := Nat.ne_of_lt hi_lt_km1
              have hi_ne_kFin : iFin.val ≠ kFin.val := by
                rw [hkFinVal]; omega
              rw [hνPivot_get_ne iFin hi_ne_kFin, hνRows_get_ne iFin hi_ne_km1 hi_ne_kFin]
              -- LHS = (s.ν.getRow iFin).get jFin. Bridge through Valid then
              -- scaledCoeffs_adjacentSwap_before.
              have hν := hν_eq iFin.val jFin.val iFin.isLt jFin.isLt hjiFin
              have hsc :=
                GramSchmidt.Int.scaledCoeffs_adjacentSwap_before s.b kFin hk0 iFin jFin
                  (by rw [hkFinVal]; omega) hjiFin
              -- The goal is `(s.ν[iFin])[jFin] = scaledCoeffs b' [iFin][jFin]`.
              show (s.ν.getRow iFin).get jFin =
                ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin
              calc (s.ν.getRow iFin).get jFin
                  = ((GramSchmidt.Int.scaledCoeffs s.b).getRow iFin).get jFin := hν
                _ = ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin := hsc.symm
      · -- d_eq: case-split on whether i = k.
        intro i hi
        change
          (s.d.set k (Int.toNat
              ((Int.ofNat dkNext * Int.ofNat dkPrev + B ^ 2) / Int.ofNat dk))
            (Nat.lt_succ_of_lt hk)).get ⟨i, hi⟩ =
            GramSchmidt.Int.gramDet (GramSchmidt.Int.adjacentSwap s.b kFin hk0) i
              (Nat.le_of_lt_succ hi)
        by_cases hik : i = k
        · subst hik
          rw [show (s.d.set i _ (Nat.lt_succ_of_lt hk)).get ⟨i, hi⟩ = _ from
                Vector.getElem_set_self (xs := s.d) hi]
          rw [hdkNext_eq, hdkPrev_eq, hdk_eq, hB_eq]
          have hgramPivot' := hgramPivot
          dsimp only at hgramPivot'
          -- Normalise `Int.ofNat` ↔ `↑` to align with `hgramPivot'`.
          show
            ((((GramSchmidt.Int.gramDet s.b (i + 1) (Nat.succ_le_of_lt hk) : Nat) : Int) *
                  ((GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) +
                GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 ^ 2) /
                ((GramSchmidt.Int.gramDet s.b i (Nat.le_of_lt hk) : Nat) : Int)).toNat =
              GramSchmidt.Int.gramDet (GramSchmidt.Int.adjacentSwap s.b kFin hk0) i
                (Nat.le_of_lt_succ hi)
          rw [← hgramPivot']
          exact Int.toNat_natCast _
        · rw [show (s.d.set k _ (Nat.lt_succ_of_lt hk)).get ⟨i, hi⟩ = _ from
                Vector.getElem_set_ne (h := fun h => hik h.symm) (xs := s.d) _ hi]
          have hvalid_d := hvalid.d_eq i hi
          change s.d.get ⟨i, hi⟩ =
            GramSchmidt.Int.gramDet (GramSchmidt.Int.adjacentSwap s.b kFin hk0) i
              (Nat.le_of_lt_succ hi)
          rw [hvalid_d]
          exact (GramSchmidt.Int.gramDet_adjacentSwap_of_ne s.b kFin hk0 i
                  (Nat.le_of_lt_succ hi) hik).symm
    · rw [dif_neg hk0]
      exact hvalid
  · rw [dif_neg hk]
    exact hvalid

/-- Adjacent swap preserves the executable Gram-determinant independence
predicate.  Mirrors `sizeReduce_independent` for the swap step of the LLL
inner loop. -/
theorem swapStep_independent (s : LLLState n m) (k : Nat)
    (hind : s.b.independent) (_hvalid : s.Valid) (hk0 : 0 < k) (hk : k < n) :
    (s.swapStep k).b.independent := by
  rw [swapStep_b_eq s k hk hk0]
  intro t
  let kFin : Fin n := ⟨k, hk⟩
  let km1 : Fin n := GramSchmidt.prevRow kFin hk0
  have hkFinVal : kFin.val = k := rfl
  have hkm1Val : km1.val = k - 1 := by
    show (GramSchmidt.prevRow kFin hk0).val = k - 1
    dsimp [GramSchmidt.prevRow]
  have hkm1 : km1.val + 1 = k := by omega
  have hkm1_lt_k : km1.val < k := by omega
  have hdk_pos : 0 < GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) := by
    have h := hind ⟨km1.val, Nat.lt_trans hkm1_lt_k hk⟩
    rw [GramSchmidt.Int.gramDet_subst_val s.b k (km1.val + 1) (Nat.le_of_lt hk)
        (Nat.succ_le_of_lt (Nat.lt_trans hkm1_lt_k hk)) hkm1.symm]
    exact h
  have hdkNext_pos :
      0 < GramSchmidt.Int.gramDet s.b (k + 1) (Nat.succ_le_of_lt hk) := hind kFin
  have hdkm1_pos :
      0 < GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) := by
    by_cases hkm1_zero : km1.val = 0
    · -- For an empty prefix, gramDet = 1 by definition.
      rw [GramSchmidt.Int.gramDet_subst_val s.b km1.val 0 (Nat.le_of_lt km1.isLt)
          (Nat.zero_le n) hkm1_zero, GramSchmidt.Int.gramDet_zero]
      exact Nat.zero_lt_one
    · have hpos : 0 < km1.val := Nat.pos_of_ne_zero hkm1_zero
      have h := hind ⟨km1.val - 1, Nat.lt_trans
        (Nat.sub_lt hpos Nat.zero_lt_one) km1.isLt⟩
      rw [GramSchmidt.Int.gramDet_subst_val s.b km1.val (km1.val - 1 + 1)
          (Nat.le_of_lt km1.isLt)
          (Nat.succ_le_of_lt (Nat.lt_trans (Nat.sub_lt hpos Nat.zero_lt_one) km1.isLt))
          (Nat.succ_pred_eq_of_pos hpos).symm]
      exact h
  by_cases hne : t.val + 1 = k
  · -- Pivot case: t.val = k - 1, gramDet b' k > 0 via gramDet_adjacentSwap_pivot.
    have hdk_ne_zero :
        GramSchmidt.Int.gramDet s.b kFin.val (Nat.le_of_lt kFin.isLt) ≠ 0 :=
      Nat.pos_iff_ne_zero.mp hdk_pos
    have hgramPivot :=
      GramSchmidt.Int.gramDet_adjacentSwap_pivot s.b kFin hk0 hdk_ne_zero
    have hdvd :=
      GramSchmidt.Int.adjacentSwap_gramDetNumerator_dvd s.b kFin hk0 hdk_ne_zero
    -- Reduce the goal to `0 < gramDet b' k` (Nat) via index substitution.
    rw [GramSchmidt.Int.gramDet_subst_val (GramSchmidt.Int.adjacentSwap s.b ⟨k, hk⟩ hk0)
        (t.val + 1) k (Nat.succ_le_of_lt t.isLt) (Nat.le_of_lt hk) hne]
    -- Cast to Int and use hgramPivot.
    suffices h : (0 : Int) < ((GramSchmidt.Int.gramDet
        (GramSchmidt.Int.adjacentSwap s.b kFin hk0) k
        (Nat.le_of_lt hk) : Nat) : Int) by
      exact_mod_cast h
    rw [hgramPivot]
    -- Now goal: 0 < (num : Int) / (denom : Int).
    have hdenom_pos :
        (0 : Int) < ((GramSchmidt.Int.gramDet s.b kFin.val
            (Nat.le_of_lt kFin.isLt) : Nat) : Int) := by exact_mod_cast hdk_pos
    have hnum_pos :
        (0 : Int) < (((GramSchmidt.Int.gramDet s.b (kFin.val + 1)
              (Nat.succ_le_of_lt kFin.isLt) : Nat) : Int) *
            ((GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) +
          GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 ^ 2) := by
      have hprod_pos :
          (0 : Int) < ((GramSchmidt.Int.gramDet s.b (kFin.val + 1)
              (Nat.succ_le_of_lt kFin.isLt) : Nat) : Int) *
            ((GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) :=
        Int.mul_pos (by exact_mod_cast hdkNext_pos) (by exact_mod_cast hdkm1_pos)
      have hsq_nn :
          (0 : Int) ≤ GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 ^ 2 :=
        sq_nonneg _
      linarith
    rcases hdvd with ⟨q, hq⟩
    -- hq : adjacentSwapGramDetNumerator = denom * q
    -- After substitution: 0 < (denom * q) / denom = q. Combined with denom > 0 and num > 0, q > 0.
    have hnum_eq :
        ((GramSchmidt.Int.gramDet s.b (kFin.val + 1)
              (Nat.succ_le_of_lt kFin.isLt) : Nat) : Int) *
            ((GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) +
          GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 ^ 2 =
        ((GramSchmidt.Int.gramDet s.b kFin.val (Nat.le_of_lt kFin.isLt) : Nat) : Int) * q := by
      have := hq
      unfold GramSchmidt.Int.adjacentSwapGramDetNumerator
            GramSchmidt.Int.adjacentSwapDenom
            GramSchmidt.Int.adjacentSwapPivotCoeff at this
      exact this
    rw [hnum_eq, Int.mul_ediv_cancel_left _ (by linarith :
        ((GramSchmidt.Int.gramDet s.b kFin.val (Nat.le_of_lt kFin.isLt) : Nat) : Int) ≠ 0)]
    -- Now need: 0 < q. Use that denom * q > 0 and denom > 0.
    have hdq_pos :
        (0 : Int) < ((GramSchmidt.Int.gramDet s.b kFin.val
            (Nat.le_of_lt kFin.isLt) : Nat) : Int) * q := by
      rw [← hnum_eq]; exact hnum_pos
    exact (mul_pos_iff_of_pos_left hdenom_pos).mp hdq_pos
  · -- Non-pivot case.
    have hbridge := GramSchmidt.Int.gramDet_adjacentSwap_of_ne s.b kFin hk0 (t.val + 1)
      (Nat.succ_le_of_lt t.isLt) hne
    rw [hbridge]
    exact hind t

/-! ### Prefix LLL invariants under `swapStep`

For row indices strictly below `k - 1`, both the Gram-Schmidt basis row and
the rational coefficient entries are preserved by `swapStep s k`, because
the swap only touches rows `k - 1` and `k`. These prefix lemmas package
that observation as the building blocks for the `prefixLLLReduced`
preservation corollary below. -/

/-- For `i + 1 < k`, the squared norm of the `i`-th Gram-Schmidt basis row
is unchanged by `swapStep s k`. -/
theorem swapStep_basisNormSq_below (s : LLLState n m) (k : Nat) (hk : k < n)
    (hk0 : 0 < k) (i : Nat) (hi : i + 1 < k) :
    LLLCore.basisNormSq (GramSchmidt.Int.basis (s.swapStep k).b)
        ⟨i, Nat.lt_of_succ_lt (Nat.lt_trans hi hk)⟩ =
      LLLCore.basisNormSq (GramSchmidt.Int.basis s.b)
        ⟨i, Nat.lt_of_succ_lt (Nat.lt_trans hi hk)⟩ := by
  rw [swapStep_b_eq s k hk hk0]
  unfold LLLCore.basisNormSq
  rw [GramSchmidt.Int.basis_adjacentSwap_of_lt s.b ⟨k, hk⟩ hk0
        ⟨i, Nat.lt_of_succ_lt (Nat.lt_trans hi hk)⟩ hi]

/-- For `j < i` and `i + 1 < k`, the rational Gram-Schmidt coefficient at
position `(i, j)` is unchanged by `swapStep s k`. -/
theorem swapStep_coeffs_below (s : LLLState n m) (k : Nat) (hk : k < n)
    (hk0 : 0 < k) (i j : Nat) (hi : i + 1 < k) (hji : j < i) :
    (GramSchmidt.Int.coeffs (s.swapStep k).b)[(⟨i, Nat.lt_of_succ_lt
          (Nat.lt_trans hi hk)⟩ : Fin n)][(⟨j, Nat.lt_trans hji
            (Nat.lt_of_succ_lt (Nat.lt_trans hi hk))⟩ : Fin n)] =
      (GramSchmidt.Int.coeffs s.b)[(⟨i, Nat.lt_of_succ_lt
          (Nat.lt_trans hi hk)⟩ : Fin n)][(⟨j, Nat.lt_trans hji
            (Nat.lt_of_succ_lt (Nat.lt_trans hi hk))⟩ : Fin n)] := by
  rw [swapStep_b_eq s k hk hk0]
  set kFin : Fin n := ⟨k, hk⟩ with hkFin_def
  set km1 : Fin n := GramSchmidt.prevRow kFin hk0 with hkm1_def
  have hkm1_succ : km1.val + 1 = kFin.val := by
    simp [km1, GramSchmidt.prevRow, kFin]; omega
  have hikm1 : i < km1.val := by
    simp [km1, GramSchmidt.prevRow, kFin]; omega
  have hcoeff := GramSchmidt.Int.coeffs_rowSwap_adjacent_before
    s.b km1 kFin
    ⟨i, Nat.lt_of_succ_lt (Nat.lt_trans hi hk)⟩
    ⟨j, Nat.lt_trans hji (Nat.lt_of_succ_lt (Nat.lt_trans hi hk))⟩
    hkm1_succ hikm1 hji
  simpa [GramSchmidt.Int.adjacentSwap, GramSchmidt.entry, Matrix.row,
    kFin, km1] using hcoeff

end Internal.LLLState

/-- The prefix `δ`-LLL-reduced predicate: the first `k` Gram-Schmidt rows
satisfy size reduction (for all `i < k`, `j < i`) and the adjacent Lovász
condition at `(i, i + 1)` (for all `i + 1 < k`). At `k = n` this coincides
with `isLLLReduced`; at `k ≤ 1` it is vacuously true. -/
@[expose]
def prefixLLLReduced (b : Matrix Int n m) (k : Nat) (δ : Rat) : Prop :=
  let basis := GramSchmidt.Int.basis b
  let coeffs := GramSchmidt.Int.coeffs b
  (∀ i j, (hik : i < k) → (hin : i < n) → (hji : j < i) →
      let iFin : Fin n := ⟨i, hin⟩
      let jFin : Fin n := ⟨j, Nat.lt_trans hji hin⟩
      let μ := coeffs[iFin][jFin]
      4 * μ * μ ≤ 1) ∧
    ∀ i, (hik : i + 1 < k) → (hin : i + 1 < n) →
      let iFin : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hin⟩
      let ip1Fin : Fin n := ⟨i + 1, hin⟩
      let μ := coeffs[ip1Fin][iFin]
      δ * LLLCore.basisNormSq basis iFin ≤
        LLLCore.basisNormSq basis ip1Fin + μ * μ * LLLCore.basisNormSq basis iFin

/-- Shrinking the row prefix weakens the predicate. -/
theorem prefixLLLReduced.mono {b : Matrix Int n m} {k k' : Nat} {δ : Rat}
    (h : prefixLLLReduced b k δ) (hk : k' ≤ k) : prefixLLLReduced b k' δ := by
  refine ⟨?_, ?_⟩
  · intro i j hik' hin hji
    exact h.1 i j (Nat.lt_of_lt_of_le hik' hk) hin hji
  · intro i hik' hin
    exact h.2 i (Nat.lt_of_lt_of_le hik' hk) hin

/-- Extending the prefix by one row: given `prefixLLLReduced b k δ`, the new
size-reducedness data for row `k` and the new Lovász data at the pair
`(k - 1, k)` (vacuous when `k = 0`) jointly yield `prefixLLLReduced b (k + 1) δ`.
This is the "add one row to the certified prefix" lemma consumed by the
`lllLoop` advance branch. -/
theorem prefixLLLReduced.advance {b : Matrix Int n m} {k : Nat} (hk : k < n) {δ : Rat}
    (hpre : prefixLLLReduced b k δ)
    (hsize : ∀ (j : Nat) (hj : j < k),
      let kFin : Fin n := ⟨k, hk⟩
      let jFin : Fin n := ⟨j, Nat.lt_trans hj hk⟩
      let μ : Rat := (GramSchmidt.Int.coeffs b)[kFin][jFin]
      4 * μ * μ ≤ 1)
    (hlovasz : (hk0 : 0 < k) →
      let kFin : Fin n := ⟨k, hk⟩
      let km1Fin : Fin n := ⟨k - 1, Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk⟩
      let μ : Rat := (GramSchmidt.Int.coeffs b)[kFin][km1Fin]
      δ * LLLCore.basisNormSq (GramSchmidt.Int.basis b) km1Fin ≤
        LLLCore.basisNormSq (GramSchmidt.Int.basis b) kFin +
          μ * μ * LLLCore.basisNormSq (GramSchmidt.Int.basis b) km1Fin) :
    prefixLLLReduced b (k + 1) δ := by
  refine ⟨?_, ?_⟩
  · -- Size-reducedness at row i ≤ k.
    intro i j hik' hin hji
    rcases Nat.lt_or_ge i k with hik | hik
    · exact hpre.1 i j hik hin hji
    · have hi_eq : i = k := Nat.le_antisymm (Nat.lt_succ_iff.mp hik') hik
      have hj_lt_k : j < k := hi_eq ▸ hji
      have hg := hsize j hj_lt_k
      let iFin : Fin n := ⟨i, hin⟩
      let jFin : Fin n := ⟨j, Nat.lt_trans hji hin⟩
      let μ : Rat := (GramSchmidt.Int.coeffs b)[iFin][jFin]
      show 4 * μ * μ ≤ 1
      have hi_fin : (⟨k, hk⟩ : Fin n) = iFin := Fin.ext hi_eq.symm
      have hj_fin : (⟨j, Nat.lt_trans hj_lt_k hk⟩ : Fin n) = jFin :=
        Fin.ext rfl
      have key := hg
      simp only [hi_fin, hj_fin] at key
      exact key
  · -- Lovász at pair i ≤ k - 1, i + 1 ≤ k.
    intro i hik' hin
    rcases Nat.lt_or_ge (i + 1) k with hik | hik
    · exact hpre.2 i hik hin
    · have hip1_eq : i + 1 = k := Nat.le_antisymm (Nat.lt_succ_iff.mp hik') hik
      have hk0 : 0 < k := by omega
      have hi_eq : i = k - 1 := by omega
      have hg := hlovasz hk0
      have hin_i : i < n := Nat.lt_of_succ_lt hin
      let iFin : Fin n := ⟨i, hin_i⟩
      let ip1Fin : Fin n := ⟨i + 1, hin⟩
      let μ : Rat := (GramSchmidt.Int.coeffs b)[ip1Fin][iFin]
      let N_i : Rat := LLLCore.basisNormSq (GramSchmidt.Int.basis b) iFin
      let N_ip1 : Rat := LLLCore.basisNormSq (GramSchmidt.Int.basis b) ip1Fin
      show δ * N_i ≤ N_ip1 + μ * μ * N_i
      have hi_fin : (⟨k - 1, Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk⟩ : Fin n) = iFin :=
        Fin.ext hi_eq.symm
      have hip1_fin : (⟨k, hk⟩ : Fin n) = ip1Fin :=
        Fin.ext (by show k = i + 1; omega)
      have key := hg
      simp only [hi_fin, hip1_fin] at key
      exact key

/-- At the empty prefix `k = 1`, `prefixLLLReduced` holds vacuously: the
`i < 1` (so `i = 0`, then `j < 0` impossible) and `i + 1 < 1` quantifiers are
empty. This is the starting state for the `lllLoop` invariant induction. -/
theorem prefixLLLReduced_one (b : Matrix Int n m) (δ : Rat) :
    prefixLLLReduced b 1 δ := by
  refine ⟨?_, ?_⟩
  · intro i j hi _ hji
    interval_cases i
    exact absurd hji (Nat.not_lt_zero j)
  · intro i hi _
    omega

/-- At the full prefix `k = n`, `prefixLLLReduced` upgrades to
`isLLLReduced b δ (1/2)`: `prefixLLLReduced` always carries the algorithm's
classical `|μ| ≤ 1/2` size-reduction guarantee, which is the
`η = 1/2` instance of the size-reduced condition `μ² ≤ η²`. -/
theorem prefixLLLReduced_to_isLLLReduced (b : Matrix Int n m) (δ : Rat)
    (h : prefixLLLReduced b n δ) : isLLLReduced b δ (1 / 2) := by
  let coeffs := GramSchmidt.Int.coeffs b
  refine ⟨?_, ?_⟩
  · intro i j hi hji
    have h4 := h.1 i j hi hi hji
    -- `h4 : 4 * μ * μ ≤ 1`. Goal: `μ * μ ≤ (1/2) * (1/2)`.
    let iFin : Fin n := ⟨i, hi⟩
    let jFin : Fin n := ⟨j, Nat.lt_trans hji hi⟩
    let μ : Rat := coeffs[iFin][jFin]
    show μ * μ ≤ (1 / 2 : Rat) * (1 / 2)
    have h4' : 4 * μ * μ ≤ 1 := h4
    have hhalf : (1 / 2 : Rat) * (1 / 2) = 1 / 4 := by grind
    grind
  · intro i hi
    exact h.2 i hi hi

namespace Internal.LLLState

/-- `swapStep s k` preserves the prefix LLL-reduced predicate, with the
prefix shrunk by one (clamped below by `1` to stay in the trivially-true
regime when `k ≤ 2`).  Mechanism: the swap only touches rows `k - 1` and
`k`, so every Gram-Schmidt quantity at indices strictly below `k - 1` is
preserved (`swapStep_basisNormSq_below`, `swapStep_coeffs_below`). -/
theorem swapStep_prefixLLLReduced (s : LLLState n m) (k : Nat) (δ : Rat)
    (h : prefixLLLReduced s.b k δ) :
    prefixLLLReduced (s.swapStep k).b (max (k - 1) 1) δ := by
  rcases Nat.eq_zero_or_pos k with hk0_eq | hk0_pos
  · -- k = 0: swapStep is identity; conclusion at max(0, 1) = 1 is vacuous.
    subst hk0_eq
    refine ⟨fun i j hik' _ hji => ?_, fun i hik' _ => ?_⟩
    · simp at hik'; omega
    · simp at hik'
  · by_cases hk : k < n
    · -- Active case: 0 < k < n.
      refine ⟨?_, ?_⟩
      · intro i j hik' hin hji
        have hi_pos : 0 < i := Nat.lt_of_le_of_lt (Nat.zero_le _) hji
        have hi_lt : i + 1 < k := by
          rcases Nat.lt_or_ge k 2 with hk_lt | hk_ge
          · interval_cases k
            simp at hik'; omega
          · have hmax_eq : max (k - 1) 1 = k - 1 := max_eq_left (by omega)
            rw [hmax_eq] at hik'; omega
        let iFin : Fin n := ⟨i, hin⟩
        let jFin : Fin n := ⟨j, Nat.lt_trans hji hin⟩
        let μ_swap : Rat := (GramSchmidt.Int.coeffs (s.swapStep k).b)[iFin][jFin]
        let μ : Rat := (GramSchmidt.Int.coeffs s.b)[iFin][jFin]
        show 4 * μ_swap * μ_swap ≤ 1
        have hcoeff : μ_swap = μ :=
          swapStep_coeffs_below s k hk hk0_pos i j hi_lt hji
        have hres : 4 * μ * μ ≤ 1 := h.1 i j (by omega) hin hji
        rw [hcoeff]; exact hres
      · intro i hik' hin
        have hi_lt : i + 2 < k := by
          rcases Nat.lt_or_ge k 3 with hk_lt | hk_ge
          · interval_cases k
            · simp at hik'
            · simp at hik'
          · have hmax_eq : max (k - 1) 1 = k - 1 := max_eq_left (by omega)
            rw [hmax_eq] at hik'; omega
        have hin_i : i < n := Nat.lt_of_succ_lt hin
        let iFin : Fin n := ⟨i, hin_i⟩
        let ip1Fin : Fin n := ⟨i + 1, hin⟩
        let N_swap_i : Rat :=
          LLLCore.basisNormSq (GramSchmidt.Int.basis (s.swapStep k).b) iFin
        let N_swap_ip1 : Rat :=
          LLLCore.basisNormSq (GramSchmidt.Int.basis (s.swapStep k).b) ip1Fin
        let N_i : Rat := LLLCore.basisNormSq (GramSchmidt.Int.basis s.b) iFin
        let N_ip1 : Rat := LLLCore.basisNormSq (GramSchmidt.Int.basis s.b) ip1Fin
        let μ_swap : Rat := (GramSchmidt.Int.coeffs (s.swapStep k).b)[ip1Fin][iFin]
        let μ : Rat := (GramSchmidt.Int.coeffs s.b)[ip1Fin][iFin]
        show δ * N_swap_i ≤ N_swap_ip1 + μ_swap * μ_swap * N_swap_i
        have hb_i : N_swap_i = N_i :=
          swapStep_basisNormSq_below s k hk hk0_pos i (by omega)
        have hb_ip1 : N_swap_ip1 = N_ip1 :=
          swapStep_basisNormSq_below s k hk hk0_pos (i + 1) hi_lt
        have hcoeff : μ_swap = μ :=
          swapStep_coeffs_below s k hk hk0_pos (i + 1) i hi_lt (Nat.lt_succ_self i)
        have hres : δ * N_i ≤ N_ip1 + μ * μ * N_i := h.2 i (by omega) hin
        rw [hb_i, hb_ip1, hcoeff]; exact hres
    · -- k ≥ n: swapStep is identity, shrink prefix via monotonicity.
      have hsw : s.swapStep k = s := by
        unfold swapStep; rw [dif_neg hk]
      rw [hsw]
      apply h.mono
      apply max_le <;> omega

/-! ### Size-reduce Valid preservation

The single-column update `sizeReduceColumn` edits `b`, `ν` at row `k`,
and leaves `d` alone.  Validity is preserved because the integer
`(b, ν)` update mirrors the Mathlib-side `scaledCoeffs` updates
(`scaledCoeffs_sizeReduce_pivot`/`_lower`/`_above_pivot`/`_other_row`)
and the Gram-determinants are unchanged (`gramDet_sizeReduce`). -/

/-- Field projection: `sizeReduceColumn`'s `.b` field under the reducing branch. -/
private theorem sizeReduceColumn_b_reduce (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val)
    (hreduce : 2 * Int.natAbs ((s.ν.getRow k).get j) >
      s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) :
    (s.sizeReduceColumn j k hjk).b =
      GramSchmidt.Int.sizeReduce s.b j k
        (nearestQuotient ((s.ν.getRow k).get j)
          (s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)) := by
  unfold sizeReduceColumn; rw [dif_pos hreduce]

/-- Field projection: `sizeReduceColumn`'s `.d` field (always unchanged). -/
private theorem sizeReduceColumn_d_eq (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) :
    (s.sizeReduceColumn j k hjk).d = s.d := by
  unfold sizeReduceColumn
  by_cases hreduce :
      2 * Int.natAbs ((s.ν.getRow k).get j) >
        s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · rw [dif_pos hreduce]
  · rw [dif_neg hreduce]

/-- Field projection: `sizeReduceColumn`'s `.ν` row at `k` under the reducing
branch.  Reads exactly the foldl + extra `.set j` from the def body.  Takes
the integer nearest quotient `r` as an explicit parameter so callers can
keep it opaque. -/
private theorem sizeReduceColumn_ν_get_k (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val)
    (hreduce : 2 * Int.natAbs ((s.ν.getRow k).get j) >
      s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
    (r : Int)
    (hr : r = nearestQuotient ((s.ν.getRow k).get j)
      (s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)) :
    (s.sizeReduceColumn j k hjk).ν.getRow k =
      (Fin.foldl j.val
        (fun (row : Vector Int n) (l : Fin j.val) =>
          let lFin : Fin n := ⟨l.val, Nat.lt_trans l.isLt j.isLt⟩
          row.set lFin ((s.ν.getRow k).get lFin - r * (s.ν.getRow j).get lFin))
        (s.ν.getRow k)).set j ((s.ν.getRow k).get j -
          r * Int.ofNat (s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)) := by
  subst hr
  unfold sizeReduceColumn; rw [dif_pos hreduce]
  exact Vector.getElem_set_self k.isLt

/-- Field projection: `sizeReduceColumn`'s `.ν` row at indices other than `k`
under the reducing branch (unchanged). -/
private theorem sizeReduceColumn_ν_get_ne (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val)
    (hreduce : 2 * Int.natAbs ((s.ν.getRow k).get j) >
      s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
    (i : Fin n) (hi : i ≠ k) :
    (s.sizeReduceColumn j k hjk).ν.getRow i = s.ν.getRow i := by
  unfold sizeReduceColumn; rw [dif_pos hreduce]
  exact Vector.getElem_set_ne k.isLt i.isLt (fun h => hi (Fin.eq_of_val_eq h.symm))

/-- The single-column size reduction preserves `Valid`. -/
theorem sizeReduceColumn_valid (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) (hvalid : s.Valid) :
    (s.sizeReduceColumn j k hjk).Valid := by
  by_cases hreduce :
      2 * Int.natAbs ((s.ν.getRow k).get j) >
        s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · -- The reducing branch.  Let r be the integer nearest quotient.
    -- Bridges from Valid to the Mathlib-side scaledCoeffs/gramDet.
    have hν_at : ∀ (i : Fin n) (j' : Fin n), j'.val < i.val →
        (s.ν.getRow i).get j' =
          GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) i j' := by
      intro i j' hj'i
      have := hvalid.ν_eq i.val j'.val i.isLt j'.isLt hj'i
      simpa [GramSchmidt.entry, Matrix.row, vector_get_eq_getElem] using this
    have hd_at : ∀ (i : Nat) (hi : i < n + 1),
        s.d.get ⟨i, hi⟩ =
          GramSchmidt.Int.gramDet s.b i (Nat.le_of_lt_succ hi) :=
      hvalid.d_eq
    set r : Int := nearestQuotient ((s.ν.getRow k).get j)
      (s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) with hr_def
    set b' : Matrix Int n m := GramSchmidt.Int.sizeReduce s.b j k r with hb'_def
    -- The b/d projections.
    have hb_eq : (s.sizeReduceColumn j k hjk).b = b' :=
      sizeReduceColumn_b_reduce s j k hjk hreduce
    have hd_state_eq : (s.sizeReduceColumn j k hjk).d = s.d :=
      sizeReduceColumn_d_eq s j k hjk
    refine ⟨?_, ?_⟩
    · -- ν_eq
      intro iVal jVal hi hj' hji
      set iFin : Fin n := ⟨iVal, hi⟩
      set jFin : Fin n := ⟨jVal, hj'⟩
      have hji' : jFin.val < iFin.val := hji
      show ((s.sizeReduceColumn j k hjk).ν.getRow iFin).get jFin =
        ((GramSchmidt.Int.scaledCoeffs (s.sizeReduceColumn j k hjk).b).getRow iFin).get jFin
      rw [hb_eq]
      by_cases hi_k : iFin = k
      · -- Case iFin = k.
        subst hi_k
        rw [sizeReduceColumn_ν_get_k s j iFin hjk hreduce r hr_def]
        by_cases hj_eq : jFin = j
        · -- Pivot column.
          subst hj_eq
          rw [show ∀ (xs : Vector Int n) (x : Int),
              (xs.set jFin.val x jFin.isLt).get jFin = x from
                fun xs x => Vector.getElem_set_self jFin.isLt]
          rw [hν_at iFin jFin hji']
          -- Want: scaledCoeffs s.b [iFin][jFin] - r * Int.ofNat (s.d[jFin+1]) =
          --       scaledCoeffs b' [iFin][jFin]
          have hd : s.d.get ⟨jFin.val + 1, Nat.succ_lt_succ jFin.isLt⟩ =
              GramSchmidt.Int.gramDet s.b (jFin.val + 1)
                (Nat.succ_le_of_lt jFin.isLt) :=
            hd_at (jFin.val + 1) (Nat.succ_lt_succ jFin.isLt)
          rw [hd]
          have hsc := GramSchmidt.Int.scaledCoeffs_sizeReduce_pivot s.b jFin iFin hjk r
          -- hsc : entry (scaledCoeffs b') iFin jFin =
          --       entry (scaledCoeffs s.b) iFin jFin - r * Int.ofNat (gramDet s.b (jFin+1))
          have hsc' : ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin =
              ((GramSchmidt.Int.scaledCoeffs s.b).getRow iFin).get jFin -
                r * Int.ofNat (GramSchmidt.Int.gramDet s.b (jFin.val + 1)
                  (Nat.succ_le_of_lt jFin.isLt)) := by
            simpa [GramSchmidt.entry, Matrix.row, vector_get_eq_getElem] using hsc
          rw [hsc']
          rfl
        · -- Non-pivot column.  The outer .set j misses jFin.
          rw [show ∀ (xs : Vector Int n) (x : Int),
              (xs.set j.val x j.isLt).get jFin = xs.get jFin from
                fun xs x => Vector.getElem_set_ne j.isLt jFin.isLt
                  (fun h => hj_eq (Fin.eq_of_val_eq h).symm)]
          -- Use foldl_finRange_set_outerSubMul_get_eq to compute rowK_inner[jFin].
          rw [LLLState.foldl_finRange_set_outerSubMul_get_eq j.val
              (Nat.le_of_lt j.isLt) (s.ν.getRow iFin) (s.ν.getRow iFin) (s.ν.getRow j) r jFin]
          by_cases hjlt : jFin.val < j.val
          · -- Below pivot.
            rw [if_pos hjlt, hν_at iFin jFin hji', hν_at j jFin hjlt]
            have hsc :=
              GramSchmidt.Int.scaledCoeffs_sizeReduce_lower s.b jFin j iFin hjlt hjk r
            have hsc' : ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin =
                ((GramSchmidt.Int.scaledCoeffs s.b).getRow iFin).get jFin -
                  r * ((GramSchmidt.Int.scaledCoeffs s.b).getRow j).get jFin := by
              simpa [GramSchmidt.entry, Matrix.row, vector_get_eq_getElem] using hsc
            rw [hsc']
            rfl
          · -- Above pivot.  jFin ≠ j and ¬ (jFin < j), so j < jFin.
            rw [if_neg hjlt]
            have hjge : j.val ≤ jFin.val := Nat.le_of_not_lt hjlt
            have hjlt' : j.val < jFin.val := lt_of_le_of_ne hjge
              (fun h => hj_eq (Fin.eq_of_val_eq h.symm))
            rw [hν_at iFin jFin hji']
            have hjlt_k : jFin.val < iFin.val := hji'
            have hsc :=
              GramSchmidt.Int.scaledCoeffs_sizeReduce_above_pivot s.b j iFin hjk r jFin
                hjlt' hjlt_k
            have hsc' : ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin =
                ((GramSchmidt.Int.scaledCoeffs s.b).getRow iFin).get jFin := by
              simpa [GramSchmidt.entry, Matrix.row, vector_get_eq_getElem] using hsc
            rw [hsc']
            rfl
      · -- Case iFin ≠ k.
        rw [sizeReduceColumn_ν_get_ne s j k hjk hreduce iFin hi_k, hν_at iFin jFin hji']
        have hsc :=
          GramSchmidt.Int.scaledCoeffs_sizeReduce_other_row s.b j k hjk r iFin hi_k
        -- hsc : (scaledCoeffs b').row iFin = (scaledCoeffs s.b).row iFin
        have hsc' : ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin =
            ((GramSchmidt.Int.scaledCoeffs s.b).getRow iFin).get jFin := by
          have hrow := hsc
          rw [Matrix.row, Matrix.row] at hrow
          exact congrArg (fun v : Vector Int n => v.get jFin) hrow
        rw [hsc']
        rfl
    · -- d_eq
      intro i hi
      rw [hd_state_eq, hd_at i hi, hb_eq]
      exact (GramSchmidt.Int.gramDet_sizeReduce s.b j k hjk r i (Nat.le_of_lt_succ hi)).symm
  · -- The non-reducing branch: state unchanged.
    have h_eq : s.sizeReduceColumn j k hjk = s := by
      unfold sizeReduceColumn; rw [dif_neg hreduce]
    rw [h_eq]; exact hvalid

/-- The size-reduction outer foldl preserves `Valid`. -/
theorem sizeReduce_valid (s : LLLState n m) (k : Nat) (hvalid : s.Valid) :
    (s.sizeReduce k).Valid := by
  unfold sizeReduce
  by_cases hk : k < n
  · rw [dif_pos hk]
    -- Foldl over `(List.finRange k).reverse` of sizeReduceColumn applications,
    -- each preserving Valid.
    suffices h : ∀ (xs : List (Fin k)) (s' : LLLState n m), s'.Valid →
        (xs.foldl
            (fun state j =>
              let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
              state.sizeReduceColumn jFin ⟨k, hk⟩ j.isLt)
            s').Valid from by
      simpa [Fin.foldr_eq_finRange_foldr] using h (List.finRange k).reverse s hvalid
    intro xs
    induction xs with
    | nil => intro s' hv; exact hv
    | cons j js ih =>
      intro s' hv
      simp only [List.foldl_cons]
      exact ih _ (sizeReduceColumn_valid s' _ _ _ hv)
  · rw [dif_neg hk]
    exact hvalid

/-! ### Size-reduce size-reducedness

After `LLLState.sizeReduce s k`, the row `k` of the integer scaled coefficients
satisfies `2 * |ν[k][j]| ≤ d[j+1]` for every `j < k` (the integer formulation
of the rational size-reducedness bound `|μ[k][j]| ≤ 1/2`).  Pair with
`scaledCoeffs_eq` to get the rational bound `4 * μ[k][j]² ≤ 1` on the
post-reduction Gram-Schmidt coefficients.  Closes the size-reduction half of
the LLL loop invariant. -/

private theorem nearestQuotient_residue_bound (νjk : Int) (dj1 : Nat)
    (hdpos : 0 < dj1) :
    2 * Int.natAbs (νjk - nearestQuotient νjk dj1 * Int.ofNat dj1) ≤ dj1 := by
  set q : Int := nearestQuotient νjk dj1 with hq_def
  unfold nearestQuotient at hq_def
  have hdj_pos_int : (0 : Int) < Int.ofNat dj1 := by
    show (0 : Int) < (dj1 : Int)
    exact_mod_cast hdpos
  have h2d_pos : (0 : Int) < 2 * Int.ofNat dj1 := by linarith
  set a : Int := 2 * νjk + Int.ofNat dj1 with ha_def
  have hqf : q = Int.fdiv a (2 * Int.ofNat dj1) := hq_def
  have hm_eq : Int.fmod a (2 * Int.ofNat dj1) = a - q * (2 * Int.ofNat dj1) := by
    rw [hqf, Int.fmod_def]; ring
  have hm_nn : (0 : Int) ≤ Int.fmod a (2 * Int.ofNat dj1) :=
    Int.fmod_nonneg_of_pos a h2d_pos
  have hm_lt : Int.fmod a (2 * Int.ofNat dj1) < 2 * Int.ofNat dj1 :=
    Int.fmod_lt_of_pos a h2d_pos
  have h2res : 2 * (νjk - q * Int.ofNat dj1) =
      Int.fmod a (2 * Int.ofNat dj1) - Int.ofNat dj1 := by
    rw [hm_eq, ha_def]; ring
  have hres_lb : -(Int.ofNat dj1) ≤ 2 * (νjk - q * Int.ofNat dj1) := by
    rw [h2res]; omega
  have hres_ub : 2 * (νjk - q * Int.ofNat dj1) ≤ Int.ofNat dj1 := by
    rw [h2res]; omega
  -- omega handles natAbs with linear bounds in Int.
  have hres_lb' : -(dj1 : Int) ≤ 2 * (νjk - q * (dj1 : Int)) := by
    have : (Int.ofNat dj1 : Int) = (dj1 : Int) := rfl
    rw [this] at hres_lb; exact hres_lb
  have hres_ub' : 2 * (νjk - q * (dj1 : Int)) ≤ (dj1 : Int) := by
    have : (Int.ofNat dj1 : Int) = (dj1 : Int) := rfl
    rw [this] at hres_ub; exact hres_ub
  show 2 * Int.natAbs (νjk - q * Int.ofNat dj1) ≤ dj1
  have : (Int.ofNat dj1 : Int) = (dj1 : Int) := rfl
  rw [this]
  omega

private theorem sizeReduceColumn_b_gramDet (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) (t : Nat) (ht : t ≤ n) :
    GramSchmidt.Int.gramDet (s.sizeReduceColumn j k hjk).b t ht =
      GramSchmidt.Int.gramDet s.b t ht := by
  unfold sizeReduceColumn
  by_cases hreduce :
      2 * Int.natAbs ((s.ν.getRow k).get j) >
        s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · rw [dif_pos hreduce]
    exact GramSchmidt.Int.gramDet_sizeReduce s.b j k hjk _ t ht
  · rw [dif_neg hreduce]

private theorem sizeReduceColumn_independent (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) (hind : s.b.independent) :
    (s.sizeReduceColumn j k hjk).b.independent := by
  intro i
  rw [sizeReduceColumn_b_gramDet s j k hjk]
  exact hind i

/-- Per-column pivot bound: after `sizeReduceColumn` at pivot `j`, the
integer `ν[k][j]` satisfies `2 * |ν[k][j]| ≤ d[j+1]`. -/
private theorem sizeReduceColumn_ν_pivot_bound (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val)
    (hdpos : 0 < s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) :
    2 * Int.natAbs (((s.sizeReduceColumn j k hjk).ν.getRow k).get j) ≤
      s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
  by_cases hreduce :
      2 * Int.natAbs ((s.ν.getRow k).get j) >
        s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · rw [sizeReduceColumn_ν_get_k s j k hjk hreduce _ rfl]
    rw [show ∀ (xs : Vector Int n) (x : Int),
            (xs.set j.val x j.isLt).get j = x from
          fun xs x => Vector.getElem_set_self j.isLt]
    exact nearestQuotient_residue_bound _ _ hdpos
  · have h_eq : s.sizeReduceColumn j k hjk = s := by
      unfold sizeReduceColumn; rw [dif_neg hreduce]
    rw [h_eq]
    exact Nat.le_of_not_lt hreduce

/-- Single-column preservation of `ν[k][l]` for columns `l` strictly above
the pivot `j`. -/
private theorem sizeReduceColumn_ν_get_above_pivot (s : LLLState n m)
    (j k : Fin n) (hjk : j.val < k.val) (l : Fin n) (hjl : j.val < l.val) :
    ((s.sizeReduceColumn j k hjk).ν.getRow k).get l = (s.ν.getRow k).get l := by
  by_cases hreduce :
      2 * Int.natAbs ((s.ν.getRow k).get j) >
        s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · rw [sizeReduceColumn_ν_get_k s j k hjk hreduce _ rfl]
    have hj_ne_l : j.val ≠ l.val := Nat.ne_of_lt hjl
    rw [show ∀ (xs : Vector Int n) (x : Int),
            (xs.set j.val x j.isLt).get l = xs.get l from
          fun xs x => Vector.getElem_set_ne j.isLt l.isLt hj_ne_l]
    rw [LLLState.foldl_finRange_set_outerSubMul_get_eq j.val
        (Nat.le_of_lt j.isLt) (s.ν.getRow k) (s.ν.getRow k) (s.ν.getRow j) _ l]
    rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt hjl))]
  · have h_eq : s.sizeReduceColumn j k hjk = s := by
      unfold sizeReduceColumn; rw [dif_neg hreduce]
    rw [h_eq]

/-- `sizeReduceColumn` does not change `s.d`. -/
private theorem sizeReduceColumn_d_get (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) (i : Fin (n + 1)) :
    (s.sizeReduceColumn j k hjk).d.get i = s.d.get i := by
  rw [sizeReduceColumn_d_eq s j k hjk]

/-- Preservation of `ν[k][e]` under foldl, when every element of the foldl
list has value strictly less than `e.val`. -/
private theorem sizeReduce_foldl_preserves_ν_above {n m : Nat}
    (k : Nat) (hk : k < n) (e : Fin n) :
    ∀ (xs : List (Fin k)) (s' : LLLState n m),
      (∀ l ∈ xs, l.val < e.val) →
      ((xs.foldl
          (fun state j =>
            let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
            state.sizeReduceColumn jFin ⟨k, hk⟩ j.isLt)
          s').ν.getRow ⟨k, hk⟩).get e = (s'.ν.getRow ⟨k, hk⟩).get e := by
  intro xs
  induction xs with
  | nil => intros; rfl
  | cons j js ih =>
    intro s' hxs
    have hj_lt_e : j.val < e.val := hxs j List.mem_cons_self
    have hjs_lt_e : ∀ l ∈ js, l.val < e.val := fun l hl =>
      hxs l (List.mem_cons.mpr (Or.inr hl))
    simp only [List.foldl_cons]
    rw [ih _ hjs_lt_e]
    let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
    exact sizeReduceColumn_ν_get_above_pivot s' jFin ⟨k, hk⟩ j.isLt e hj_lt_e

/-- Preservation of `s.d` under foldl. -/
private theorem sizeReduce_foldl_d_get {n m : Nat}
    (k : Nat) (hk : k < n) (i : Fin (n + 1)) :
    ∀ (xs : List (Fin k)) (s' : LLLState n m),
      (xs.foldl
          (fun state j =>
            let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
            state.sizeReduceColumn jFin ⟨k, hk⟩ j.isLt)
          s').d.get i = s'.d.get i := by
  intro xs
  induction xs with
  | nil => intros; rfl
  | cons j js ih =>
    intro s'
    simp only [List.foldl_cons]
    rw [ih _]; rw [sizeReduceColumn_d_get]

/-- Foldl invariant: if the iterating list is strictly decreasing, then after
foldl every iterated column is size-reduced. -/
private theorem sizeReduce_foldl_size_reduced {n m : Nat}
    (k : Nat) (hk : k < n) :
    ∀ (xs : List (Fin k)),
      xs.Pairwise (fun a b : Fin k => b.val < a.val) →
      ∀ (s' : LLLState n m), s'.Valid → s'.b.independent →
        ∀ e ∈ xs,
          2 * Int.natAbs
              (((xs.foldl
                  (fun state j =>
                    let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
                    state.sizeReduceColumn jFin ⟨k, hk⟩ j.isLt)
                  s').ν.getRow ⟨k, hk⟩).get
                ⟨e.val, Nat.lt_trans e.isLt hk⟩) ≤
            s'.d.get ⟨e.val + 1, Nat.succ_lt_succ (Nat.lt_trans e.isLt hk)⟩ := by
  intro xs
  induction xs with
  | nil =>
    intro _ s' _ _ e he
    exact absurd he List.not_mem_nil
  | cons j js ih =>
    intro hpairwise s' hvalid hind e he
    have hpairwise' : js.Pairwise (fun a b : Fin k => b.val < a.val) :=
      List.Pairwise.tail hpairwise
    have hj_gt_js : ∀ l ∈ js, l.val < j.val := by
      intro l hl
      have := List.rel_of_pairwise_cons hpairwise hl
      exact this
    simp only [List.foldl_cons]
    -- Set up the Fin n version of j and the post-step state.
    set jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩ with hjFin_def
    have hjFinLt : jFin.val < k := j.isLt
    set s'' : LLLState n m := s'.sizeReduceColumn jFin ⟨k, hk⟩ hjFinLt with hs''_def
    by_cases h_eq : e = j
    · -- e = j: per-column bound + preservation through js.
      subst h_eq
      have hdpos :
          0 < s'.d.get ⟨jFin.val + 1, Nat.succ_lt_succ jFin.isLt⟩ := by
        have := hvalid.d_eq (jFin.val + 1) (Nat.succ_lt_succ jFin.isLt)
        rw [this]
        exact hind ⟨jFin.val, jFin.isLt⟩
      have hpivot :=
        sizeReduceColumn_ν_pivot_bound s' jFin ⟨k, hk⟩ hjFinLt hdpos
      have hpres :=
        sizeReduce_foldl_preserves_ν_above k hk
          (⟨e.val, Nat.lt_trans e.isLt hk⟩ : Fin n) js
          s'' hj_gt_js
      show 2 * Int.natAbs ((((js.foldl _ s'').ν.getRow ⟨k, hk⟩).get _)) ≤ _
      rw [hpres]
      exact hpivot
    · -- e ∈ js: apply IH (with d preserved through the head step).
      have he_js : e ∈ js := by
        rcases List.mem_cons.mp he with h | h
        · exact absurd h h_eq
        · exact h
      have hd_step := sizeReduceColumn_d_get s' jFin ⟨k, hk⟩ hjFinLt
        ⟨e.val + 1, Nat.succ_lt_succ (Nat.lt_trans e.isLt hk)⟩
      rw [← hd_step]
      exact ih hpairwise' s''
        (sizeReduceColumn_valid s' jFin ⟨k, hk⟩ hjFinLt hvalid)
        (sizeReduceColumn_independent s' jFin ⟨k, hk⟩ hjFinLt hind)
        e he_js

/-- `(List.finRange k).reverse` is Pairwise strictly decreasing. -/
private theorem pairwise_finRange_reverse_lt (k : Nat) :
    ((List.finRange k).reverse).Pairwise (fun a b : Fin k => b.val < a.val) := by
  rw [List.pairwise_reverse, List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [List.length_finRange] at hi hj
  rw [List.getElem_finRange (by rw [List.length_finRange]; exact hi),
    List.getElem_finRange (by rw [List.length_finRange]; exact hj)]
  exact hij

/-- Integer formulation: after `s.sizeReduce k`, every column `j < k` of
row `k` of the scaled coefficients satisfies `2 * |ν[k][j]| ≤ d[j+1]`. -/
theorem sizeReduce_ν_bound (s : LLLState n m) (k : Nat) (hk : k < n)
    (hvalid : s.Valid) (hind : s.b.independent) :
    ∀ (j : Nat) (hj : j < k),
      let kFin : Fin n := ⟨k, hk⟩
      let jFin : Fin n := ⟨j, Nat.lt_trans hj hk⟩
      2 * Int.natAbs (((s.sizeReduce k).ν.getRow kFin).get jFin) ≤
        s.d.get ⟨j + 1, Nat.succ_lt_succ (Nat.lt_trans hj hk)⟩ := by
  intro j hj
  unfold sizeReduce
  rw [dif_pos hk]
  simpa [Fin.foldr_eq_finRange_foldr] using
    sizeReduce_foldl_size_reduced k hk (List.finRange k).reverse
      (pairwise_finRange_reverse_lt k)
      s hvalid hind ⟨j, hj⟩ (List.mem_reverse.mpr (List.mem_finRange _))

/-- **The size-reduce size-reducedness theorem (Sub-issue A of #6576).**
After `LLLState.sizeReduce s k`, the row `k` of the rational Gram-Schmidt
coefficients is size-reduced: `4 * μ[k][j]² ≤ 1` for every `j < k`. -/
theorem sizeReduce_size_reduced (s : LLLState n m) (k : Nat) (hk : k < n)
    (hvalid : s.Valid) (hind : s.b.independent) :
    ∀ (j : Nat) (hj : j < k),
      let kFin : Fin n := ⟨k, hk⟩
      let jFin : Fin n := ⟨j, Nat.lt_trans hj hk⟩
      let μ := GramSchmidt.entry (GramSchmidt.Int.coeffs (s.sizeReduce k).b)
        kFin jFin
      4 * μ * μ ≤ 1 := by
  intro j hj
  have hjn : j < n := Nat.lt_trans hj hk
  have hjsuc : j + 1 ≤ n := Nat.succ_le_of_lt hjn
  -- Integer bound: 2 * |ν'[k][j]| ≤ d[j+1].
  have hν_bound := sizeReduce_ν_bound s k hk hvalid hind j hj
  -- Validity is preserved.
  have hvalid' : (s.sizeReduce k).Valid := sizeReduce_valid s k hvalid
  -- gramDet is preserved by sizeReduce (via d-vector preservation + post-Valid).
  have hgramDet_preserved :
      GramSchmidt.Int.gramDet (s.sizeReduce k).b (j + 1) hjsuc =
        GramSchmidt.Int.gramDet s.b (j + 1) hjsuc := by
    have h1 := hvalid'.d_eq (j + 1) (Nat.succ_lt_succ hjn)
    have h2 := hvalid.d_eq (j + 1) (Nat.succ_lt_succ hjn)
    have h3 : (s.sizeReduce k).d.get ⟨j + 1, Nat.succ_lt_succ hjn⟩ =
        s.d.get ⟨j + 1, Nat.succ_lt_succ hjn⟩ := by
      simpa using congrArg (fun d : Vector Nat (n + 1) =>
        d.get ⟨j + 1, Nat.succ_lt_succ hjn⟩) (sizeReduce_d s k)
    rw [← h1, h3, h2]
  -- gramDet (s.sizeReduce k).b (j+1) > 0 from independence of s.b.
  have hgd_pos : 0 < GramSchmidt.Int.gramDet (s.sizeReduce k).b (j + 1) hjsuc := by
    rw [hgramDet_preserved]
    exact hind ⟨j, hjn⟩
  -- Bridge via scaledCoeffs_eq.
  have hsc := GramSchmidt.Int.scaledCoeffs_eq (s.sizeReduce k).b
    k j hk hj
  -- Cast hν_bound to Rat as `|2 * ν'| ≤ d[j+1]`.
  set kFin : Fin n := ⟨k, hk⟩
  set jFin : Fin n := ⟨j, hjn⟩
  set ν' : Int := ((s.sizeReduce k).ν.getRow kFin).get jFin with hν'_def
  set d_jp1 : Nat := s.d.get ⟨j + 1, Nat.succ_lt_succ hjn⟩ with hd_jp1_def
  set μ : Rat := GramSchmidt.entry (GramSchmidt.Int.coeffs (s.sizeReduce k).b)
    kFin jFin with hμ_def
  -- Cast d_jp1 to Rat is positive.
  have hd_rat_pos : (0 : Rat) < (d_jp1 : Rat) := by
    have hd_nat_pos : 0 < d_jp1 := by
      rw [hd_jp1_def, hvalid.d_eq (j + 1) (Nat.succ_lt_succ hjn)]
      exact hind ⟨j, hjn⟩
    exact_mod_cast hd_nat_pos
  have hd_ne : (d_jp1 : Rat) ≠ 0 := ne_of_gt hd_rat_pos
  -- ν' bridges to μ via scaledCoeffs_eq + Valid.
  have hν'_bridge : (ν' : Rat) = (d_jp1 : Rat) * μ := by
    have hν_at : ν' =
        ((GramSchmidt.Int.scaledCoeffs (s.sizeReduce k).b).getRow kFin).get jFin :=
      hvalid'.ν_eq kFin.val jFin.val kFin.isLt jFin.isLt hj
    have hd_eq_rat : (d_jp1 : Rat) =
        ((GramSchmidt.Int.gramDet (s.sizeReduce k).b (j+1) hjsuc : Nat) : Rat) := by
      rw [hgramDet_preserved]
      show ((s.d.get _ : Nat) : Rat) = ((GramSchmidt.Int.gramDet s.b (j+1) hjsuc : Nat) : Rat)
      rw [hvalid.d_eq (j + 1) (Nat.succ_lt_succ hjn)]
    have hsc' : ((GramSchmidt.entry
        (GramSchmidt.Int.scaledCoeffs (s.sizeReduce k).b) kFin jFin : Int) : Rat) =
      ((GramSchmidt.Int.gramDet (s.sizeReduce k).b (j+1) hjsuc : Nat) : Rat) * μ := hsc
    have hν'_eq : ((ν' : Int) : Rat) =
        ((GramSchmidt.entry
          (GramSchmidt.Int.scaledCoeffs (s.sizeReduce k).b) kFin jFin : Int) : Rat) := by
      rw [hν_at]; rfl
    rw [hν'_eq, hsc', hd_eq_rat]
  -- Now: |2 * ν'| ≤ d_jp1 (as Int), so (2*ν')² ≤ d_jp1² (as Rat).
  have h_int_le : 2 * (ν' : Int).natAbs ≤ (d_jp1 : Nat) := hν_bound
  have habs2_int : |(2 * ν' : Int)| ≤ (d_jp1 : Int) := by
    rw [Int.abs_eq_natAbs, Int.natAbs_mul]
    show ((2 * ν'.natAbs : Nat) : Int) ≤ (d_jp1 : Int)
    exact_mod_cast h_int_le
  have habs2_rat : |(2 * ν' : Rat)| ≤ (d_jp1 : Rat) := by
    have h_cast : |((2 * ν' : Int) : Rat)| ≤ ((d_jp1 : Int) : Rat) := by
      exact_mod_cast habs2_int
    push_cast at h_cast
    exact h_cast
  -- (2 * ν')² ≤ d_jp1² since |·| is bounded.
  have hsq_le : (2 * (ν' : Rat))^2 ≤ (d_jp1 : Rat)^2 := by
    have h := abs_le_abs habs2_rat (by linarith [abs_nonneg (2 * (ν' : Rat))])
    have : |(2 * (ν' : Rat))| ≤ |((d_jp1 : Rat))| := by
      rw [abs_of_nonneg (le_of_lt hd_rat_pos)]
      exact habs2_rat
    calc (2 * (ν' : Rat))^2 = |(2 * (ν' : Rat))|^2 := (sq_abs _).symm
      _ ≤ |((d_jp1 : Rat))|^2 := by
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = (d_jp1 : Rat)^2 := sq_abs _
  -- Conclude 4μ² ≤ 1: 4μ² = (2ν')²/d_jp1² ≤ 1.
  show 4 * μ * μ ≤ 1
  have hμ_eq : μ = (ν' : Rat) / (d_jp1 : Rat) := by
    field_simp
    linarith [hν'_bridge]
  rw [hμ_eq]
  rw [show 4 * ((ν' : Rat) / (d_jp1 : Rat)) * ((ν' : Rat) / (d_jp1 : Rat)) =
      (2 * (ν' : Rat))^2 / (d_jp1 : Rat)^2 by ring]
  rw [div_le_one (by positivity)]
  exact hsq_le

/-! ### Potential strict-decrease under failing Lovász

These lemmas package the multiplicative termination potential
`d_1 · … · d_{n-1}` behaviour under the two inner-loop updates:

* `sizeReduce_potential`: size reduction is potential-neutral (it only
  edits `ν`, never `d`).
* `swapStep_d_pivot`: the post-swap Gram-determinant slot reads
  `Int.toNat ⌊(d_{k+1}·d_{k-1} + B²)/d_k⌋` directly off `swapStep`'s
  definition (pairs with `swapStep_d_eq` to identify this slot with
  `gramDet (adjacentSwap b k) k`).
* `swapStep_potential_lt`: when the integer Lovász test fails at row
  `k` (the swap branch of `lllLoop`), the potential strictly decreases.
-/

/-- Size reduction leaves the multiplicative termination potential
unchanged, since it does not modify the stored Gram determinants. -/
theorem sizeReduce_potential (s : LLLState n m) (k : Nat) :
    (s.sizeReduce k).potential = s.potential := by
  unfold potential
  rw [sizeReduce_d]

/-- Value lemma for the post-swap Gram-determinant slot at the pivot
index. Reads `swapStep` directly: at index `k`, the updated `d` holds
`Int.toNat ⌊(d_{k+1}·d_{k-1} + B²)/d_k⌋`, where `B = ν[k][k-1]`. Pairs
with `swapStep_d_eq` to identify this slot with the post-swap basis'
Gram determinant via `gramDet_adjacentSwap_pivot`. -/
theorem swapStep_d_pivot (s : LLLState n m) (k : Nat) (hk : k < n) (hk0 : 0 < k) :
    have hkm1lt : k - 1 < n := Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk
    (s.swapStep k).d.get ⟨k, Nat.lt_succ_of_lt hk⟩ =
      Int.toNat
        ((Int.ofNat (s.d.get ⟨k + 1, Nat.succ_lt_succ hk⟩) *
              Int.ofNat (s.d.get ⟨k - 1, Nat.lt_succ_of_lt hkm1lt⟩) +
            ((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩) ^ 2) /
          Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩)) := by
  intro _hkm1lt
  unfold swapStep
  rw [dif_pos hk, dif_pos hk0]
  exact Vector.getElem_set_self (xs := s.d) (Nat.lt_succ_of_lt hk)

private theorem foldl_mul_pull {α : Type*} (xs : List α) (f : α → Nat) (a : Nat) :
    xs.foldl (fun acc i => acc * f i) a =
      a * xs.foldl (fun acc i => acc * f i) 1 := by
  induction xs generalizing a with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons]
    rw [ih (a * f x), ih (1 * f x), Nat.one_mul, Nat.mul_assoc]

private theorem foldl_mul_pos {α : Type*} (xs : List α) (f : α → Nat) (a : Nat)
    (ha : 0 < a) (hpos : ∀ i ∈ xs, 0 < f i) :
    0 < xs.foldl (fun acc i => acc * f i) a := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact Nat.mul_pos ha (hpos x List.mem_cons_self)
    · exact fun i hi => hpos i (List.mem_cons.mpr (Or.inr hi))

private theorem foldl_mul_congr_pointwise {α : Type*} (xs : List α) (f g : α → Nat) (a : Nat)
    (heq : ∀ i ∈ xs, f i = g i) :
    xs.foldl (fun acc i => acc * f i) a = xs.foldl (fun acc i => acc * g i) a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.foldl_cons]
    rw [heq x List.mem_cons_self]
    exact ih _ (fun i hi => heq i (List.mem_cons.mpr (Or.inr hi)))

/-- Strict-decrease helper: if exactly one factor in the foldl-product
strictly decreases and the others are unchanged, and all factors are
positive, then the product strictly decreases. -/
private theorem foldl_mul_strict_lt {α : Type*} {xs : List α} (hnd : xs.Nodup)
    {k : α} (hk : k ∈ xs) (f g : α → Nat)
    (hpos : ∀ i ∈ xs, 0 < f i)
    (heq : ∀ i ∈ xs, i ≠ k → f i = g i)
    (hlt : g k < f k) :
    ∀ a, 0 < a →
      xs.foldl (fun acc i => acc * g i) a <
        xs.foldl (fun acc i => acc * f i) a := by
  induction xs with
  | nil => exact absurd hk List.not_mem_nil
  | cons x rest ih =>
    intro a ha
    have hxnd : x ∉ rest := (List.nodup_cons.mp hnd).1
    have hrnd : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hpos_x : 0 < f x := hpos x List.mem_cons_self
    simp only [List.foldl_cons]
    by_cases hxk : x = k
    · subst hxk
      have heq_rest : ∀ i ∈ rest, f i = g i := fun i hi =>
        heq i (List.mem_cons.mpr (Or.inr hi)) (fun h => hxnd (h ▸ hi))
      have hpos_rest : ∀ i ∈ rest, 0 < f i := fun i hi =>
        hpos i (List.mem_cons.mpr (Or.inr hi))
      have hP_pos : 0 < rest.foldl (fun acc i => acc * f i) 1 :=
        foldl_mul_pos rest f 1 Nat.one_pos hpos_rest
      rw [foldl_mul_pull rest g (a * g x), foldl_mul_pull rest f (a * f x),
        ← foldl_mul_congr_pointwise rest f g 1 heq_rest]
      have h_factor : a * g x < a * f x := (Nat.mul_lt_mul_left ha).mpr hlt
      exact (Nat.mul_lt_mul_right hP_pos).mpr h_factor
    · have hk_rest : k ∈ rest := by
        rcases List.mem_cons.mp hk with rfl | h
        · exact absurd rfl hxk
        · exact h
      have heq_x : f x = g x := heq x List.mem_cons_self hxk
      rw [heq_x]
      apply ih hrnd hk_rest
      · exact fun i hi => hpos i (List.mem_cons.mpr (Or.inr hi))
      · exact fun i hi => heq i (List.mem_cons.mpr (Or.inr hi))
      · exact Nat.mul_pos ha (heq_x ▸ hpos_x)

/-- Strict decrease of the LLL termination potential across a swap that
fails the integer Lovász test at row `k`.

Hypotheses:
* `s.Valid`, `s.b.independent`: the proof-facing interpretation of the
  state. Independence gives positivity of all `d_j` factors.
* `0 < k < n`: the swap acts on adjacent rows `k - 1, k`.
* `0 < δnum` and `δnum ≤ δden`: the Lovász parameter `δ ∈ (0, 1]` as an
  integer inequality on its numerator and denominator (in the form
  `lllLoop`'s integer Lovász test consumes; follows from `1/4 < δ ≤ 1`).
* `hfail`: the failing integer Lovász condition at `k`, exactly the
  test `lllLoop` evaluates before dispatching the swap branch.

Conclusion: `(s.swapStep k).potential < s.potential`. -/
theorem swapStep_potential_lt (s : LLLState n m) (k : Nat)
    (hind : s.b.independent) (hvalid : s.Valid)
    (hk0 : 0 < k) (hk : k < n)
    (δnum : Int) (δden : Nat) (_hδnum_pos : 0 < δnum)
    (hδden_pos : 0 < δden) (hδ_le_one : δnum ≤ Int.ofNat δden)
    (hfail :
      Int.ofNat δden *
          (Int.ofNat (s.d.get ⟨k + 1, Nat.succ_lt_succ hk⟩) *
              Int.ofNat (s.d.get ⟨k - 1,
                Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk)⟩) +
            ((s.ν.getRow ⟨k, hk⟩).get
                ⟨k - 1, Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk⟩) ^ 2) <
        δnum * (Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩)) ^ 2) :
    (s.swapStep k).potential < s.potential := by
  -- Abbreviations matching the hypotheses' shapes.
  have hkm1lt : k - 1 < n := Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk
  let kFin : Fin n := ⟨k, hk⟩
  let km1 : Fin n := ⟨k - 1, hkm1lt⟩
  have hkm1_lt_k : km1.val < k := by show k - 1 < k; omega
  have hkm1Pred_eq : (GramSchmidt.prevRow kFin hk0) = km1 := by
    apply Fin.eq_of_val_eq
    show k - 1 = k - 1
    rfl
  -- Positivity of the gramDets at indices k-1, k, k+1.
  have hdk_pos : 0 < GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) := by
    have h := hind ⟨km1.val, Nat.lt_trans hkm1_lt_k hk⟩
    have hkm1_succ : km1.val + 1 = k := by show k - 1 + 1 = k; omega
    rwa [GramSchmidt.Int.gramDet_subst_val s.b (km1.val + 1) k _ _ hkm1_succ] at h
  have hdkNext_pos :
      0 < GramSchmidt.Int.gramDet s.b (k + 1) (Nat.succ_le_of_lt hk) := hind kFin
  have hdkm1_pos :
      0 < GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) := by
    by_cases hkm1_zero : km1.val = 0
    · rw [GramSchmidt.Int.gramDet_subst_val s.b km1.val 0 (Nat.le_of_lt km1.isLt)
          (Nat.zero_le n) hkm1_zero, GramSchmidt.Int.gramDet_zero]
      exact Nat.zero_lt_one
    · have hpos : 0 < km1.val := Nat.pos_of_ne_zero hkm1_zero
      have h := hind ⟨km1.val - 1, Nat.lt_trans
        (Nat.sub_lt hpos Nat.zero_lt_one) km1.isLt⟩
      rw [GramSchmidt.Int.gramDet_subst_val s.b km1.val (km1.val - 1 + 1)
          (Nat.le_of_lt km1.isLt)
          (Nat.succ_le_of_lt (Nat.lt_trans (Nat.sub_lt hpos Nat.zero_lt_one) km1.isLt))
          (Nat.succ_pred_eq_of_pos hpos).symm]
      exact h
  -- Valid bridge.
  have hdk_eq : s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩ =
      GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) := by
    have := hvalid.d_eq k (Nat.lt_succ_of_lt hk); simpa using this
  have hdkPrev_eq : s.d.get ⟨k - 1, Nat.lt_succ_of_lt hkm1lt⟩ =
      GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) := by
    have := hvalid.d_eq km1.val (Nat.lt_succ_of_lt km1.isLt); simpa using this
  have hdkNext_eq : s.d.get ⟨k + 1, Nat.succ_lt_succ hk⟩ =
      GramSchmidt.Int.gramDet s.b (k + 1) (Nat.succ_le_of_lt hk) := by
    have := hvalid.d_eq (k + 1) (Nat.succ_lt_succ hk); simpa using this
  have hdk_nat_pos : 0 < s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩ := hdk_eq ▸ hdk_pos
  -- Step 1: failing Lovász + δ ≤ 1 ⇒ (d_{k+1} * d_{k-1} + B^2) < d_k^2 (as Int).
  have hδden_int_pos : (0 : Int) < Int.ofNat δden := by
    show (0 : Int) < ((δden : Nat) : Int)
    exact_mod_cast hδden_pos
  have hsq_lt :
      Int.ofNat (s.d.get ⟨k + 1, Nat.succ_lt_succ hk⟩) *
            Int.ofNat (s.d.get ⟨k - 1, Nat.lt_succ_of_lt hkm1lt⟩) +
          ((s.ν.getRow kFin).get ⟨k - 1, hkm1lt⟩) ^ 2 <
      (Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩)) ^ 2 := by
    have hsq_nn : (0 : Int) ≤ (Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩)) ^ 2 :=
      sq_nonneg _
    have h_bound :
        δnum * (Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩)) ^ 2 ≤
          Int.ofNat δden * (Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩)) ^ 2 :=
      Int.mul_le_mul_of_nonneg_right hδ_le_one hsq_nn
    exact Int.lt_of_mul_lt_mul_left (hfail.trans_le h_bound) (le_of_lt hδden_int_pos)
  -- Step 2: bridge to gramDet form via Valid, and use the pivot product identity.
  have hvalid' : (s.swapStep k).Valid := swapStep_valid s k hind hvalid
  have hswap_d_at_k :
      ((s.swapStep k).d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Nat) =
        GramSchmidt.Int.gramDet (GramSchmidt.Int.adjacentSwap s.b kFin hk0) k
          (Nat.le_of_lt hk) := by
    have := hvalid'.d_eq k (Nat.lt_succ_of_lt hk)
    simpa [swapStep_b_eq s k hk hk0] using this
  have hB_via_valid :
      ((s.ν.getRow kFin).get ⟨k - 1, hkm1lt⟩ : Int) =
        GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 := by
    have h := hvalid.ν_eq kFin.val km1.val kFin.isLt km1.isLt
      (by show k - 1 < k; omega)
    simpa [GramSchmidt.entry, Matrix.row, vector_get_eq_getElem] using h
  -- The pivot-product identity (no division needed since it's exact).
  have hprod :=
    GramSchmidt.Int.gramDet_rowSwap_adjacent_pivot_product (b := s.b)
      (km1 := km1) (k := kFin) (by show k - 1 + 1 = k; omega)
  -- Combine to get: dk' * dk = (d_{k+1} * d_{k-1} + B^2) as Int.
  have hdk'_mul_dk :
      ((s.swapStep k).d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Int) *
        (Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩)) =
      Int.ofNat (s.d.get ⟨k + 1, Nat.succ_lt_succ hk⟩) *
            Int.ofNat (s.d.get ⟨k - 1, Nat.lt_succ_of_lt hkm1lt⟩) +
          ((s.ν.getRow kFin).get ⟨k - 1, hkm1lt⟩) ^ 2 := by
    -- Restate hprod with the unfolded `km1` and `kFin` to match our shapes.
    have hprod' :
        ((GramSchmidt.Int.gramDet (Matrix.rowSwap s.b km1 kFin) k
            (Nat.le_of_lt hk) : Nat) : Int) *
          ((GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) : Nat) : Int) =
        ((GramSchmidt.Int.gramDet s.b (k + 1) (Nat.succ_le_of_lt hk) : Nat) : Int) *
            ((GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) +
          (GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1) ^ 2 := hprod
    -- Normalize all Int.ofNat to Nat.cast for uniform rewriting.
    show ((s.swapStep k).d.get _ : Nat) * ((s.d.get _ : Nat) : Int) =
      ((s.d.get _ : Nat) : Int) * ((s.d.get _ : Nat) : Int) +
        ((s.ν.getRow kFin).get _) ^ 2
    rw [hdk_eq, hdkPrev_eq, hdkNext_eq]
    rw [show ((s.ν.getRow kFin).get ⟨k - 1, hkm1lt⟩ : Int) =
        GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 from
        hB_via_valid]
    rw [hswap_d_at_k]
    show ((GramSchmidt.Int.gramDet
        (Matrix.rowSwap s.b (GramSchmidt.prevRow kFin hk0) kFin) k
        (Nat.le_of_lt hk) : Nat) : Int) *
        ((GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) : Nat) : Int) = _
    rw [hkm1Pred_eq]
    exact hprod'
  -- Step 3: dk > 0 + dk'*dk < dk² ⇒ dk' < dk.
  have hdk_int_pos : (0 : Int) < Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩) := by
    show (0 : Int) < ((s.d.get _ : Nat) : Int)
    exact_mod_cast hdk_nat_pos
  have hdk'_lt_dk_int :
      ((s.swapStep k).d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Int) <
        Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩) := by
    have h_mul_lt :
        ((s.swapStep k).d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Int) *
            (Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩)) <
          Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩) *
            Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩) := by
      rw [hdk'_mul_dk]
      have hsq : (Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩) : Int) ^ 2 =
          Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩) *
            Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩) := by ring
      rw [← hsq]; exact hsq_lt
    exact Int.lt_of_mul_lt_mul_right h_mul_lt (le_of_lt hdk_int_pos)
  have hdk'_lt_dk :
      (s.swapStep k).d.get ⟨k, Nat.lt_succ_of_lt hk⟩ <
        s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩ := by
    have :
        ((s.swapStep k).d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Int) <
          ((s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Nat) : Int) := hdk'_lt_dk_int
    exact_mod_cast this
  -- Step 4: only `d` index k changes; all others equal.
  have hd_off_pivot : ∀ (i : Nat) (hi : i < n + 1), i ≠ k →
      (s.swapStep k).d.get ⟨i, hi⟩ = s.d.get ⟨i, hi⟩ := by
    intro i hi hik
    unfold swapStep
    rw [dif_pos hk, dif_pos hk0]
    exact Vector.getElem_set_ne (Nat.lt_succ_of_lt hk) hi (fun h => hik h.symm)
  -- Step 5: apply the foldl strict-decrease helper.
  unfold potential
  rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl]
  have hkm1_lt_nsub : k - 1 < n - 1 := by omega
  let i₀ : Fin (n - 1) := ⟨k - 1, hkm1_lt_nsub⟩
  have hi₀_mem : i₀ ∈ List.finRange (n - 1) := List.mem_finRange _
  have hi₀_plus : i₀.val + 1 = k := by show k - 1 + 1 = k; omega
  let g : Fin (n - 1) → Nat := fun i =>
    (s.swapStep k).d.get
      ⟨i.val + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1))⟩
  let f : Fin (n - 1) → Nat := fun i =>
    s.d.get
      ⟨i.val + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1))⟩
  have hfg_eq : ∀ i ∈ List.finRange (n - 1), i ≠ i₀ → f i = g i := by
    intro i _ hi
    have hindex_ne : i.val + 1 ≠ k := by
      intro h
      apply hi
      apply Fin.eq_of_val_eq
      show i.val = k - 1
      omega
    show s.d.get _ = (s.swapStep k).d.get _
    exact (hd_off_pivot (i.val + 1) _ hindex_ne).symm
  have hglt : g i₀ < f i₀ := by
    show (s.swapStep k).d.get _ < s.d.get _
    have hidx : (⟨i₀.val + 1,
        Nat.succ_lt_succ (Nat.lt_of_lt_of_le i₀.isLt (Nat.sub_le n 1))⟩ : Fin (n + 1)) =
      ⟨k, Nat.lt_succ_of_lt hk⟩ := Fin.eq_of_val_eq hi₀_plus
    rw [hidx]
    exact hdk'_lt_dk
  have hf_pos : ∀ i ∈ List.finRange (n - 1), 0 < f i := by
    intro i _
    show 0 < s.d.get _
    have hi_succ_le : i.val + 1 ≤ n := by have := i.isLt; omega
    have hdpos : 0 < GramSchmidt.Int.gramDet s.b (i.val + 1) hi_succ_le :=
      hind ⟨i.val, by omega⟩
    have h := hvalid.d_eq (i.val + 1)
      (Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)))
    rw [h]
    exact hdpos
  exact foldl_mul_strict_lt (List.nodup_finRange _) hi₀_mem f g hf_pos hfg_eq hglt 1
    Nat.one_pos

/-! ### Fuel sufficiency for `lllLoop`

The outer LLL loop `lllLoop` was made total in #6564 by structural
recursion on a `fuel` argument, with `fuel = 0` returning the current
basis as a pipeline-unreachable fallback (per SPEC §8).  This section
proves the fallback unreachable for valid input: the bound
`lllFuel s = (s.potential + 1) * (n + 1)` is sufficient for the loop
started at `k = 1` on `s = ofBasis b`.

The argument tracks the lexicographic measure
`s.potential * (n + 1) + (n - k)`:

* size reduction is potential-neutral (`sizeReduce_potential`) and is
  immediately followed by either an advance (decreases `n - k` by 1)
  or a swap;
* swaps strictly decrease the potential (`swapStep_potential_lt`),
  swallowing the `n - k` reset.

So each loop iteration strictly decreases the measure by ≥ 1, and the
measure starts strictly below `lllFuel s`, so the loop hits the
`k = n` base case before fuel exhausts.
-/

/-- When `k = n`, the loop returns `s.b` regardless of fuel (the `hdone`
branch fires). -/
private theorem lllLoop_eq_b_at_n
    (s : LLLState n m) (δ : Rat) (hδ : 1/4 < δ) (hδ' : δ ≤ 1)
    (hk : 1 ≤ n) (hkn : n ≤ n) (fuel : Nat) :
    lllLoop s n δ hδ hδ' hk hkn fuel = s.b := by
  cases fuel with
  | zero => rfl
  | succ f =>
    show (if hdone : n = n then s.b
          else _) = s.b
    rw [dif_pos rfl]

/-- The inner body of `lllLoop`'s `fuel = g + 1` branch (under `k < n`),
extracted for use in fuel-sufficiency reasoning. -/
private def lllLoopBody (s : LLLState n m) (k : Nat) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hlt : k < n) (fuel : Nat) : Matrix Int n m :=
  let sReduced := s.sizeReduce k
  let kFin : Fin n := ⟨k, hlt⟩
  let km1Fin : Fin n := ⟨k - 1, Nat.lt_of_le_of_lt (Nat.sub_le k 1) hlt⟩
  let dkPrev := sReduced.d.get
    ⟨k - 1, Nat.lt_trans
      (Nat.lt_of_le_of_lt (Nat.sub_le k 1) hlt) (Nat.lt_succ_self n)⟩
  let dk := sReduced.d.get ⟨k, Nat.lt_succ_of_lt hlt⟩
  let dkNext := sReduced.d.get ⟨k + 1, Nat.succ_lt_succ hlt⟩
  let B := (sReduced.ν.getRow kFin).get km1Fin
  let lovaszLhs : Int :=
    Int.ofNat δ.den * (Int.ofNat dkNext * Int.ofNat dkPrev + B ^ 2)
  let lovaszRhs : Int := δ.num * (Int.ofNat dk ^ 2)
  if lovaszLhs ≥ lovaszRhs then
    lllLoop sReduced (k + 1) δ hδ hδ' (Nat.succ_pos k)
      (Nat.succ_le_of_lt hlt) fuel
  else
    let sSwapped := sReduced.swapStep k
    let k' := max (k - 1) 1
    lllLoop sSwapped k' δ hδ hδ' (Nat.le_max_right (k - 1) 1)
      ((Nat.max_le).2 ⟨Nat.le_trans (Nat.sub_le k 1) hkn, Nat.le_trans hk hkn⟩)
      fuel

private theorem lllLoop_succ_eq_body
    (s : LLLState n m) (k : Nat) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hk : 1 ≤ k) (hkn : k ≤ n) (hlt : k < n)
    (fuel : Nat) :
    lllLoop s k δ hδ hδ' hk hkn (fuel + 1) =
      lllLoopBody s k δ hδ hδ' hk hkn hlt fuel := by
  show (if hdone : k = n then s.b else _) = _
  rw [dif_neg (Nat.ne_of_lt hlt)]
  rfl

/-- δ.num positivity and δ.num ≤ δ.den from `1/4 < δ ≤ 1`.  These are the
integer hypotheses consumed by `swapStep_potential_lt`. -/
private theorem lovasz_swap_hyps (δ : Rat) (hδ : 1/4 < δ) (hδ' : δ ≤ 1) :
    0 < δ.num ∧ 0 < δ.den ∧ δ.num ≤ Int.ofNat δ.den := by
  have hδpos : (0 : Rat) < δ := lt_trans (by norm_num) hδ
  refine ⟨Rat.num_pos.mpr hδpos, δ.pos, ?_⟩
  -- δ ≤ 1 ↔ δ.num ≤ δ.den (under δ.den > 0).
  have hden_pos : (0 : Rat) < (δ.den : Rat) := by exact_mod_cast δ.pos
  have h_rat : (δ.num : Rat) ≤ (δ.den : Rat) := by
    have heq : δ = (δ.num : Rat) / (δ.den : Rat) := (Rat.num_div_den δ).symm
    rw [heq] at hδ'
    rw [div_le_one hden_pos] at hδ'
    exact hδ'
  exact_mod_cast h_rat

private theorem lllLoop_eq_of_fuel_gt_measure
    (δ : Rat) (hδ : 1/4 < δ) (hδ' : δ ≤ 1) :
    ∀ (fuel : Nat) (s : LLLState n m) (k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n),
      s.Valid → s.b.independent →
      s.potential * (n + 1) + (n - k) < fuel →
      ∀ {fuel' : Nat}, fuel ≤ fuel' →
        lllLoop s k δ hδ hδ' hk hkn fuel = lllLoop s k δ hδ hδ' hk hkn fuel' := by
  intro fuel
  induction fuel with
  | zero =>
    intros _ _ _ _ _ _ hmeasure _ _
    exact absurd hmeasure (Nat.not_lt_zero _)
  | succ f ih =>
    intros s k hk hkn hvalid hind hmeasure fuel' hf
    obtain ⟨f', rfl⟩ : ∃ f', fuel' = f' + 1 :=
      ⟨fuel' - 1, by omega⟩
    have hf' : f ≤ f' := Nat.le_of_succ_le_succ hf
    by_cases hkn_eq : k = n
    · subst hkn_eq
      rw [lllLoop_eq_b_at_n, lllLoop_eq_b_at_n]
    · -- Recursive case: k < n.
      have hlt : k < n := Nat.lt_of_le_of_ne hkn hkn_eq
      -- Establish post-sizeReduce invariants.
      have hsR_valid : (s.sizeReduce k).Valid := sizeReduce_valid s k hvalid
      have hsR_ind : (s.sizeReduce k).b.independent :=
        sizeReduce_independent s k hind hvalid hsR_valid
      have hsR_pot : (s.sizeReduce k).potential = s.potential := sizeReduce_potential s k
      -- Unfold lllLoop on both sides.  The `f + 1` and `f' + 1` cases match the
      -- second arm of the definition; the `hdone : k = n` dispatches to the else
      -- branch.  The recursive call uses fuel `f` on the LHS and `f'` on the RHS.
      rw [lllLoop_succ_eq_body s k δ hδ hδ' hk hkn hlt,
          lllLoop_succ_eq_body s k δ hδ hδ' hk hkn hlt]
      -- The body's lets are identical on both sides; only the recursive call's
      -- fuel arg differs.  Split on the Lovász check.
      dsimp only [lllLoopBody]
      split_ifs with hcond
      · -- Advance branch.
        apply ih (s.sizeReduce k) (k + 1) (Nat.succ_pos k) (Nat.succ_le_of_lt hlt)
          hsR_valid hsR_ind
        · rw [hsR_pot]
          have : n - (k + 1) + 1 ≤ n - k := by omega
          omega
        · exact hf'
      · -- Swap branch.
        obtain ⟨hnum_pos, hden_pos, hnum_le_den⟩ := lovasz_swap_hyps δ hδ hδ'
        have hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
        -- Convert the negated `≥` to the strict `<` shape expected by
        -- swapStep_potential_lt.
        push Not at hcond
        have hpot_lt :
            ((s.sizeReduce k).swapStep k).potential < (s.sizeReduce k).potential :=
          swapStep_potential_lt (s.sizeReduce k) k hsR_ind hsR_valid hk0 hlt
            δ.num δ.den hnum_pos hden_pos hnum_le_den (by
              convert hcond using 2)
        have hsS_pot_lt : ((s.sizeReduce k).swapStep k).potential < s.potential := by
          rw [← hsR_pot]; exact hpot_lt
        have hsS_valid : ((s.sizeReduce k).swapStep k).Valid :=
          swapStep_valid (s.sizeReduce k) k hsR_ind hsR_valid
        have hsS_ind : ((s.sizeReduce k).swapStep k).b.independent :=
          swapStep_independent (s.sizeReduce k) k hsR_ind hsR_valid hk0 hlt
        have hk'n :
            max (k - 1) 1 ≤ n :=
          (Nat.max_le).2 ⟨Nat.le_trans (Nat.sub_le k 1) hkn, Nat.le_trans hk hkn⟩
        apply ih ((s.sizeReduce k).swapStep k) (max (k - 1) 1)
          (Nat.le_max_right (k - 1) 1) hk'n hsS_valid hsS_ind
        · -- measure(sSwapped, k') < f
          have hmeasure_le : s.potential * (n + 1) + (n - k) ≤ f :=
            Nat.lt_succ_iff.mp hmeasure
          have hspot_pos : 0 < s.potential := by
            have : 0 ≤ ((s.sizeReduce k).swapStep k).potential := Nat.zero_le _
            omega
          have hmul_bound :
              ((s.sizeReduce k).swapStep k).potential * (n + 1) ≤
                (s.potential - 1) * (n + 1) :=
            Nat.mul_le_mul_right (n + 1)
              (by omega : ((s.sizeReduce k).swapStep k).potential ≤ s.potential - 1)
          have hsub_mul : (s.potential - 1) * (n + 1) + (n + 1) = s.potential * (n + 1) := by
            have hp : s.potential = (s.potential - 1) + 1 := by omega
            calc (s.potential - 1) * (n + 1) + (n + 1)
                = ((s.potential - 1) + 1) * (n + 1) := by ring
              _ = s.potential * (n + 1) := by rw [← hp]
          -- Combine into the bound.
          have hnk' : n - max (k - 1) 1 ≤ n := Nat.sub_le n _
          have hgoal :
              ((s.sizeReduce k).swapStep k).potential * (n + 1) + (n - max (k - 1) 1) ≤
                s.potential * (n + 1) - 1 := by
            have : ((s.sizeReduce k).swapStep k).potential * (n + 1) + n ≤
                (s.potential - 1) * (n + 1) + n := by omega
            have hsum_le : ((s.sizeReduce k).swapStep k).potential * (n + 1) +
                (n - max (k - 1) 1) ≤ (s.potential - 1) * (n + 1) + n := by omega
            have hrhs_eq : (s.potential - 1) * (n + 1) + n = s.potential * (n + 1) - 1 := by
              omega
            omega
          have h1 : s.potential * (n + 1) - 1 ≤ s.potential * (n + 1) + (n - k) - 1 := by
            omega
          have h_meas : s.potential * (n + 1) + (n - k) - 1 ≤ f - 1 := by omega
          have h_f_pos : 0 < f := by
            -- Need f > 0 to subtract.  We use measure_old < f + 1 with measure_old ≥ 1.
            have h1 : 1 ≤ s.potential * (n + 1) := by
              calc 1 = 1 * (n + 1) - n := by omega
                _ ≤ s.potential * (n + 1) - n := by
                  have := Nat.mul_le_mul_right (n + 1) hspot_pos
                  omega
                _ ≤ s.potential * (n + 1) := Nat.sub_le _ _
            omega
          omega
        · exact hf'

/-- **Fuel sufficiency for `lllLoop`.**  For a valid state `s` with an
independent basis, started at row `k = 1`, the bound
`lllFuel s = (s.potential + 1) * (n + 1)` is enough fuel to reach the
`k = n` base case.  Equivalently, `lllLoop` is fuel-stable above this
threshold: running with any `fuel' ≥ lllFuel s` returns the same matrix.
This discharges the SPEC §8 "unreachable-by-pipeline-invariant"
classification for the `fuel = 0` fallback in `lllLoop` (introduced by
the Route A totality refactor #6564). -/
theorem lllLoop_fuel_sufficient
    (s : LLLState n m) (δ : Rat) (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (hvalid : s.Valid) (hind : s.b.independent) {fuel' : Nat}
    (hfuel : lllFuel s ≤ fuel') :
    lllLoop s 1 δ hδ hδ' (Nat.le_refl 1) hn (lllFuel s) =
      lllLoop s 1 δ hδ hδ' (Nat.le_refl 1) hn fuel' := by
  apply lllLoop_eq_of_fuel_gt_measure δ hδ hδ' (lllFuel s) s 1 (Nat.le_refl 1) hn
    hvalid hind
  · -- s.potential * (n + 1) + (n - 1) < (s.potential + 1) * (n + 1)
    show s.potential * (n + 1) + (n - 1) < (s.potential + 1) * (n + 1)
    have : (s.potential + 1) * (n + 1) = s.potential * (n + 1) + (n + 1) := by ring
    omega
  · exact hfuel

/-! ### Size-reduce coefficient-row preservation

Size reduction at row `k` rewrites only that row's coefficients; rows at
indices `i ≠ k` are preserved by every iteration of the inner foldl.  This
packages the preservation as a single statement so the loop-invariant proof
below can quote it without re-running the inductive `coeffs_sizeReduce_other_row`
chain. -/

private theorem sizeReduceColumn_coeffs_row_of_ne (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) (i : Fin n) (hik : i ≠ k) :
    (GramSchmidt.Int.coeffs (s.sizeReduceColumn j k hjk).b).row i =
      (GramSchmidt.Int.coeffs s.b).row i := by
  unfold sizeReduceColumn
  by_cases hreduce :
      2 * Int.natAbs ((s.ν.getRow k).get j) >
        s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · rw [dif_pos hreduce]
    exact GramSchmidt.Int.coeffs_sizeReduce_other_row s.b j k hjk _ i hik
  · rw [dif_neg hreduce]

private theorem sizeReduce_foldl_coeffs_row_of_ne {n m : Nat}
    (k : Nat) (hk : k < n) (i : Fin n) (hik : i ≠ ⟨k, hk⟩) :
    ∀ (xs : List (Fin k)) (s' : LLLState n m),
      (GramSchmidt.Int.coeffs (xs.foldl
          (fun state j =>
            let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
            state.sizeReduceColumn jFin ⟨k, hk⟩ j.isLt)
          s').b).row i = (GramSchmidt.Int.coeffs s'.b).row i := by
  intro xs
  induction xs with
  | nil => intro s'; rfl
  | cons j js ih =>
    intro s'
    simp only [List.foldl_cons]
    rw [ih _]
    exact sizeReduceColumn_coeffs_row_of_ne s' _ _ j.isLt i hik

/-- Coefficient rows at `i ≠ k` survive `s.sizeReduce k` intact. -/
theorem sizeReduce_coeffs_row_of_ne (s : LLLState n m) (k : Nat) (i : Fin n)
    (hik : i.val ≠ k) :
    (GramSchmidt.Int.coeffs (s.sizeReduce k).b).row i =
      (GramSchmidt.Int.coeffs s.b).row i := by
  unfold sizeReduce
  by_cases hk : k < n
  · rw [dif_pos hk]
    have hik' : i ≠ ⟨k, hk⟩ := fun h => hik (by rw [h])
    simpa [Fin.foldr_eq_finRange_foldr] using
      sizeReduce_foldl_coeffs_row_of_ne k hk i hik' (List.finRange k).reverse s
  · rw [dif_neg hk]

/-- Size reduction preserves `prefixLLLReduced` at the same prefix length: rows
strictly below `k` are unaffected by the row-`k` update, so the prefix invariant
on the input transfers to the output. -/
theorem sizeReduce_prefixLLLReduced (s : LLLState n m) (k : Nat) (δ : Rat)
    (h : prefixLLLReduced s.b k δ) :
    prefixLLLReduced (s.sizeReduce k).b k δ := by
  refine ⟨?_, ?_⟩
  · -- Size-reducedness for i < k: coefficient row at i is preserved.
    intro i j hik hin hji
    have hi_ne_k : (⟨i, hin⟩ : Fin n).val ≠ k := Nat.ne_of_lt hik
    have hrow := sizeReduce_coeffs_row_of_ne s k ⟨i, hin⟩ hi_ne_k
    let iFin : Fin n := ⟨i, hin⟩
    let jFin : Fin n := ⟨j, Nat.lt_trans hji hin⟩
    let μ_sr : Rat := (GramSchmidt.Int.coeffs (s.sizeReduce k).b)[iFin][jFin]
    show 4 * μ_sr * μ_sr ≤ 1
    have hμ_eq : μ_sr =
        (GramSchmidt.Int.coeffs s.b)[iFin][jFin] := by
      show ((GramSchmidt.Int.coeffs (s.sizeReduce k).b).row iFin)[jFin] =
        ((GramSchmidt.Int.coeffs s.b).row iFin)[jFin]
      rw [hrow]
    rw [hμ_eq]
    exact h.1 i j hik hin hji
  · -- Lovász for i + 1 < k: basis (norm) and coeffs at row i+1 preserved.
    intro i hik hin
    have hbasis_eq := sizeReduce_basis s k
    have hip1_ne_k : (⟨i + 1, hin⟩ : Fin n).val ≠ k := Nat.ne_of_lt hik
    have hrow := sizeReduce_coeffs_row_of_ne s k ⟨i + 1, hin⟩ hip1_ne_k
    have hin_i : i < n := Nat.lt_of_succ_lt hin
    let iFin : Fin n := ⟨i, hin_i⟩
    let ip1Fin : Fin n := ⟨i + 1, hin⟩
    let N_sr_i : Rat :=
      LLLCore.basisNormSq (GramSchmidt.Int.basis (s.sizeReduce k).b) iFin
    let N_sr_ip1 : Rat :=
      LLLCore.basisNormSq (GramSchmidt.Int.basis (s.sizeReduce k).b) ip1Fin
    let μ_sr : Rat :=
      (GramSchmidt.Int.coeffs (s.sizeReduce k).b)[ip1Fin][iFin]
    show δ * N_sr_i ≤ N_sr_ip1 + μ_sr * μ_sr * N_sr_i
    have hb_i : N_sr_i = LLLCore.basisNormSq (GramSchmidt.Int.basis s.b) iFin := by
      show LLLCore.basisNormSq (GramSchmidt.Int.basis (s.sizeReduce k).b) iFin = _
      rw [hbasis_eq]
    have hb_ip1 : N_sr_ip1 =
        LLLCore.basisNormSq (GramSchmidt.Int.basis s.b) ip1Fin := by
      show LLLCore.basisNormSq (GramSchmidt.Int.basis (s.sizeReduce k).b) ip1Fin = _
      rw [hbasis_eq]
    have hμ_eq : μ_sr = (GramSchmidt.Int.coeffs s.b)[ip1Fin][iFin] := by
      show ((GramSchmidt.Int.coeffs (s.sizeReduce k).b).row ip1Fin)[iFin] =
        ((GramSchmidt.Int.coeffs s.b).row ip1Fin)[iFin]
      rw [hrow]
    rw [hb_i, hb_ip1, hμ_eq]
    exact h.2 i hik hin

/-! ### Loop invariant induction

The `prefixLLLReduced` predicate is preserved by every iteration of `lllLoop`
under the standard validity / independence hypotheses, and at the `k = n`
base case it coincides with `isLLLReduced`. This packages those two facts
into a single fuel-bounded induction. -/

/-- With enough fuel and a starting state carrying `prefixLLLReduced s.b k δ`,
`lllLoop` produces a `δ`-LLL-reduced basis. The fuel hypothesis
`s.potential * (n + 1) + (n - k) < fuel` matches the measure used by
`lllLoop_eq_of_fuel_gt_measure`. -/
theorem lllLoop_isLLLReduced_of_fuel_gt_measure
    (δ : Rat) (hδ : 1/4 < δ) (hδ' : δ ≤ 1) :
    ∀ (fuel : Nat) (s : LLLState n m) (k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n),
      s.Valid → s.b.independent → prefixLLLReduced s.b k δ →
      s.potential * (n + 1) + (n - k) < fuel →
      isLLLReduced (lllLoop s k δ hδ hδ' hk hkn fuel) δ (1 / 2) := by
  intro fuel
  induction fuel with
  | zero =>
    intros _ _ _ _ _ _ _ hmeasure
    exact absurd hmeasure (Nat.not_lt_zero _)
  | succ f ih =>
    intros s k hk hkn hvalid hind hpre hmeasure
    by_cases hkn_eq : k = n
    · subst hkn_eq
      rw [lllLoop_eq_b_at_n]
      exact prefixLLLReduced_to_isLLLReduced s.b δ hpre
    · have hlt : k < n := Nat.lt_of_le_of_ne hkn hkn_eq
      have hsR_valid : (s.sizeReduce k).Valid := sizeReduce_valid s k hvalid
      have hsR_ind : (s.sizeReduce k).b.independent :=
        sizeReduce_independent s k hind hvalid hsR_valid
      have hsR_pot : (s.sizeReduce k).potential = s.potential := sizeReduce_potential s k
      have hsR_pre : prefixLLLReduced (s.sizeReduce k).b k δ :=
        sizeReduce_prefixLLLReduced s k δ hpre
      have hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
      rw [lllLoop_succ_eq_body s k δ hδ hδ' hk hkn hlt]
      dsimp only [lllLoopBody]
      split_ifs with hcond
      · -- Advance branch: Lovász integer check holds, extend prefix and recurse.
        have hpre_advance : prefixLLLReduced (s.sizeReduce k).b (k + 1) δ := by
          apply prefixLLLReduced.advance hlt hsR_pre
          · intro j hj
            exact sizeReduce_size_reduced s k hlt hvalid hind j hj
          · intro _hk0
            have hiff := HexLLLMathlib.lovasz_check_iff_isLLLReduced_pair
              (s.sizeReduce k) k hlt hk0 hsR_valid hsR_ind hδ hδ'
            exact hiff.mp hcond
        apply ih (s.sizeReduce k) (k + 1) (Nat.succ_pos k) (Nat.succ_le_of_lt hlt)
          hsR_valid hsR_ind hpre_advance
        rw [hsR_pot]
        have : n - (k + 1) + 1 ≤ n - k := by omega
        omega
      · -- Swap branch: Lovász integer check fails, swap shortens prefix.
        push Not at hcond
        obtain ⟨hnum_pos, hden_pos, hnum_le_den⟩ := lovasz_swap_hyps δ hδ hδ'
        have hpot_lt :
            ((s.sizeReduce k).swapStep k).potential < (s.sizeReduce k).potential :=
          swapStep_potential_lt (s.sizeReduce k) k hsR_ind hsR_valid hk0 hlt
            δ.num δ.den hnum_pos hden_pos hnum_le_den (by convert hcond using 2)
        have hsS_pot_lt : ((s.sizeReduce k).swapStep k).potential < s.potential := by
          rw [← hsR_pot]; exact hpot_lt
        have hsS_valid : ((s.sizeReduce k).swapStep k).Valid :=
          swapStep_valid (s.sizeReduce k) k hsR_ind hsR_valid
        have hsS_ind : ((s.sizeReduce k).swapStep k).b.independent :=
          swapStep_independent (s.sizeReduce k) k hsR_ind hsR_valid hk0 hlt
        have hsS_pre :
            prefixLLLReduced ((s.sizeReduce k).swapStep k).b (max (k - 1) 1) δ :=
          swapStep_prefixLLLReduced (s.sizeReduce k) k δ hsR_pre
        have hk'n : max (k - 1) 1 ≤ n :=
          (Nat.max_le).2 ⟨Nat.le_trans (Nat.sub_le k 1) hkn, Nat.le_trans hk hkn⟩
        apply ih ((s.sizeReduce k).swapStep k) (max (k - 1) 1)
          (Nat.le_max_right (k - 1) 1) hk'n hsS_valid hsS_ind hsS_pre
        -- Measure decrease.
        have hmeasure_le : s.potential * (n + 1) + (n - k) ≤ f := Nat.lt_succ_iff.mp hmeasure
        have hspot_pos : 0 < s.potential := by
          have : 0 ≤ ((s.sizeReduce k).swapStep k).potential := Nat.zero_le _
          omega
        have hmul_bound :
            ((s.sizeReduce k).swapStep k).potential * (n + 1) ≤
              (s.potential - 1) * (n + 1) :=
          Nat.mul_le_mul_right (n + 1)
            (by omega : ((s.sizeReduce k).swapStep k).potential ≤ s.potential - 1)
        have hsub_mul : (s.potential - 1) * (n + 1) + (n + 1) = s.potential * (n + 1) := by
          have hp : s.potential = (s.potential - 1) + 1 := by omega
          calc (s.potential - 1) * (n + 1) + (n + 1)
              = ((s.potential - 1) + 1) * (n + 1) := by ring
            _ = s.potential * (n + 1) := by rw [← hp]
        have h_fpos : 0 < f := by
          have h1 : 1 ≤ s.potential * (n + 1) := by
            calc 1 = 1 * (n + 1) - n := by omega
              _ ≤ s.potential * (n + 1) - n := by
                have := Nat.mul_le_mul_right (n + 1) hspot_pos
                omega
              _ ≤ s.potential * (n + 1) := Nat.sub_le _ _
          omega
        have hnk' : n - max (k - 1) 1 ≤ n := Nat.sub_le n _
        show ((s.sizeReduce k).swapStep k).potential * (n + 1) + (n - max (k - 1) 1) < f
        omega

/-- `lllLoop` preserves the independence of the starting basis: every iteration
is either a `sizeReduce` (preserved by `sizeReduce_independent`) or an adjacent
swap (preserved by `swapStep_independent`). -/
theorem lllLoop_independent
    (δ : Rat) (hδ : 1/4 < δ) (hδ' : δ ≤ 1) :
    ∀ (fuel : Nat) (s : LLLState n m) (k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n),
      s.Valid → s.b.independent →
      Matrix.independent (lllLoop s k δ hδ hδ' hk hkn fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s _ _ _ _ hind
    exact hind
  | succ f ih =>
    intro s k hk hkn hvalid hind
    by_cases hkn_eq : k = n
    · subst hkn_eq
      rw [lllLoop_eq_b_at_n]
      exact hind
    · have hlt : k < n := Nat.lt_of_le_of_ne hkn hkn_eq
      have hsR_valid : (s.sizeReduce k).Valid := sizeReduce_valid s k hvalid
      have hsR_ind : (s.sizeReduce k).b.independent :=
        sizeReduce_independent s k hind hvalid hsR_valid
      rw [lllLoop_succ_eq_body s k δ hδ hδ' hk hkn hlt]
      dsimp only [lllLoopBody]
      split_ifs
      · exact ih (s.sizeReduce k) (k + 1) (Nat.succ_pos k)
          (Nat.succ_le_of_lt hlt) hsR_valid hsR_ind
      · have hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
        have hsS_valid : ((s.sizeReduce k).swapStep k).Valid :=
          swapStep_valid (s.sizeReduce k) k hsR_ind hsR_valid
        have hsS_ind : ((s.sizeReduce k).swapStep k).b.independent :=
          swapStep_independent (s.sizeReduce k) k hsR_ind hsR_valid hk0 hlt
        have hk'n : max (k - 1) 1 ≤ n :=
          (Nat.max_le).2 ⟨Nat.le_trans (Nat.sub_le k 1) hkn, Nat.le_trans hk hkn⟩
        exact ih ((s.sizeReduce k).swapStep k) (max (k - 1) 1)
          (Nat.le_max_right (k - 1) 1) hk'n hsS_valid hsS_ind

end Internal.LLLState

/-! ### Capstones

The unconditional LLL guarantees split across two surfaces:

* **Native** (`Hex.lllNative`, classical bound, precondition `1/4 < δ`).
  Carries `isLLLReduced … δ (1/2)` because the integer size-reduction step
  inside the loop produces exact `|μ| ≤ 1/2`. The short-vector denominator
  is `δ − 1/4`.
* **Public** (`Hex.lll`, precondition `121/400 < δ`). Wraps `lllNative` and
  carries `isLLLReduced … δ (11/20)` (the η = 1/2 native bound weakens to
  η = 11/20 by `isLLLReduced.mono_η`). The short-vector denominator is
  `δ − 121/400`. This is the uniform bound an external reducer can promise. -/

/-- The native LLL body produces a `(δ, 1/2)`-LLL-reduced matrix. Combines the
fuel-sufficiency theorem (`lllLoop_fuel_sufficient`) with the loop invariant
induction (`lllLoop_isLLLReduced_of_fuel_gt_measure`). -/
theorem lllNative_isLLLReduced (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) (hind : b.independent) :
    isLLLReduced (lllNative b δ hδ hδ' hn) δ (1 / 2) := by
  show isLLLReduced (lllLoop (LLLState.ofBasis b) 1 δ hδ hδ'
    (Nat.le_refl 1) hn (lllFuel (LLLState.ofBasis b))) δ (1 / 2)
  set s := LLLState.ofBasis b with hs_def
  have hs_valid : s.Valid := by
    show (LLLState.ofBasis b).Valid
    exact HexLLLMathlib.LLLState.ofBasis_valid b
  have hs_ind : s.b.independent := hind
  have hs_pre : prefixLLLReduced s.b 1 δ := prefixLLLReduced_one s.b δ
  apply LLLState.lllLoop_isLLLReduced_of_fuel_gt_measure δ hδ hδ' (lllFuel s) s 1
    (Nat.le_refl 1) hn hs_valid hs_ind hs_pre
  show s.potential * (n + 1) + (n - 1) < (s.potential + 1) * (n + 1)
  have : (s.potential + 1) * (n + 1) = s.potential * (n + 1) + (n + 1) := by ring
  omega

/-- The generated lattice is preserved by `Hex.lllNative`. -/
theorem lllNative_memLattice_iff (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (v : Vector Int m) :
    Matrix.memLattice (lllNative b δ hδ hδ' hn) v ↔ Matrix.memLattice b v := by
  show Matrix.memLattice (lllLoop (LLLState.ofBasis b) 1 δ hδ hδ'
    (Nat.le_refl 1) hn (lllFuel (LLLState.ofBasis b))) v ↔ _
  exact lllLoop_memLattice_iff _ 1 δ hδ hδ' (Nat.le_refl 1) hn _ v

/-- Independence is preserved by `Hex.lllNative`. -/
theorem lllNative_independent (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) (hind : b.independent) :
    (lllNative b δ hδ hδ' hn).independent := by
  have hs_valid : (LLLState.ofBasis b).Valid :=
    HexLLLMathlib.LLLState.ofBasis_valid b
  show (lllLoop (LLLState.ofBasis b) 1 δ hδ hδ'
    (Nat.le_refl 1) hn (lllFuel (LLLState.ofBasis b))).independent
  exact LLLState.lllLoop_independent δ hδ hδ' _ _ 1
    (Nat.le_refl 1) hn hs_valid hind

/-- Classical native LLL short-vector bound at `η = 1/2`. For any independent
integer basis `b`, the first row of `Hex.lllNative b δ ...` has squared norm
at most `(1 / (δ − 1/4))^(n − 1)` times the squared norm of any nonzero
lattice vector. -/
theorem lllNative_short_vector
    (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) (hind : b.independent)
    {v : Vector Int m} (hv : Matrix.memLattice b v) (hv' : v ≠ 0) :
    ((((lllNative b δ hδ hδ' hn).row
        ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩).normSq : Int) : Rat) ≤
      (1 / (δ - 1 / 4)) ^ (n - 1) * ((v.normSq : Int) : Rat) := by
  have hred : isLLLReduced (lllNative b δ hδ hδ' hn) δ (1 / 2) :=
    lllNative_isLLLReduced b δ hδ hδ' hn hind
  have hind' : (lllNative b δ hδ hδ' hn).independent :=
    lllNative_independent b δ hδ hδ' hn hind
  have hv_lll : Matrix.memLattice (lllNative b δ hδ hδ' hn) v :=
    (lllNative_memLattice_iff b δ hδ hδ' hn v).mpr hv
  have hbnd := Hex.short_vector_bound_of_size_bound (lllNative b δ hδ hδ' hn) hind'
    hred (by grind) (by grind) hδ' hn hv_lll hv'
  -- Rewrite `(1/2) * (1/2)` as `1/4` in the resulting denominator.
  have hηη : (1 / 2 : Rat) * (1 / 2) = 1 / 4 := by grind
  rw [hηη] at hbnd
  exact hbnd

/-- Property triple for an accepted dispatch result: a `B'` returned by
`LLLProvider.dispatch b δ` generates the same lattice as `b`, is independent,
and is `(δ, 11/20)`-LLL-reduced. Composes `dispatch_some_certCheck` with
`HexLLLMathlib.certCheck_sound`, the single trusted property-level bridge of
`hex-lll` §"Certified external dispatch". -/
theorem dispatch_some_property {b : Matrix Int n m} {δ : Rat}
    {B' : Matrix Int n m} (h : LLLProvider.dispatch b δ = some B') :
    (∀ v, b.memLattice v ↔ B'.memLattice v) ∧
      B'.independent ∧ isLLLReduced B' δ (11 / 20) := by
  obtain ⟨U, V, hcheck⟩ := LLLProvider.dispatch_some_certCheck h
  exact HexLLLMathlib.certCheck_sound hcheck

/-- The public LLL `lll` produces a `(δ, 11/20)`-LLL-reduced matrix. On the
native path this is `lllNative_isLLLReduced` (`η = 1/2`) lifted to `η = 11/20`
by `isLLLReduced.mono_η`. On the certified-dispatch path it follows from
`certCheck_sound` via `dispatch_some_property`. -/
theorem lll_isLLLReduced (b : Matrix Int n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (hind : b.independent) :
    isLLLReduced (lll b δ hδ hδ' hn hind) δ (11 / 20) := by
  unfold lll
  cases hd : LLLProvider.dispatch b δ with
  | none =>
      exact Hex.Internal.isLLLReduced.mono_η _ (by grind) (by grind)
        (lllNative_isLLLReduced b δ
          (Hex.Internal.one_quarter_lt_of_eta_eleven_twentieths hδ) hδ' hn hind)
  | some B' =>
      exact (dispatch_some_property hd).2.2

/-- The generated lattice is preserved by `Hex.lll`. -/
theorem lll_memLattice_iff (b : Matrix Int n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (hind : b.independent) (v : Vector Int m) :
    Matrix.memLattice (lll b δ hδ hδ' hn hind) v ↔ Matrix.memLattice b v := by
  unfold lll
  cases hd : LLLProvider.dispatch b δ with
  | none =>
      exact lllNative_memLattice_iff b δ
        (Hex.Internal.one_quarter_lt_of_eta_eleven_twentieths hδ) hδ' hn v
  | some B' =>
      exact ((dispatch_some_property hd).1 v).symm

/-- Independence is preserved by `Hex.lll`. -/
theorem lll_independent (b : Matrix Int n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (hind : b.independent) :
    (lll b δ hδ hδ' hn hind).independent := by
  unfold lll
  cases hd : LLLProvider.dispatch b δ with
  | none =>
      exact lllNative_independent b δ
        (Hex.Internal.one_quarter_lt_of_eta_eleven_twentieths hδ) hδ' hn hind
  | some B' =>
      exact (dispatch_some_property hd).2.1

/-- Public LLL short-vector bound at `η = 11/20`. For any independent
integer basis `b`, the first row of `Hex.lll b δ ... hind` has squared norm at
most `(1 / (δ − 121/400))^(n − 1)` times the squared norm of any nonzero
lattice vector. -/
theorem lll_short_vector
    (b : Matrix Int n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (hind : b.independent)
    {v : Vector Int m} (hv : Matrix.memLattice b v) (hv' : v ≠ 0) :
    ((((lll b δ hδ hδ' hn hind).row
        ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩).normSq : Int) : Rat) ≤
      (1 / (δ - 121 / 400)) ^ (n - 1) * ((v.normSq : Int) : Rat) := by
  have hred : isLLLReduced (lll b δ hδ hδ' hn hind) δ (11 / 20) :=
    lll_isLLLReduced b δ hδ hδ' hn hind
  have hind' : (lll b δ hδ hδ' hn hind).independent :=
    lll_independent b δ hδ hδ' hn hind
  have hv_lll : Matrix.memLattice (lll b δ hδ hδ' hn hind) v :=
    (lll_memLattice_iff b δ hδ hδ' hn hind v).mpr hv
  have hδη : (11 / 20 : Rat) * (11 / 20) < δ := by
    have : (11 / 20 : Rat) * (11 / 20) = 121 / 400 := by grind
    grind
  have hbnd := Hex.short_vector_bound_of_size_bound (lll b δ hδ hδ' hn hind)
    hind' hred (by grind) hδη hδ' hn hv_lll hv'
  have hηη : (11 / 20 : Rat) * (11 / 20) = 121 / 400 := by grind
  simpa [hηη] using hbnd

end Hex

