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
      set B : Int := (s.ν.get kFin).get km1 with hB_def
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
        simpa [GramSchmidt.entry, Matrix.row] using
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
      -- which destructures `pairs.get i = ((s.ν.get i).get kFin, (s.ν.get i).get km1)`
      -- in the `k < i.val` branch (see `hpairs_at` below).
      let pairs : Vector (Int × Int) n :=
        Vector.ofFn fun i =>
          if _ : k < i.val then ((s.ν.get i).get kFin, (s.ν.get i).get km1)
          else (0, 0)
      let upd : Fin n → Vector Int n → Vector Int n :=
        fun i row =>
          let prev :=
            (Int.ofNat dkPrev * (pairs.get i).1 + B * (pairs.get i).2) / Int.ofNat dk
          let curr :=
            (Int.ofNat dkNext * (pairs.get i).2 - B * (pairs.get i).1) / Int.ofNat dk
          (row.set km1 prev).set kFin curr
      have hpairs_at : ∀ (i : Fin n), k < i.val →
          pairs.get i = ((s.ν.get i).get kFin, (s.ν.get i).get km1) := by
        intro i hi
        show (Vector.ofFn _).get i = _
        rw [Vector.get_ofFn]
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
          (s.ν.modify km1.val (setPrefix (s.ν.get kFin) · km1)).modify kFin.val
            (setPrefix (s.ν.get km1) · km1) with hνRows_def
        set νPivot : Hex.Matrix Int n n := νRowsSwapped.modify kFin.val (·.set km1 B)
          with hνPivot_def
        -- Unfold the goal to expose the ν' foldl, then apply
        -- `foldl_modify_rows_get`.
        change
          (((List.finRange n).foldl
              (fun (ν : Hex.Matrix Int n n) (i : Fin n) =>
                if _ : k < i.val then
                  ν.modify i.val (upd i)
                else ν)
              νPivot).get iFin).get jFin =
            ((GramSchmidt.Int.scaledCoeffs b').get iFin).get jFin
        have hν'_get :
            ((List.finRange n).foldl
                (fun (ν : Hex.Matrix Int n n) (i : Fin n) =>
                  if k < i.val then ν.modify i.val (upd i) else ν)
                νPivot).get iFin =
              if k < iFin.val then upd iFin (νPivot.get iFin) else νPivot.get iFin := by
          have := foldl_modify_rows_get (n := n) (α := Vector Int n) k
            (List.finRange n) (List.nodup_finRange n) νPivot upd iFin
          simp [List.mem_finRange] at this
          exact this
        -- Bridge `if _ : ...` (`dite`) to `if ...` (`ite`).
        have hbody_eq :
            (fun (ν : Hex.Matrix Int n n) (i : Fin n) =>
                if _ : k < i.val then ν.modify i.val (upd i) else ν) =
              (fun (ν : Hex.Matrix Int n n) (i : Fin n) =>
                if k < i.val then ν.modify i.val (upd i) else ν) := by
          funext ν i
          split <;> rfl
        rw [hbody_eq, hν'_get]
        -- Helper: evaluate νRowsSwapped.get at a given row.
        have hνRows_get_ne :
            ∀ (l : Fin n), l.val ≠ km1.val → l.val ≠ kFin.val →
              νRowsSwapped.get l = s.ν.get l := by
          intro l hl_km1 hl_kFin
          rw [hνRows_def]
          rw [vector_modify_get_ne _ kFin.val _ l (fun h => hl_kFin h.symm)]
          rw [vector_modify_get_ne _ km1.val _ l (fun h => hl_km1 h.symm)]
        have hνRows_get_km1 : νRowsSwapped.get km1 = setPrefix (s.ν.get kFin) (s.ν.get km1) km1 := by
          rw [hνRows_def]
          rw [vector_modify_get_ne _ kFin.val _ km1 (fun h => hkm1_val_ne_kFin h.symm)]
          exact vector_modify_get_self _ km1 _
        have hνRows_get_kFin :
            νRowsSwapped.get kFin = setPrefix (s.ν.get km1) (s.ν.get kFin) km1 := by
          rw [hνRows_def]
          rw [vector_modify_get_self _ kFin _]
          rw [vector_modify_get_ne _ km1.val _ kFin hkm1_val_ne_kFin]
        -- Evaluate νPivot.get.
        have hνPivot_get_ne :
            ∀ (l : Fin n), l.val ≠ kFin.val → νPivot.get l = νRowsSwapped.get l := by
          intro l hl_kFin
          rw [hνPivot_def]
          exact vector_modify_get_ne _ kFin.val _ l (fun h => hl_kFin h.symm)
        have hνPivot_get_kFin :
            νPivot.get kFin = (νRowsSwapped.get kFin).set km1.val B hkm1_lt_n := by
          rw [hνPivot_def]
          exact vector_modify_get_self _ kFin _
        -- Cache the `Valid` bridge from ν entries to scaledCoeffs.
        have hν_eq := hvalid.ν_eq
        -- Now case analysis on iFin's position.
        by_cases hki : k < iFin.val
        · -- Case D: k < iFin.val. ν' = upd iFin (νPivot.get iFin) and iFin ≠ km1, ≠ kFin.
          rw [if_pos hki]
          have hi_ne_km1 : iFin.val ≠ km1.val := by
            have : iFin.val > km1.val := by omega
            omega
          have hi_ne_kFin : iFin.val ≠ kFin.val := by
            have : iFin.val > kFin.val := hki
            omega
          rw [hνPivot_get_ne iFin hi_ne_kFin]
          rw [hνRows_get_ne iFin hi_ne_km1 hi_ne_kFin]
          -- Now LHS = (upd iFin (s.ν.get iFin)).get jFin. Unfold `upd` to expose
          -- the `pairs.get iFin` reference, then substitute it with its explicit
          -- value (valid since `k < iFin.val` in this branch).
          show ((let prev := (Int.ofNat dkPrev * (pairs.get iFin).1 +
                              B * (pairs.get iFin).2) / Int.ofNat dk
                 let curr := (Int.ofNat dkNext * (pairs.get iFin).2 -
                              B * (pairs.get iFin).1) / Int.ofNat dk
                 ((s.ν.get iFin).set km1 prev).set kFin curr).get jFin) =
            ((GramSchmidt.Int.scaledCoeffs b').get iFin).get jFin
          rw [show pairs.get iFin = ((s.ν.get iFin).get kFin, (s.ν.get iFin).get km1)
              from hpairs_at iFin hki]
          show ((((s.ν.get iFin).set km1.val
                ((Int.ofNat dkPrev * (s.ν.get iFin).get kFin +
                    B * (s.ν.get iFin).get km1) /
                  Int.ofNat dk) hkm1_lt_n).set kFin.val
              ((Int.ofNat dkNext * (s.ν.get iFin).get km1 -
                  B * (s.ν.get iFin).get kFin) /
                Int.ofNat dk) hk).get jFin) =
            ((GramSchmidt.Int.scaledCoeffs b').get iFin).get jFin
          -- Bridge `s.ν.get iFin .get k(Fin/m1)` to `scaledCoeffs s.b ...` for the
          -- two pivot columns used by the formulas.
          have hν_at_kFin :
              (s.ν.get iFin).get kFin =
                GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) iFin kFin := by
            have := hν_eq iFin.val kFin.val iFin.isLt kFin.isLt
              (by rw [hkFinVal]; exact hki)
            simpa [GramSchmidt.entry, Matrix.row] using this
          have hν_at_km1 :
              (s.ν.get iFin).get km1 =
                GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) iFin km1 := by
            have hkm1_lt_i : km1.val < iFin.val := by omega
            have := hν_eq iFin.val km1.val iFin.isLt km1.isLt hkm1_lt_i
            simpa [GramSchmidt.entry, Matrix.row] using this
          by_cases hjk : jFin.val = kFin.val
          · -- D2: jFin = kFin. Outer .set kFin curr_i applies.
            rw [show jFin = kFin from Fin.eq_of_val_eq hjk]
            show ((((s.ν.get iFin).set km1.val _ hkm1_lt_n).set kFin.val _ hk).get kFin) = _
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
              show ((((s.ν.get iFin).set km1.val _ hkm1_lt_n).set kFin.val _ hk).get km1) = _
              rw [show ((((s.ν.get iFin).set km1.val _ hkm1_lt_n).set kFin.val _ hk).get km1) =
                    (((s.ν.get iFin).set km1.val _ hkm1_lt_n).get km1) from
                  Vector.getElem_set_ne (h := hkFin_ne_km1) _ km1.isLt]
              rw [show (((s.ν.get iFin).set km1.val _ hkm1_lt_n).get km1) = _ from
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
              show ((((s.ν.get iFin).set km1.val _ hkm1_lt_n).set kFin.val _ hk).get jFin) = _
              rw [show ((((s.ν.get iFin).set km1.val _ hkm1_lt_n).set kFin.val _ hk).get jFin) =
                    (((s.ν.get iFin).set km1.val _ hkm1_lt_n).get jFin) from
                  Vector.getElem_set_ne (h := hkFin_ne_jFin) _ jFin.isLt]
              rw [show (((s.ν.get iFin).set km1.val _ hkm1_lt_n).get jFin) = _ from
                  Vector.getElem_set_ne (h := hkm1_ne_jFin) _ jFin.isLt]
              have hν := hν_eq iFin.val jFin.val iFin.isLt jFin.isLt hjiFin
              by_cases hj_lt_km1 : jFin.val < km1.val
              · -- jFin below km1.
                have hsc :=
                  GramSchmidt.Int.scaledCoeffs_adjacentSwap_above_low s.b kFin hk0 iFin jFin
                    hki (by rw [hkFinVal]; omega)
                show (s.ν.get iFin)[jFin.val] = _
                calc (s.ν.get iFin)[jFin.val]
                    = ((GramSchmidt.Int.scaledCoeffs s.b).get iFin).get jFin := hν
                  _ = ((GramSchmidt.Int.scaledCoeffs b').get iFin).get jFin := by
                        simpa [GramSchmidt.entry, Matrix.row] using hsc.symm
              · -- jFin above kFin.
                have hj_gt_k : kFin.val < jFin.val := by
                  rw [hkFinVal]; rw [hkm1Val] at hj_lt_km1; omega
                have hsc :=
                  GramSchmidt.Int.scaledCoeffs_adjacentSwap_above_high s.b kFin hk0 iFin jFin
                    hki hj_gt_k hjiFin
                show (s.ν.get iFin)[jFin.val] = _
                calc (s.ν.get iFin)[jFin.val]
                    = ((GramSchmidt.Int.scaledCoeffs s.b).get iFin).get jFin := hν
                  _ = ((GramSchmidt.Int.scaledCoeffs b').get iFin).get jFin := by
                        simpa [GramSchmidt.entry, Matrix.row] using hsc.symm
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
                show ((νRowsSwapped.get kFin).set km1.val B hkm1_lt_n).get km1 = B from
                    Vector.getElem_set_self km1.isLt]
              -- B = scaledCoeffs b' kFin km1 via hB_eq + scaledCoeffs_adjacentSwap_pivot.
              have hsc := GramSchmidt.Int.scaledCoeffs_adjacentSwap_pivot s.b kFin hk0
              show B = ((GramSchmidt.Int.scaledCoeffs b').get kFin).get km1
              calc B = GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 := hB_eq
                _ = ((GramSchmidt.Int.scaledCoeffs s.b).get kFin).get km1 := rfl
                _ = ((GramSchmidt.Int.scaledCoeffs b').get kFin).get km1 := by
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
              rw [show ((νRowsSwapped.get kFin).set km1.val B hkm1_lt_n).get jFin = _ from
                    Vector.getElem_set_ne (h := hj_ne_km1) _ jFin.isLt]
              rw [hνRows_get_kFin]
              change (setPrefix (s.ν.get km1) (s.ν.get kFin) km1).get jFin = _
              rw [setPrefix_get_lt jFin hj_lt_km1]
              have hν := hν_eq km1.val jFin.val km1.isLt jFin.isLt hj_lt_km1
              have hsc :=
                GramSchmidt.Int.scaledCoeffs_adjacentSwap_lower_curr s.b kFin hk0 jFin
                  (by rw [hkFinVal]; exact hj_succ_lt_k)
              show (s.ν.get km1).get jFin =
                ((GramSchmidt.Int.scaledCoeffs b').get kFin).get jFin
              calc (s.ν.get km1).get jFin
                  = ((GramSchmidt.Int.scaledCoeffs s.b).get km1).get jFin := hν
                _ = ((GramSchmidt.Int.scaledCoeffs b').get kFin).get jFin := by
                      simpa [GramSchmidt.entry, Matrix.row] using hsc.symm
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
              -- our goal uses `(M.get _).get _`. Bridge via simp.
              show (s.ν.get kFin).get jFin =
                ((GramSchmidt.Int.scaledCoeffs b').get km1).get jFin
              calc (s.ν.get kFin).get jFin
                  = ((GramSchmidt.Int.scaledCoeffs s.b).get kFin).get jFin := hν
                _ = ((GramSchmidt.Int.scaledCoeffs b').get km1).get jFin := by
                      simpa [GramSchmidt.entry, Matrix.row] using hsc.symm
            · -- Case A: iFin.val < km1.val.
              have hi_lt_km1 : iFin.val < km1.val := by omega
              have hi_ne_km1 : iFin.val ≠ km1.val := Nat.ne_of_lt hi_lt_km1
              have hi_ne_kFin : iFin.val ≠ kFin.val := by
                rw [hkFinVal]; omega
              rw [hνPivot_get_ne iFin hi_ne_kFin]
              rw [hνRows_get_ne iFin hi_ne_km1 hi_ne_kFin]
              -- LHS = (s.ν.get iFin).get jFin. Bridge through Valid then
              -- scaledCoeffs_adjacentSwap_before.
              have hν := hν_eq iFin.val jFin.val iFin.isLt jFin.isLt hjiFin
              have hsc :=
                GramSchmidt.Int.scaledCoeffs_adjacentSwap_before s.b kFin hk0 iFin jFin
                  (by rw [hkFinVal]; omega) hjiFin
              -- The goal is `(s.ν[iFin])[jFin] = scaledCoeffs b' [iFin][jFin]`.
              show (s.ν.get iFin).get jFin =
                ((GramSchmidt.Int.scaledCoeffs b').get iFin).get jFin
              calc (s.ν.get iFin).get jFin
                  = ((GramSchmidt.Int.scaledCoeffs s.b).get iFin).get jFin := hν
                _ = ((GramSchmidt.Int.scaledCoeffs b').get iFin).get jFin := hsc.symm
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
    (hind : s.b.independent) (hvalid : s.Valid) (hk0 : 0 < k) (hk : k < n) :
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
            ((s.ν.get ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩) ^ 2) /
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
      rw [foldl_mul_pull rest g (a * g x), foldl_mul_pull rest f (a * f x)]
      rw [← foldl_mul_congr_pointwise rest f g 1 heq_rest]
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
            ((s.ν.get ⟨k, hk⟩).get
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
          ((s.ν.get kFin).get ⟨k - 1, hkm1lt⟩) ^ 2 <
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
      ((s.ν.get kFin).get ⟨k - 1, hkm1lt⟩ : Int) =
        GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 := by
    have h := hvalid.ν_eq kFin.val km1.val kFin.isLt km1.isLt
      (by show k - 1 < k; omega)
    simpa [GramSchmidt.entry, Matrix.row] using h
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
          ((s.ν.get kFin).get ⟨k - 1, hkm1lt⟩) ^ 2 := by
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
        ((s.ν.get kFin).get _) ^ 2
    rw [hdk_eq, hdkPrev_eq, hdkNext_eq]
    rw [show ((s.ν.get kFin).get ⟨k - 1, hkm1lt⟩ : Int) =
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

end LLLState

end Hex
