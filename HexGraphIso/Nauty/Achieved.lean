/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SpecCanon

public section

/-!
The achieved leaf: the spec key's rows are the leaf rows of a
labelling reachable from the initial state, which fills each cell of
every ancestor partition with the same vertices. This is the content
of `specCanon_iso`: the total canonical form is isomorphic to its
input.

The engine is multiset preservation: every labelling write in `refine`
and `breakout` reorders one region confined to a cell of the current
partition, and partitions only gain boundaries, so contents of the
original cells never change.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Boundary-monotone coarsening -/

theorem cellEnd_go_le {ptn : Array Nat} {level j : Nat}
    (hj : ptn[j]! ≤ level) :
    ∀ (fuel i : Nat), i ≤ j → j < i + fuel →
      cellEnd.go ptn level fuel i ≤ j
  | 0, i, hij, hf => by omega
  | fuel + 1, i, hij, hf => by
    rw [cellEnd.go]
    rcases Decidable.em (ptn[i]! > level) with h | h
    · rw [ite_eq_left h]
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · omega
      · exact cellEnd_go_le hj fuel (i + 1) (by omega) (by omega)
    · rw [ite_eq_right h]
      exact hij

theorem cellEnd_le {ptn : Array Nat} {level i j : Nat} (hij : i ≤ j)
    (hj : ptn[j]! ≤ level) (hjs : j < ptn.size) :
    cellEnd ptn level i ≤ j := by
  rw [cellEnd]
  exact cellEnd_go_le hj (ptn.size - i) i hij (by omega)

/-- Segments between fine boundaries split into fine cells, so
cell-contents equivalence transfers to any coarser span. -/
theorem segN_perm_tiled {ptnF : Array Nat} {levF : Nat}
    {lab1 lab2 : Array Nat} (hfine : cellsPerm ptnF levF lab1 lab2)
    (hendF : ptnF[ptnF.size - 1]! ≤ levF) :
    ∀ (len a : Nat), 0 < len → a + len ≤ ptnF.size →
      (a = 0 ∨ ptnF[a - 1]! ≤ levF) → ptnF[a + len - 1]! ≤ levF →
      (segN lab1 a len).Perm (segN lab2 a len)
  | len, a, hlen, hsz, hstart, hend => by
    have hge : a ≤ cellEnd ptnF levF a := cellEnd_ge
    have hle : cellEnd ptnF levF a ≤ a + len - 1 :=
      cellEnd_le (by omega) hend (by omega)
    have hcell : IsCell ptnF levF a (cellEnd ptnF levF a + 1 - a) :=
      isCell_cellEnd (by omega) hstart hendF
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · have hlen' : len = cellEnd ptnF levF a + 1 - a := by omega
      rw [hlen']
      exact hfine _ _ hcell
    · have hsplit : len = (cellEnd ptnF levF a + 1 - a) +
          (len - (cellEnd ptnF levF a + 1 - a)) := by omega
      rw [hsplit, segN_append, segN_append]
      refine List.Perm.append (hfine _ _ hcell)
        (segN_perm_tiled hfine hendF _ _ (by omega) (by omega)
          (Or.inr ?_) ?_)
      · rw [show a + (cellEnd ptnF levF a + 1 - a) - 1 =
          cellEnd ptnF levF a from by omega]
        have h1 := hcell.2.2.2
        rw [show a + (cellEnd ptnF levF a + 1 - a) - 1 =
          cellEnd ptnF levF a from by omega] at h1
        exact h1
      · rw [show a + (cellEnd ptnF levF a + 1 - a) +
          (len - (cellEnd ptnF levF a + 1 - a)) - 1 =
          a + len - 1 from by omega]
        exact hend
  termination_by len _ => len
  decreasing_by
    have := hcell.1
    omega

/-- Cell-contents equivalence transfers from a finer partition (more
boundaries, possibly at a later level) to a coarser one. -/
theorem cellsPerm_coarsen {ptnC ptnF : Array Nat} {levC levF : Nat}
    {lab1 lab2 : Array Nat} (hszp : ptnC.size = ptnF.size)
    (hs1 : lab1.size = ptnF.size) (hs2 : lab2.size = ptnF.size)
    (hfine : cellsPerm ptnF levF lab1 lab2)
    (hendF : ptnF[ptnF.size - 1]! ≤ levF)
    (hendC : ptnC[ptnC.size - 1]! ≤ levC)
    (hb : ∀ q : Nat, ptnC[q]! ≤ levC → ptnF[q]! ≤ levF) :
    cellsPerm ptnC levC lab1 lab2 := by
  intro a len hcell
  have hlen0 := hcell.1
  rcases Nat.lt_or_ge a ptnF.size with han | han
  · have hain : a + len ≤ ptnF.size := by
      rcases Nat.lt_or_ge (a + len) (ptnF.size + 1) with h1 | h1
      · omega
      · exfalso
        have hi := hcell.2.2.1 (ptnF.size - 1) (by omega) (by omega)
        have h2 := hendC
        rw [hszp] at h2
        omega
    refine segN_perm_tiled hfine hendF len a (by omega) hain ?_ ?_
    · rcases hcell.2.1 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (hb _ h0)
    · exact hb _ hcell.2.2.2
  · have hlen1 : len = 1 := by
      rcases Nat.lt_or_ge len 2 with h2 | h2
      · omega
      · exfalso
        have hi := hcell.2.2.1 a (Nat.le_refl a) (by omega)
        rw [getElem!_neg _ _ (by omega)] at hi
        have hd : (default : Nat) = 0 := rfl
        omega
    subst hlen1
    rw [show (1 : Nat) = 0 + 1 from rfl, segN_cons, segN_cons,
      segN_zero, segN_zero, getElem!_neg _ _ (by omega),
      getElem!_neg _ _ (by omega)]

/-! # Region-confined labelling rewrites -/

/-- A labelling rewrite confined to a span of one cell, permuting its
contents, preserves every cell's contents. -/
theorem cellsPerm_of_confined {ptn : Array Nat} {level : Nat}
    {lab lab' : Array Nat} {A lenA : Nat}
    {c lenC : Nat} (hc : IsCell ptn level c lenC) (hcA : c ≤ A)
    (hAc : A + lenA ≤ c + lenC)
    (hperm : (segN lab A lenA).Perm (segN lab' A lenA))
    (hout : ∀ q, q < A ∨ A + lenA ≤ q → lab'[q]! = lab[q]!) :
    cellsPerm ptn level lab lab' := by
  intro a len hcell
  rcases isCell_disjoint_or_eq hcell hc with hd | hd | hd
  · -- the cell lies entirely after the region
    have he : segN lab a len = segN lab' a len :=
      segN_congr fun o ho => (hout _ (Or.inr (by omega))).symm
    rw [he]
  · -- the cell lies entirely before the region
    have he : segN lab a len = segN lab' a len :=
      segN_congr fun o ho => (hout _ (Or.inl (by omega))).symm
    rw [he]
  · -- the enclosing cell: pre ++ region ++ post
    obtain ⟨he1, he2⟩ := hd
    rw [he1, he2]
    have hsplit : lenC = (A - c) + (lenA + (c + lenC - A - lenA)) :=
      by omega
    rw [hsplit, segN_append, segN_append, segN_append, segN_append]
    refine List.Perm.append ?_ (List.Perm.append ?_ ?_)
    · have he : segN lab c (A - c) = segN lab' c (A - c) :=
        segN_congr fun o ho => (hout _ (Or.inl (by omega))).symm
      rw [he]
    · rw [show c + (A - c) = A from by omega]
      exact hperm
    · have he : segN lab (c + (A - c) + lenA)
          (c + lenC - A - lenA) = segN lab' (c + (A - c) + lenA)
          (c + lenC - A - lenA) :=
        segN_congr fun o ho => (hout _ (Or.inr (by omega))).symm
      rw [he]

/-! # The refine-internal invariant -/

theorem cellsPerm_refl (ptn : Array Nat) (level : Nat)
    (lab : Array Nat) : cellsPerm ptn level lab lab :=
  fun _ _ _ => List.Perm.refl _

theorem cellsPerm_trans {ptn : Array Nat} {level : Nat}
    {lab1 lab2 lab3 : Array Nat}
    (h1 : cellsPerm ptn level lab1 lab2)
    (h2 : cellsPerm ptn level lab2 lab3) :
    cellsPerm ptn level lab1 lab3 :=
  fun a len hc => (h1 a len hc).trans (h2 a len hc)

/-- The state facts carried through `refine` relative to its input. -/
structure RefInv (level : Nat) (lab0 ptn0 : Array Nat)
    (st : RefineSt) : Prop where
  labSize : st.lab.size = lab0.size
  ptnSize : st.ptn.size = ptn0.size
  grow : ∀ q : Nat, ptn0[q]! ≤ level → st.ptn[q]! ≤ level
  perm : cellsPerm ptn0 level lab0 st.lab

theorem RefInv.init (level : Nat) (lab0 ptn0 : Array Nat)
    (active numcells : Nat) :
    RefInv level lab0 ptn0
      { lab := lab0, ptn := ptn0, active := active,
        numcells := numcells, hint := 0, maxpos := 0,
        longcode := numcells } :=
  ⟨rfl, rfl, fun _ h => h, cellsPerm_refl _ _ _⟩

theorem RefInv.step {level : Nat} {lab0 ptn0 : Array Nat}
    {st st' : RefineSt} (h : RefInv level lab0 ptn0 st)
    (hls : st'.lab.size = st.lab.size)
    (hps : st'.ptn.size = st.ptn.size)
    (hpv : ∀ q : Nat, st'.ptn[q]! = st.ptn[q]! ∨ st'.ptn[q]! = level)
    (hlab : cellsPerm ptn0 level st.lab st'.lab) :
    RefInv level lab0 ptn0 st' :=
  ⟨hls.trans h.labSize, hps.trans h.ptnSize,
    fun q hq => by
      rcases hpv q with he | he
      · rw [he]
        exact h.grow q hq
      · rw [he]
        exact Nat.le_refl level,
    cellsPerm_trans h.perm hlab⟩

/-- A cell of a boundary-richer partition sits inside a cell of the
original. -/
theorem subcell_of_grow {ptn0 ptnP : Array Nat} {level A lenA : Nat}
    (_hszp : ptn0.size = ptnP.size)
    (hcellP : IsCell ptnP level A lenA)
    (hend0 : ptn0[ptn0.size - 1]! ≤ level)
    (hb : ∀ q : Nat, ptn0[q]! ≤ level → ptnP[q]! ≤ level)
    (hA0 : A < ptn0.size) (_hA : A + lenA ≤ ptn0.size) :
    ∃ c lenC, IsCell ptn0 level c lenC ∧ c ≤ A ∧
      A + lenA ≤ c + lenC := by
  obtain ⟨p, hpm, hp1, hp2⟩ := cells_cover (ptn := ptn0)
    (level := level) (nn := ptn0.size) A hA0
  have hpc := cells_isCell (Nat.le_refl ptn0.size) hend0 p hpm
  have hple := cells_le p hpm
  have hpb := cells_bound (Nat.le_refl ptn0.size) hend0 p hpm
  refine ⟨p.1, p.2 + 1 - p.1, hpc, by omega, ?_⟩
  rcases Nat.lt_or_ge (p.2 + 1) (A + lenA) with hlt | hge
  · exfalso
    have hv0 : ptn0[p.2]! ≤ level := by
      have h1 := hpc.2.2.2
      rw [show p.1 + (p.2 + 1 - p.1) - 1 = p.2 from by omega] at h1
      exact h1
    have hvP := hb _ hv0
    have hint := hcellP.2.2.1 p.2 (by omega) (by omega)
    omega
  · omega

/-! # The trivial-splitter pass preserves the invariant -/

theorem splitCellLoop_region_perm {gRow : Nat} {lab : Array Nat}
    {cell1 cell2 : Nat} (h12 : cell1 ≤ cell2)
    (hsz : cell2 < lab.size) :
    (segN (splitCellLoop gRow (cell2 - cell1 + 2) lab
      (Int.ofNat cell1) (Int.ofNat cell2)).1 cell1
      (cell2 + 1 - cell1)).Perm
      (segN lab cell1 (cell2 + 1 - cell1)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := splitCellLoop_spec
    (gRow := gRow) (cell2 + 1 - cell1) (cell2 - cell1 + 2) lab
    (Int.ofNat cell1) (Int.ofNat cell2)
    (by simp only [Int.ofNat_eq_natCast]; omega)
    (by
      have : (cell2 : Int) < (lab.size : Int) := by
        exact_mod_cast hsz
      simpa using this)
    (by
      rw [show (Int.ofNat cell2 + 1 - Int.ofNat cell1) =
        ((cell2 + 1 - cell1 : Nat) : Int) from by
          simp only [Int.ofNat_eq_natCast]
          omega])
    (by omega)
  have htn : (Int.ofNat cell1).toNat = cell1 := rfl
  rw [htn] at h5 h6
  have hcnt : (segN lab cell1 (cell2 + 1 - cell1)).countP
      (elem gRow ·) ≤ cell2 + 1 - cell1 := by
    have := List.countP_le_length
      (p := (elem gRow ·)) (l := segN lab cell1 (cell2 + 1 - cell1))
    rw [segN_length] at this
    exact this
  have hsplit : cell2 + 1 - cell1 =
      (segN lab cell1 (cell2 + 1 - cell1)).countP (elem gRow ·) +
      ((cell2 + 1 - cell1) -
        (segN lab cell1 (cell2 + 1 - cell1)).countP (elem gRow ·)) :=
    by omega
  rw [hsplit, segN_append]
  rw [← hsplit]
  refine ((h5.append h6).trans ?_)
  exact List.filter_append_perm _ _

theorem trivialSplit_lab (level cell1 cell2 : Nat) (c1 c2 : Int)
    (st : RefineSt) :
    (trivialSplit level cell1 cell2 c1 c2 st).lab = st.lab := by
  rw [trivialSplit]
  repeat' split
  all_goals rfl

theorem trivialSplit_ptn (level cell1 cell2 : Nat) (c1 c2 : Int)
    (st : RefineSt) :
    (trivialSplit level cell1 cell2 c1 c2 st).ptn = st.ptn ∨
      (trivialSplit level cell1 cell2 c1 c2 st).ptn =
        st.ptn.set! c2.toNat level := by
  rw [trivialSplit]
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl

theorem refInv_trivialCell {level gRow cell1 cell2 : Nat}
    {lab0 ptn0 : Array Nat} {st : RefineSt}
    (hinv : RefInv level lab0 ptn0 st)
    {c lenC : Nat} (hc : IsCell ptn0 level c lenC) (hcA : c ≤ cell1)
    (hAc : cell2 + 1 ≤ c + lenC) (h12 : cell1 ≤ cell2)
    (hsz : cell2 < st.lab.size) :
    RefInv level lab0 ptn0 (trivialCell level gRow cell1 cell2 st) :=
  by
  rw [trivialCell]
  split
  · exact hinv
  · obtain ⟨hh1, hh2, hh3, hh4, hh5, hh6⟩ := splitCellLoop_spec
      (gRow := gRow) (cell2 + 1 - cell1) (cell2 - cell1 + 2) st.lab
      (Int.ofNat cell1) (Int.ofNat cell2)
      (by simp only [Int.ofNat_eq_natCast]; omega)
      (by
        have : (cell2 : Int) < (st.lab.size : Int) := by
          exact_mod_cast hsz
        simpa using this)
      (by
        rw [show (Int.ofNat cell2 + 1 - Int.ofNat cell1) =
          ((cell2 + 1 - cell1 : Nat) : Int) from by
            simp only [Int.ofNat_eq_natCast]
            omega])
      (by omega)
    have hstep1 : RefInv level lab0 ptn0
        { st with lab := (splitCellLoop gRow (cell2 - cell1 + 2)
            st.lab (Int.ofNat cell1) (Int.ofNat cell2)).1 } := by
      refine RefInv.step hinv hh3 rfl (fun q => Or.inl rfl) ?_
      refine cellsPerm_of_confined (A := cell1)
        (lenA := cell2 + 1 - cell1) hc hcA (by omega)
        (splitCellLoop_region_perm h12 hsz).symm ?_
      intro q hq
      refine hh4 q ?_
      rcases hq with hq | hq
      · left
        show (q : Int) < Int.ofNat cell1
        simp only [Int.ofNat_eq_natCast]
        omega
      · right
        show (Int.ofNat cell2) < (q : Int)
        simp only [Int.ofNat_eq_natCast]
        omega
    refine RefInv.step hstep1 (by rw [trivialSplit_lab]) ?_ ?_
      (by rw [trivialSplit_lab]; exact cellsPerm_refl _ _ _)
    · rcases trivialSplit_ptn level cell1 cell2 _ _ _ with he | he
      · rw [he]
      · rw [he, Array.size_set!]
    · intro q
      rcases trivialSplit_ptn level cell1 cell2
        (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
          (Int.ofNat cell1) (Int.ofNat cell2)).2.1
        (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
          (Int.ofNat cell1) (Int.ofNat cell2)).2.2
        { st with lab := (splitCellLoop gRow (cell2 - cell1 + 2)
            st.lab (Int.ofNat cell1) (Int.ofNat cell2)).1 }
        with he | he
      · rw [he]
        exact Or.inl rfl
      · rw [he]
        rcases getElem!_set!_cases
          ({ st with lab := (splitCellLoop gRow (cell2 - cell1 + 2)
              st.lab (Int.ofNat cell1) (Int.ofNat cell2)).1 } :
            RefineSt).ptn
          ((splitCellLoop gRow (cell2 - cell1 + 2) st.lab
            (Int.ofNat cell1) (Int.ofNat cell2)).2.2).toNat level q
          with hg | hg
        · rw [hg]
          exact Or.inl rfl
        · rw [hg]
          exact Or.inr rfl

/-! # The nontrivial-splitter pass preserves the invariant -/

theorem mem_countValues {counts : List Nat} {v : Nat}
    (hlo : counts.foldl Nat.min (counts.headD 0) ≤ v)
    (hhi : v ≤ counts.foldl Nat.max (counts.headD 0)) :
    v ∈ countValues counts := by
  rw [countValues]
  refine List.mem_map.mpr ⟨v - counts.foldl Nat.min
    (counts.headD 0), List.mem_range.mpr (by omega), by omega⟩

theorem segmentOf_perm (ctx : Ctx) (lab : Array Nat)
    (workset cell1 cell2 : Nat) (_hsz : cell2 < lab.size)
    (_h12 : cell1 ≤ cell2) :
    (segmentOf lab cell1 (countsOf ctx lab workset cell1 cell2)
      (countValues (countsOf ctx lab workset cell1 cell2))).Perm
      (segN lab cell1 (cell2 + 1 - cell1)) := by
  rw [countsOf_eq_map]
  rw [segmentOf_eq_flatMap lab cell1
    (segN lab cell1 (cell2 + 1 - cell1))
    (fun v => popCount (workset &&& ctx.g[v]!))
    (countValues ((segN lab cell1 (cell2 + 1 - cell1)).map
      fun v => popCount (workset &&& ctx.g[v]!)))
    (fun j hj => by
      rw [segN_length] at hj
      exact (segN_getElem! lab cell1 (cell2 + 1 - cell1) j hj).symm)]
  refine flatMap_filters_perm _ _ ?_ ?_
  · rw [countValues]
    exact nodup_range_map_add _ _
  · intro x hx
    have hmem : popCount (workset &&& ctx.g[x]!) ∈
        (segN lab cell1 (cell2 + 1 - cell1)).map
          fun v => popCount (workset &&& ctx.g[v]!) :=
      List.mem_map_of_mem hx
    exact mem_countValues
      (foldl_min_le_mem _ _ _ hmem) (foldl_max_ge_mem _ _ _ hmem)

theorem nontrivialFix_lab (cell1 : Nat) (st : RefineSt) :
    (nontrivialFix cell1 st).lab = st.lab := by
  rw [nontrivialFix]
  split <;> rfl

theorem nontrivialFix_ptn (cell1 : Nat) (st : RefineSt) :
    (nontrivialFix cell1 st).ptn = st.ptn := by
  rw [nontrivialFix]
  split <;> rfl

theorem refInv_nontrivialCell {ctx : Ctx}
    {level workset cell1 cell2 : Nat}
    {lab0 ptn0 : Array Nat} {st : RefineSt}
    (hinv : RefInv level lab0 ptn0 st)
    {c lenC : Nat} (hc : IsCell ptn0 level c lenC)
    (hcA : c ≤ cell1) (hAc : cell2 + 1 ≤ c + lenC)
    (h12 : cell1 ≤ cell2) (hsz : cell2 < st.lab.size) :
    RefInv level lab0 ptn0
      (nontrivialCell ctx level workset cell1 cell2 st) := by
  rw [nontrivialCell]
  split
  · exact hinv
  · split
    · exact RefInv.step hinv rfl rfl (fun _ => Or.inl rfl)
        (cellsPerm_refl _ _ _)
    · -- the real split: window scan then the counting rewrite
      have hws : RefInv level lab0 ptn0 (windowScan level cell1 cell2
        (countsOf ctx st.lab workset cell1 cell2)
        (countValues (countsOf ctx st.lab workset cell1 cell2))
        cell1 (-1) st) := by
        refine RefInv.step hinv
          (by rw [lab_windowScan]) (by rw [ptn_windowScan_size]) ?_
          (by rw [lab_windowScan]; exact cellsPerm_refl _ _ _)
        intro q
        exact ptn_windowScan_vals level cell1 cell2 _ _ _ _ _ q
      refine RefInv.step (st := windowScan level cell1 cell2
        (countsOf ctx st.lab workset cell1 cell2)
        (countValues (countsOf ctx st.lab workset cell1 cell2))
        cell1 (-1) st) hws ?_ ?_
        (fun q => by rw [nontrivialFix_ptn]; exact Or.inl rfl)
        ?_
      · rw [nontrivialFix_lab]
        show (writeSegment (windowScan level cell1 cell2
        (countsOf ctx st.lab workset cell1 cell2)
        (countValues (countsOf ctx st.lab workset cell1 cell2))
        cell1 (-1) st).lab cell1
          (segmentOf (windowScan level cell1 cell2
        (countsOf ctx st.lab workset cell1 cell2)
        (countValues (countsOf ctx st.lab workset cell1 cell2))
        cell1 (-1) st).lab cell1
            (countsOf ctx st.lab workset cell1 cell2)
            (countValues (countsOf ctx st.lab workset cell1
              cell2)))).size = (windowScan level cell1 cell2
        (countsOf ctx st.lab workset cell1 cell2)
        (countValues (countsOf ctx st.lab workset cell1 cell2))
        cell1 (-1) st).lab.size
        rw [writeSegment_size]
      · rw [nontrivialFix_ptn]
      · rw [nontrivialFix_lab]
        have hlws : (windowScan level cell1 cell2
        (countsOf ctx st.lab workset cell1 cell2)
        (countValues (countsOf ctx st.lab workset cell1 cell2))
        cell1 (-1) st).lab = st.lab := lab_windowScan _ _ _ _ _ _
          _ _
        rw [hlws]
        have hperm := segmentOf_perm ctx st.lab workset cell1 cell2
          hsz h12
        have hlen : (segmentOf st.lab cell1
            (countsOf ctx st.lab workset cell1 cell2)
            (countValues (countsOf ctx st.lab workset cell1
              cell2))).length = cell2 + 1 - cell1 := by
          rw [hperm.length_eq, segN_length]
        refine cellsPerm_of_confined (A := cell1)
          (lenA := cell2 + 1 - cell1) hc hcA (by omega) ?_ ?_
        · rw [show segN (writeSegment st.lab cell1 (segmentOf st.lab
              cell1 (countsOf ctx st.lab workset cell1 cell2)
              (countValues (countsOf ctx st.lab workset cell1
                cell2)))) cell1 (cell2 + 1 - cell1) =
              segmentOf st.lab cell1
                (countsOf ctx st.lab workset cell1 cell2)
                (countValues (countsOf ctx st.lab workset cell1
                  cell2)) from by
            rw [← hlen]
            exact segN_writeSegment _ _ _ (by omega)]
          exact hperm.symm
        · intro q hq
          refine writeSegment_outside _ _ _ _ ?_
          rcases hq with hq | hq
          · exact Or.inl hq
          · right
            omega

/-! # The passes, the loop, and `refine` -/

theorem refInv_cells_facts {ctx : Ctx} {level : Nat}
    {lab0 ptn0 : Array Nat} {st : RefineSt}
    (hinv : RefInv level lab0 ptn0 st)
    (hnn : ctx.n ≤ ptn0.size) (hs : lab0.size = ptn0.size)
    (hend0 : ptn0[ptn0.size - 1]! ≤ level) :
    ∀ p ∈ cells st.ptn level ctx.n, p.1 ≤ p.2 ∧ p.2 < lab0.size ∧
      ∃ c lenC, IsCell ptn0 level c lenC ∧ c ≤ p.1 ∧
        p.2 + 1 ≤ c + lenC := by
  intro p hp
  have hps := hinv.ptnSize
  have hls := hinv.labSize
  have hendSt : st.ptn[st.ptn.size - 1]! ≤ level := by
    rw [hinv.ptnSize]
    exact hinv.grow _ hend0
  have hple := cells_le p hp
  have hpb := cells_bound (nn := ctx.n)
    (by rw [hinv.ptnSize]; omega) hendSt p hp
  have hic := cells_isCell (ptn := st.ptn)
    (by rw [hinv.ptnSize]; omega) hendSt p hp
  obtain ⟨c, lenC, hcell, hc1, hc2⟩ := subcell_of_grow
    (ptnP := st.ptn) hinv.ptnSize.symm hic hend0 hinv.grow
    (by omega) (by omega)
  exact ⟨hple, by omega, c, lenC, hcell, hc1, by omega⟩

theorem refInv_refineTrivial_go {level gRow : Nat}
    {lab0 ptn0 : Array Nat} :
    ∀ (l : List (Nat × Nat)) (st : RefineSt),
      RefInv level lab0 ptn0 st →
      (∀ p ∈ l, p.1 ≤ p.2 ∧ p.2 < lab0.size ∧
        ∃ c lenC, IsCell ptn0 level c lenC ∧ c ≤ p.1 ∧
          p.2 + 1 ≤ c + lenC) →
      RefInv level lab0 ptn0 (refineTrivial.go level gRow l st)
  | [], st, hinv, _ => hinv
  | (cell1, cell2) :: rest, st, hinv, hl => by
    rw [refineTrivial.go]
    obtain ⟨h12, hb2, c, lenC, hcell, hc1, hc2⟩ :=
      hl _ (List.mem_cons.mpr (Or.inl rfl))
    exact refInv_refineTrivial_go rest _
      (refInv_trivialCell hinv hcell hc1 hc2 h12
        (by rw [hinv.labSize]; exact hb2))
      (fun p hp => hl p (List.mem_cons.mpr (Or.inr hp)))

theorem refInv_refineNontrivial_go {ctx : Ctx}
    {level workset : Nat} {lab0 ptn0 : Array Nat} :
    ∀ (l : List (Nat × Nat)) (st : RefineSt),
      RefInv level lab0 ptn0 st →
      (∀ p ∈ l, p.1 ≤ p.2 ∧ p.2 < lab0.size ∧
        ∃ c lenC, IsCell ptn0 level c lenC ∧ c ≤ p.1 ∧
          p.2 + 1 ≤ c + lenC) →
      RefInv level lab0 ptn0
        (refineNontrivial.go ctx level workset l st)
  | [], st, hinv, _ => hinv
  | (cell1, cell2) :: rest, st, hinv, hl => by
    rw [refineNontrivial.go]
    obtain ⟨h12, hb2, c, lenC, hcell, hc1, hc2⟩ :=
      hl _ (List.mem_cons.mpr (Or.inl rfl))
    exact refInv_refineNontrivial_go rest _
      (refInv_nontrivialCell hinv hcell hc1 hc2 h12
        (by rw [hinv.labSize]; exact hb2))
      (fun p hp => hl p (List.mem_cons.mpr (Or.inr hp)))

theorem refInv_record {level : Nat} {lab0 ptn0 : Array Nat}
    {st st' : RefineSt} (hinv : RefInv level lab0 ptn0 st)
    (hl : st'.lab = st.lab) (hp : st'.ptn = st.ptn) :
    RefInv level lab0 ptn0 st' :=
  RefInv.step hinv (by rw [hl]) (by rw [hp])
    (fun q => by rw [hp]; exact Or.inl rfl)
    (by rw [hl]; exact cellsPerm_refl _ _ _)

theorem refInv_refineStep {ctx : Ctx} {level split1 : Nat}
    {lab0 ptn0 : Array Nat} {st : RefineSt}
    (hinv : RefInv level lab0 ptn0 st)
    (hnn : ctx.n ≤ ptn0.size) (hs : lab0.size = ptn0.size)
    (hend0 : ptn0[ptn0.size - 1]! ≤ level) :
    RefInv level lab0 ptn0 (refineStep ctx level split1 st) := by
  rw [refineStep]
  split
  · rw [refineTrivial]
    exact refInv_refineTrivial_go _ _ (refInv_record hinv rfl rfl)
      (refInv_cells_facts (refInv_record hinv rfl rfl) hnn hs hend0)
  · rw [refineNontrivial]
    exact refInv_refineNontrivial_go _ _ (refInv_record hinv rfl rfl)
      (refInv_cells_facts (refInv_record hinv rfl rfl) hnn hs hend0)

theorem refInv_refineLoop {ctx : Ctx} {level : Nat}
    {lab0 ptn0 : Array Nat}
    (hnn : ctx.n ≤ ptn0.size) (hs : lab0.size = ptn0.size)
    (hend0 : ptn0[ptn0.size - 1]! ≤ level) :
    ∀ (fuel : Nat) (st : RefineSt), RefInv level lab0 ptn0 st →
      RefInv level lab0 ptn0 (refineLoop ctx level fuel st)
  | 0, st, hinv => hinv
  | fuel + 1, st, hinv => by
    rw [refineLoop]
    split
    · split
      · exact refInv_refineLoop hnn hs hend0 fuel _
          (refInv_refineStep hinv hnn hs hend0)
      · exact hinv
    · exact hinv

/-- `refine` preserves labelling size and every input cell's contents,
and only adds partition boundaries. -/
theorem refine_refInv {ctx : Ctx} {level : Nat}
    {lab ptn : Array Nat} {active numcells : Nat}
    (hnn : ctx.n ≤ ptn.size) (hs : lab.size = ptn.size)
    (hend : ptn[ptn.size - 1]! ≤ level) :
    RefInv level lab ptn (refine ctx level lab ptn active
      numcells) := by
  rw [refine]
  have h1 := refInv_refineLoop (lab0 := lab) (ptn0 := ptn) hnn hs
    hend (4 * ctx.n + 8)
    { lab := lab, ptn := ptn, active := active,
      numcells := numcells, hint := 0, maxpos := 0,
      longcode := numcells }
    (RefInv.init level lab ptn active numcells)
  exact refInv_record h1 rfl rfl

/-! # Boundary counting: the search always reaches its leaves -/

/-- The number of positions carrying a boundary at `level`. -/
@[expose] def bcount (ptn : Array Nat) (level nn : Nat) : Nat :=
  (List.range nn).countP fun q => decide (ptn[q]! ≤ level)

theorem bcount_le (ptn : Array Nat) (level nn : Nat) :
    bcount ptn level nn ≤ nn := by
  rw [bcount]
  have := List.countP_le_length
    (p := fun q => decide (ptn[q]! ≤ level)) (l := List.range nn)
  rw [List.length_range] at this
  exact this

theorem bcount_mono {ptn ptn' : Array Nat} {level level' nn : Nat}
    (h : ∀ q : Nat, ptn[q]! ≤ level → ptn'[q]! ≤ level') :
    bcount ptn level nn ≤ bcount ptn' level' nn := by
  rw [bcount, bcount]
  refine List.countP_mono_left fun x _ hx => ?_
  simp only [decide_eq_true_eq] at hx ⊢
  exact h x hx

theorem countP_succ_le {p p' : Nat → Bool} :
    ∀ (l : List Nat), l.Nodup →
      (∀ x ∈ l, p x = true → p' x = true) →
      ∀ x0 ∈ l, p x0 = false → p' x0 = true →
      l.countP p + 1 ≤ l.countP p'
  | [], _, _, x0, hx0, _, _ => absurd hx0 (by simp)
  | y :: l, hnd, himp, x0, hx0, hp0, hp'0 => by
    rcases List.mem_cons.mp hx0 with rfl | hmem
    · have hmono : l.countP p ≤ l.countP p' :=
        List.countP_mono_left fun x hx hpx =>
          himp x (List.mem_cons.mpr (Or.inr hx)) hpx
      rw [List.countP_cons_of_neg (by simp [hp0]),
        List.countP_cons_of_pos (by simp [hp'0])]
      omega
    · have hrec := countP_succ_le l (List.pairwise_cons.mp hnd).2
        (fun x hx hpx => himp x (List.mem_cons.mpr (Or.inr hx)) hpx)
        x0 hmem hp0 hp'0
      rcases hpy : p y with _ | _
      · rcases hp'y : p' y with _ | _
        · rw [List.countP_cons_of_neg (by simp [hpy]),
            List.countP_cons_of_neg (by simp [hp'y])]
          omega
        · rw [List.countP_cons_of_neg (by simp [hpy]),
            List.countP_cons_of_pos (by simp [hp'y])]
          omega
      · rw [List.countP_cons_of_pos (by simp [hpy]),
          List.countP_cons_of_pos (by
            simp [himp y (List.mem_cons.mpr (Or.inl rfl)) hpy])]
        omega

/-- Individualizing one vertex of a nontrivial cell adds a boundary. -/
theorem bcount_breakout {ptn : Array Nat} {level tc nn : Nat}
    (_hvals : ∀ q : Nat, ptn[q]! ≤ level ∨ ptn[q]! = n + 2)
    (_hlev : level + 1 < n + 2)
    (htc : ptn[tc]! > level) (htcn : tc < nn) (htcs : tc < ptn.size) :
    bcount ptn level nn + 1 ≤
      bcount (ptn.set! tc (level + 1)) (level + 1) nn := by
  rw [bcount, bcount]
  refine countP_succ_le (List.range nn) List.nodup_range ?_ tc
    (List.mem_range.mpr htcn) (by simp; omega) ?_
  · intro x _ hx
    simp only [decide_eq_true_eq] at hx ⊢
    have hne : tc ≠ x := by
      intro he
      rw [← he] at hx
      omega
    rw [Array.getElem!_set!_ne _ _ _ _ hne]
    omega
  · simp only [decide_eq_true_eq]
    rw [Array.getElem!_set!_self _ _ _ htcs]
    omega

theorem bcount_pos_of_boundary {ptn : Array Nat} {level nn q : Nat}
    (hq : q < nn) (hv : ptn[q]! ≤ level) :
    1 ≤ bcount ptn level nn := by
  rw [bcount]
  refine List.countP_pos_iff.mpr ⟨q, List.mem_range.mpr hq, ?_⟩
  simpa using hv

/-! # The achieved leaf -/

/-- The spec key's rows are the leaf rows of a labelling that fills
every cell of this node's partition with the same vertices. -/
theorem specNode_achieved {ctx : Ctx} (hn : ctx.n = n)
    (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active numcells : Nat),
      NodeOk n level lab ptn active →
      n + 1 ≤ level + fuel →
      level ≤ bcount ptn level n →
      ∃ llab : Array Nat, llab.size = n ∧
        cellsPerm ptn level lab llab ∧
        (specNode ctx tcLevel fuel level lab ptn active
          numcells).rows = leafRows ctx llab
  | 0, level, lab, ptn, active, numcells, hok, hlfl, hbc => by
    exfalso
    have := bcount_le ptn level n
    omega
  | fuel + 1, level, lab, ptn, active, numcells, hok, hlfl, hbc => by
    have hlevn : level ≤ n := by
      have := bcount_le ptn level n
      omega
    have hstR := refine_stOk (ctx := ctx) hn (level := level)
      (numcells := numcells) hok.labSize hok.labOk hok.ptnSize
      hok.act hok.ptnEnd
    have hRvals : ∀ q : Nat,
        (refine ctx level lab ptn active numcells).ptn[q]! ≤ level ∨ (refine ctx level lab ptn active numcells).ptn[q]! = n + 2 := by
      intro q
      rcases ptn_refine_vals ctx level lab ptn active numcells q
        with he | he
      · rw [he]
        exact hok.vals q
      · rw [he]
        exact Or.inl (Nat.le_refl level)
    have hRinv := refine_refInv (ctx := ctx) (level := level)
      (lab := lab) (ptn := ptn) (active := active)
      (numcells := numcells) (by rw [hok.ptnSize]; omega)
      (by rw [hok.labSize, hok.ptnSize]) hok.ptnEnd
    rcases hdisc : discreteAt (refine ctx level lab ptn active numcells).ptn level ctx.n with _ | _
    · -- non-discrete: recurse into the maximal child
      obtain ⟨p, hptc, hp12, hpb, hicp, hce⟩ := targetcell_facts hn
        (tcLevel := tcLevel) (refine ctx level lab ptn active numcells).lab hstR.ptnSize hstR.ptnEnd hdisc
      have hM1 : (specMaketargetcell ctx (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn level
          tcLevel).1 = p.1 := hptc
      have hM22 : (specMaketargetcell ctx (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn level
          tcLevel).2.2 = p.2 + 1 - p.1 := by
        show cellEnd (refine ctx level lab ptn active numcells).ptn level
          (specTargetcell ctx (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn level tcLevel + 1) -
          specTargetcell ctx (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn level tcLevel + 1 =
          p.2 + 1 - p.1
        rw [hptc, hce]
        omega
      obtain ⟨m, hm⟩ : ∃ m, p.2 + 1 - p.1 = m + 1 :=
        ⟨p.2 - p.1, by omega⟩
      have hspec : specNode ctx tcLevel (fuel + 1) level lab ptn
          active numcells =
          ⟨(refine ctx level lab ptn active numcells).longcode ::
            (keysMax (childKey ctx tcLevel fuel level
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells 0)
              ((List.range m).map
                ((fun o => childKey ctx tcLevel fuel level
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells o) ∘ Nat.succ))).codes,
          (keysMax (childKey ctx tcLevel fuel level
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells 0)
            ((List.range m).map
              ((fun o => childKey ctx tcLevel fuel level
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells o) ∘ Nat.succ))).rows⟩ := by
        rw [specNode]
        simp only [hdisc, Bool.false_eq_true, ite_false]
        rw [hM1, hM22, hm, List.range_succ_eq_map, List.map_cons,
          List.map_map]
      -- the maximum is one of the children
      have hmem : ∃ o, o < m + 1 ∧
          keysMax (childKey ctx tcLevel fuel level
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells 0)
            ((List.range m).map ((fun o => childKey ctx tcLevel fuel level
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells o) ∘ Nat.succ)) =
          childKey ctx tcLevel fuel level
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells o := by
        rcases keysMax_mem ((List.range m).map fun j =>
          childKey ctx tcLevel fuel level
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells (j + 1)) (childKey ctx tcLevel fuel level
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells 0) with he | he
        · exact ⟨0, by omega, he⟩
        · rcases List.mem_map.mp he with ⟨j, hj, hje⟩
          exact ⟨j + 1, by
            have := List.mem_range.mp hj
            omega, hje.symm⟩
      obtain ⟨o, hom, hkm⟩ := hmem
      -- facts feeding the child recursion
      have hicp1 : IsCell (refine ctx level lab ptn active numcells).ptn level p.1 (p.2 + 1 - p.1) := hicp
      have hchildOk := childNodeOk (n := n) (level := level)
        (tc := p.1) (lenT := p.2 + 1 - p.1) (o := o)
        hstR.labSize hstR.labOk hstR.ptnSize hstR.ptnEnd hRvals
        hicp1 (by omega) (by omega)
      have hbcChild : level + 1 ≤
          bcount ((refine ctx level lab ptn active numcells).ptn.set! p.1 (level + 1)) (level + 1) n := by
        have h1 : bcount ptn level n ≤ bcount (refine ctx level lab ptn active numcells).ptn level n :=
          bcount_mono hRinv.grow
        have h2 := bcount_breakout (n := n)
          (ptn := (refine ctx level lab ptn active numcells).ptn) (level := level) (tc := p.1) (nn := n)
          hRvals (by omega)
          (hicp.2.2.1 p.1 (Nat.le_refl p.1) (by omega))
          (by omega) (by rw [hstR.ptnSize]; omega)
        omega
      obtain ⟨llab, hlsz, hlperm, hlrows⟩ := specNode_achieved hn
        tcLevel fuel (level + 1)
        (breakout (refine ctx level lab ptn active numcells).lab
        (refine ctx level lab ptn active numcells).ptn (level + 1) p.1
        (refine ctx level lab ptn active numcells).lab[p.1 + o]!).1
        (breakout (refine ctx level lab ptn active numcells).lab
        (refine ctx level lab ptn active numcells).ptn (level + 1) p.1
        (refine ctx level lab ptn active numcells).lab[p.1 + o]!).2.1
        (breakout (refine ctx level lab ptn active numcells).lab
        (refine ctx level lab ptn active numcells).ptn (level + 1) p.1
        (refine ctx level lab ptn active numcells).lab[p.1 + o]!).2.2
        ((refine ctx level lab ptn active numcells).numcells + 1) hchildOk (by omega) hbcChild
      refine ⟨llab, hlsz, ?_, ?_⟩
      · -- chain the three reorder stages
        have htv : (refine ctx level lab ptn active numcells).lab[p.1 + o]! ∈
            segN (refine ctx level lab ptn active numcells).lab p.1 (p.2 + 1 - p.1) := by
          rw [segN]
          exact List.mem_map.mpr ⟨o, List.mem_range.mpr (by omega),
            rfl⟩
        have hwit : ∃ kL, p.1 ≤ kL ∧ kL < p.1 + (p.2 + 1 - p.1) ∧
            kL < (refine ctx level lab ptn active numcells).lab.size ∧
            (refine ctx level lab ptn active numcells).lab[kL]! = (refine ctx level lab ptn active numcells).lab[p.1 + o]! :=
          ⟨p.1 + o, by omega, by omega,
            by
              have h1 := hstR.labSize
              have h2 := hstR.ptnSize
              omega,
            rfl⟩
        have hseg := breakout_go_seg (tv := (refine ctx level lab ptn active numcells).lab[p.1 + o]!)
          ((refine ctx level lab ptn active numcells).lab.size + 1) (p.2 + 1 - p.1)
          (refine ctx level lab ptn active numcells).lab p.1 (refine ctx level lab ptn active numcells).lab[p.1 + o]! hwit
          (by
            have h1 := hstR.labSize
            have h2 := hstR.ptnSize
            omega)
          (by
            have h1 := hstR.labSize
            have h2 := hstR.ptnSize
            omega)
        have hs2 : cellsPerm (refine ctx level lab ptn active numcells).ptn level (refine ctx level lab ptn active numcells).lab
            (breakout (refine ctx level lab ptn active numcells).lab
        (refine ctx level lab ptn active numcells).ptn (level + 1) p.1
        (refine ctx level lab ptn active numcells).lab[p.1 + o]!).1 := by
          refine cellsPerm_of_confined (A := p.1)
            (lenA := p.2 + 1 - p.1) hicp (Nat.le_refl p.1)
            (Nat.le_refl _) ?_ ?_
          · have hsg : segN (breakout (refine ctx level lab ptn active numcells).lab
        (refine ctx level lab ptn active numcells).ptn (level + 1) p.1
        (refine ctx level lab ptn active numcells).lab[p.1 + o]!).1 p.1 (p.2 + 1 - p.1) =
                (refine ctx level lab ptn active numcells).lab[p.1 + o]! ::
                (segN (refine ctx level lab ptn active numcells).lab p.1 (p.2 + 1 - p.1)).erase
                  (refine ctx level lab ptn active numcells).lab[p.1 + o]! := by
              rw [breakout]
              exact hseg
            rw [hsg]
            exact List.perm_cons_erase htv
          · intro q hq
            rw [breakout]
            rcases hq with hq | hq
            · exact breakout_go_outside _ _ _ _ _ hq
            · exact breakout_go_outside_right _ (p.2 + 1 - p.1) _
                _ _ hwit _ hq
        have hs2' : cellsPerm ptn level (refine ctx level lab ptn active numcells).lab (breakout (refine ctx level lab ptn active numcells).lab
        (refine ctx level lab ptn active numcells).ptn (level + 1) p.1
        (refine ctx level lab ptn active numcells).lab[p.1 + o]!).1 := by
          refine cellsPerm_coarsen (ptnF := (refine ctx level lab ptn active numcells).ptn)
            (by rw [hok.ptnSize, hstR.ptnSize])
            (by rw [hstR.labSize, hstR.ptnSize])
            ?_ hs2 hstR.ptnEnd hok.ptnEnd hRinv.grow
          have hbo := breakout_ok (lab := (refine ctx level lab ptn active numcells).lab)
            (ptn := (refine ctx level lab ptn active numcells).ptn) (level := level + 1) (tc := p.1)
            (tv := (refine ctx level lab ptn active numcells).lab[p.1 + o]!) hstR.labOk (by omega)
            (hstR.labOk _ (by
              have h1 := hstR.labSize
              have h2 := hstR.ptnSize
              omega))
          rw [hbo.1, hstR.labSize, hstR.ptnSize]
        have hs3 : cellsPerm ptn level (breakout (refine ctx level lab ptn active numcells).lab
        (refine ctx level lab ptn active numcells).ptn (level + 1) p.1
        (refine ctx level lab ptn active numcells).lab[p.1 + o]!).1 llab := by
          refine cellsPerm_coarsen (ptnF := (breakout (refine ctx level lab ptn active numcells).lab
        (refine ctx level lab ptn active numcells).ptn (level + 1) p.1
        (refine ctx level lab ptn active numcells).lab[p.1 + o]!).2.1)
            (levF := level + 1) ?_ ?_ ?_ hlperm hchildOk.ptnEnd
            hok.ptnEnd ?_
          · show ptn.size =
              ((refine ctx level lab ptn active numcells).ptn.set! p.1 (level + 1)).size
            have h1 := hchildOk.ptnSize
            have h2 := hok.ptnSize
            omega
          · show (breakout (refine ctx level lab ptn active numcells).lab
        (refine ctx level lab ptn active numcells).ptn (level + 1) p.1
        (refine ctx level lab ptn active numcells).lab[p.1 + o]!).1.size =
              ((refine ctx level lab ptn active numcells).ptn.set! p.1 (level + 1)).size
            have h1 := hchildOk.labSize
            have h2 := hchildOk.ptnSize
            omega
          · show llab.size =
              ((refine ctx level lab ptn active numcells).ptn.set! p.1 (level + 1)).size
            have h1 := hchildOk.ptnSize
            omega
          · intro q hq
            show ((refine ctx level lab ptn active numcells).ptn.set! p.1 (level + 1))[q]! ≤ level + 1
            rcases getElem!_set!_cases (refine ctx level lab ptn active numcells).ptn p.1 (level + 1) q
              with he | he
            · rw [he]
              exact Nat.le_trans (hRinv.grow q hq) (by omega)
            · rw [he]
              exact Nat.le_refl _
        exact cellsPerm_trans hRinv.perm (cellsPerm_trans hs2' hs3)
      · rw [hspec]
        show (keysMax (childKey ctx tcLevel fuel level
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells 0)
          ((List.range m).map ((fun o => childKey ctx tcLevel fuel level
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells o) ∘ Nat.succ))).rows =
          leafRows ctx llab
        rw [hkm]
        exact hlrows
    · -- discrete: this node is the leaf
      refine ⟨(refine ctx level lab ptn active numcells).lab, hstR.labSize, hRinv.perm, ?_⟩
      rw [specNode, ite_eq_left hdisc]
/-! # Positions, classes, and colours of the achieved leaf -/

theorem segN_eq_toList {arr : Array Nat} {m : Nat}
    (hsz : arr.size = m) : segN arr 0 m = arr.toList := by
  refine List.ext_getElem (by rw [segN_length, Array.length_toList,
    hsz]) fun i h1 h2 => ?_
  rw [segN_length] at h1
  have h3 := segN_getElem! arr 0 m i h1
  rw [getElem!_pos _ _ (by rw [segN_length]; exact h1)] at h3
  rw [h3]
  show arr[0 + i]! = arr.toList[i]
  rw [Array.getElem_toList, getElem!_pos _ _ (by omega)]
  congr 1
  omega

theorem endsOf_append :
    ∀ (l1 l2 : List (List Nat)) (s : Nat),
      endsOf (l1 ++ l2) s = endsOf l1 s ++ endsOf l2 (s + totalOf l1)
  | [], l2, s => by
    rw [List.nil_append, endsOf]
    simp [totalOf_nil]
  | cl :: l1, l2, s => by
    rw [List.cons_append, endsOf, endsOf, totalOf_cons]
    rcases hcl : cl.isEmpty with _ | _
    · simp only [Bool.false_eq_true, ite_false]
      rw [show s + (cl.length + totalOf l1) = s + cl.length +
        totalOf l1 from by omega,
        endsOf_append l1 l2 (s + cl.length), List.cons_append]
    · have hnil : cl = [] := by
        rcases cl with _ | _
        · rfl
        · simp at hcl
      subst hnil
      simp only [ite_true]
      rw [endsOf_append l1 l2 s]
      congr 2
      simp

theorem pos_in_class :
    ∀ (cls : List (List Nat)) (i : Nat), i < totalOf cls →
      ∃ pre cl suf, cls = pre ++ cl :: suf ∧ totalOf pre ≤ i ∧
        i < totalOf pre + cl.length
  | [], i, hi => by
    rw [totalOf_nil] at hi
    omega
  | cl :: rest, i, hi => by
    rw [totalOf_cons] at hi
    rcases Nat.lt_or_ge i cl.length with h | h
    · exact ⟨[], cl, rest, rfl, by
        rw [totalOf_nil]
        omega, by
        rw [totalOf_nil]
        omega⟩
    · obtain ⟨pre, cl', suf, hsplit, h1, h2⟩ :=
        pos_in_class rest (i - cl.length) (by omega)
      refine ⟨cl :: pre, cl', suf, by rw [hsplit]; rfl, ?_, ?_⟩
      · rw [totalOf_cons]
        omega
      · rw [totalOf_cons]
        omega

theorem getElem!_append_block {l1 mid l2 : List Nat} {off : Nat}
    (hoff : off < mid.length) :
    (l1 ++ (mid ++ l2))[l1.length + off]! = mid[off]! := by
  rw [getElem!_pos _ _ (by
    rw [List.length_append, List.length_append]
    omega)]
  rw [List.getElem_append_right (by omega)]
  rw [getElem_congr_idx (by omega : l1.length + off - l1.length =
    off)]
  rw [List.getElem_append_left hoff]
  exact (getElem!_pos mid off hoff).symm

/-- Within its block, the sorted colour sequence is constant. -/
theorem sortedColorSeq_at (G : Colored n k) {c : Nat} (hc : c < k)
    {off : Nat} (hoff : off < (colorClass G c).length) :
    (sortedColorSeq G)[totalOf (((List.range k).map
      (colorClass G)).take c) + off]! = c := by
  have hck : c < (List.range k).length := by
    rw [List.length_range]
    exact hc
  have hsplit : List.range k = (List.range k).take c ++
      c :: (List.range k).drop (c + 1) := by
    have hd := List.drop_eq_getElem_cons hck
    rw [List.getElem_range] at hd
    rw [← hd]
    exact (List.take_append_drop c _).symm
  have hlen : (((List.range k).take c).flatMap fun c' =>
      List.replicate (colorClass G c').length c').length =
      totalOf (((List.range k).map (colorClass G)).take c) := by
    rw [List.length_flatMap, totalOf, ← List.map_take,
      List.map_map]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    show (List.replicate (colorClass G x).length x).length =
      (List.length ∘ colorClass G) x
    rw [List.length_replicate]
    rfl
  have hmain : (((List.range k).take c ++
      c :: (List.range k).drop (c + 1)).flatMap fun c' =>
      List.replicate (colorClass G c').length
        c')[totalOf (((List.range k).map (colorClass G)).take c) +
        off]! = c := by
    rw [List.flatMap_append, List.flatMap_cons, ← hlen,
      getElem!_append_block (by
        rw [List.length_replicate]
        exact hoff)]
    rw [getElem!_pos _ _ (by
      rw [List.length_replicate]
      exact hoff)]
    exact List.getElem_replicate ..
  rw [sortedColorSeq]
  rw [show ((List.range k).flatMap fun c' =>
    List.replicate (colorClass G c').length c') =
    (((List.range k).take c ++
      c :: (List.range k).drop (c + 1)).flatMap fun c' =>
      List.replicate (colorClass G c').length c') from by
    rw [← hsplit]]
  exact hmain

theorem totalOf_append :
    ∀ (l1 l2 : List (List Nat)),
      totalOf (l1 ++ l2) = totalOf l1 + totalOf l2
  | [], l2 => by
    rw [List.nil_append, totalOf_nil]
    omega
  | cl :: l1, l2 => by
    rw [List.cons_append, totalOf_cons, totalOf_cons,
      totalOf_append l1 l2]
    omega

/-- Each nonempty class occupies one cell of the initial partition. -/
theorem interval_isCell (G : Colored n k) {pre suf : List (List Nat)}
    {cl : List Nat}
    (hsplit : (List.range k).map (colorClass G) = pre ++ cl :: suf)
    (hne : 0 < cl.length) :
    IsCell (initPtn n (n + 2) (initialPartition G).2) 1
      (totalOf pre) cl.length := by
  have htot := totalOf_classes G
  rw [hsplit, totalOf_append, totalOf_cons] at htot
  have hEnds : (initialPartition G).2 =
      endsOf pre 0 ++ ((totalOf pre + cl.length - 1) ::
        endsOf suf (totalOf pre + cl.length)) := by
    rw [initialPartition_snd_eq, hsplit, endsOf_append, endsOf]
    have hcl : cl.isEmpty = false := by
      rcases cl with _ | _
      · simp at hne
      · simp
    rw [hcl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show (0 : Nat) + totalOf pre = totalOf pre from by omega]
  refine ⟨hne, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (totalOf pre) with h0 | hpos
    · exact Or.inl h0
    · right
      have hmem : totalOf pre - 1 ∈ (initialPartition G).2 := by
        rw [hEnds]
        refine List.mem_append.mpr (Or.inl ?_)
        have := endsOf_last_mem pre 0 hpos
        simpa using this
      rw [getElem!_initPtn, ite_eq_left ⟨hmem, by omega⟩]
      omega
  · intro q hq1 hq2
    have hqn : q < n := by omega
    have hnotmem : q ∉ (initialPartition G).2 := by
      rw [hEnds]
      intro hmem
      rcases List.mem_append.mp hmem with hm | hm
      · have := endsOf_lt pre 0 q hm
        omega
      · rcases List.mem_cons.mp hm with he | hm
        · omega
        · have := endsOf_ge suf _ q hm
          omega
    rw [getElem!_initPtn, ite_eq_right (fun hc => hnotmem hc.1),
      ite_eq_left hqn]
    omega
  · have hmem : totalOf pre + cl.length - 1 ∈
        (initialPartition G).2 := by
      rw [hEnds]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr
        (Or.inl rfl)))
    rw [getElem!_initPtn, ite_eq_left ⟨hmem, by omega⟩]
    omega

/-- Positions of any labelling that fills the initial cells with the
initial contents carry the sorted colours. -/
theorem achieved_position_colors {G : Colored n k}
    {llab : Array Nat}
    (hcp : cellsPerm (initPtn n (n + 2) (initialPartition G).2) 1
      (initialPartition G).1 llab) :
    ∀ (i : Nat), i < n → ∃ hv : llab[i]! < n,
      (G.coloring.cells[(⟨llab[i]!, hv⟩ : Fin n)]).val =
        (sortedColorSeq G)[i]! := by
  intro i hi
  have htot := totalOf_classes G
  obtain ⟨pre, cl, suf, hsplit, hlo, hhi⟩ := pos_in_class
    ((List.range k).map (colorClass G)) i (by omega)
  have hlenG : ((List.range k).map (colorClass G)).length = k := by
    simp
  have hj : pre.length < k := by
    have := congrArg List.length hsplit
    rw [hlenG, List.length_append, List.length_cons] at this
    omega
  have hclG : cl = colorClass G pre.length := by
    have h1 : ((List.range k).map (colorClass G))[pre.length]! =
        cl := by
      rw [hsplit]
      exact getElem!_append_middle pre cl suf
    have h2 : ((List.range k).map (colorClass G))[pre.length]! =
        colorClass G pre.length := by
      rw [getElem!_pos _ _ (by rw [hlenG]; exact hj),
        List.getElem_map, List.getElem_range]
    exact h1.symm.trans h2
  have htake : ((List.range k).map (colorClass G)).take pre.length =
      pre := by
    rw [hsplit]
    exact List.take_left
  have hcell := interval_isCell G hsplit (by omega)
  have hseg := hcp _ _ hcell
  have hseg0 : segN (initialPartition G).1 (totalOf pre) cl.length =
      cl := by
    rw [initialPartition_fst, hsplit]
    exact segN_flatten pre cl suf
  have hmem : llab[i]! ∈ segN llab (totalOf pre) cl.length := by
    rw [segN]
    refine List.mem_map.mpr ⟨i - totalOf pre,
      List.mem_range.mpr (by omega), ?_⟩
    congr 1
    omega
  have hmem2 : llab[i]! ∈ colorClass G pre.length := by
    rw [← hclG, ← hseg0]
    exact hseg.mem_iff.mpr hmem
  obtain ⟨hv, hc, he⟩ := mem_colorClass.mp hmem2
  refine ⟨hv, ?_⟩
  rw [he]
  show pre.length = (sortedColorSeq G)[i]!
  have hat := sortedColorSeq_at G hc
    (off := i - totalOf pre) (by rw [← hclG]; omega)
  rw [htake] at hat
  rw [show totalOf pre + (i - totalOf pre) = i from by omega] at hat
  exact hat.symm

/-! # The achieved labelling is a genuine relabelling -/

theorem achieved_perm_range {G : Colored n k} {llab : Array Nat}
    (hsz : llab.size = n) (hn0 : 0 < n)
    (hcp : cellsPerm (initPtn n (n + 2) (initialPartition G).2) 1
      (initialPartition G).1 llab) :
    llab.toList.Perm (List.range n) := by
  have hok := initial_nodeOk G hn0
  have hend1 : (initPtn n (n + 2)
      (initialPartition G).2)[(initPtn n (n + 2)
      (initialPartition G).2).size - 1]! ≤ 1 := hok.ptnEnd
  have hwhole := segN_perm_tiled (ptnF := initPtn n (n + 2)
    (initialPartition G).2) (levF := 1) hcp hend1 n 0 (by omega)
    (by rw [size_initPtn]; omega) (Or.inl rfl)
    (by
      have h1 := hend1
      rw [size_initPtn] at h1
      rw [show (0 : Nat) + n - 1 = n - 1 from by omega]
      exact h1)
  rw [segN_eq_toList (size_initialPartition G),
    segN_eq_toList hsz] at hwhole
  refine hwhole.symm.trans ?_
  rw [initialPartition_fst]
  have hrt : ((((List.range k).map (colorClass G)).flatMap
      id).toArray).toList =
      ((List.range k).map (colorClass G)).flatMap id := by
    simp
  rw [hrt]
  exact flatten_classes_perm G

theorem label_of_perm_range {llab : Array Nat} (hsz : llab.size = n)
    (hperm : llab.toList.Perm (List.range n)) :
    ∃ l : Label n, ∀ (i : Nat) (hi : i < n),
      (l.get ⟨i, hi⟩).val = llab[i]! := by
  have hbound : ∀ (i : Nat), i < n → llab[i]! < n := by
    intro i hi
    have hm : llab[i]! ∈ llab.toList := by
      rw [getElem!_pos _ _ (by omega)]
      rw [← Array.getElem_toList (by
        rw [Array.length_toList]
        omega)]
      exact List.getElem_mem _
    exact List.mem_range.mp (hperm.mem_iff.mp hm)
  have hlist : (Hex.Vector.ofFn' fun i : Fin n =>
      (⟨llab[i.val]!, hbound i.val i.isLt⟩ : Fin n)).toList =
      List.ofFn fun i : Fin n =>
        (⟨llab[i.val]!, hbound i.val i.isLt⟩ : Fin n) := by
    show ((List.ofFn _).toArray).toList = _
    simp
  have hmapval : (List.ofFn fun i : Fin n =>
      (⟨llab[i.val]!, hbound i.val i.isLt⟩ : Fin n)).map Fin.val =
      llab.toList := by
    refine List.ext_getElem (by simp [hsz]) fun i h1 h2 => ?_
    rw [List.getElem_map, List.getElem_ofFn]
    show llab[i]! = llab.toList[i]
    rw [Array.getElem_toList, getElem!_pos _ _ (by
      rw [Array.length_toList] at h2
      omega)]
  have hnodup : (List.ofFn fun i : Fin n =>
      (⟨llab[i.val]!, hbound i.val i.isLt⟩ : Fin n)).Nodup := by
    have hmv : ((List.ofFn fun i : Fin n =>
        (⟨llab[i.val]!, hbound i.val i.isLt⟩ : Fin n)).map
        Fin.val).Nodup := by
      rw [hmapval]
      exact hperm.symm.nodup List.nodup_range
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hmv
    rw [List.nodup_iff_pairwise_ne]
    exact hmv.imp fun h he => h (congrArg Fin.val he)
  have hcomplete : ∀ i : Fin n, i ∈ (List.ofFn fun i : Fin n =>
      (⟨llab[i.val]!, hbound i.val i.isLt⟩ : Fin n)) := by
    intro i
    have hm : i.val ∈ llab.toList :=
      hperm.mem_iff.mpr (List.mem_range.mpr i.isLt)
    rw [← hmapval] at hm
    rcases List.mem_map.mp hm with ⟨x, hx, hxe⟩
    exact (Fin.eq_of_val_eq hxe : x = i) ▸ hx
  refine ⟨⟨⟨Hex.Vector.ofFn' fun i : Fin n =>
    (⟨llab[i.val]!, hbound i.val i.isLt⟩ : Fin n), by
      rw [hlist]
      exact hnodup, by
      intro i
      rw [hlist]
      exact hcomplete i⟩⟩, ?_⟩
  intro i hi
  show ((Hex.Vector.ofFn' fun i : Fin n =>
    (⟨llab[i.val]!, hbound i.val i.isLt⟩ : Fin n))[(⟨i, hi⟩ :
      Fin n)]).val = llab[i]!
  simp only [Fin.getElem_fin, Hex.Vector.getElem_ofFn']

/-- A form with a key's rows and the sorted colours is the form of
that key. -/
theorem form_eq_formOfKey {G F : Colored n k} {rows : List Nat}
    (hrows : rowsOf F = rows.toArray)
    (hcols : ∀ (i : Nat) (hi : i < n),
      (F.coloring.cells[i]'(by omega)).val =
        (sortedColorSeq G)[i]!) :
    F = formOfKey G rows := by
  refine Colored.ext ?_ ?_
  · intro i j
    have hadjL : F.graph.adj i j =
        (rows[i.val]!).testBit j.val := by
      have h1 : F.graph.adj i j =
          ((rowsOf F)[i.val]!).testBit j.val := by
        rw [getElem!_rowsOf _ i.isLt, testBit_rowOf_lt _ i.isLt
          j.isLt]
      rw [h1, hrows, List.getElem!_toArray]
    have hadjLs : F.graph.adj j i =
        (rows[j.val]!).testBit i.val := by
      have h1 : F.graph.adj j i =
          ((rowsOf F)[j.val]!).testBit i.val := by
        rw [getElem!_rowsOf _ j.isLt, testBit_rowOf_lt _ j.isLt
          i.isLt]
      rw [h1, hrows, List.getElem!_toArray]
    have hsym : (rows[j.val]!).testBit i.val =
        (rows[i.val]!).testBit j.val := by
      rw [← hadjL, ← hadjLs]
      exact (Hex.Graph.adj_symm _ i j).symm
    have hR : (formOfKey G rows).graph.adj i j =
        ((rows[i.val]!).testBit j.val &&
          (rows[j.val]!).testBit i.val && i.val != j.val) := by
      simp only [formOfKey, Hex.Graph.adj_ofAdj]
    rw [hadjL, hR, hsym]
    rcases Decidable.em (i.val = j.val) with he | he
    · have hii : i = j := Fin.eq_of_val_eq he
      subst hii
      have hL : F.graph.adj i i = false := Hex.Graph.adj_self _ i
      rw [← hadjL, hL]
      simp
    · have hne : (i.val != j.val) = true := by simpa using he
      rw [hne]
      rcases hb : (rows[i.val]!).testBit j.val with _ | _ <;> simp
  · intro i
    refine Fin.eq_of_val_eq ?_
    have h1 := hcols i.val i.isLt
    have h2 : ((formOfKey G rows).coloring.cells[i]).val =
        (sortedColorSeq G)[i.val]! := by
      simp only [formOfKey, Fin.getElem_fin,
        Hex.Vector.getElem_ofFn']
    rw [h2]
    exact h1

/-- The total nauty-semantic canonical form is isomorphic to its
input. -/
theorem specCanon_iso (G : Colored n k) :
    Isomorphic G (specCanon G) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact Isomorphic.intro (Perm.id 0)
      (IsIso.intro (fun i => i.elim0) (fun i => i.elim0))
  · have hok := initial_nodeOk G hn0
    have hbc : 1 ≤ bcount (initPtn n (n + 2)
        (initialPartition G).2) 1 n := by
      refine bcount_pos_of_boundary (q := n - 1) (by omega) ?_
      have h1 := hok.ptnEnd
      rw [size_initPtn] at h1
      exact h1
    obtain ⟨llab, hlsz, hlcp, hlrows⟩ := specNode_achieved
      (ctx := { n := n, g := rowsOf G }) rfl 100 n 1
      (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2)
      (initActive (initialPartition G).2)
      (initialPartition G).2.length hok
      (by show n + 1 ≤ 1 + n; omega) hbc
    have hkrows : (canonSpecKey G).rows =
        leafRows { n := n, g := rowsOf G } llab := by
      rw [canonSpecKey, canonSpec, ite_eq_right (by simp; omega)]
      exact hlrows
    obtain ⟨l, hag⟩ := label_of_perm_range hlsz
      (achieved_perm_range hlsz hn0 hlcp)
    have hcols := achieved_position_colors hlcp
    have hform : G.relabel l =
        formOfKey G (canonSpecKey G).rows := by
      refine form_eq_formOfKey ?_ ?_
      · rw [rowsOf_relabel_eq_leafRows hlsz hag, hkrows]
      · intro i hi
        obtain ⟨hv, hc⟩ := hcols i hi
        rw [Colored.cells_relabel G l i hi]
        have hfg : l.get ⟨i, hi⟩ = ⟨llab[i]!, hv⟩ :=
          Fin.eq_of_val_eq (hag i hi)
        have hcg := congrArg (fun x : Fin n =>
          (G.coloring.cells[x]).val) hfg
        exact hcg.trans hc
    rw [specCanon, ← hform]
    exact isomorphic_relabel G l

/-- Isomorphism is equivalent to equality of the nauty-semantic
canonical forms. -/
theorem iso_iff_specCanon_eq {G H : Colored n k} :
    Isomorphic G H ↔ specCanon G = specCanon H := by
  constructor
  · exact specCanon_invariant
  · intro he
    exact (specCanon_iso G).trans (he ▸ (specCanon_iso H).symm)

end Hex.GraphIso.Nauty
