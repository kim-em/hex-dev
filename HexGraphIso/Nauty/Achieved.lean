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
    · rw [if_pos h]
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · omega
      · exact cellEnd_go_le hj fuel (i + 1) (by omega) (by omega)
    · rw [if_neg h]
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
    (hszp : ptn0.size = ptnP.size)
    (hcellP : IsCell ptnP level A lenA)
    (hend0 : ptn0[ptn0.size - 1]! ≤ level)
    (hb : ∀ q : Nat, ptn0[q]! ≤ level → ptnP[q]! ≤ level)
    (hA0 : A < ptn0.size) (hA : A + lenA ≤ ptn0.size) :
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
    (workset cell1 cell2 : Nat) (hsz : cell2 < lab.size)
    (h12 : cell1 ≤ cell2) :
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

end Hex.GraphIso.Nauty
