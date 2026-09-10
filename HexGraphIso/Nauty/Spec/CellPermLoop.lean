/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Spec.CellPerm

public section

/-!
Refinement as a function of cell contents, part two: the
nontrivial-splitter window scan, the pass and loop assembly, and
level transfer. Builds on the cell primitives and the trivial
splitter of `Nauty.Spec.CellPerm`.
-/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-! # Window-scan structure -/

/-- The window-scan bookkeeping never reads the labelling. -/
theorem windowStep_setLab (level cell1 cell2 v c1 c2 : Nat)
    (maxcell : Int) (st : RefineSt n) (X : Array Nat) :
    windowStep level cell1 cell2 v c1 c2 maxcell { st with lab := X } =
      { windowStep level cell1 cell2 v c1 c2 maxcell st with
        lab := X } := by
  rw [windowStep, windowStep]
  dsimp only
  rcases Decidable.em (Int.ofNat (c2 - c1) > maxcell) with h1 | h1 <;>
  rcases hB : (c1 != cell1) with _ | _ <;>
  rcases hC : (c2 - c1 == 1) with _ | _ <;>
  rcases Decidable.em (c2 ≤ cell2) with h4 | h4 <;>
    simp only [h1, h4, Bool.false_eq_true, ite_false, ite_true]

theorem windowScan_setLab (level cell1 cell2 : Nat) (counts : List Nat) :
    ∀ (values : List Nat) (c1 : Nat) (maxcell : Int) (st : RefineSt n)
      (X : Array Nat),
      windowScan level cell1 cell2 counts values c1 maxcell
          { st with lab := X } =
        { windowScan level cell1 cell2 counts values c1 maxcell st with
          lab := X }
  | [], _, _, _, _ => rfl
  | v :: vs, c1, maxcell, st, X => by
    rw [windowScan, windowScan]
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · simp only [ite_eq_left hm]
      rw [windowStep_setLab]
      exact windowScan_setLab level cell1 cell2 counts vs _ _ _ X
    · simp only [ite_eq_right hm]
      exact windowScan_setLab level cell1 cell2 counts vs c1 maxcell st X

/-- The window scan reads the counts only through the multiplicities. -/
theorem windowScan_counts_congr (level cell1 cell2 : Nat)
    {counts counts' : List Nat}
    (hm : ∀ v, multOf counts v = multOf counts' v) :
    ∀ (values : List Nat) (c1 : Nat) (maxcell : Int) (st : RefineSt n),
      windowScan level cell1 cell2 counts values c1 maxcell st =
        windowScan level cell1 cell2 counts' values c1 maxcell st
  | [], _, _, _ => rfl
  | v :: vs, c1, maxcell, st => by
    rw [windowScan, windowScan, hm v]
    rcases Decidable.em (multOf counts' v > 0) with hmv | hmv
    · simp only [ite_eq_left hmv]
      rw [windowScan_counts_congr level cell1 cell2 hm vs _ _ _]
    · simp only [ite_eq_right hmv]
      exact windowScan_counts_congr level cell1 cell2 hm vs c1 maxcell st

/-- One window step's partition effect: the group end boundary, if it
lies inside the cell. -/
theorem ptn_windowStep_eq (level cell1 cell2 v c1 c2 : Nat)
    (maxcell : Int) (st : RefineSt n) :
    (windowStep level cell1 cell2 v c1 c2 maxcell st).ptn =
      if c2 ≤ cell2 then st.ptn.set! (c2 - 1) level else st.ptn := by
  rw [windowStep]
  dsimp only
  rcases Decidable.em (Int.ofNat (c2 - c1) > maxcell) with h1 | h1 <;>
  rcases hB : (c1 != cell1) with _ | _ <;>
  rcases hC : (c2 - c1 == 1) with _ | _ <;>
  rcases Decidable.em (c2 ≤ cell2) with h4 | h4 <;>
    simp only [h1, h4, Bool.false_eq_true, ite_false, ite_true]

/-! # Segment write-back -/

/-- Writing a segment and reading it back. -/
theorem segN_writeSegment :
    ∀ (seg : List Nat) (lab : Array Nat) (lo : Nat),
      lo + seg.length ≤ lab.size →
      segN (writeSegment lab lo seg) lo seg.length = seg
  | [], _, _, _ => rfl
  | x :: seg, lab, lo, hsz => by
    simp only [List.length_cons] at hsz ⊢
    rw [segN_cons, writeSegment]
    refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
    · rw [writeSegment_outside seg _ (lo + 1) lo (by omega),
        Array.getElem!_set!_self _ _ _ (by omega)]
    · exact segN_writeSegment seg (lab.set! lo x) (lo + 1)
        (by rw [Array.size_set!]; omega)

/-! # Group decomposition -/

theorem isCell_split_right {ptn : Array Nat} {level A lenA c : Nat}
    (h : IsCell ptn level A lenA) (hc1 : A ≤ c) (hc2 : c + 1 < A + lenA)
    (hcs : c < ptn.size) :
    IsCell (ptn.set! c level) level (c + 1) (A + lenA - (c + 1)) := by
  obtain ⟨hl, hs, hi, he⟩ := h
  refine ⟨by omega, Or.inr ?_, ?_, ?_⟩
  · rw [show c + 1 - 1 = c by omega, Array.getElem!_set!_self _ _ _ hcs]
    exact Nat.le_refl level
  · intro i hi1 hi2
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact hi i (by omega) (by omega)
  · rw [show c + 1 + (A + lenA - (c + 1)) - 1 = A + lenA - 1 by omega,
      Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact he

theorem flatMap_congr_mem {g g' : Nat → List Nat} :
    ∀ (l : List Nat), (∀ a ∈ l, g a = g' a) →
      l.flatMap g = l.flatMap g'
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (by simp),
      flatMap_congr_mem l (fun a ha => h a (by simp [ha]))]

theorem flatMap_perm_of_pointwise {g g' : Nat → List Nat} :
    ∀ (vs : List Nat), (∀ v ∈ vs, (g v).Perm (g' v)) →
      (vs.flatMap g).Perm (vs.flatMap g')
  | [], _ => List.Perm.refl _
  | v :: vs, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (h v (by simp)).append
      (flatMap_perm_of_pointwise vs fun u hu => h u (by simp [hu]))

theorem zipIdx_filter_map_eq_filter (f : Nat → Nat) (v : Nat) :
    ∀ (S : List Nat) (k : Nat) (get : Nat → Nat),
      (∀ j, j < S.length → get (k + j) = S[j]!) →
      ((((S.map f).zipIdx k).filter fun p => p.1 == v).map
        fun p => get p.2) = S.filter fun x => f x == v
  | [], _, _, _ => rfl
  | x :: S, k, get, hget => by
    rw [List.map_cons, List.zipIdx_cons, List.filter_cons, List.filter_cons]
    have hx : get k = x := by
      have := hget 0 (by simp)
      simpa using this
    rcases hfx : (f x == v) with _ | _
    · simp only [Bool.false_eq_true, ite_false]
      exact zipIdx_filter_map_eq_filter f v S (k + 1) get
        (fun j hj => by
          rw [show k + 1 + j = k + (j + 1) by omega]
          have := hget (j + 1) (by simp; omega)
          simpa using this)
    · simp only [ite_true, List.map_cons]
      refine List.cons_eq_cons.mpr ⟨hx, ?_⟩
      exact zipIdx_filter_map_eq_filter f v S (k + 1) get
        (fun j hj => by
          rw [show k + 1 + j = k + (j + 1) by omega]
          have := hget (j + 1) (by simp; omega)
          simpa using this)

/-- The stable counting redistribution groups the segment by count
value: with counts read off the segment, `segmentOf` is the
concatenation of the value filters. -/
theorem segmentOf_eq_flatMap (lab : Array Nat) (cell1 : Nat)
    (S : List Nat) (f : Nat → Nat) (values : List Nat)
    (hS : ∀ j, j < S.length → lab[cell1 + j]! = S[j]!) :
    segmentOf lab cell1 (S.map f) values =
      values.flatMap fun v => S.filter fun x => f x == v := by
  rw [segmentOf]
  refine congrArg values.flatMap ?_
  funext v
  exact zipIdx_filter_map_eq_filter f v S 0 (fun j => lab[cell1 + j]!)
    (fun j hj => by rw [Nat.zero_add]; exact hS j hj)

theorem segN_getElem! (lab : Array Nat) (lo len j : Nat) (hj : j < len) :
    (segN lab lo len)[j]! = lab[lo + j]! := by
  rw [segN, getElem!_pos _ _ (by rw [List.length_map, List.length_range]; exact hj),
    List.getElem_map, List.getElem_range]

theorem filter_filter_ne {f : Nat → Nat} {u v : Nat} (huv : u ≠ v)
    (S : List Nat) :
    (S.filter fun x => !(f x == v)).filter (fun x => f x == u) =
      S.filter fun x => f x == u := by
  induction S with
  | nil => rfl
  | cons x S ih =>
    rw [List.filter_cons]
    rcases hfv : (f x == v) with _ | _
    · simp only [Bool.not_false, ite_true]
      rw [List.filter_cons, List.filter_cons, ih]
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      rw [List.filter_cons, ih]
      have hfu : (f x == u) = false := by
        simp only [beq_iff_eq] at hfv
        simp only [beq_eq_false_iff_ne, ne_eq]
        omega
      rw [hfu]
      simp

/-- Concatenating the value-filters over distinct values that cover the
list recovers the list, as a multiset. -/
theorem flatMap_filters_perm {f : Nat → Nat} :
    ∀ (values S : List Nat), values.Nodup → (∀ x ∈ S, f x ∈ values) →
      ((values.flatMap fun v => S.filter fun x => f x == v).Perm S)
  | [], S, _, hcov => by
    rcases S with _ | ⟨x, S⟩
    · exact List.Perm.refl _
    · exact absurd (hcov x (by simp)) (by simp)
  | v :: values, S, hnd, hcov => by
    rw [List.flatMap_cons]
    have hrec := flatMap_filters_perm values
      (S.filter fun x => !(f x == v)) (List.nodup_cons.mp hnd).2
      (fun x hx => by
        have hm := List.mem_filter.mp hx
        have := hcov x hm.1
        simp only [List.mem_cons] at this
        rcases this with heq | hmem
        · exfalso
          have := hm.2
          simp [heq] at this
        · exact hmem)
    have hcong : (values.flatMap fun u =>
        (S.filter fun x => !(f x == v)).filter fun x => f x == u) =
        values.flatMap fun u => S.filter fun x => f x == u := by
      refine flatMap_congr_mem values fun u hu => ?_
      refine filter_filter_ne (fun heq => ?_) S
      subst heq
      exact (List.nodup_cons.mp hnd).1 hu
    rw [hcong] at hrec
    exact (List.Perm.append (List.Perm.refl _) hrec).trans
      (List.filter_append_perm _ S)

/-! # Window writes preserve cell equivalence -/

theorem ptn_windowScan_outside (level cell1 cell2 : Nat)
    (counts : List Nat) :
    ∀ (vs : List Nat) (c1acc : Nat) (maxcell : Int) (st : RefineSt n),
      cell1 ≤ c1acc → ∀ q, q < cell1 ∨ cell2 ≤ q →
      (windowScan level cell1 cell2 counts vs c1acc maxcell
        st).ptn[q]! = st.ptn[q]!
  | [], _, _, _, _, _, _ => rfl
  | v :: vs, c1acc, maxcell, st, hc1, q, hq => by
    rw [windowScan]
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · simp only [ite_eq_left hm]
      rw [ptn_windowScan_outside level cell1 cell2 counts vs _ _ _
        (by omega) q hq, ptn_windowStep_eq]
      split
      · next hle =>
        rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      · rfl
    · simp only [ite_eq_right hm]
      exact ptn_windowScan_outside level cell1 cell2 counts vs _ _ _
        hc1 q hq

theorem ptn_windowScan_size (level cell1 cell2 : Nat) (counts : List Nat) :
    ∀ (vs : List Nat) (c1acc : Nat) (maxcell : Int) (st : RefineSt n),
      (windowScan level cell1 cell2 counts vs c1acc maxcell
        st).ptn.size = st.ptn.size
  | [], _, _, _ => rfl
  | v :: vs, c1acc, maxcell, st => by
    rw [windowScan]
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · simp only [ite_eq_left hm]
      rw [ptn_windowScan_size level cell1 cell2 counts vs _ _ _,
        ptn_windowStep_eq]
      split
      · rw [Array.size_set!]
      · rfl
    · simp only [ite_eq_right hm]
      exact ptn_windowScan_size level cell1 cell2 counts vs _ _ _

/-- The window scan's boundary writes preserve cell-contents equivalence
of the final labellings: each nonempty group becomes a cell whose two
contents are permutations of matching value filters. -/
theorem windowScan_region_perm (level cell1 cell2 : Nat)
    (counts : List Nat) {L L' : Array Nat} (gL gL' : Nat → List Nat)
    (hGperm : ∀ v, (gL v).Perm (gL' v))
    (hGlen : ∀ v, (gL v).length = multOf counts v) :
    ∀ (vs : List Nat) (start : Nat) (maxcell : Int) (st : RefineSt n),
      (start ≤ cell2 → IsCell st.ptn level start (cell2 + 1 - start)) →
      cell2 < st.ptn.size →
      cellsPerm st.ptn level L L' →
      segN L start (cell2 + 1 - start) = vs.flatMap gL →
      segN L' start (cell2 + 1 - start) = vs.flatMap gL' →
      cellsPerm (windowScan level cell1 cell2 counts vs start
        maxcell st).ptn level L L'
  | [], _, _, _, _, _, hcp, _, _ => hcp
  | v :: vs, start, maxcell, st, hcellR, hc2s, hcp, hlayL, hlayL' => by
    rw [windowScan]
    have hGlen' : ∀ u, (gL' u).length = multOf counts u := fun u => by
      rw [← (hGperm u).length_eq]
      exact hGlen u
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · simp only [ite_eq_left hm]
      -- the group is nonempty, so the region reaches it
      have hlen0 := congrArg List.length hlayL
      rw [segN_length, List.flatMap_cons, List.length_append,
        hGlen v] at hlen0
      have hlen0' := congrArg List.length hlayL'
      rw [segN_length, List.flatMap_cons, List.length_append,
        hGlen' v] at hlen0'
      have hstart2 : start ≤ cell2 := by omega
      have hsplitL : segN L start (cell2 + 1 - start) =
          segN L start (multOf counts v) ++
            segN L (start + multOf counts v)
              (cell2 + 1 - start - multOf counts v) := by
        rw [← segN_append]
        congr 1
        omega
      have hsplitL' : segN L' start (cell2 + 1 - start) =
          segN L' start (multOf counts v) ++
            segN L' (start + multOf counts v)
              (cell2 + 1 - start - multOf counts v) := by
        rw [← segN_append]
        congr 1
        omega
      obtain ⟨hchunkL, hrestL⟩ := List.append_inj
        (hsplitL.symm.trans (by rw [hlayL, List.flatMap_cons]))
        (by rw [segN_length, hGlen v])
      obtain ⟨hchunkL', hrestL'⟩ := List.append_inj
        (hsplitL'.symm.trans (by rw [hlayL', List.flatMap_cons]))
        (by rw [segN_length, hGlen' v])
      have hptn1 := ptn_windowStep_eq level cell1 cell2 v start
        (start + multOf counts v) maxcell st
      rcases Decidable.em (start + multOf counts v ≤ cell2) with
        hin | houtc
      · rw [ite_eq_left hin] at hptn1
        have hcellS := hcellR hstart2
        have hcp1 : cellsPerm (st.ptn.set!
            (start + multOf counts v - 1) level) level L L' := by
          refine cellsPerm_set! hcellS (by omega) (by omega) (by omega)
            ?_ ?_ (fun x len hx _ => hcp x len hx)
          · rw [show start + multOf counts v - 1 + 1 - start =
              multOf counts v by omega, hchunkL, hchunkL']
            exact hGperm v
          · rw [show start + multOf counts v - 1 + 1 =
                start + multOf counts v by omega,
              show start + (cell2 + 1 - start) -
                (start + multOf counts v) =
                cell2 + 1 - start - multOf counts v by omega,
              hrestL, hrestL']
            exact flatMap_perm_of_pointwise vs fun u _ => hGperm u
        have hcell1 : start + multOf counts v ≤ cell2 →
            IsCell (windowStep level cell1 cell2 v start
              (start + multOf counts v) maxcell st).ptn level
              (start + multOf counts v)
              (cell2 + 1 - (start + multOf counts v)) := by
          intro _
          rw [hptn1]
          have hs := isCell_split_right
            (c := start + multOf counts v - 1) hcellS (by omega)
            (by omega) (by omega)
          rw [show start + multOf counts v - 1 + 1 =
            start + multOf counts v by omega,
            show start + (cell2 + 1 - start) -
              (start + multOf counts v) =
              cell2 + 1 - (start + multOf counts v) by omega] at hs
          exact hs
        refine windowScan_region_perm level cell1 cell2 counts gL gL'
          hGperm hGlen vs (start + multOf counts v) _ _ hcell1
          (by rw [hptn1, Array.size_set!]; exact hc2s)
          (by rw [hptn1]; exact hcp1)
          (by
            rw [show cell2 + 1 - (start + multOf counts v) =
              cell2 + 1 - start - multOf counts v by omega]
            exact hrestL)
          (by
            rw [show cell2 + 1 - (start + multOf counts v) =
              cell2 + 1 - start - multOf counts v by omega]
            exact hrestL')
      · rw [ite_eq_right houtc] at hptn1
        have hend : start + multOf counts v = cell2 + 1 := by omega
        refine windowScan_region_perm level cell1 cell2 counts gL gL'
          hGperm hGlen vs (start + multOf counts v) _ _
          (fun hcon => absurd hcon (by omega))
          (by rw [hptn1]; exact hc2s)
          (by rw [hptn1]; exact hcp)
          ?_ ?_
        · rw [show cell2 + 1 - (start + multOf counts v) = 0 by omega,
            segN_zero]
          have := hrestL
          rw [show cell2 + 1 - start - multOf counts v = 0 by omega,
            segN_zero] at this
          exact this
        · rw [show cell2 + 1 - (start + multOf counts v) = 0 by omega,
            segN_zero]
          have := hrestL'
          rw [show cell2 + 1 - start - multOf counts v = 0 by omega,
            segN_zero] at this
          exact this
    · simp only [ite_eq_right hm]
      have hgv : gL v = [] :=
        List.length_eq_zero_iff.mp (by rw [hGlen v]; omega)
      have hgv' : gL' v = [] :=
        List.length_eq_zero_iff.mp (by rw [hGlen' v]; omega)
      exact windowScan_region_perm level cell1 cell2 counts gL gL'
        hGperm hGlen vs start maxcell st hcellR hc2s hcp
        (by rw [hlayL, List.flatMap_cons, hgv, List.nil_append])
        (by rw [hlayL', List.flatMap_cons, hgv', List.nil_append])

/-! # The nontrivial-splitter cell -/

theorem nontrivialFix_setLab (cell1 : Nat) (st : RefineSt n)
    (X : Array Nat) :
    nontrivialFix cell1 { st with lab := X } =
      { nontrivialFix cell1 st with lab := X } := by
  rw [nontrivialFix, nontrivialFix]
  dsimp only
  rcases Decidable.em (¬ st.active.mem cell1 = true) with hcx | hcx
  · simp only [ite_eq_left hcx]
  · simp only [ite_eq_right hcx]

theorem ptn_nontrivialFix (cell1 : Nat) (st : RefineSt n) :
    (nontrivialFix cell1 st).ptn = st.ptn := by
  rw [nontrivialFix]
  split <;> rfl

/-- One nontrivial-splitter cell preserves cell-contents equivalence:
the positional results agree and the labellings stay cell-equivalent
for the result's partition, which changes only strictly inside the
processed cell. -/
theorem nontrivialCell_perm {ctx : Ctx n} {level cell1 cell2 : Nat} {workset : VSet n}
    {st st' : RefineSt n} (h : StPerm level st st')
    (hcell : IsCell st.ptn level cell1 (cell2 + 1 - cell1))
    (hc12 : cell1 ≤ cell2) (h2 : cell2 < st.lab.size)
    (hsz : st.ptn.size = st.lab.size) :
    StPerm level (nontrivialCell ctx level workset cell1 cell2 st)
      (nontrivialCell ctx level workset cell1 cell2 st') ∧
    (∀ q : Nat, q < cell1 ∨ cell2 ≤ q →
      (nontrivialCell ctx level workset cell1 cell2 st).ptn[q]! =
        st.ptn[q]!) ∧
    (nontrivialCell ctx level workset cell1 cell2 st).ptn.size =
      st.ptn.size ∧
    (nontrivialCell ctx level workset cell1 cell2 st).lab.size =
      st.lab.size := by
  rw [nontrivialCell, nontrivialCell]
  rcases hc : (cell1 == cell2) with _ | _
  case true =>
    rw [ite_eq_left rfl, ite_eq_left rfl]
    exact ⟨h, fun q _ => rfl, rfl, rfl⟩
  case false =>
  simp only [Bool.false_eq_true, ite_false]
  have hseg : (segN st.lab cell1 (cell2 + 1 - cell1)).Perm
      (segN st'.lab cell1 (cell2 + 1 - cell1)) :=
    h.cells cell1 _ hcell
  have hcm := countsOf_eq_map ctx st.lab workset cell1 cell2
  have hcm' := countsOf_eq_map ctx st'.lab workset cell1 cell2
  have hcp : (countsOf ctx st.lab workset cell1 cell2).Perm
      (countsOf ctx st'.lab workset cell1 cell2) := by
    rw [hcm, hcm']
    exact hseg.map _
  have hbmin : (countsOf ctx st'.lab workset cell1 cell2).foldl Nat.min
      ((countsOf ctx st'.lab workset cell1 cell2).headD 0) =
      (countsOf ctx st.lab workset cell1 cell2).foldl Nat.min
        ((countsOf ctx st.lab workset cell1 cell2).headD 0) :=
    (foldl_min_headD_perm hcp).symm
  have hbmax : (countsOf ctx st'.lab workset cell1 cell2).foldl Nat.max
      ((countsOf ctx st'.lab workset cell1 cell2).headD 0) =
      (countsOf ctx st.lab workset cell1 cell2).foldl Nat.max
        ((countsOf ctx st.lab workset cell1 cell2).headD 0) :=
    (foldl_max_headD_perm hcp).symm
  rw [hbmin, hbmax]
  rcases hbm : ((countsOf ctx st.lab workset cell1 cell2).foldl Nat.min
      ((countsOf ctx st.lab workset cell1 cell2).headD 0) ==
      (countsOf ctx st.lab workset cell1 cell2).foldl Nat.max
        ((countsOf ctx st.lab workset cell1 cell2).headD 0)) with _ | _
  case true =>
    rw [ite_eq_left rfl, ite_eq_left rfl]
    exact ⟨⟨h.ptn, h.active, h.numcells, h.hint, h.maxpos,
      by dsimp only; rw [h.longcode], h.labSize, h.cells⟩,
      fun q _ => rfl, rfl, rfl⟩
  case false =>
  simp only [Bool.false_eq_true, ite_false]
  have hvals : countValues (countsOf ctx st'.lab workset cell1 cell2) =
      countValues (countsOf ctx st.lab workset cell1 cell2) := by
    rw [countValues, countValues, hbmin, hbmax]
  rw [hvals]
  have hW' : windowScan level cell1 cell2
      (countsOf ctx st'.lab workset cell1 cell2)
      (countValues (countsOf ctx st.lab workset cell1 cell2))
      cell1 (-1) st' =
      { windowScan level cell1 cell2
          (countsOf ctx st.lab workset cell1 cell2)
          (countValues (countsOf ctx st.lab workset cell1 cell2))
          cell1 (-1) st with
        lab := st'.lab } := by
    rw [← windowScan_counts_congr level cell1 cell2
      (fun v => hcp.countP_eq _) _ _ _ st']
    conv =>
      lhs
      rw [h.eq_setLab]
    rw [windowScan_setLab]
  rw [hW']
  dsimp only
  rw [lab_windowScan level cell1 cell2
    (countsOf ctx st.lab workset cell1 cell2)]
  rw [nontrivialFix_setLab cell1
      (windowScan level cell1 cell2
        (countsOf ctx st.lab workset cell1 cell2)
        (countValues (countsOf ctx st.lab workset cell1 cell2))
        cell1 (-1) st)]
  rw [nontrivialFix_setLab cell1
      (windowScan level cell1 cell2
        (countsOf ctx st.lab workset cell1 cell2)
        (countValues (countsOf ctx st.lab workset cell1 cell2))
        cell1 (-1) st)
      (writeSegment st'.lab cell1
        (segmentOf st'.lab cell1
          (countsOf ctx st'.lab workset cell1 cell2)
          (countValues (countsOf ctx st.lab workset cell1 cell2))))]
  -- layout facts for both written labellings
  have hSEG : segmentOf st.lab cell1
      (countsOf ctx st.lab workset cell1 cell2)
      (countValues (countsOf ctx st.lab workset cell1 cell2)) =
      (countValues (countsOf ctx st.lab workset cell1 cell2)).flatMap
        fun v => (segN st.lab cell1 (cell2 + 1 - cell1)).filter
          fun x => (workset.cardInter ctx.g[x]!) == v := by
    rw [hcm]
    exact segmentOf_eq_flatMap st.lab cell1 _ _ _
      (fun j hj => by
        rw [segN_length] at hj
        exact (segN_getElem! st.lab cell1 _ j hj).symm)
  have hSEG' : segmentOf st'.lab cell1
      (countsOf ctx st'.lab workset cell1 cell2)
      (countValues (countsOf ctx st.lab workset cell1 cell2)) =
      (countValues (countsOf ctx st.lab workset cell1 cell2)).flatMap
        fun v => (segN st'.lab cell1 (cell2 + 1 - cell1)).filter
          fun x => (workset.cardInter ctx.g[x]!) == v := by
    rw [hcm']
    exact segmentOf_eq_flatMap st'.lab cell1 _ _ _
      (fun j hj => by
        rw [segN_length] at hj
        exact (segN_getElem! st'.lab cell1 _ j hj).symm)
  have hnd : (countValues (countsOf ctx st.lab workset cell1
      cell2)).Nodup := by
    rw [countValues]
    exact nodup_range_map_add _ _
  have hcov : ∀ x ∈ segN st.lab cell1 (cell2 + 1 - cell1),
      workset.cardInter ctx.g[x]! ∈
        countValues (countsOf ctx st.lab workset cell1 cell2) := by
    intro x hx
    have hmemc : workset.cardInter ctx.g[x]! ∈
        countsOf ctx st.lab workset cell1 cell2 := by
      rw [hcm]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
    have hlo := foldl_min_le_mem _
      ((countsOf ctx st.lab workset cell1 cell2).headD 0) _ hmemc
    have hhi := foldl_max_ge_mem _
      ((countsOf ctx st.lab workset cell1 cell2).headD 0) _ hmemc
    rw [countValues]
    refine List.mem_map.mpr ⟨workset.cardInter ctx.g[x]! -
      (countsOf ctx st.lab workset cell1 cell2).foldl Nat.min
        ((countsOf ctx st.lab workset cell1 cell2).headD 0),
      List.mem_range.mpr (by omega), by omega⟩
  have hcov' : ∀ x ∈ segN st'.lab cell1 (cell2 + 1 - cell1),
      workset.cardInter ctx.g[x]! ∈
        countValues (countsOf ctx st.lab workset cell1 cell2) := by
    intro x hx
    exact hcov x (hseg.mem_iff.mpr hx)
  have hflat : (((countValues (countsOf ctx st.lab workset cell1
      cell2)).flatMap fun v => (segN st.lab cell1 (cell2 + 1 -
        cell1)).filter fun x => (workset.cardInter ctx.g[x]!) ==
          v).Perm (segN st.lab cell1 (cell2 + 1 - cell1))) :=
    flatMap_filters_perm _ _ hnd hcov
  have hflat' : (((countValues (countsOf ctx st.lab workset cell1
      cell2)).flatMap fun v => (segN st'.lab cell1 (cell2 + 1 -
        cell1)).filter fun x => (workset.cardInter ctx.g[x]!) ==
          v).Perm (segN st'.lab cell1 (cell2 + 1 - cell1))) :=
    flatMap_filters_perm _ _ hnd hcov'
  have hSEGlen : (segmentOf st.lab cell1
      (countsOf ctx st.lab workset cell1 cell2)
      (countValues (countsOf ctx st.lab workset cell1
        cell2))).length = cell2 + 1 - cell1 := by
    rw [hSEG, hflat.length_eq, segN_length]
  have hSEGlen' : (segmentOf st'.lab cell1
      (countsOf ctx st'.lab workset cell1 cell2)
      (countValues (countsOf ctx st.lab workset cell1
        cell2))).length = cell2 + 1 - cell1 := by
    rw [hSEG', hflat'.length_eq, segN_length]
  have hlay : segN (writeSegment st.lab cell1
      (segmentOf st.lab cell1 (countsOf ctx st.lab workset cell1 cell2)
        (countValues (countsOf ctx st.lab workset cell1 cell2))))
      cell1 (cell2 + 1 - cell1) =
      (countValues (countsOf ctx st.lab workset cell1 cell2)).flatMap
        fun v => (segN st.lab cell1 (cell2 + 1 - cell1)).filter
          fun x => (workset.cardInter ctx.g[x]!) == v := by
    rw [← hSEG, show cell2 + 1 - cell1 = (segmentOf st.lab cell1
      (countsOf ctx st.lab workset cell1 cell2)
      (countValues (countsOf ctx st.lab workset cell1
        cell2))).length from hSEGlen.symm]
    exact segN_writeSegment _ st.lab cell1 (by rw [hSEGlen]; omega)
  have hlay' : segN (writeSegment st'.lab cell1
      (segmentOf st'.lab cell1
        (countsOf ctx st'.lab workset cell1 cell2)
        (countValues (countsOf ctx st.lab workset cell1 cell2))))
      cell1 (cell2 + 1 - cell1) =
      (countValues (countsOf ctx st.lab workset cell1 cell2)).flatMap
        fun v => (segN st'.lab cell1 (cell2 + 1 - cell1)).filter
          fun x => (workset.cardInter ctx.g[x]!) == v := by
    rw [← hSEG', show cell2 + 1 - cell1 = (segmentOf st'.lab cell1
      (countsOf ctx st'.lab workset cell1 cell2)
      (countValues (countsOf ctx st.lab workset cell1
        cell2))).length from hSEGlen'.symm]
    exact segN_writeSegment _ st'.lab cell1 (by
      rw [hSEGlen']
      have := h.labSize
      omega)
  -- the two written labellings are cell-equivalent for the input partition
  have hLout : ∀ a len, IsCell st.ptn level a len →
      a + len ≤ cell1 ∨ cell2 + 1 ≤ a →
      (segN (writeSegment st.lab cell1
        (segmentOf st.lab cell1
          (countsOf ctx st.lab workset cell1 cell2)
          (countValues (countsOf ctx st.lab workset cell1 cell2))))
        a len).Perm
      (segN (writeSegment st'.lab cell1
        (segmentOf st'.lab cell1
          (countsOf ctx st'.lab workset cell1 cell2)
          (countValues (countsOf ctx st.lab workset cell1 cell2))))
        a len) := by
    intro a len hic hdis
    have hLs : segN (writeSegment st.lab cell1
        (segmentOf st.lab cell1
          (countsOf ctx st.lab workset cell1 cell2)
          (countValues (countsOf ctx st.lab workset cell1 cell2))))
        a len = segN st.lab a len :=
      segN_congr fun o ho => writeSegment_outside _ _ _ _
        (by rw [hSEGlen]; omega)
    have hRs : segN (writeSegment st'.lab cell1
        (segmentOf st'.lab cell1
          (countsOf ctx st'.lab workset cell1 cell2)
          (countValues (countsOf ctx st.lab workset cell1 cell2))))
        a len = segN st'.lab a len :=
      segN_congr fun o ho => writeSegment_outside _ _ _ _
        (by rw [hSEGlen']; omega)
    rw [hLs, hRs]
    exact h.cells a len hic
  have hcp0 : cellsPerm st.ptn level
      (writeSegment st.lab cell1
        (segmentOf st.lab cell1
          (countsOf ctx st.lab workset cell1 cell2)
          (countValues (countsOf ctx st.lab workset cell1 cell2))))
      (writeSegment st'.lab cell1
        (segmentOf st'.lab cell1
          (countsOf ctx st'.lab workset cell1 cell2)
          (countValues (countsOf ctx st.lab workset cell1 cell2)))) := by
    intro a len hic
    rcases isCell_disjoint_or_eq hic hcell with hd | hd | ⟨ha, hlen⟩
    · exact hLout a len hic (Or.inr (by omega))
    · exact hLout a len hic (Or.inl (by omega))
    · subst ha
      rw [hlen, hlay, hlay']
      exact (flatMap_perm_of_pointwise _ fun v _ =>
        hseg.filter _).trans (List.Perm.refl _)
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl,
    by
      dsimp only
      rw [writeSegment_size, writeSegment_size]
      exact h.labSize,
    ?_⟩, ?_, ?_, ?_⟩
  · -- cell equivalence for the result partition
    dsimp only
    rw [ptn_nontrivialFix]
    refine windowScan_region_perm level cell1 cell2
      (countsOf ctx st.lab workset cell1 cell2)
      (fun v => (segN st.lab cell1 (cell2 + 1 - cell1)).filter
        fun x => (workset.cardInter ctx.g[x]!) == v)
      (fun v => (segN st'.lab cell1 (cell2 + 1 - cell1)).filter
        fun x => (workset.cardInter ctx.g[x]!) == v)
      (fun v => hseg.filter _)
      (fun v => by
        rw [← List.countP_eq_length_filter, hcm, multOf,
          List.countP_map]
        rfl)
      (countValues (countsOf ctx st.lab workset cell1 cell2)) cell1
      (-1) st (fun _ => hcell) (by omega) hcp0 hlay hlay'
  · intro q hq
    dsimp only
    rw [ptn_nontrivialFix]
    exact ptn_windowScan_outside level cell1 cell2 _ _ _ _ _
      (Nat.le_refl cell1) q hq
  · dsimp only
    rw [ptn_nontrivialFix]
    exact ptn_windowScan_size level cell1 cell2 _ _ _ _ _
  · dsimp only
    rw [writeSegment_size]

/-! # Active positions are cell starts -/

/-- Every active position starts a cell of the partition at `level`. -/
@[expose] def StartsOk (level : Nat) (st : RefineSt n) : Prop :=
  ∀ v : Nat, st.active.mem v = true →
    v = 0 ∨ st.ptn[v - 1]! ≤ level

theorem getElem!_set!_cases (a : Array Nat) (i x q : Nat) :
    (a.set! i x)[q]! = a[q]! ∨ (a.set! i x)[q]! = x := by
  rcases Decidable.em (i = q) with rfl | hne
  · rcases Nat.lt_or_ge i a.size with hlt | hge
    · exact Or.inr (Array.getElem!_set!_self _ _ _ hlt)
    · left
      rw [getElem!_neg _ _ (by rw [Array.size_set!]; omega),
        getElem!_neg _ _ (by omega)]
  · exact Or.inl (Array.getElem!_set!_ne _ _ _ _ hne)

theorem starts_insert {active : VSet n} {ptnQ : Array Nat} {level w : Nat}
    (hold : ∀ v : Nat, active.mem v = true →
      v = 0 ∨ ptnQ[v - 1]! ≤ level)
    (hw : w = 0 ∨ ptnQ[w - 1]! ≤ level) :
    ∀ v : Nat, (active.insert w).mem v = true →
      v = 0 ∨ ptnQ[v - 1]! ≤ level := by
  intro v hv
  rw [VSet.mem_insert] at hv
  rcases Bool.or_eq_true_iff.mp hv with hb | hb
  · exact hold v hb
  · rw [Bool.and_eq_true, beq_iff_eq] at hb
    rw [← hb.1]
    exact hw

/-- New actives after the trivial split start cells: the reused cell
start, or the fresh boundary written one position earlier. -/
theorem trivialSplit_starts {level cell1 cell2 : Nat} {c1 c2 : Int}
    {st : RefineSt n} (hst : StartsOk level st)
    (hcellstart : cell1 = 0 ∨ st.ptn[cell1 - 1]! ≤ level)
    (hc2eq : c2 = c1 - 1) (hc2s : cell2 < st.ptn.size) :
    StartsOk level (trivialSplit level cell1 cell2 c1 c2 st) := by
  rw [trivialSplit]
  rcases Decidable.em (c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2) with
    hA | hA
  · have hA' : cell1 ≤ c2.toNat ∧ c2.toNat + 1 ≤ cell2 ∧
        c1.toNat = c2.toNat + 1 := by
      obtain ⟨h1, h2⟩ := hA
      simp only [Int.ofNat_eq_natCast] at h1 h2
      omega
    have hold : ∀ v : Nat, st.active.mem v = true → v = 0 ∨
        (st.ptn.set! c2.toNat level)[v - 1]! ≤ level := by
      intro v hv
      rcases hst v hv with h0 | hb
      · exact Or.inl h0
      · rcases getElem!_set!_cases st.ptn c2.toNat level (v - 1) with
          he | he
        · right
          rw [he]
          exact hb
        · right
          rw [he]
          exact Nat.le_refl level
    have hbound : (st.ptn.set! c2.toNat level)[c1.toNat - 1]! ≤
        level := by
      rw [show c1.toNat - 1 = c2.toNat by omega,
        Array.getElem!_set!_self _ _ _ (by omega)]
      exact Nat.le_refl level
    have hcs' : cell1 = 0 ∨
        (st.ptn.set! c2.toNat level)[cell1 - 1]! ≤ level := by
      rcases Nat.eq_zero_or_pos cell1 with h0 | hpos
      · exact Or.inl h0
      · right
        rcases hcellstart with h0 | hb
        · omega
        · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
          exact hb
    simp only [ite_eq_left hA]
    rcases Decidable.em
        (st.active.mem cell1 ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat) with
      hBc | hBc
    · simp only [ite_eq_left hBc]
      rcases hC : (c1.toNat == cell2) with _ | _ <;>
        simp only [Bool.false_eq_true, ite_false, ite_true] <;>
        exact starts_insert hold (Or.inr hbound)
    · simp only [ite_eq_right hBc]
      rcases hD : (c2.toNat == cell1) with _ | _ <;>
        simp only [Bool.false_eq_true, ite_false, ite_true] <;>
        exact starts_insert hold hcs'
  · simp only [ite_eq_right hA]
    exact hst

theorem trivialCell_starts {level cell1 cell2 : Nat} {gRow : VSet n} {st : RefineSt n}
    (hst : StartsOk level st)
    (hcellstart : cell1 = 0 ∨ st.ptn[cell1 - 1]! ≤ level)
    (hc12 : cell1 ≤ cell2) (hc2s : cell2 < st.ptn.size)
    (_h2 : cell2 < st.lab.size) :
    StartsOk level (trivialCell level gRow cell1 cell2 st) := by
  rw [trivialCell]
  rcases hc : (cell1 == cell2) with _ | _
  · simp only [Bool.false_eq_true, ite_false]
    obtain ⟨hp1, hp2, _, _, _, _⟩ :=
      splitCellLoop_spec (gRow := gRow) (cell2 + 1 - cell1)
        (cell2 - cell1 + 2) st.lab (Int.ofNat cell1) (Int.ofNat cell2)
        (by simp only [Int.ofNat_eq_natCast]; omega)
        (by simp only [Int.ofNat_eq_natCast]; omega)
        (by simp only [Int.ofNat_eq_natCast]; omega)
        (by omega)
    exact trivialSplit_starts hst hcellstart
      (by rw [hp1, hp2]) hc2s
  · simp only [ite_true]
    exact hst

theorem active_windowStep_eq (level cell1 cell2 v c1 c2 : Nat)
    (maxcell : Int) (st : RefineSt n) :
    (windowStep level cell1 cell2 v c1 c2 maxcell st).active =
      if c1 != cell1 then st.active.insert c1 else st.active := by
  rw [windowStep]
  dsimp only
  rcases Decidable.em (Int.ofNat (c2 - c1) > maxcell) with h1 | h1 <;>
  rcases hB : (c1 != cell1) with _ | _ <;>
  rcases hC : (c2 - c1 == 1) with _ | _ <;>
  rcases Decidable.em (c2 ≤ cell2) with h4 | h4 <;>
    simp only [h1, h4, Bool.false_eq_true, ite_false, ite_true]

/-- Through the window scan, every active position keeps starting a
cell: interior group starts follow the boundary written for the
preceding group. -/
theorem windowScan_starts (level cell1 cell2 : Nat) (counts : List Nat) :
    ∀ (vs : List Nat) (c1acc : Nat) (maxcell : Int) (st : RefineSt n),
      StartsOk level st →
      (c1acc = cell1 ∨ c1acc = 0 ∨ st.ptn[c1acc - 1]! ≤ level ∨
        cell2 + 1 ≤ c1acc) →
      c1acc + (vs.map (multOf counts)).sum ≤ cell2 + 1 →
      cell2 < st.ptn.size →
      StartsOk level
        (windowScan level cell1 cell2 counts vs c1acc maxcell st)
  | [], _, _, _, hst, _, _, _ => hst
  | v :: vs, c1acc, maxcell, st, hst, hacc, hsum, hc2s => by
    rw [windowScan]
    have hsplit : (List.map (multOf counts) (v :: vs)).sum =
        multOf counts v + (vs.map (multOf counts)).sum := by
      rw [List.map_cons, List.sum_cons]
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · simp only [ite_eq_left hm]
      have hin : c1acc + multOf counts v ≤ cell2 + 1 := by omega
      have hptn1 := ptn_windowStep_eq level cell1 cell2 v c1acc
        (c1acc + multOf counts v) maxcell st
      have hact1 := active_windowStep_eq level cell1 cell2 v c1acc
        (c1acc + multOf counts v) maxcell st
      have hstepOk : StartsOk level (windowStep level cell1 cell2 v
          c1acc (c1acc + multOf counts v) maxcell st) := by
        intro w hw
        rw [hact1] at hw
        have hold : ∀ u : Nat, st.active.mem u = true → u = 0 ∨
            (windowStep level cell1 cell2 v c1acc
              (c1acc + multOf counts v) maxcell st).ptn[u - 1]! ≤
                level := by
          intro u hu
          rcases hst u hu with h0 | hb
          · exact Or.inl h0
          · right
            rw [hptn1]
            split
            · rcases getElem!_set!_cases st.ptn
                (c1acc + multOf counts v - 1) level (u - 1) with he | he
              · rw [he]
                exact hb
              · rw [he]
                exact Nat.le_refl level
            · exact hb
        rcases hbc : (c1acc != cell1) with _ | _
        · rw [hbc] at hw
          simp only [Bool.false_eq_true, ite_false] at hw
          exact hold w hw
        · rw [hbc] at hw
          simp only [ite_true] at hw
          refine starts_insert hold ?_ w hw
          rcases hacc with h1 | h1 | h1 | h1
          · exfalso
            simp only [bne_iff_ne, ne_eq] at hbc
            exact hbc h1
          · exact Or.inl h1
          · right
            rw [hptn1]
            split
            · rcases getElem!_set!_cases st.ptn
                (c1acc + multOf counts v - 1) level (c1acc - 1) with
                he | he
              · rw [he]
                exact h1
              · rw [he]
                exact Nat.le_refl level
            · exact h1
          · omega
      refine windowScan_starts level cell1 cell2 counts vs
        (c1acc + multOf counts v) _ _ hstepOk ?_ (by omega) ?_
      · rcases Decidable.em (c1acc + multOf counts v ≤ cell2) with
          hle | hgt
        · right
          right
          left
          rw [hptn1, ite_eq_left hle,
            Array.getElem!_set!_self _ _ _ (by omega)]
          exact Nat.le_refl level
        · right
          right
          right
          omega
      · rw [hptn1]
        split
        · rw [Array.size_set!]
          exact hc2s
        · exact hc2s
    · simp only [ite_eq_right hm]
      exact windowScan_starts level cell1 cell2 counts vs c1acc maxcell
        st hst hacc (by omega) hc2s

theorem nontrivialFix_starts {level cell1 : Nat} {st : RefineSt n}
    (hst : StartsOk level st)
    (hc : cell1 = 0 ∨ st.ptn[cell1 - 1]! ≤ level) :
    StartsOk level (nontrivialFix cell1 st) := by
  rw [nontrivialFix]
  split
  · intro w hw
    have hw' : (st.active.insert cell1).mem w = true := by
      rw [VSet.mem_erase] at hw
      simp only [Bool.and_eq_true] at hw
      exact hw.1
    exact starts_insert hst hc w hw'
  · exact hst

theorem nontrivialCell_starts {ctx : Ctx n}
    {level cell1 cell2 : Nat} {workset : VSet n} {st : RefineSt n}
    (hst : StartsOk level st)
    (hcellstart : cell1 = 0 ∨ st.ptn[cell1 - 1]! ≤ level)
    (hc12 : cell1 ≤ cell2) (hc2s : cell2 < st.ptn.size)
    (_h2 : cell2 < st.lab.size) :
    StartsOk level (nontrivialCell ctx level workset cell1 cell2 st) := by
  rw [nontrivialCell]
  rcases hc : (cell1 == cell2) with _ | _
  case true =>
    rw [ite_eq_left rfl]
    exact hst
  case false =>
  rw [ite_eq_right (by simp)]
  split
  · exact hst
  · have hnd : (countValues (countsOf ctx st.lab workset cell1
        cell2)).Nodup := by
      rw [countValues]
      exact nodup_range_map_add _ _
    have hsum := sum_multOf_le hnd
      (countsOf ctx st.lab workset cell1 cell2)
    have hlen := countsOf_length ctx st.lab workset cell1 cell2
    have hW : StartsOk level (windowScan level cell1 cell2
        (countsOf ctx st.lab workset cell1 cell2)
        (countValues (countsOf ctx st.lab workset cell1 cell2))
        cell1 (-1) st) :=
      windowScan_starts level cell1 cell2 _ _ cell1 (-1) st hst
        (Or.inl rfl) (by omega) hc2s
    refine nontrivialFix_starts (fun w hw => ?_) ?_
    · exact hW w hw
    · rcases Nat.eq_zero_or_pos cell1 with h0 | hpos
      · exact Or.inl h0
      · right
        rw [ptn_windowScan_outside level cell1 cell2
          (countsOf ctx st.lab workset cell1 cell2)
          (countValues (countsOf ctx st.lab workset cell1 cell2))
          cell1 (-1) st (Nat.le_refl cell1) (cell1 - 1)
          (Or.inl (by omega))]
        rcases hcellstart with h0 | hb
        · omega
        · exact hb

/-! # Passes, step, loop -/

theorem StPerm.refl (level : Nat) (st : RefineSt n) : StPerm level st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => List.Perm.refl _⟩

theorem pickSplit_mem {active : VSet n} {hint s : Nat} :
    pickSplit active hint = some s → active.mem s = true := by
  rw [pickSplit]
  split
  · next h =>
    intro he
    injection he with he
    subst he
    exact h
  · intro he
    rcases hne : active.nextElem (some hint) with _ | v
    · rw [hne] at he
      exact VSet.nextElem_mem he
    · rw [hne] at he
      injection he with he
      subst he
      exact VSet.nextElem_mem hne

theorem starts_erase {level : Nat} {st : RefineSt n} {w : Nat}
    (hst : StartsOk level st) :
    StartsOk level { st with active := st.active.erase w } := by
  intro v hv
  refine hst v ?_
  change (st.active.erase w).mem v = true at hv
  rw [VSet.mem_erase] at hv
  simp only [Bool.and_eq_true] at hv
  exact hv.1

theorem refineTrivial_go_starts {level : Nat} {gRow : VSet n} :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt n), StartsOk level st →
      st.ptn.size = st.lab.size →
      (∀ p ∈ cs, IsCell st.ptn level p.1 (p.2 + 1 - p.1) ∧
        p.2 < st.lab.size) →
      cs.Pairwise (fun p q => p.2 < q.1) →
      StartsOk level (refineTrivial.go level gRow cs st)
  | [], _, hst, _, _, _ => hst
  | (c1, c2) :: rest, st, hst, hsz, hcs, hpair => by
    rw [refineTrivial.go]
    have hic := (hcs (c1, c2) (by simp)).1
    have hc12 : c1 ≤ c2 := by
      have := hic.1
      omega
    have h2 := (hcs (c1, c2) (by simp)).2
    obtain ⟨-, hdiff, hpsz, hlsz⟩ := trivialCell_perm (gRow := gRow)
      (StPerm.refl level st) hic hc12 h2 hsz
    have hstep := trivialCell_starts (gRow := gRow) hst hic.2.1 hc12
      (by omega) h2
    have hrest := (List.pairwise_cons.mp hpair).1
    exact refineTrivial_go_starts rest _ hstep
      (by rw [hpsz, hlsz]; exact hsz)
      (fun p hp => ⟨isCell_of_agree (hcs p (by simp [hp])).1
          (fun q hq1 hq2 => hdiff q (Or.inr (by
            have := hrest p hp
            omega))),
        by rw [hlsz]; exact (hcs p (by simp [hp])).2⟩)
      (List.pairwise_cons.mp hpair).2

theorem refineTrivial_starts {ctx : Ctx n} {level split1 : Nat}
    {st : RefineSt n} (hst : StartsOk level st)
    (hsz : st.ptn.size = st.lab.size) (hnn : n ≤ st.ptn.size)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    StartsOk level (refineTrivial ctx level split1 st) := by
  rw [refineTrivial]
  exact refineTrivial_go_starts _ _ hst hsz
    (fun p hp => ⟨cells_isCell hnn hend p hp,
      by
        have := cells_bound hnn hend p hp
        omega⟩)
    cells_pairwise

theorem refineNontrivial_go_perm {ctx : Ctx n} {level : Nat} {workset : VSet n} :
    ∀ (cs : List (Nat × Nat)) (st st' : RefineSt n), StPerm level st st' →
      st.ptn.size = st.lab.size →
      (∀ p ∈ cs, IsCell st.ptn level p.1 (p.2 + 1 - p.1) ∧
        p.2 < st.lab.size) →
      cs.Pairwise (fun p q => p.2 < q.1) →
      StPerm level (refineNontrivial.go ctx level workset cs st)
        (refineNontrivial.go ctx level workset cs st') ∧
      (refineNontrivial.go ctx level workset cs st).lab.size =
        st.lab.size ∧
      (refineNontrivial.go ctx level workset cs st).ptn.size =
        st.ptn.size
  | [], _, _, h, _, _, _ => ⟨h, rfl, rfl⟩
  | (c1, c2) :: rest, st, st', h, hsz, hcs, hpair => by
    rw [refineNontrivial.go, refineNontrivial.go]
    have hic := (hcs (c1, c2) (by simp)).1
    have hc12 : c1 ≤ c2 := by
      have := hic.1
      omega
    have h2 := (hcs (c1, c2) (by simp)).2
    obtain ⟨hstep, hdiff, hpsz, hlsz⟩ := nontrivialCell_perm
      (ctx := ctx) (workset := workset) h hic hc12 h2 hsz
    have hrest := (List.pairwise_cons.mp hpair).1
    obtain ⟨hrec, hrsz, hrpsz⟩ := refineNontrivial_go_perm rest
      (nontrivialCell ctx level workset c1 c2 st)
      (nontrivialCell ctx level workset c1 c2 st') hstep
      (by rw [hpsz, hlsz]; exact hsz)
      (fun p hp => ⟨isCell_of_agree (hcs p (by simp [hp])).1
          (fun q hq1 hq2 => hdiff q (Or.inr (by
            have := hrest p hp
            omega))),
        by rw [hlsz]; exact (hcs p (by simp [hp])).2⟩)
      (List.pairwise_cons.mp hpair).2
    exact ⟨hrec, by rw [hrsz, hlsz], by rw [hrpsz, hpsz]⟩

theorem refineNontrivial_go_starts {ctx : Ctx n} {level : Nat} {workset : VSet n} :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt n), StartsOk level st →
      st.ptn.size = st.lab.size →
      (∀ p ∈ cs, IsCell st.ptn level p.1 (p.2 + 1 - p.1) ∧
        p.2 < st.lab.size) →
      cs.Pairwise (fun p q => p.2 < q.1) →
      StartsOk level (refineNontrivial.go ctx level workset cs st)
  | [], _, hst, _, _, _ => hst
  | (c1, c2) :: rest, st, hst, hsz, hcs, hpair => by
    rw [refineNontrivial.go]
    have hic := (hcs (c1, c2) (by simp)).1
    have hc12 : c1 ≤ c2 := by
      have := hic.1
      omega
    have h2 := (hcs (c1, c2) (by simp)).2
    obtain ⟨-, hdiff, hpsz, hlsz⟩ := nontrivialCell_perm
      (ctx := ctx) (workset := workset) (StPerm.refl level st) hic hc12
      h2 hsz
    have hstep := nontrivialCell_starts (ctx := ctx)
      (workset := workset) hst hic.2.1 hc12 (by omega) h2
    have hrest := (List.pairwise_cons.mp hpair).1
    exact refineNontrivial_go_starts rest _ hstep
      (by rw [hpsz, hlsz]; exact hsz)
      (fun p hp => ⟨isCell_of_agree (hcs p (by simp [hp])).1
          (fun q hq1 hq2 => hdiff q (Or.inr (by
            have := hrest p hp
            omega))),
        by rw [hlsz]; exact (hcs p (by simp [hp])).2⟩)
      (List.pairwise_cons.mp hpair).2

theorem refineNontrivial_perm {ctx : Ctx n} {level split1 split2 : Nat}
    {st st' : RefineSt n} (h : StPerm level st st')
    (hsz : st.ptn.size = st.lab.size) (hnn : n ≤ st.ptn.size)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hsc : IsCell st.ptn level split1 (split2 + 1 - split1)) :
    StPerm level (refineNontrivial ctx level split1 split2 st)
      (refineNontrivial ctx level split1 split2 st') := by
  rw [refineNontrivial, refineNontrivial]
  dsimp only
  rw [show worksetOf n st'.lab split1 split2 =
      worksetOf n st.lab split1 split2 from
      (worksetOf_perm (h.cells split1 _ hsc)).symm,
    h.ptn, h.longcode]
  exact (refineNontrivial_go_perm (ctx := ctx)
    (workset := worksetOf n st.lab split1 split2) _
    { st with longcode := mash st.longcode (split2 - split1 + 1) }
    { st' with
      ptn := st.ptn
      longcode := mash st.longcode (split2 - split1 + 1) }
    ⟨rfl, h.active, h.numcells, h.hint, h.maxpos, rfl, h.labSize,
      h.cells⟩
    hsz
    (fun p hp => ⟨cells_isCell (by omega) hend p hp,
      by
        have := cells_bound (nn := n) (by omega) hend p hp
        show p.2 < st.lab.size
        omega⟩)
    cells_pairwise).1

theorem refineNontrivial_starts {ctx : Ctx n} {level split1 split2 : Nat}
    {st : RefineSt n} (hst : StartsOk level st)
    (hsz : st.ptn.size = st.lab.size) (hnn : n ≤ st.ptn.size)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    StartsOk level (refineNontrivial ctx level split1 split2 st) := by
  rw [refineNontrivial]
  dsimp only
  exact refineNontrivial_go_starts _
    { st with longcode := mash st.longcode (split2 - split1 + 1) }
    hst hsz
    (fun p hp => ⟨cells_isCell hnn hend p hp,
      by
        have := cells_bound hnn hend p hp
        show p.2 < st.lab.size
        omega⟩)
    cells_pairwise

/-- One active-cell iteration preserves cell-contents equivalence. -/
theorem refineStep_perm {ctx : Ctx n} {level split1 : Nat}
    {st st' : RefineSt n} (h : StPerm level st st')
    (hOk : StOk n level st)
    (hst : StartsOk level st) (hmem : st.active.mem split1 = true) :
    StPerm level (refineStep ctx level split1 st)
      (refineStep ctx level split1 st') := by
  rw [refineStep, refineStep]
  dsimp only
  rw [h.active, h.ptn, h.longcode]
  have hs1lt : split1 < st.ptn.size := by
    have h1 := VSet.mem_lt hmem
    have h2 := hOk.ptnSize
    omega
  have hcellS : IsCell st.ptn level split1
      (cellEnd st.ptn level split1 + 1 - split1) :=
    isCell_cellEnd hs1lt (hst split1 hmem) hOk.ptnEnd
  have hbridge : StPerm level
      { st with
        active := st.active.erase split1
        longcode := mash st.longcode
          (split1 + cellEnd st.ptn level split1) }
      { st' with
        ptn := st.ptn
        active := st.active.erase split1
        longcode := mash st.longcode
          (split1 + cellEnd st.ptn level split1) } :=
    ⟨rfl, rfl, h.numcells, h.hint, h.maxpos, rfl, h.labSize, h.cells⟩
  rcases hg : (split1 == cellEnd st.ptn level split1) with _ | _
  · simp only [Bool.false_eq_true, ite_false]
    exact refineNontrivial_perm hbridge
      (by
        show st.ptn.size = st.lab.size
        have := hOk.ptnSize
        have := hOk.labSize
        omega)
      (by
        show n ≤ st.ptn.size
        have := hOk.ptnSize
        omega)
      hOk.ptnEnd hcellS
  · simp only [ite_true]
    have hone : IsCell st.ptn level split1 1 := by
      have heq : cellEnd st.ptn level split1 = split1 := by
        have := hg
        simp only [beq_iff_eq] at this
        omega
      rw [show (1 : Nat) = cellEnd st.ptn level split1 + 1 - split1 by
        omega]
      exact hcellS
    exact (refineTrivial_perm hbridge
      (by
        show st.ptn.size = st.lab.size
        have := hOk.ptnSize
        have := hOk.labSize
        omega)
      (by
        show n ≤ st.ptn.size
        have := hOk.ptnSize
        omega)
      hOk.ptnEnd hone).1

theorem refineStep_starts {ctx : Ctx n} {level split1 : Nat}
    {st : RefineSt n} (hOk : StOk n level st)
    (hst : StartsOk level st) :
    StartsOk level (refineStep ctx level split1 st) := by
  rw [refineStep]
  dsimp only
  have hst1 : StartsOk level
      { st with
        active := st.active.erase split1
        longcode := mash st.longcode
          (split1 + cellEnd st.ptn level split1) } := by
    intro v hv
    exact starts_erase (w := split1) hst v hv
  split
  · exact refineTrivial_starts hst1
      (by
        show st.ptn.size = st.lab.size
        have := hOk.ptnSize
        have := hOk.labSize
        omega)
      (by
        show n ≤ st.ptn.size
        have := hOk.ptnSize
        omega)
      hOk.ptnEnd
  · exact refineNontrivial_starts hst1
      (by
        show st.ptn.size = st.lab.size
        have := hOk.ptnSize
        have := hOk.labSize
        omega)
      (by
        show n ≤ st.ptn.size
        have := hOk.ptnSize
        omega)
      hOk.ptnEnd

/-- The active-cell loop preserves cell-contents equivalence. -/
theorem refineLoop_perm {ctx : Ctx n} {level : Nat} :
    ∀ (fuel : Nat) (st st' : RefineSt n), StPerm level st st' →
      StOk n level st → StartsOk level st →
      StPerm level (refineLoop ctx level fuel st)
        (refineLoop ctx level fuel st')
  | 0, _, _, h, _, _ => h
  | fuel + 1, st, st', h, hOk, hst => by
    rw [refineLoop, refineLoop, h.numcells, h.active, h.hint]
    rcases Decidable.em (st.numcells < n) with hlt | hlt
    · simp only [ite_eq_left hlt]
      rcases hps : pickSplit st.active st.hint with _ | s
      · exact h
      · exact refineLoop_perm fuel _ _
          (refineStep_perm h hOk hst (pickSplit_mem hps))
          (refineStep_stOk hOk)
          (refineStep_starts hOk hst)
    · simp only [ite_eq_right hlt]
      exact h

/-- nauty's `refine` depends on the ordered partition only through the
cell contents: cell-equivalent labellings refine to equal positions and
codes with cell-equivalent labellings. -/
theorem refine_perm {ctx : Ctx n} {level : Nat}
    {lab lab' ptn : Array Nat} {active : VSet n} {numcells : Nat}
    (hcp : cellsPerm ptn level lab lab') (hls : lab'.size = lab.size)
    (hsl : lab.size = n) (hlab : LabOk lab n) (hsp : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hstarts : ∀ v : Nat, active.mem v = true →
      v = 0 ∨ ptn[v - 1]! ≤ level) :
    StPerm level (refine ctx level lab ptn active numcells)
      (refine ctx level lab' ptn active numcells) := by
  rw [refine, refine]
  have hloop := refineLoop_perm (ctx := ctx) (4 * n + 8)
    { lab, ptn, active, numcells, hint := 0, maxpos := 0,
      longcode := numcells }
    { lab := lab', ptn, active, numcells, hint := 0, maxpos := 0,
      longcode := numcells }
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, hls, hcp⟩
    ⟨hsl, hlab, hsp, hend⟩
    (fun v hv => hstarts v hv)
  exact ⟨hloop.ptn, hloop.active, hloop.numcells, hloop.hint,
    hloop.maxpos, by dsimp only; rw [hloop.longcode, hloop.numcells],
    hloop.labSize, hloop.cells⟩

/-! # All partition writes carry the current level -/

theorem ptn_trivialSplit_vals (level cell1 cell2 : Nat) (c1 c2 : Int)
    (st : RefineSt n) (q : Nat) :
    (trivialSplit level cell1 cell2 c1 c2 st).ptn[q]! = st.ptn[q]! ∨
      (trivialSplit level cell1 cell2 c1 c2 st).ptn[q]! = level := by
  rw [trivialSplit]
  split
  · split
    · split <;> exact getElem!_set!_cases st.ptn _ level q
    · split <;> exact getElem!_set!_cases st.ptn _ level q
  · exact Or.inl rfl

theorem ptn_trivialCell_vals (level : Nat) (gRow : VSet n) (cell1 cell2 : Nat)
    (st : RefineSt n) (q : Nat) :
    (trivialCell level gRow cell1 cell2 st).ptn[q]! = st.ptn[q]! ∨
      (trivialCell level gRow cell1 cell2 st).ptn[q]! = level := by
  rw [trivialCell]
  split
  · exact Or.inl rfl
  · exact ptn_trivialSplit_vals level cell1 cell2 _ _ _ q

theorem ptn_windowScan_vals (level cell1 cell2 : Nat)
    (counts : List Nat) :
    ∀ (vs : List Nat) (c1acc : Nat) (maxcell : Int) (st : RefineSt n)
      (q : Nat),
      (windowScan level cell1 cell2 counts vs c1acc maxcell
          st).ptn[q]! = st.ptn[q]! ∨
        (windowScan level cell1 cell2 counts vs c1acc maxcell
          st).ptn[q]! = level
  | [], _, _, _, _ => Or.inl rfl
  | v :: vs, c1acc, maxcell, st, q => by
    rw [windowScan]
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · simp only [ite_eq_left hm]
      rcases ptn_windowScan_vals level cell1 cell2 counts vs _ _ _ q with
        he | he
      · rw [he, ptn_windowStep_eq]
        split
        · exact getElem!_set!_cases st.ptn _ level q
        · exact Or.inl rfl
      · exact Or.inr he
    · simp only [ite_eq_right hm]
      exact ptn_windowScan_vals level cell1 cell2 counts vs _ _ _ q

theorem ptn_nontrivialCell_vals (ctx : Ctx n)
    (level : Nat) (workset : VSet n) (cell1 cell2 : Nat) (st : RefineSt n) (q : Nat) :
    (nontrivialCell ctx level workset cell1 cell2 st).ptn[q]! =
        st.ptn[q]! ∨
      (nontrivialCell ctx level workset cell1 cell2 st).ptn[q]! =
        level := by
  rw [nontrivialCell]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · rw [ptn_nontrivialFix]
      exact ptn_windowScan_vals level cell1 cell2 _ _ _ _ _ q

theorem ptn_refineTrivial_go_vals (level : Nat) (gRow : VSet n) :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt n) (q : Nat),
      (refineTrivial.go level gRow cs st).ptn[q]! = st.ptn[q]! ∨
        (refineTrivial.go level gRow cs st).ptn[q]! = level
  | [], _, _ => Or.inl rfl
  | (c1, c2) :: rest, st, q => by
    rw [refineTrivial.go]
    rcases ptn_refineTrivial_go_vals level gRow rest _ q with he | he
    · rw [he]
      exact ptn_trivialCell_vals level gRow c1 c2 st q
    · exact Or.inr he

theorem ptn_refineNontrivial_go_vals (ctx : Ctx n) (level : Nat) (workset : VSet n) :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt n) (q : Nat),
      (refineNontrivial.go ctx level workset cs st).ptn[q]! =
          st.ptn[q]! ∨
        (refineNontrivial.go ctx level workset cs st).ptn[q]! = level
  | [], _, _ => Or.inl rfl
  | (c1, c2) :: rest, st, q => by
    rw [refineNontrivial.go]
    rcases ptn_refineNontrivial_go_vals ctx level workset rest _ q with
      he | he
    · rw [he]
      exact ptn_nontrivialCell_vals ctx level workset c1 c2 st q
    · exact Or.inr he

theorem ptn_refineStep_vals (ctx : Ctx n) (level split1 : Nat)
    (st : RefineSt n) (q : Nat) :
    (refineStep ctx level split1 st).ptn[q]! = st.ptn[q]! ∨
      (refineStep ctx level split1 st).ptn[q]! = level := by
  rw [refineStep]
  dsimp only
  split
  · exact ptn_refineTrivial_go_vals level _ _ _ q
  · rw [refineNontrivial]
    dsimp only
    exact ptn_refineNontrivial_go_vals ctx level _ _ _ q

theorem ptn_refineLoop_vals (ctx : Ctx n) (level : Nat) :
    ∀ (fuel : Nat) (st : RefineSt n) (q : Nat),
      (refineLoop ctx level fuel st).ptn[q]! = st.ptn[q]! ∨
        (refineLoop ctx level fuel st).ptn[q]! = level
  | 0, _, _ => Or.inl rfl
  | fuel + 1, st, q => by
    rw [refineLoop]
    split
    · rcases hps : pickSplit st.active st.hint with _ | s
      · exact Or.inl rfl
      · rcases ptn_refineLoop_vals ctx level fuel
          (refineStep ctx level s st) q with he | he
        · rw [he]
          exact ptn_refineStep_vals ctx level s st q
        · exact Or.inr he
    · exact Or.inl rfl

/-- Every partition write in `refine` carries the current level. -/
theorem ptn_refine_vals (ctx : Ctx n) (level : Nat)
    (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) (q : Nat) :
    (refine ctx level lab ptn active numcells).ptn[q]! = ptn[q]! ∨
      (refine ctx level lab ptn active numcells).ptn[q]! = level := by
  rw [refine]
  exact ptn_refineLoop_vals ctx level _ _ q

/-! # Level transfer and individualization -/

/-- With no partition value exactly `level + 1`, runs at `level` and
`level + 1` coincide. -/
theorem isCell_succ_iff {ptn : Array Nat} {level a len : Nat}
    (hvals : ∀ q : Nat, ptn[q]! ≠ level + 1) :
    IsCell ptn (level + 1) a len ↔ IsCell ptn level a len := by
  constructor
  · rintro ⟨hl, hs, hi, he⟩
    refine ⟨hl, ?_, ?_, ?_⟩
    · rcases hs with h0 | hb
      · exact Or.inl h0
      · right
        have := hvals (a - 1)
        omega
    · intro i hi1 hi2
      have := hi i hi1 hi2
      omega
    · have := hvals (a + len - 1)
      omega
  · rintro ⟨hl, hs, hi, he⟩
    refine ⟨hl, ?_, ?_, ?_⟩
    · rcases hs with h0 | hb
      · exact Or.inl h0
      · right
        omega
    · intro i hi1 hi2
      have := hi i hi1 hi2
      have := hvals i
      omega
    · omega

theorem cellsPerm_succ {ptn : Array Nat} {level : Nat}
    {lab lab' : Array Nat} (hvals : ∀ q : Nat, ptn[q]! ≠ level + 1)
    (h : cellsPerm ptn level lab lab') :
    cellsPerm ptn (level + 1) lab lab' :=
  fun a len hic => h a len ((isCell_succ_iff hvals).mp hic)

theorem breakout_go_size {tv : Nat} :
    ∀ (fuel : Nat) (lab : Array Nat) (i prev : Nat),
      (breakout.go tv fuel lab i prev).size = lab.size
  | 0, _, _, _ => rfl
  | fuel + 1, lab, i, prev => by
    rw [breakout.go]
    split
    · rw [Array.size_set!]
    · rw [breakout_go_size fuel _ (i + 1) _, Array.size_set!]

theorem breakout_go_outside {tv : Nat} :
    ∀ (fuel : Nat) (lab : Array Nat) (i prev q : Nat), q < i →
      (breakout.go tv fuel lab i prev)[q]! = lab[q]!
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, lab, i, prev, q, hq => by
    rw [breakout.go]
    split
    · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    · rw [breakout_go_outside fuel _ (i + 1) _ q (by omega),
        Array.getElem!_set!_ne _ _ _ _ (by omega)]

theorem breakout_go_outside_right {tv : Nat} :
    ∀ (fuel len : Nat) (lab : Array Nat) (i prev : Nat),
      (∃ k, i ≤ k ∧ k < i + len ∧ k < lab.size ∧ lab[k]! = tv) →
      ∀ q, i + len ≤ q →
      (breakout.go tv fuel lab i prev)[q]! = lab[q]!
  | 0, _, _, _, _, _, _, _ => rfl
  | fuel + 1, len, lab, i, prev, ⟨k, hik, hkl, hks, hkv⟩, q, hq => by
    rw [breakout.go]
    split
    · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    · next hne =>
      simp only [beq_iff_eq] at hne
      have hki : k ≠ i := by
        intro h
        rw [h] at hkv
        exact hne hkv
      rw [breakout_go_outside_right fuel (len - 1) _ (i + 1) _
        ⟨k, by omega, by omega, by rw [Array.size_set!]; omega,
          by rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]; exact hkv⟩
        q (by omega),
        Array.getElem!_set!_ne _ _ _ _ (by omega)]

/-- Individualization rotates the target vertex to the front of the
segment: the result is the incoming vertex followed by the segment with
its first occurrence of `tv` erased. -/
theorem breakout_go_seg {tv : Nat} :
    ∀ (fuel len : Nat) (lab : Array Nat) (i prev : Nat),
      (∃ k, i ≤ k ∧ k < i + len ∧ k < lab.size ∧ lab[k]! = tv) →
      len ≤ fuel → i + len ≤ lab.size →
      segN (breakout.go tv fuel lab i prev) i len =
        prev :: (segN lab i len).erase tv
  | fuel, 0, lab, i, prev, ⟨k, hik, hkl, _, _⟩, _, _ => by omega
  | 0, len + 1, lab, i, prev, hw, hf, _ => by omega
  | fuel + 1, len + 1, lab, i, prev, ⟨k, hik, hkl, hks, hkv⟩, hf,
      hsz => by
    rw [breakout.go]
    have his : i < lab.size := by omega
    split
    · next heq =>
      simp only [beq_iff_eq] at heq
      rw [segN_cons, Array.getElem!_set!_self _ _ _ his,
        segN_congr (fun o ho =>
          Array.getElem!_set!_ne lab i _ prev (by omega)),
        segN_cons lab i len, heq, List.erase_cons_head]
    · next hne =>
      simp only [beq_iff_eq] at hne
      have hki : k ≠ i := by
        intro h
        rw [h] at hkv
        exact hne hkv
      rw [segN_cons,
        breakout_go_outside fuel _ (i + 1) _ i (by omega),
        Array.getElem!_set!_self _ _ _ his,
        breakout_go_seg fuel len _ (i + 1) _
          ⟨k, by omega, by omega, by rw [Array.size_set!]; omega,
            by rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
               exact hkv⟩
          (by omega) (by rw [Array.size_set!]; omega),
        segN_congr (fun o ho =>
          Array.getElem!_set!_ne lab i _ prev (by omega)),
        segN_cons lab i len,
        List.erase_cons_tail (by simp only [beq_iff_eq]; exact hne)]

end Hex.GraphIso.Nauty
