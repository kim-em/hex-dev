/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.TranscriptionInv

public section

/-!
Write-site invariants of `refine` for the quartet induction
(`canonlab_cellsReach`): `refine` writes partition boundaries only at
positions that are open at its level, so closed positions keep their
exact values (`refine_frozen`), and every write is paired with a
`numcells` increment, so an accurate cell count stays accurate
(`refine_bcount`). Both are consequences of one invariant
(`FreezeInv`) threaded through the splitting passes over the ordered,
open-interior cell list (`CellsFresh`).
-/

namespace Hex.GraphIso.Nauty

/-! # Boundary-count arithmetic -/

theorem bcount_succ (ptn : Array Nat) (level m : Nat) :
    bcount ptn level (m + 1) =
      bcount ptn level m + if ptn[m]! ≤ level then 1 else 0 := by
  rw [bcount, bcount, List.range_succ, List.countP_append]
  rcases Decidable.em (ptn[m]! ≤ level) with h | h
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h]
    simp [h]

theorem bcount_congr {ptn ptn' : Array Nat} {level : Nat} :
    ∀ {nn : Nat}, (∀ q, q < nn → ptn'[q]! = ptn[q]!) →
      bcount ptn' level nn = bcount ptn level nn := by
  intro nn
  induction nn with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    rw [bcount_succ, bcount_succ, ih (fun q hq => h q (by omega)),
      h m (by omega)]

/-- Writing `level` at an open position adds exactly one boundary. -/
theorem bcount_set!_open {ptn : Array Nat} {level p : Nat}
    (hps : p < ptn.size) (hopen : ptn[p]! > level) :
    ∀ {nn : Nat}, p < nn →
      bcount (ptn.set! p level) level nn = bcount ptn level nn + 1 := by
  intro nn
  induction nn with
  | zero => omega
  | succ m ih =>
    intro hp
    rcases Decidable.em (p = m) with rfl | hne
    · rw [bcount_succ, bcount_succ,
        Array.getElem!_set!_self _ _ _ hps,
        ite_eq_left (Nat.le_refl level), ite_eq_right (by omega),
        bcount_congr (ptn := ptn) (ptn' := ptn.set! p level)
          (fun q hq => Array.getElem!_set!_ne _ _ _ _ (by omega))]
    · rw [bcount_succ, bcount_succ, ih (by omega),
        Array.getElem!_set!_ne _ _ _ _ hne]
      omega

/-! # Multiplicity coverage of the value window -/

theorem sum_eq_zero' : ∀ {l : List Nat}, (∀ x ∈ l, x = 0) → l.sum = 0
  | [], _ => rfl
  | x :: l, h => by
    rw [List.sum_cons, h x (by simp),
      sum_eq_zero' fun y hy => h y (List.mem_cons.mpr (Or.inr hy))]

theorem sum_map_indicator {c : Nat} :
    ∀ {vs : List Nat}, vs.Pairwise (· < ·) → c ∈ vs →
      (vs.map fun v => if c == v then 1 else 0).sum = 1
  | [], _, hmem => absurd hmem (by simp)
  | v :: vs, hnd, hmem => by
    obtain ⟨hlt, hnd'⟩ := List.pairwise_cons.mp hnd
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · rw [ite_eq_left (by simp)]
      have hz : (vs.map fun v => if c == v then 1 else 0).sum = 0 := by
        refine sum_eq_zero' fun x hx => ?_
        rcases List.mem_map.mp hx with ⟨v', hv', rfl⟩
        rw [ite_eq_right (by
          have := hlt v' hv'
          simp only [beq_iff_eq]
          omega)]
      rw [hz]
    · rw [sum_map_indicator hnd' hmem', ite_eq_right (by
        have hne : c ≠ v := by
          intro he
          rw [he] at hmem'
          have := hlt v hmem'
          omega
        simpa using hne)]

theorem sum_map_countP :
    ∀ (counts : List Nat) {vs : List Nat}, vs.Pairwise (· < ·) →
      (∀ c ∈ counts, c ∈ vs) →
      (vs.map (multOf counts)).sum = counts.length
  | [], vs, _, _ => by
    rw [List.length_nil]
    refine sum_eq_zero' fun x hx => ?_
    rcases List.mem_map.mp hx with ⟨v', _, rfl⟩
    rfl
  | c :: counts, vs, hnd, hmem => by
    have hsplit : vs.map (multOf (c :: counts)) =
        vs.map fun v =>
          (if c == v then 1 else 0) + multOf counts v := by
      refine List.map_congr_left fun v _ => ?_
      rw [multOf, multOf, List.countP_cons]
      rcases Decidable.em (c = v) with rfl | hne
      · rw [ite_eq_left (by simp)]
        omega
      · rw [ite_eq_right (by simpa using hne)]
        omega
    rw [hsplit, sum_map_add, sum_map_indicator hnd (hmem c (by simp)),
      sum_map_countP counts hnd
        (fun x hx => hmem x (List.mem_cons.mpr (Or.inr hx))),
      List.length_cons]
    omega

theorem countValues_pairwise (counts : List Nat) :
    (countValues counts).Pairwise (· < ·) := by
  rw [countValues]
  refine List.pairwise_map.mpr ?_
  refine List.Pairwise.imp ?_ List.pairwise_lt_range
  intro a b h
  omega

/-- The value window's multiplicities cover the whole cell. -/
theorem sum_multOf_countValues (counts : List Nat) :
    ((countValues counts).map (multOf counts)).sum = counts.length :=
  sum_map_countP counts (countValues_pairwise counts)
    fun c hc => mem_countValues
      (foldl_min_le_mem counts (counts.headD 0) c hc)
      (foldl_max_ge_mem counts (counts.headD 0) c hc)

/-! # The freeze invariant -/

/-- Positions closed at `level` in the entry partition keep their
exact values, and the boundary count stays in step with `numcells`. -/
structure FreezeInv (level nn : Nat) (ptn0 : Array Nat) (nc0 : Nat)
    (st : RefineSt) : Prop where
  ptnSize : st.ptn.size = ptn0.size
  labPtn : st.lab.size = st.ptn.size
  frozen : ∀ q : Nat, ptn0[q]! ≤ level → st.ptn[q]! = ptn0[q]!
  count : st.numcells + bcount ptn0 level nn =
    nc0 + bcount st.ptn level nn

/-- A step that touches neither the partition, the count, nor the
labelling size preserves the invariant. -/
theorem FreezeInv.same {level nn : Nat} {ptn0 : Array Nat} {nc0 : Nat}
    {st st' : RefineSt} (h : FreezeInv level nn ptn0 nc0 st)
    (hp : st'.ptn = st.ptn) (hc : st'.numcells = st.numcells)
    (hl : st'.lab.size = st.lab.size) :
    FreezeInv level nn ptn0 nc0 st' :=
  ⟨by rw [hp]; exact h.ptnSize,
    by rw [hl, hp]; exact h.labPtn,
    fun q hq => by rw [hp]; exact h.frozen q hq,
    by rw [hp, hc]; exact h.count⟩

/-- One paired write: `level` at an open in-range position together
with one `numcells` increment. -/
theorem FreezeInv.write {level nn : Nat} {ptn0 : Array Nat} {nc0 : Nat}
    {st st' : RefineSt} {p : Nat} (h : FreezeInv level nn ptn0 nc0 st)
    (hp : st'.ptn = st.ptn.set! p level)
    (hc : st'.numcells = st.numcells + 1)
    (hl : st'.lab.size = st.lab.size)
    (hpn : p < nn) (hpsz : p < st.ptn.size)
    (hopen : st.ptn[p]! > level) :
    FreezeInv level nn ptn0 nc0 st' := by
  refine ⟨by rw [hp, Array.size_set!]; exact h.ptnSize,
    by rw [hl, hp, Array.size_set!]; exact h.labPtn, ?_, ?_⟩
  · intro q hq
    rw [hp]
    have hne : p ≠ q := by
      intro he
      rw [he, h.frozen q hq] at hopen
      omega
    rw [Array.getElem!_set!_ne _ _ _ _ hne]
    exact h.frozen q hq
  · rw [hp, hc, bcount_set!_open hpsz hopen hpn]
    have := h.count
    omega

/-! # The trivial-splitter pass -/

theorem freezeInv_trivialSplit {level nn : Nat} {ptn0 : Array Nat}
    {nc0 : Nat} {st : RefineSt} {cell1 cell2 : Nat} {c1 c2 : Int}
    (hinv : FreezeInv level nn ptn0 nc0 st)
    (hbounds : Int.ofNat cell1 ≤ c2 → c1 ≤ Int.ofNat cell2 →
      cell1 ≤ c2.toNat ∧ c2.toNat < cell2)
    (hfresh : ∀ p, cell1 ≤ p → p < cell2 → st.ptn[p]! > level)
    (hb : cell2 < nn) (hsz : cell2 < st.ptn.size) :
    FreezeInv level nn ptn0 nc0
        (trivialSplit level cell1 cell2 c1 c2 st) ∧
      ∀ q, (q < cell1 ∨ cell2 ≤ q) →
        (trivialSplit level cell1 cell2 c1 c2 st).ptn[q]! =
          st.ptn[q]! := by
  rw [trivialSplit]
  split
  · next hg =>
    obtain ⟨hlo, hhi⟩ := hbounds hg.1 hg.2
    have hopen := hfresh _ hlo hhi
    constructor
    · split
      · split <;>
          exact FreezeInv.write hinv rfl rfl rfl (by omega) (by omega)
            hopen
      · split <;>
          exact FreezeInv.write hinv rfl rfl rfl (by omega) (by omega)
            hopen
    · intro q hq
      have hne : c2.toNat ≠ q := by omega
      split
      · split <;> exact Array.getElem!_set!_ne _ _ _ _ hne
      · split <;> exact Array.getElem!_set!_ne _ _ _ _ hne
  · exact ⟨hinv, fun _ _ => rfl⟩

theorem freezeInv_trivialCell {level nn gRow : Nat} {ptn0 : Array Nat}
    {nc0 : Nat} {st : RefineSt} {cell1 cell2 : Nat}
    (hinv : FreezeInv level nn ptn0 nc0 st)
    (hfresh : ∀ p, cell1 ≤ p → p < cell2 → st.ptn[p]! > level)
    (h12 : cell1 ≤ cell2) (hb : cell2 < nn)
    (hsz : cell2 < st.ptn.size) :
    FreezeInv level nn ptn0 nc0
        (trivialCell level gRow cell1 cell2 st) ∧
      ∀ q, (q < cell1 ∨ cell2 ≤ q) →
        (trivialCell level gRow cell1 cell2 st).ptn[q]! =
          st.ptn[q]! := by
  rw [trivialCell]
  split
  · exact ⟨hinv, fun _ _ => rfl⟩
  · next hne =>
    have hlsz : cell2 < st.lab.size := by
      rw [hinv.labPtn]
      exact hsz
    obtain ⟨hp1, hp2, hlsize, hout, hleft, hright⟩ :=
      splitCellLoop_spec (gRow := gRow) (cell2 + 1 - cell1)
        (cell2 - cell1 + 2) st.lab (Int.ofNat cell1) (Int.ofNat cell2)
        (by simp only [Int.ofNat_eq_natCast]; omega)
        (by
          have : (cell2 : Int) < (st.lab.size : Int) := by
            exact_mod_cast hlsz
          simpa using this)
        (by simp only [Int.ofNat_eq_natCast]; omega) (by omega)
    refine freezeInv_trivialSplit
      (st := { st with
        lab := (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
          (Int.ofNat cell1) (Int.ofNat cell2)).1 })
      (hinv.same rfl rfl hlsize) ?_ hfresh hb hsz
    intro hg1 hg2
    rw [hp2] at hg1 ⊢
    rw [hp1] at hg2
    simp only [Int.ofNat_eq_natCast] at hg1 hg2 ⊢
    omega

/-! # The nontrivial-splitter pass -/

theorem nc_windowStep_eq (level cell1 cell2 v c1 c2 : Nat)
    (maxcell : Int) (st : RefineSt) :
    (windowStep level cell1 cell2 v c1 c2 maxcell st).numcells =
      if c1 = cell1 then st.numcells else st.numcells + 1 := by
  rw [windowStep]
  dsimp only
  rcases hB : (c1 != cell1) with _ | _
  · have hcc : c1 = cell1 := by simpa using hB
    simp only [Bool.false_eq_true, ite_false, ite_eq_left hcc]
    repeat' first | rfl | split
  · have hcc : ¬c1 = cell1 := by simpa using hB
    simp only [ite_true, ite_eq_right hcc]
    repeat' first | rfl | split

/-- The window scan's paired writes: each nonempty group except the
final one writes one fresh boundary, and each nonempty group except
the first counts one new cell, so over a whole cell the two
balance. -/
theorem windowScan_payload {level nn : Nat} {cell1 cell2 : Nat}
    {counts : List Nat} (hb : cell2 < nn) :
    ∀ (vs : List Nat) (c1 : Nat) (maxcell : Int) (st : RefineSt),
      cell1 ≤ c1 →
      c1 + (vs.map (multOf counts)).sum = cell2 + 1 →
      cell2 < st.ptn.size →
      (∀ p, c1 ≤ p → p < cell2 → st.ptn[p]! > level) →
      (windowScan level cell1 cell2 counts vs c1 maxcell
            st).numcells + bcount st.ptn level nn =
        st.numcells +
          bcount (windowScan level cell1 cell2 counts vs c1 maxcell
            st).ptn level nn +
          (if c1 = cell1 ∨ (vs.map (multOf counts)).sum = 0 then 0
            else 1) ∧
      (∀ q : Nat, st.ptn[q]! ≤ level →
        (windowScan level cell1 cell2 counts vs c1 maxcell
          st).ptn[q]! = st.ptn[q]!) ∧
      (∀ q : Nat, (q < c1 ∨ cell2 ≤ q) →
        (windowScan level cell1 cell2 counts vs c1 maxcell
          st).ptn[q]! = st.ptn[q]!) ∧
      (windowScan level cell1 cell2 counts vs c1 maxcell
        st).ptn.size = st.ptn.size ∧
      (windowScan level cell1 cell2 counts vs c1 maxcell
        st).lab = st.lab
  | [], c1, maxcell, st, hc1, htot, hsz, hfresh => by
    rw [windowScan]
    refine ⟨?_, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
    rw [ite_eq_left (Or.inr (by simp))]
    omega
  | v :: vs, c1, maxcell, st, hc1, htot, hsz, hfresh => by
    rw [windowScan]
    have hsum : (List.map (multOf counts) (v :: vs)).sum =
        multOf counts v + (List.map (multOf counts) vs).sum := by
      rw [List.map_cons, List.sum_cons]
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · simp only [ite_eq_left hm]
      generalize (if Int.ofNat (multOf counts v) > maxcell then
        Int.ofNat (multOf counts v) else maxcell) = mc
      have hp1 := ptn_windowStep_eq level cell1 cell2 v c1
        (c1 + multOf counts v) maxcell st
      have hn1 := nc_windowStep_eq level cell1 cell2 v c1
        (c1 + multOf counts v) maxcell st
      have hl1 := lab_windowStep level cell1 cell2 v c1
        (c1 + multOf counts v) maxcell st
      have hs1 : (windowStep level cell1 cell2 v c1
          (c1 + multOf counts v) maxcell st).ptn.size =
          st.ptn.size := by
        rw [hp1]
        split
        · rw [Array.size_set!]
        · rfl
      have hout1 : ∀ q : Nat,
          (q < c1 ∨ cell2 ≤ q ∨ c1 + multOf counts v ≤ q) →
          (windowStep level cell1 cell2 v c1
            (c1 + multOf counts v) maxcell st).ptn[q]! =
            st.ptn[q]! := by
        intro q hq
        rw [hp1]
        split
        · next hle => exact Array.getElem!_set!_ne _ _ _ _ (by omega)
        · rfl
      have hfroz1 : ∀ q : Nat, st.ptn[q]! ≤ level →
          (windowStep level cell1 cell2 v c1
            (c1 + multOf counts v) maxcell st).ptn[q]! =
            st.ptn[q]! := by
        intro q hq
        rw [hp1]
        split
        · next hle =>
          refine Array.getElem!_set!_ne _ _ _ _ ?_
          intro he
          have := hfresh (c1 + multOf counts v - 1) (by omega)
            (by omega)
          rw [he] at this
          omega
        · rfl
      obtain ⟨ihcount, ihfroz, ihout, ihsize, ihlab⟩ :=
        windowScan_payload (counts := counts) (cell1 := cell1) hb vs
          (c1 + multOf counts v) mc
          (windowStep level cell1 cell2 v c1
            (c1 + multOf counts v) maxcell st)
          (by omega) (by omega) (by rw [hs1]; omega)
          (fun p hp1' hp2' => by
            rw [hout1 p (Or.inr (Or.inr hp1'))]
            exact hfresh p (by omega) hp2')
      refine ⟨?_, ?_, ?_, by rw [ihsize, hs1], by rw [ihlab, hl1]⟩
      · rcases Decidable.em ((List.map (multOf counts) vs).sum = 0)
          with hz | hz
        · -- final group: no boundary write, the cell end is the
          -- cell's own
          have hbc1 : bcount (windowStep level cell1 cell2 v c1
              (c1 + multOf counts v) maxcell st).ptn level nn =
              bcount st.ptn level nn := by
            rw [hp1, ite_eq_right (by omega)]
          rw [ite_eq_left (Or.inr hz)] at ihcount
          rw [hbc1] at ihcount
          rcases Decidable.em (c1 = cell1) with hcc | hcc
          · rw [ite_eq_left (Or.inl hcc)]
            rw [ite_eq_left hcc] at hn1
            omega
          · rw [ite_eq_right (by
              intro h
              rcases h with h | h
              · exact hcc h
              · omega)]
            rw [ite_eq_right hcc] at hn1
            omega
        · -- inner group: one paired write
          have hle : c1 + multOf counts v ≤ cell2 := by omega
          have hbc1 : bcount (windowStep level cell1 cell2 v c1
              (c1 + multOf counts v) maxcell st).ptn level nn =
              bcount st.ptn level nn + 1 := by
            rw [hp1, ite_eq_left hle]
            exact bcount_set!_open (by omega)
              (hfresh (c1 + multOf counts v - 1) (by omega)
                (by omega)) (by omega)
          rw [ite_eq_right (by
            intro h
            rcases h with h | h
            · omega
            · exact hz h)] at ihcount
          rw [hbc1] at ihcount
          rcases Decidable.em (c1 = cell1) with hcc | hcc
          · rw [ite_eq_left (Or.inl hcc)]
            rw [ite_eq_left hcc] at hn1
            omega
          · rw [ite_eq_right (by
              intro h
              rcases h with h | h
              · exact hcc h
              · omega)]
            rw [ite_eq_right hcc] at hn1
            omega
      · intro q hq
        rw [ihfroz q (by rw [hfroz1 q hq]; exact hq), hfroz1 q hq]
      · intro q hq
        rw [ihout q (by omega), hout1 q (by omega)]
    · simp only [ite_eq_right hm]
      have hz : multOf counts v = 0 := by omega
      obtain ⟨ihcount, ihfroz, ihout, ihsize, ihlab⟩ :=
        windowScan_payload (counts := counts) hb vs c1 maxcell st hc1
          (by omega) hsz hfresh
      refine ⟨?_, ihfroz, ihout, ihsize, ihlab⟩
      rw [hsum, hz]
      simpa using ihcount

theorem nc_nontrivialFix (cell1 : Nat) (st : RefineSt) :
    (nontrivialFix cell1 st).numcells = st.numcells := by
  rw [nontrivialFix]
  split <;> rfl

theorem freezeInv_nontrivialCell {ctx : Ctx} {level nn workset : Nat}
    {ptn0 : Array Nat} {nc0 : Nat} {st : RefineSt} {cell1 cell2 : Nat}
    (hinv : FreezeInv level nn ptn0 nc0 st)
    (hfresh : ∀ p, cell1 ≤ p → p < cell2 → st.ptn[p]! > level)
    (h12 : cell1 ≤ cell2) (hb : cell2 < nn)
    (hsz : cell2 < st.ptn.size) :
    FreezeInv level nn ptn0 nc0
        (nontrivialCell ctx level workset cell1 cell2 st) ∧
      ∀ q, (q < cell1 ∨ cell2 ≤ q) →
        (nontrivialCell ctx level workset cell1 cell2 st).ptn[q]! =
          st.ptn[q]! := by
  rw [nontrivialCell]
  split
  · exact ⟨hinv, fun _ _ => rfl⟩
  · split
    · exact ⟨hinv.same rfl rfl rfl, fun _ _ => rfl⟩
    · have htot : cell1 + ((countValues (countsOf ctx st.lab workset
          cell1 cell2)).map (multOf (countsOf ctx st.lab workset
            cell1 cell2))).sum = cell2 + 1 := by
        rw [sum_multOf_countValues, countsOf, List.length_map,
          List.length_range]
        omega
      obtain ⟨hcount, hfroz, hout, hsize, hlab⟩ :=
        windowScan_payload (counts := countsOf ctx st.lab workset
          cell1 cell2) hb (countValues (countsOf ctx st.lab workset
          cell1 cell2)) cell1 (-1) st (Nat.le_refl cell1) htot hsz
          hfresh
      rw [ite_eq_left (Or.inl rfl)] at hcount
      rw [nontrivialFix_setLab]
      constructor
      · refine ⟨?_, ?_, ?_, ?_⟩
        · dsimp only
          rw [ptn_nontrivialFix, hsize]
          exact hinv.ptnSize
        · dsimp only
          rw [writeSegment_size, ptn_nontrivialFix, hsize, hlab]
          exact hinv.labPtn
        · intro q hq
          dsimp only
          rw [ptn_nontrivialFix,
            hfroz q (by rw [hinv.frozen q hq]; exact hq)]
          exact hinv.frozen q hq
        · dsimp only
          rw [nc_nontrivialFix, ptn_nontrivialFix]
          have h1 := hinv.count
          omega
      · intro q hq
        dsimp only
        rw [ptn_nontrivialFix]
        exact hout q hq

/-! # Pass plumbing over the cell list -/

/-- The remaining cells of a pass: ordered left to right, in range,
with open interiors in the current state. -/
def CellsFresh (level nn : Nat) (st : RefineSt) :
    List (Nat × Nat) → Prop
  | [] => True
  | (a, b) :: rest => a ≤ b ∧ b < nn ∧
      (∀ p, a ≤ p → p < b → st.ptn[p]! > level) ∧
      (∀ p ∈ rest, b < p.1) ∧ CellsFresh level nn st rest

theorem cellsFresh_congr {level nn b0 : Nat} {st st' : RefineSt}
    (hagree : ∀ q, b0 ≤ q → st'.ptn[q]! = st.ptn[q]!) :
    ∀ {cs : List (Nat × Nat)}, (∀ p ∈ cs, b0 ≤ p.1) →
      CellsFresh level nn st cs → CellsFresh level nn st' cs
  | [], _, _ => trivial
  | (a, b) :: rest, hge, hcf => by
    obtain ⟨hab, hbn, hfresh, hord, hrest⟩ := hcf
    refine ⟨hab, hbn, ?_, hord, ?_⟩
    · intro p hp1 hp2
      rw [hagree p (Nat.le_trans (hge (a, b) (by simp)) hp1)]
      exact hfresh p hp1 hp2
    · exact cellsFresh_congr hagree
        (fun p hp => hge p (List.mem_cons.mpr (Or.inr hp))) hrest

theorem cells_go_ge {ptn : Array Nat} {level nn : Nat} :
    ∀ (fuel c1 : Nat) (p : Nat × Nat),
      p ∈ cells.go ptn level nn fuel c1 → c1 ≤ p.1
  | 0, _, p, hp => absurd hp (by simp [cells.go])
  | fuel + 1, c1, p, hp => by
    rw [cells.go] at hp
    split at hp
    · simp only [List.mem_cons] at hp
      rcases hp with rfl | hmem
      · exact Nat.le_refl _
      · have h1 := cells_go_ge fuel _ p hmem
        have h2 := cellEnd_ge (ptn := ptn) (level := level) (i := c1)
        omega
    · exact absurd hp (by simp)

theorem cellsFresh_cells {level nn : Nat} {st : RefineSt}
    (hnn : st.ptn.size = nn)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    ∀ (fuel c1 : Nat),
      CellsFresh level nn st (cells.go st.ptn level nn fuel c1)
  | 0, c1 => by rw [cells.go]; trivial
  | fuel + 1, c1 => by
    rw [cells.go]
    split
    · next hc1 =>
      refine ⟨cellEnd_ge, ?_, ?_, ?_, cellsFresh_cells hnn hend fuel _⟩
      · rw [← hnn]
        exact cellEnd_lt (by omega) hend
      · intro p hp1 hp2
        rw [cellEnd] at hp2
        exact cellEnd_go_interior _ _ p hp1 hp2
      · intro p hp
        have := cells_go_ge fuel _ p hp
        omega
    · trivial

theorem freezeInv_refineTrivial_go {level nn gRow : Nat}
    {ptn0 : Array Nat} {nc0 : Nat} :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt),
      FreezeInv level nn ptn0 nc0 st →
      nn ≤ st.ptn.size →
      CellsFresh level nn st cs →
      FreezeInv level nn ptn0 nc0 (refineTrivial.go level gRow cs st)
  | [], st, hinv, _, _ => hinv
  | (a, b) :: rest, st, hinv, hnn, hcf => by
    rw [refineTrivial.go]
    obtain ⟨hab, hbn, hfresh, hord, hrest⟩ := hcf
    obtain ⟨hstep, hconf⟩ := freezeInv_trivialCell (gRow := gRow)
      hinv hfresh hab hbn (by omega)
    refine freezeInv_refineTrivial_go rest _ hstep ?_ ?_
    · rw [hstep.ptnSize, ← hinv.ptnSize]
      exact hnn
    · refine cellsFresh_congr (b0 := b)
        (fun q hq => hconf q (Or.inr hq)) ?_ hrest
      intro p hp
      have := hord p hp
      omega

theorem freezeInv_refineNontrivial_go {ctx : Ctx}
    {level nn workset : Nat} {ptn0 : Array Nat} {nc0 : Nat} :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt),
      FreezeInv level nn ptn0 nc0 st →
      nn ≤ st.ptn.size →
      CellsFresh level nn st cs →
      FreezeInv level nn ptn0 nc0
        (refineNontrivial.go ctx level workset cs st)
  | [], st, hinv, _, _ => hinv
  | (a, b) :: rest, st, hinv, hnn, hcf => by
    rw [refineNontrivial.go]
    obtain ⟨hab, hbn, hfresh, hord, hrest⟩ := hcf
    obtain ⟨hstep, hconf⟩ := freezeInv_nontrivialCell (ctx := ctx)
      (workset := workset) hinv hfresh hab hbn (by omega)
    refine freezeInv_refineNontrivial_go rest _ hstep ?_ ?_
    · rw [hstep.ptnSize, ← hinv.ptnSize]
      exact hnn
    · refine cellsFresh_congr (b0 := b)
        (fun q hq => hconf q (Or.inr hq)) ?_ hrest
      intro p hp
      have := hord p hp
      omega

theorem freezeInv_refineStep {ctx : Ctx} {level split1 : Nat}
    {ptn0 : Array Nat} {nc0 : Nat} {st : RefineSt}
    (hinv : FreezeInv level ctx.n ptn0 nc0 st)
    (hnn : ctx.n = ptn0.size)
    (hend0 : ptn0[ptn0.size - 1]! ≤ level) :
    FreezeInv level ctx.n ptn0 nc0
      (refineStep ctx level split1 st) := by
  have hendst : st.ptn[st.ptn.size - 1]! ≤ level := by
    rw [hinv.ptnSize, hinv.frozen (ptn0.size - 1) hend0]
    exact hend0
  have hsz : st.ptn.size = ctx.n := by
    rw [hinv.ptnSize, hnn]
  rw [refineStep]
  dsimp only
  split
  · rw [refineTrivial]
    refine freezeInv_refineTrivial_go _ _ (hinv.same rfl rfl rfl)
      (by dsimp only; omega) ?_
    rw [cells]
    exact cellsFresh_cells (st := { st with
      active := erase st.active split1
      longcode := mash st.longcode (split1 + cellEnd st.ptn level split1) })
      hsz hendst ctx.n 0
  · rw [refineNontrivial]
    dsimp only
    refine freezeInv_refineNontrivial_go _ _ (hinv.same rfl rfl rfl)
      (by dsimp only; omega) ?_
    rw [cells]
    exact cellsFresh_cells (st := { st with
      active := erase st.active split1
      longcode := mash (mash st.longcode
        (split1 + cellEnd st.ptn level split1))
        (cellEnd st.ptn level split1 - split1 + 1) })
      hsz hendst ctx.n 0

theorem freezeInv_refineLoop {ctx : Ctx} {level : Nat}
    {ptn0 : Array Nat} {nc0 : Nat}
    (hnn : ctx.n = ptn0.size) (hend0 : ptn0[ptn0.size - 1]! ≤ level) :
    ∀ (fuel : Nat) (st : RefineSt),
      FreezeInv level ctx.n ptn0 nc0 st →
      FreezeInv level ctx.n ptn0 nc0 (refineLoop ctx level fuel st)
  | 0, st, hinv => hinv
  | fuel + 1, st, hinv => by
    rw [refineLoop]
    split
    · rcases hps : pickSplit st.active st.hint with _ | s
      · exact hinv
      · exact freezeInv_refineLoop hnn hend0 fuel _
          (freezeInv_refineStep hinv hnn hend0)
    · exact hinv

theorem refine_freezeInv {ctx : Ctx} {level : Nat}
    {lab ptn : Array Nat} {active numcells : Nat}
    (hnn : ctx.n = ptn.size) (hls : lab.size = ptn.size)
    (hend : ptn[ptn.size - 1]! ≤ level) :
    FreezeInv level ctx.n ptn numcells
      (refine ctx level lab ptn active numcells) := by
  rw [refine]
  have h := freezeInv_refineLoop (ptn0 := ptn) (nc0 := numcells) hnn
    hend (4 * ctx.n + 8)
    { lab, ptn, active, numcells, hint := 0, maxpos := 0,
      longcode := numcells }
    ⟨rfl, hls, fun _ _ => rfl, rfl⟩
  exact h.same rfl rfl rfl

/-- `refine` keeps every closed position's exact value. -/
theorem refine_frozen {ctx : Ctx} {level : Nat} {lab ptn : Array Nat}
    {active numcells : Nat} (hnn : ctx.n = ptn.size)
    (hls : lab.size = ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    {q : Nat} (hq : ptn[q]! ≤ level) :
    (refine ctx level lab ptn active numcells).ptn[q]! = ptn[q]! :=
  (refine_freezeInv hnn hls hend).frozen q hq

/-- `refine` keeps an accurate cell count accurate. -/
theorem refine_bcount {ctx : Ctx} {level : Nat} {lab ptn : Array Nat}
    {active numcells : Nat} (hnn : ctx.n = ptn.size)
    (hls : lab.size = ptn.size) (hend : ptn[ptn.size - 1]! ≤ level) :
    (refine ctx level lab ptn active numcells).numcells +
        bcount ptn level ctx.n =
      numcells +
        bcount (refine ctx level lab ptn active numcells).ptn level
          ctx.n :=
  (refine_freezeInv hnn hls hend).count

/-! # Target-cell openness -/

/-- A short boundary count exposes an open position. -/
theorem exists_open_of_bcount_lt {ptn : Array Nat} {level : Nat} :
    ∀ {nn : Nat}, bcount ptn level nn < nn →
      ∃ q, q < nn ∧ ptn[q]! > level := by
  intro nn
  induction nn with
  | zero => intro h; omega
  | succ m ih =>
    intro h
    rw [bcount_succ] at h
    rcases Decidable.em (ptn[m]! ≤ level) with hm | hm
    · rw [ite_eq_left hm] at h
      obtain ⟨q, hq1, hq2⟩ := ih (by omega)
      exact ⟨q, by omega, hq2⟩
    · exact ⟨m, by omega, by omega⟩

/-- An open position lies in a nontrivial cell. -/
theorem exists_nontrivial_cell_of_open {ptn : Array Nat}
    {level nn : Nat} (hnn : nn ≤ ptn.size)
    (hend : ptn[ptn.size - 1]! ≤ level) {q : Nat} (hq : q < nn)
    (hopen : ptn[q]! > level) :
    ∃ p ∈ cells ptn level nn, p.1 ≠ p.2 := by
  obtain ⟨p, hpm, hp1, hp2⟩ := cells_cover (ptn := ptn)
    (level := level) (nn := nn) q hq
  refine ⟨p, hpm, ?_⟩
  intro he
  have hic := cells_isCell hnn hend p hpm
  have hq1 : q = p.1 := by omega
  have hend1 := hic.2.2.2
  rw [show p.1 + (p.2 + 1 - p.1) - 1 = p.2 from by omega] at hend1
  rw [hq1, he] at hopen
  omega

/-- The executable target cell of a live state is an in-range
nontrivial cell start, whatever the hint. -/
theorem targetcell_open {ctx : Ctx} {lab ptn : Array Nat}
    {level tcLevel : Nat} {hint : Int} (_hn1 : 1 ≤ level)
    (hsz : ptn.size = ctx.n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hex : ∃ p ∈ cells ptn level ctx.n, p.1 ≠ p.2) :
    ∃ p ∈ cells ptn level ctx.n, p.1 ≠ p.2 ∧
      targetcell ctx lab ptn level tcLevel hint = p.1 := by
  rcases Decidable.em (hint ≥ 0 ∧ ptn[hint.toNat]! > level ∧
      (hint == 0 ∨ ptn[hint.toNat - 1]! ≤ level)) with hg | hg
  · rw [targetcell, ite_eq_left hg]
    obtain ⟨hpos, hopen, hstart⟩ := hg
    have hlt : hint.toNat < ptn.size := by
      rcases Nat.lt_or_ge hint.toNat ptn.size with h | h
      · exact h
      · rw [getElem!_neg _ _ (by omega)] at hopen
        exact absurd hopen (Nat.not_lt.mpr (Nat.zero_le level))
    obtain ⟨p, hpm, hp1, hp2⟩ := cells_cover (ptn := ptn)
      (level := level) (nn := ctx.n) hint.toNat (by omega)
    have hic := cells_isCell (by omega) hend p hpm
    have hstart' : hint.toNat = 0 ∨ ptn[hint.toNat - 1]! ≤ level := by
      rcases hstart with h0 | hb
      · left
        have : hint = 0 := by simpa using h0
        rw [this]
        rfl
      · exact Or.inr hb
    have heq : p.1 = hint.toNat := by
      rcases Nat.lt_or_ge p.1 hint.toNat with hlt1 | hge1
      · exfalso
        have hint1 : ptn[hint.toNat - 1]! > level := by
          refine hic.2.2.1 (hint.toNat - 1) (by omega) ?_
          omega
        rcases hstart' with h0 | hb
        · omega
        · omega
      · omega
    refine ⟨p, hpm, ?_, heq.symm⟩
    intro he
    have hend1 := hic.2.2.2
    rw [show p.1 + (p.2 + 1 - p.1) - 1 = p.2 from by omega] at hend1
    rw [← he, heq] at hend1
    omega
  · have hgneg : ¬((-1 : Int) ≥ 0 ∧ ptn[(-1 : Int).toNat]! > level ∧
        (((-1 : Int) == 0) = true ∨
          ptn[(-1 : Int).toNat - 1]! ≤ level)) := by
      rintro ⟨h0, -⟩
      omega
    have he : targetcell ctx lab ptn level tcLevel hint =
        targetcell ctx lab ptn level tcLevel (-1) := by
      rw [targetcell, targetcell, ite_eq_right hg,
        ite_eq_right hgneg]
    rw [he]
    exact targetcell_nontrivial hex

/-- The executable `maketargetcell` of a live state: an open
nontrivial cell with its exact extent and contents. -/
theorem maketargetcell_open {ctx : Ctx} {lab ptn : Array Nat}
    {level tcLevel : Nat} {hint : Int} (hn1 : 1 ≤ level)
    (hsz : ptn.size = ctx.n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hlive : bcount ptn level ctx.n < ctx.n) :
    ∃ tc len,
      maketargetcell ctx lab ptn level tcLevel hint =
        (tc, worksetOf lab tc (tc + len - 1), len) ∧
      IsCell ptn level tc len ∧ 2 ≤ len ∧ tc + len ≤ ctx.n := by
  obtain ⟨q, hqn, hqopen⟩ := exists_open_of_bcount_lt hlive
  have hex := exists_nontrivial_cell_of_open (by omega) hend hqn
    hqopen
  obtain ⟨p, hpm, hpne, htc⟩ := targetcell_open (lab := lab)
    (tcLevel := tcLevel) (hint := hint) hn1 hsz hend hex
  have hple := cells_le p hpm
  have hpb := cells_bound (nn := ctx.n) (by omega) hend p hpm
  have hic := cells_isCell (by omega) hend p hpm
  have hce : cellEnd ptn level (p.1 + 1) = p.2 := by
    have h0 := cellEnd_of_isCell hic (by omega) (by omega)
    rw [show p.1 + (p.2 + 1 - p.1) - 1 = p.2 from by omega] at h0
    exact h0
  refine ⟨p.1, p.2 + 1 - p.1, ?_, hic, by omega, by omega⟩
  rw [maketargetcell, htc, hce,
    show p.1 + (p.2 + 1 - p.1) - 1 = p.2 from by omega,
    show p.2 - p.1 + 1 = p.2 + 1 - p.1 from by omega]

/-! # The root boundary count -/

theorem countP_eq_sum_map {α : Type} (p : α → Bool) :
    ∀ l : List α,
      l.countP p = (l.map fun x => if p x then 1 else 0).sum
  | [] => rfl
  | x :: l => by
    rw [List.countP_cons, List.map_cons, List.sum_cons,
      countP_eq_sum_map p l]
    omega

theorem countP_mem_range {nn : Nat} :
    ∀ {l : List Nat}, l.Pairwise (· < ·) → (∀ e ∈ l, e < nn) →
      (List.range nn).countP (fun q => decide (q ∈ l)) = l.length
  | [], _, _ => by simp
  | e :: l, hnd, hlt => by
    obtain ⟨hlt', hnd'⟩ := List.pairwise_cons.mp hnd
    rw [countP_eq_sum_map]
    have hsplit : (List.range nn).map
        (fun q => if decide (q ∈ e :: l) then 1 else 0) =
        (List.range nn).map (fun q =>
          (if e == q then 1 else 0) +
          (if decide (q ∈ l) then 1 else 0)) := by
      refine List.map_congr_left fun q _ => ?_
      rcases Decidable.em (q = e) with rfl | hne
      · have hnm : q ∉ l := fun hm => by
          have := hlt' q hm
          omega
        simp [hnm]
      · rcases Decidable.em (q ∈ l) with hm | hm
        · simp [hm, hne, Ne.symm hne]
        · simp [hm, hne, Ne.symm hne]
    rw [hsplit, sum_map_add,
      sum_map_indicator List.pairwise_lt_range
        (List.mem_range.mpr (hlt e (by simp))),
      ← countP_eq_sum_map,
      countP_mem_range hnd' (fun x hx => hlt x (by simp [hx])),
      List.length_cons]
    omega

/-- The initial partition's boundary count is its cell count. -/
theorem bcount_initPtn {n k : Nat} (G : Colored n k) :
    bcount (initPtn n (n + 2) (initialPartition G).2) 1 n =
      (initialPartition G).2.length := by
  have hEnds := initialPartition_snd_eq G
  have hpw : (initialPartition G).2.Pairwise (· < ·) := by
    rw [hEnds]
    exact endsOf_pairwise _ 0
  have hlt : ∀ e ∈ (initialPartition G).2, e < n := by
    intro e he
    have h1 := endsOf_lt _ 0 e (hEnds ▸ he)
    have h2 := totalOf_classes G
    omega
  rw [bcount, ← countP_mem_range hpw hlt]
  refine List.countP_congr fun q hq => ?_
  have hqn := List.mem_range.mp hq
  rw [getElem!_initPtn]
  rcases Decidable.em (q ∈ (initialPartition G).2) with hm | hm
  · rw [ite_eq_left ⟨hm, hqn⟩]
    simp [hm]
  · rw [ite_eq_right (fun hc => hm hc.1), ite_eq_left hqn,
      decide_eq_false (p := n + 2 ≤ 1) (by omega),
      decide_eq_false hm]

/-! # The quartet invariants

The per-node invariant (`SearchOk`) and per-call effect (`SearchOut`)
of the transcribed search, with their composition toolkit. The
quartet induction itself consumes these downstream. -/

variable {n k : Nat}

/-- The per-node invariant of the transcribed search at `level` with
claimed cell count `numcells`. -/
structure SearchOk (G : Colored n k) (level numcells : Nat)
    (st : SearchSt) : Prop where
  labSize : st.lab.size = n
  ptnSize : st.ptn.size = n
  reach : CellsReach G st.lab
  init1 : ∀ q : Nat,
    (initPtn n (n + 2) (initialPartition G).2)[q]! ≤ 1 →
    st.ptn[q]! ≤ 1
  vals : ∀ q : Nat, q < n → st.ptn[q]! ≤ level ∨ st.ptn[q]! = n + 2
  count : numcells = bcount st.ptn level n
  bc : level ≤ bcount st.ptn level n
  canon : st.canonlab = Array.replicate n 0 ∨
    (st.canonlab.size = n ∧ CellsReach G st.canonlab)

/-- What a quartet call leaves behind: sizes kept, reachability kept,
the partition preserved exactly wherever it is (or becomes) closed at
`B`, the labelling permuted only within cells of the entry partition
at `lev`, and `canonlab` kept or installed reached. -/
structure SearchOut (G : Colored n k) (B lev : Nat)
    (st st' : SearchSt) : Prop where
  labSize : st'.lab.size = st.lab.size
  ptnSize : st'.ptn.size = st.ptn.size
  reach : CellsReach G st'.lab
  low : ∀ q : Nat, st.ptn[q]! ≤ B ∨ st'.ptn[q]! ≤ B →
    st'.ptn[q]! = st.ptn[q]!
  perm : cellsPerm st.ptn lev st.lab st'.lab
  canon : st'.canonlab = st.canonlab ∨
    (st'.canonlab.size = n ∧ CellsReach G st'.canonlab)

theorem SearchOut.refl (G : Colored n k) (B lev : Nat)
    {st : SearchSt} (hreach : CellsReach G st.lab) :
    SearchOut G B lev st st :=
  ⟨rfl, rfl, hreach, fun _ _ => rfl, cellsPerm_refl _ _ _, Or.inl rfl⟩

/-- A quartet call cannot move the entry of a singleton cell. -/
theorem SearchOut.atSingleton {G : Colored n k} {B lev : Nat}
    {st st' : SearchSt} (h : SearchOut G B lev st st') {a : Nat}
    (hc : IsCell st.ptn lev a 1) : st'.lab[a]! = st.lab[a]! :=
  (cellsPerm_singleton h.perm hc).symm

/-- The exact-preservation clause fixes the boundary count. -/
theorem bcount_eq_of_low {ptn ptn' : Array Nat} {lev : Nat}
    (h : ∀ q : Nat, ptn[q]! ≤ lev ∨ ptn'[q]! ≤ lev →
      ptn'[q]! = ptn[q]!) (nn : Nat) :
    bcount ptn' lev nn = bcount ptn lev nn := by
  rw [bcount, bcount]
  refine List.countP_congr fun q _ => ?_
  rcases Decidable.em (ptn[q]! ≤ lev) with h1 | h1
  · rw [h q (Or.inl h1)]
  · rcases Decidable.em (ptn'[q]! ≤ lev) with h2 | h2
    · rw [h q (Or.inr h2)] at h2
      exact absurd h2 h1
    · rw [decide_eq_false h2, decide_eq_false h1]

/-- The exact-preservation clause keeps cells intact. -/
theorem isCell_of_low {ptn ptn' : Array Nat} {lev a len : Nat}
    (h : ∀ q : Nat, ptn[q]! ≤ lev ∨ ptn'[q]! ≤ lev →
      ptn'[q]! = ptn[q]!)
    (hc : IsCell ptn lev a len) : IsCell ptn' lev a len := by
  obtain ⟨h0, hstart, hint, hend⟩ := hc
  refine ⟨h0, ?_, ?_, ?_⟩
  · rcases hstart with h1 | h1
    · exact Or.inl h1
    · right
      rw [h _ (Or.inl h1)]
      exact h1
  · intro i hi1 hi2
    have hop := hint i hi1 hi2
    rcases Decidable.em (ptn'[i]! ≤ lev) with h2 | h2
    · rw [h i (Or.inr h2)] at h2
      omega
    · omega
  · rw [h _ (Or.inl hend)]
    exact hend

/-- Under the level dichotomy, the boundary count is level-blind one
step up. -/
theorem bcount_succ_of_vals {ptn : Array Nat} {lev nn : Nat}
    (hvals : ∀ q : Nat, q < nn → ptn[q]! ≤ lev ∨ ptn[q]! = nn + 2)
    (hlev : lev + 1 < nn + 2) :
    bcount ptn (lev + 1) nn = bcount ptn lev nn := by
  rw [bcount, bcount]
  refine List.countP_congr fun q hq => ?_
  have hqn := List.mem_range.mp hq
  rcases hvals q hqn with h | h
  · rw [decide_eq_true (by omega : ptn[q]! ≤ lev + 1),
      decide_eq_true h]
  · rw [decide_eq_false (by omega), decide_eq_false (by omega)]

/-- Compose two call effects at matching bounds. -/
theorem SearchOut.trans {G : Colored n k} {B : Nat}
    {st1 st2 st3 : SearchSt} (h12 : SearchOut G B B st1 st2)
    (h23 : SearchOut G B B st2 st3) : SearchOut G B B st1 st3 := by
  refine ⟨h23.labSize.trans h12.labSize,
    h23.ptnSize.trans h12.ptnSize, h23.reach, ?_, ?_, ?_⟩
  · intro q hq
    rcases hq with h1 | h1
    · rw [h23.low q (Or.inl (by rw [h12.low q (Or.inl h1)]; exact h1)),
        h12.low q (Or.inl h1)]
    · have h2 := h23.low q (Or.inr h1)
      rw [h2] at h1
      rw [h2, h12.low q (Or.inr h1)]
  · refine cellsPerm_trans h12.perm ?_
    intro a len hc
    exact h23.perm a len (isCell_of_low h12.low hc)
  · rcases h23.canon with h | h
    · rw [h]
      exact h12.canon
    · exact Or.inr h

/-- Weaken the preservation bound. -/
theorem SearchOut.mono {G : Colored n k} {B B' lev : Nat}
    {st st' : SearchSt} (h : SearchOut G B lev st st')
    (hB : B' ≤ B) : SearchOut G B' lev st st' :=
  ⟨h.labSize, h.ptnSize, h.reach,
    fun q hq => h.low q (by omega), h.perm, h.canon⟩

/-! # Quartet step helpers -/

theorem elem_ne_zero {s v : Nat} (h : elem s v = true) :
    s ≠ 0 := by
  rintro rfl
  rw [elem, Nat.zero_testBit] at h
  cases h

theorem mem_segN_iff {lab : Array Nat} {tc len v : Nat} :
    v ∈ segN lab tc len ↔ ∃ o, o < len ∧ lab[tc + o]! = v := by
  rw [segN]
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨o, ho, rfl⟩
    exact ⟨o, List.mem_range.mp ho, rfl⟩
  · rintro ⟨o, ho, rfl⟩
    exact List.mem_map.mpr ⟨o, List.mem_range.mpr ho, rfl⟩

theorem breakout_ptn (lab ptn : Array Nat)
    (lev tc tv : Nat) :
    (breakout lab ptn lev tc tv).2.1 = ptn.set! tc lev := rfl

theorem breakout_lab_size (lab ptn : Array Nat)
    (lev tc tv : Nat) :
    (breakout lab ptn lev tc tv).1.size = lab.size := by
  rw [breakout]
  exact breakout_go_size _ _ _ _

/-- The end of the partition stays closed: position `n - 1` is an
initial boundary. -/
theorem searchOk_end {G : Colored n k}
    {level numcells : Nat} {st : SearchSt} (hn0 : 0 < n)
    (hok : SearchOk G level numcells st) (h1 : 1 ≤ level) :
    st.ptn[st.ptn.size - 1]! ≤ level := by
  have hinitEnd := (initial_nodeOk G hn0).ptnEnd
  rw [size_initPtn] at hinitEnd
  rw [hok.ptnSize]
  have := hok.init1 (n - 1) hinitEnd
  omega

/-- The invariant survives an iteration whose net effect preserves
the closed positions, provided the final partition satisfies the
level dichotomy (which `recover` restores unconditionally). -/
theorem searchOk_of_out {G : Colored n k}
    {level numcells : Nat} {st st' : SearchSt}
    (hok : SearchOk G level numcells st) (h1 : 1 ≤ level)
    (hout : SearchOut G level level st st')
    (hvals : ∀ q : Nat, q < n →
      st'.ptn[q]! ≤ level ∨ st'.ptn[q]! = n + 2) :
    SearchOk G level numcells st' := by
  refine ⟨hout.labSize.trans hok.labSize,
    hout.ptnSize.trans hok.ptnSize, hout.reach, ?_, hvals, ?_, ?_, ?_⟩
  · intro q hq
    have h0 := hok.init1 q hq
    rw [hout.low q (Or.inl (by omega))]
    exact h0
  · rw [hok.count, bcount_eq_of_low hout.low]
  · rw [bcount_eq_of_low hout.low]
    exact hok.bc
  · rcases hout.canon with h | h
    · rw [h]
      exact hok.canon
    · exact Or.inr h

/-- Individualizing a target-cell vertex yields the child invariant
one level down with one more cell. -/
theorem breakout_searchOk {G : Colored n k}
    {level numcells tc len o : Nat} {st st' : SearchSt} (hn0 : 0 < n)
    (hok : SearchOk G level numcells st) (h1 : 1 ≤ level)
    (hcell : IsCell st.ptn level tc len) (hlen2 : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len)
    (hl : st'.lab =
      (breakout st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1)
    (hp : st'.ptn = st.ptn.set! tc (level + 1))
    (hc : st'.canonlab = st.canonlab) :
    SearchOk G (level + 1) (numcells + 1) st' := by
  have htcopen : st.ptn[tc]! > level :=
    hcell.2.2.1 tc (Nat.le_refl tc) (by omega)
  have htcinf : st.ptn[tc]! = n + 2 := by
    rcases hok.vals tc (by omega) with h | h
    · omega
    · exact h
  have hlevn : level ≤ n := Nat.le_trans hok.bc (bcount_le _ _ _)
  have hbsucc : bcount st.ptn (level + 1) n = bcount st.ptn level n :=
    bcount_succ_of_vals hok.vals (by omega)
  have hbnew : bcount (st.ptn.set! tc (level + 1)) (level + 1) n =
      bcount st.ptn level n + 1 := by
    rw [bcount_set!_open (by rw [hok.ptnSize]; omega) (by omega)
      (by omega), hbsucc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hl, breakout_lab_size]
    exact hok.labSize
  · rw [hp, Array.size_set!]
    exact hok.ptnSize
  · rw [hl]
    exact breakout_cellsReach hn0 hok.reach hcell
      (by rw [hok.ptnSize]; exact hrange) hok.labSize hok.ptnSize ho
      (searchOk_end hn0 hok h1)
      (fun q hq => Nat.le_trans (hok.init1 q hq) h1)
  · intro q hq
    rw [hp]
    have hne : tc ≠ q := by
      intro he
      have := hok.init1 q hq
      rw [← he] at this
      omega
    rw [Array.getElem!_set!_ne _ _ _ _ hne]
    exact hok.init1 q hq
  · intro q hqn
    rw [hp]
    rcases Decidable.em (tc = q) with rfl | hne
    · rw [Array.getElem!_set!_self _ _ _ (by rw [hok.ptnSize]; omega)]
      exact Or.inl (Nat.le_refl _)
    · rw [Array.getElem!_set!_ne _ _ _ _ hne]
      rcases hok.vals q hqn with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
  · rw [hp, hbnew, ← hok.count]
  · rw [hp, hbnew]
    have := hok.bc
    omega
  · rw [hc]
    exact hok.canon

/-- The effect of individualization followed by a child call, in the
parent loop's frame. -/
theorem breakout_child_out {G : Colored n k}
    {level numcells tc len o : Nat} {st stC stD : SearchSt}
    (hn0 : 0 < n) (hok : SearchOk G level numcells st) (h1 : 1 ≤ level)
    (hcell : IsCell st.ptn level tc len) (hlen2 : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len)
    (hCout : SearchOut G level (level + 1) stC stD)
    (hl : stC.lab =
      (breakout st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1)
    (hp : stC.ptn = st.ptn.set! tc (level + 1))
    (hc : stC.canonlab = st.canonlab) :
    SearchOut G level level st stD := by
  have htcopen : st.ptn[tc]! > level :=
    hcell.2.2.1 tc (Nat.le_refl tc) (by omega)
  have hCok := breakout_searchOk hn0 hok h1 hcell hlen2 hrange ho
    hl hp hc
  have hlowC : ∀ q : Nat, st.ptn[q]! ≤ level ∨ stC.ptn[q]! ≤ level →
      stC.ptn[q]! = st.ptn[q]! := by
    intro q hq
    rw [hp]
    rcases Decidable.em (tc = q) with rfl | hne
    · exfalso
      rcases hq with h | h
      · omega
      · rw [hp, Array.getElem!_set!_self _ _ _
          (by rw [hok.ptnSize]; omega)] at h
        omega
    · rw [Array.getElem!_set!_ne _ _ _ _ hne]
  refine ⟨?_, ?_, hCout.reach, ?_, ?_, ?_⟩
  · rw [hCout.labSize, hl, breakout_lab_size]
  · rw [hCout.ptnSize, hp, Array.size_set!]
  · intro q hq
    rcases hq with hq1 | hq1
    · have hCq : stC.ptn[q]! = st.ptn[q]! := hlowC q (Or.inl hq1)
      rw [hCout.low q (Or.inl (by rw [hCq]; omega)), hCq]
    · have hDq := hCout.low q (Or.inr (by omega))
      rw [hDq] at hq1 ⊢
      exact hlowC q (Or.inr hq1)
  · -- the labelling moves only within cells: individualize, then the
    -- child's finer moves coarsen to this level
    have hperm1 : cellsPerm st.ptn level st.lab stC.lab := by
      rw [hl]
      exact breakout_cellsPerm hcell
        (by rw [hok.ptnSize]; exact hrange)
        (by rw [hok.labSize, hok.ptnSize]) ho
    have hperm2 : cellsPerm st.ptn level stC.lab stD.lab := by
      refine cellsPerm_coarsen (ptnF := stC.ptn) (levF := level + 1)
        (by rw [hCok.ptnSize, hok.ptnSize])
        (by rw [hCok.labSize, hCok.ptnSize])
        (by rw [hCout.labSize, hCok.labSize, hCok.ptnSize])
        hCout.perm (searchOk_end hn0 hCok (by omega))
        (searchOk_end hn0 hok h1) ?_
      intro q hq
      rw [hlowC q (Or.inl hq)]
      omega
    exact cellsPerm_trans hperm1 hperm2
  · rcases hCout.canon with h | h
    · rw [h, hc]
      exact Or.inl rfl
    · exact Or.inr h

theorem SearchOut.congr {G : Colored n k} {B lev : Nat}
    {st st' st'' : SearchSt} (h : SearchOut G B lev st st')
    (hl : st''.lab = st'.lab) (hp : st''.ptn = st'.ptn)
    (hc : st''.canonlab = st'.canonlab) : SearchOut G B lev st st'' :=
  ⟨by rw [hl]; exact h.labSize, by rw [hp]; exact h.ptnSize,
    by rw [hl]; exact h.reach,
    fun q hq => by
      rw [hp]
      exact h.low q (by rw [hp] at hq; exact hq),
    by rw [hl]; exact h.perm,
    by rw [hc]; exact h.canon⟩

theorem searchOut_id {G : Colored n k} (B lev : Nat)
    {stX : SearchSt} {labR : Array Nat} (hl : stX.lab = labR)
    (hreach : CellsReach G labR) : SearchOut G B lev stX stX :=
  SearchOut.refl G B lev (by rw [hl]; exact hreach)

theorem match_option_or {α γ : Type} {P : γ → Prop}
    (x : Option α) (f : α → γ) (g : γ)
    (hf : ∀ a, P (f a)) (hg : P g) :
    P (match x with | some a => f a | none => g) := by
  rcases x with _ | a
  · exact hg
  · exact hf a

/-- The invariant after `refine`, for any state carrying the refined
labelling and partition. -/
theorem refine_searchOk {G : Colored n k} {ctx : Ctx}
    (hn : ctx.n = n) (hn0 : 0 < n) {level numcells : Nat}
    {st st2 : SearchSt} (hok : SearchOk G level numcells st)
    (h1 : 1 ≤ level)
    (hl : st2.lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab)
    (hp : st2.ptn =
      (refine ctx level st.lab st.ptn st.active numcells).ptn)
    (hcanon : st2.canonlab = st.canonlab ∨
      (st2.canonlab.size = n ∧ CellsReach G st2.canonlab)) :
    SearchOk G level
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      st2 := by
  have hend := searchOk_end hn0 hok h1
  have hnn : ctx.n ≤ st.ptn.size := by
    rw [hok.ptnSize, hn]
    exact Nat.le_refl n
  have hnn' : ctx.n = st.ptn.size := by
    rw [hok.ptnSize, hn]
  have hls : st.lab.size = st.ptn.size := by
    rw [hok.labSize, hok.ptnSize]
  have hRinv := refine_refInv (ctx := ctx) (level := level)
    (lab := st.lab) (ptn := st.ptn) (active := st.active)
    (numcells := numcells) hnn hls hend
  have hcount := refine_bcount (ctx := ctx) (level := level)
    (lab := st.lab) (ptn := st.ptn) (active := st.active)
    (numcells := numcells) hnn' hls hend
  rw [hn] at hcount
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hl, hRinv.labSize, hok.labSize]
  · rw [hp, hRinv.ptnSize, hok.ptnSize]
  · rw [hl]
    exact refine_cellsReach hn hn0 hok.reach hok.labSize hok.ptnSize
      hend (fun q hq => Nat.le_trans (hok.init1 q hq) h1)
  · intro q hq
    rw [hp, refine_frozen hnn' hls hend
      (Nat.le_trans (hok.init1 q hq) h1)]
    exact hok.init1 q hq
  · intro q hqn
    rw [hp]
    rcases ptn_refine_vals ctx level st.lab st.ptn st.active
      numcells q with he | he
    · rw [he]
      exact hok.vals q hqn
    · rw [he]
      exact Or.inl (Nat.le_refl _)
  · rw [hp]
    have h0 := hok.count
    omega
  · rw [hp]
    exact Nat.le_trans hok.bc (bcount_mono hRinv.grow)
  · rcases hcanon with h | h
    · rw [h]
      exact hok.canon
    · exact Or.inr h

/-- Compose the refine step with the rest of a node's work. -/
theorem refine_loop_out {G : Colored n k} {ctx : Ctx}
    (hn : ctx.n = n) (hn0 : 0 < n) {level numcells : Nat}
    {st STL stX : SearchSt} (hok : SearchOk G level numcells st)
    (h1 : 1 ≤ level)
    (hl : STL.lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab)
    (hp : STL.ptn =
      (refine ctx level st.lab st.ptn st.active numcells).ptn)
    (hcanon : STL.canonlab = st.canonlab ∨
      (STL.canonlab.size = n ∧ CellsReach G STL.canonlab))
    (hXout : SearchOut G level level STL stX) :
    SearchOut G (level - 1) level st stX := by
  have hend := searchOk_end hn0 hok h1
  have hnn : ctx.n ≤ st.ptn.size := by
    rw [hok.ptnSize, hn]
    exact Nat.le_refl n
  have hnn' : ctx.n = st.ptn.size := by
    rw [hok.ptnSize, hn]
  have hls : st.lab.size = st.ptn.size := by
    rw [hok.labSize, hok.ptnSize]
  have hRinv := refine_refInv (ctx := ctx) (level := level)
    (lab := st.lab) (ptn := st.ptn) (active := st.active)
    (numcells := numcells) hnn hls hend
  have hfrz : ∀ q : Nat, st.ptn[q]! ≤ level → STL.ptn[q]! =
      st.ptn[q]! := by
    intro q hq
    rw [hp, refine_frozen hnn' hls hend hq]
  have hendL : STL.ptn[STL.ptn.size - 1]! ≤ level := by
    have hsz : STL.ptn.size = st.ptn.size := by
      rw [hp, hRinv.ptnSize]
    rw [hsz, hfrz _ hend]
    exact hend
  refine ⟨?_, ?_, hXout.reach, ?_, ?_, ?_⟩
  · rw [hXout.labSize, hl, hRinv.labSize]
  · rw [hXout.ptnSize, hp, hRinv.ptnSize]
  · intro q hq
    rcases hq with hq1 | hq1
    · have hLq : STL.ptn[q]! = st.ptn[q]! := hfrz q (by omega)
      rw [hXout.low q (Or.inl (by rw [hLq]; omega)), hLq]
    · have hXq := hXout.low q (Or.inr (by omega))
      rw [hXq] at hq1 ⊢
      rw [hp] at hq1 ⊢
      rcases ptn_refine_vals ctx level st.lab st.ptn st.active
        numcells q with he | he
      · rw [he]
      · rw [he] at hq1
        omega
  · refine cellsPerm_trans (hl ▸ hRinv.perm : cellsPerm st.ptn level
      st.lab STL.lab) ?_
    refine cellsPerm_coarsen (ptnF := STL.ptn) (levF := level)
      (by rw [hp, hRinv.ptnSize]) ?_ ?_ hXout.perm hendL hend ?_
    · rw [hl, hRinv.labSize, hls, hp, hRinv.ptnSize]
    · rw [hXout.labSize, hl, hRinv.labSize, hls, hp, hRinv.ptnSize]
    · intro q hq
      rw [hfrz q hq]
      exact hq
  · rcases hXout.canon with h | h
    · rw [h]
      rcases hcanon with h2 | h2
      · rw [h2]
        exact Or.inl rfl
      · exact Or.inr h2
    · exact Or.inr h

end Hex.GraphIso.Nauty
