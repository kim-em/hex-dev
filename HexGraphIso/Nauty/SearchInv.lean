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

end Hex.GraphIso.Nauty
