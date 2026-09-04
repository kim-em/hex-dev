/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeLocatedProof

public section

/-!
Preservation rules for the active-frame reach ledger.
-/

namespace Hex.GraphIso.Nauty

/-- Refinement preserves an existing singleton cell. -/
theorem isCell_refine_one {ctx : Ctx} {level active numcells a : Nat}
    {lab ptn : Array Nat} (hnn : ctx.n = ptn.size)
    (hls : lab.size = ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    (hc : IsCell ptn level a 1) :
    IsCell (Nauty.refine ctx level lab ptn active numcells).ptn
      level a 1 := by
  obtain ⟨hpos, hstart, _, hclose⟩ := hc
  refine ⟨hpos, ?_, ?_, ?_⟩
  · rcases hstart with rfl | hstart
    · exact Or.inl rfl
    · right
      rw [refine_frozen hnn hls hend hstart]
      exact hstart
  · intro i hi hlt
    omega
  · have hclose' : ptn[a]! ≤ level := by simpa using hclose
    change (Nauty.refine ctx level lab ptn active numcells).ptn[a]! ≤ level
    rw [refine_frozen hnn hls hend hclose']
    exact hclose'

/-- Splitting a different non-singleton cell preserves a singleton. -/
theorem isCell_set_miss {ptn : Array Nat} {level a tc len : Nat}
    (ha : IsCell ptn level a 1) (ht : IsCell ptn level tc len)
    (hlen : 2 ≤ len) :
    IsCell (ptn.set! tc (level + 1)) (level + 1) a 1 := by
  have hne : tc ≠ a ∧ tc ≠ a - 1 := by
    rcases isCell_disjoint_or_eq ha ht with hleft | hright | heq
    · constructor <;> omega
    · constructor <;> omega
    · omega
  obtain ⟨hpos, hstart, _, hclose⟩ := ha
  refine ⟨hpos, ?_, ?_, ?_⟩
  · rcases hstart with rfl | hstart
    · exact Or.inl rfl
    · right
      rw [Array.getElem!_set!_ne _ _ _ _ hne.2]
      omega
  · intro i hi hlt
    omega
  · have hclose' : ptn[a]! ≤ level := by simpa using hclose
    simpa using (show (ptn.set! tc (level + 1))[a]! ≤ level + 1 by
      rw [Array.getElem!_set!_ne _ _ _ _ hne.1]
      omega)

/-- Reindex frame reach across unchanged labelling and partition fields. -/
theorem TrailOk.stateEq {ctx : Ctx} {level : Nat} {st st' : SearchSt}
    {trail : FrameTrail} (h : TrailOk ctx level st trail)
    (hlab : st'.lab = st.lab) (hptn : st'.ptn = st.ptn) :
    TrailOk ctx level st' trail := by
  constructor
  · intro target entry hlt hentry
    rw [hlab]
    exact h.reach target entry hlt hentry
  · exact h.ptnSize
  · exact h.endClosed
  · intro target entry hlt hentry q hq
    rw [hptn]
    exact h.frozen target entry hlt hentry q hq
  · intro target entry hlt hentry
    obtain ⟨len, hcell, hoff, hsplit, hsingle, hat⟩ :=
      h.picked target entry hlt hentry
    exact ⟨len, hcell, hoff, by rw [hptn]; exact hsplit,
      by rw [hptn]; exact hsingle, by rw [hlab]; exact hat⟩

/-- Refinement preserves reach from every active ancestor and leaves all
of their closed boundaries untouched. -/
theorem TrailOk.refine {ctx : Ctx} {level active numcells : Nat}
    {st out : SearchSt} {trail : FrameTrail}
    (h : TrailOk ctx level st trail)
    (hls : st.lab.size = ctx.n) (hps : st.ptn.size = ctx.n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hlab : out.lab =
      (Nauty.refine ctx level st.lab st.ptn active numcells).lab)
    (hptn : out.ptn =
      (Nauty.refine ctx level st.lab st.ptn active numcells).ptn) :
    TrailOk ctx level out trail := by
  constructor
  · intro target entry hlt hentry
    rw [hlab]
    apply refine_reachAt (h.reach target entry hlt hentry)
    · rw [hps]
      exact Nat.le_refl _
    · rw [h.ptnSize target entry hlt hentry, hps]
    · rw [hls, hps]
    · exact hend
    · exact h.endClosed target entry hlt hentry
    · intro q hq
      rw [h.frozen target entry hlt hentry q hq]
      omega
  · exact h.ptnSize
  · exact h.endClosed
  · intro target entry hlt hentry q hq
    rw [hptn]
    have hf := h.frozen target entry hlt hentry q hq
    calc
      (Nauty.refine ctx level st.lab st.ptn active numcells).ptn[q]! =
          st.ptn[q]! := by
        apply refine_frozen hps.symm
          (by rw [hls, hps]) hend
        rw [hf]
        omega
      _ = entry.frame.rsPtn[q]! := hf
  · intro target entry hlt hentry
    obtain ⟨len, hcell, hoff, hsplit, hsingle, hat⟩ :=
      h.picked target entry hlt hentry
    refine ⟨len, hcell, hoff, ?_, ?_, ?_⟩
    · rw [hptn]
      calc
        (Nauty.refine ctx level st.lab st.ptn active
            numcells).ptn[entry.frame.tc]! = st.ptn[entry.frame.tc]! := by
          apply refine_frozen hps.symm (by rw [hls, hps]) hend
          rw [hsplit]
          omega
        _ = target + 1 := hsplit
    · rw [hptn]
      exact isCell_refine_one hps.symm (by rw [hls, hps]) hend hsingle
    · rw [hlab]
      exact (refine_fixes_singleton (by rw [hps]; exact Nat.le_refl _)
        (by rw [hls, hps]) hend hsingle).trans hat

/-- Leaf processing changes neither the current labelling nor partition. -/
theorem TrailOk.processnode {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt} {trail : FrameTrail}
    (h : TrailOk ctx level st trail) :
    TrailOk ctx level (Nauty.processnode ctx level numcells st).2 trail := by
  obtain ⟨hlab, hptn, _, _, _, _, _, _, _⟩ :=
    processnode_frames ctx level numcells st
  exact h.stateEq hlab hptn

/-- Reopening to an ancestor preserves every older active frame. -/
theorem TrailOk.recover {ctx : Ctx} {current level inf : Nat}
    {st : SearchSt} {trail : FrameTrail}
    (h : TrailOk ctx current st trail) (hle : level ≤ current) :
    TrailOk ctx level (Nauty.recover ctx.n inf level st) trail := by
  constructor
  · intro target entry hlt hentry
    rw [recover_lab]
    exact h.reach target entry (Nat.lt_of_lt_of_le hlt hle) hentry
  · intro target entry hlt hentry
    exact h.ptnSize target entry (Nat.lt_of_lt_of_le hlt hle) hentry
  · intro target entry hlt hentry
    exact h.endClosed target entry (Nat.lt_of_lt_of_le hlt hle) hentry
  · intro target entry hlt hentry q hq
    have hf := h.frozen target entry
      (Nat.lt_of_lt_of_le hlt hle) hentry q hq
    rw [recover_ptn]
    rw [ite_eq_right]
    · exact hf
    · intro hc
      rw [hf] at hc
      omega
  · intro target entry hlt hentry
    have hlt' := Nat.lt_of_lt_of_le hlt hle
    obtain ⟨len, hcell, hoff, hsplit, _, hat⟩ :=
      h.picked target entry hlt' hentry
    have hsplit' : (Nauty.recover ctx.n inf level st).ptn[entry.frame.tc]! =
        target + 1 := by
      rw [recover_ptn, ite_eq_right]
      · exact hsplit
      · intro hc
        rw [hsplit] at hc
        omega
    refine ⟨len, hcell, hoff, hsplit', ?_, ?_⟩
    · refine ⟨Nat.one_pos, ?_, ?_, ?_⟩
      · rcases hcell.2.1 with hzero | hstart
        · exact Or.inl hzero
        · right
          have hf := h.frozen target entry hlt' hentry
            (entry.frame.tc - 1) hstart
          rw [recover_ptn, ite_eq_right]
          · rw [hf]
            omega
          · intro hc
            rw [hf] at hc
            omega
      · intro i hi hbound
        omega
      · change (Nauty.recover ctx.n inf level st).ptn[entry.frame.tc]! ≤
          level
        rw [hsplit']
        omega
    · rw [recover_lab]
      exact hat

/-- Individualization extends the active trail with the selected parent
child while preserving reach from every older frame. -/
theorem TrailOk.push {ctx : Ctx} {level specFuel numcells tc len o : Nat}
    {codes : List Nat} {st out : SearchSt} {trail : FrameTrail}
    (h : TrailOk ctx level st trail)
    (hls : st.lab.size = ctx.n) (hps : st.ptn.size = ctx.n)
    (hinj : LabInj st.lab st.lab.size)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ ctx.n)
    (ho : o < len)
    (hlab : out.lab =
      (breakout st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1)
    (hptn : out.ptn = st.ptn.set! tc (level + 1)) :
    TrailOk ctx (level + 1) out
      (trail.push level
        ⟨sweepFrame specFuel codes st.lab st.ptn tc numcells, o⟩) := by
  let pushed : TrailEntry :=
    ⟨sweepFrame specFuel codes st.lab st.ptn tc numcells, o⟩
  constructor
  · intro target entry hlt hentry
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hold | hhere
    · rw [FrameTrail.push_of_ne _ pushed (Nat.ne_of_lt hold)] at hentry
      rw [hlab]
      apply breakout_reachAt (h.reach target entry hold hentry) hcell
      · rw [hps]
        exact hrange
      · rw [h.ptnSize target entry hold hentry, hps]
      · rw [hls, hps]
      · exact ho
      · exact hend
      · exact h.endClosed target entry hold hentry
      · intro q hq
        rw [h.frozen target entry hold hentry q hq]
        omega
    · subst target
      change (trail.push level pushed) level = some entry at hentry
      rw [FrameTrail.push_self] at hentry
      have he : pushed = entry := Option.some.inj hentry
      subst entry
      change cellsPerm st.ptn level st.lab out.lab
      rw [hlab]
      exact breakout_cellsPerm hcell
        (by rw [hps]; exact hrange) (by rw [hls, hps]) ho
  · intro target entry hlt hentry
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hold | hhere
    · rw [FrameTrail.push_of_ne _ pushed (Nat.ne_of_lt hold)] at hentry
      exact h.ptnSize target entry hold hentry
    · subst target
      change (trail.push level pushed) level = some entry at hentry
      rw [FrameTrail.push_self] at hentry
      have he : pushed = entry := Option.some.inj hentry
      subst entry
      simpa only [pushed, sweepFrame] using hps
  · intro target entry hlt hentry
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hold | hhere
    · rw [FrameTrail.push_of_ne _ pushed (Nat.ne_of_lt hold)] at hentry
      exact h.endClosed target entry hold hentry
    · subst target
      change (trail.push level pushed) level = some entry at hentry
      rw [FrameTrail.push_self] at hentry
      have he : pushed = entry := Option.some.inj hentry
      subst entry
      simpa only [pushed, sweepFrame] using hend
  · intro target entry hlt hentry q hq
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hold | hhere
    · rw [FrameTrail.push_of_ne _ pushed (Nat.ne_of_lt hold)] at hentry
      have hf := h.frozen target entry hold hentry q hq
      have hne : tc ≠ q := by
        intro heq
        subst q
        have hopen := hcell.2.2.1 tc (Nat.le_refl tc) (by omega)
        have hclosed : st.ptn[tc]! ≤ level := calc
          st.ptn[tc]! = entry.frame.rsPtn[tc]! := hf
          _ ≤ target := hq
          _ ≤ level := Nat.le_of_lt hold
        exact (Nat.not_lt_of_ge hclosed hopen).elim
      rw [hptn, Array.getElem!_set!_ne _ _ _ _ hne]
      exact hf
    · subst target
      change (trail.push level pushed) level = some entry at hentry
      rw [FrameTrail.push_self] at hentry
      have he : pushed = entry := Option.some.inj hentry
      subst entry
      have hq' : st.ptn[q]! ≤ level := by
        simpa only [pushed, sweepFrame] using hq
      have hne : tc ≠ q := by
        intro heq
        subst q
        have hopen := hcell.2.2.1 tc (Nat.le_refl tc) (by omega)
        exact (Nat.not_lt_of_ge hq' hopen).elim
      rw [hptn, Array.getElem!_set!_ne _ _ _ _ hne]
      simpa only [pushed, sweepFrame]
  · intro target entry hlt hentry
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hold | hhere
    · rw [FrameTrail.push_of_ne _ pushed (Nat.ne_of_lt hold)] at hentry
      obtain ⟨oldLen, holdCell, hoff, hsplit, hsingle, hat⟩ :=
        h.picked target entry hold hentry
      have hne : entry.frame.tc ≠ tc := by
        intro heq
        rcases isCell_disjoint_or_eq hsingle hcell with hleft | hright |
            hequal
        · rw [heq] at hleft
          have := hcell.1
          omega
        · rw [heq] at hright
          omega
        · omega
      have houtside := singleton_outside_cell hsingle hcell hne ho
      refine ⟨oldLen, holdCell, hoff, ?_, ?_, ?_⟩
      · rw [hptn, Array.getElem!_set!_ne _ _ _ _ hne.symm]
        exact hsplit
      · rw [hptn]
        exact isCell_set_miss hsingle hcell hlen
      · rw [hlab]
        exact (breakout_misses_singleton hinj
          (by rw [hls]; omega) houtside).trans hat
    · subst target
      change (trail.push level pushed) level = some entry at hentry
      rw [FrameTrail.push_self] at hentry
      have he : pushed = entry := Option.some.inj hentry
      subst entry
      refine ⟨len, ?_, ho, ?_, ?_, ?_⟩
      · simpa only [pushed, sweepFrame] using hcell
      · change out.ptn[tc]! = level + 1
        rw [hptn, Array.getElem!_set!_self _ _ _]
        rw [hps]
        omega
      · change IsCell out.ptn (level + 1) tc 1
        rw [hptn]
        simpa only [breakout_ptn] using
          (isCell_breakout_target (lab := st.lab)
            (tv := st.lab[tc + o]!) (by rw [hps]; omega) hcell.2.1)
      · change out.lab[tc]! = st.lab[tc + o]!
        rw [hlab]
        exact breakout_at_target hinj (by rw [hls]; omega)

end Hex.GraphIso.Nauty
