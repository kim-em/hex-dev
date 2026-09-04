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

/-! # Child guide installation -/

/-- Package one already-covered child of a frozen sweep as a generator
guide. The reference labelling may be either the first leaf or the current
canonical leaf. -/
@[expose] def Guide.ofSweep {ctx : Ctx} {tcLevel specFuel level : Nat}
    {codes : List Nat} {rsLab rsPtn ref : Array Nat}
    {tc len numcells offset : Nat} {best : Option Key}
    (hlevel : 1 ≤ level)
    (hdone : ChildDone ctx tcLevel specFuel level codes rsLab rsPtn tc
      numcells best offset)
    (hls : rsLab.size = ctx.n) (hlab : LabOk rsLab ctx.n)
    (hps : rsPtn.size = ctx.n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = ctx.n + 2)
    (hcell : IsCell rsPtn level tc len) (hrange : tc + len ≤ ctx.n)
    (hoff : offset < len)
    (hfuel : level + 1 + specFuel ≤ ctx.n + 1)
    (hat : ref[tc]! = rsLab[tc + offset]!)
    (hrefSize : ref.size = ctx.n)
    (hrefReach : cellsPerm rsPtn level rsLab ref) :
    Guide ctx tcLevel level best :=
  { positive := hlevel
    specFuel := specFuel
    codes := codes
    rsLab := rsLab
    rsPtn := rsPtn
    ref := ref
    tc := tc
    len := len
    numcells := numcells
    offset := offset
    done := hdone
    labSize := hls
    labOk := hlab
    ptnSize := hps
    endClosed := hend
    values := hvals
    cell := hcell
    range := hrange
    offsetLt := hoff
    fuelBound := hfuel
    atRef := hat
    refSize := hrefSize
    refReach := hrefReach }

/-- Descending into a sweep child extends both guide ledgers. A guide
whose control is the current level is supplied by an already-covered
child of that sweep; older guides are transported automatically. -/
theorem GuideStore.pushSweep {ctx : Ctx}
    {tcLevel specFuel level numcells tc len activeOffset : Nat}
    {codes : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : GuideStore ctx tcLevel level st best trail)
    (hlevel : 1 ≤ level)
    (hls : st.lab.size = ctx.n) (hlab : LabOk st.lab ctx.n)
    (hps : st.ptn.size = ctx.n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, st.ptn[q]! ≤ level ∨
      st.ptn[q]! = ctx.n + 2)
    (hcell : IsCell st.ptn level tc len) (hrange : tc + len ≤ ctx.n)
    (hfuel : level + 1 + specFuel ≤ ctx.n + 1)
    (hfirstSize : st.firstlab.size = ctx.n)
    (hcanonSize : st.canonlab.size = ctx.n)
    (hfirst : st.gcaFirst = level →
      ∃ o, o < len ∧
        ChildDone ctx tcLevel specFuel level codes st.lab st.ptn tc
          numcells best o ∧
        st.firstlab[tc]! = st.lab[tc + o]! ∧
        cellsPerm st.ptn level st.lab st.firstlab)
    (hcanon : st.gcaCanon = level →
      ∃ o, o < len ∧
        ChildDone ctx tcLevel specFuel level codes st.lab st.ptn tc
          numcells best o ∧
        st.canonlab[tc]! = st.lab[tc + o]! ∧
        cellsPerm st.ptn level st.lab st.canonlab) :
    GuideStore ctx tcLevel (level + 1) st best
      (trail.push level
        ⟨sweepFrame specFuel codes st.lab st.ptn tc numcells,
          activeOffset⟩) := by
  let entry : TrailEntry :=
    ⟨sweepFrame specFuel codes st.lab st.ptn tc numcells, activeOffset⟩
  apply h.push entry
  · intro heq _
    obtain ⟨o, ho, hdone, hat, hreach⟩ := hfirst heq
    let g := Guide.ofSweep hlevel hdone hls hlab hps hend hvals hcell
      hrange ho hfuel hat hfirstSize hreach
    rw [heq]
    refine ⟨g, rfl, ?_⟩
    simpa only [entry, g, Guide.ofSweep, Guide.frame, sweepFrame] using
      Guide.Located.pushSelf trail g activeOffset
  · intro heq _
    obtain ⟨o, ho, hdone, hat, hreach⟩ := hcanon heq
    let g := Guide.ofSweep hlevel hdone hls hlab hps hend hvals hcell
      hrange ho hfuel hat hcanonSize hreach
    rw [heq]
    refine ⟨g, rfl, ?_⟩
    simpa only [entry, g, Guide.ofSweep, Guide.frame, sweepFrame] using
      Guide.Located.pushSelf trail g activeOffset

/-! # Located direct unwinds -/

/-- Positive runtime fuel exposes the semantic soundness carried by every
non-exhausted node result. -/
theorem NodeResult.sound {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells : Nat} {cs : List Nat}
    {st out : SearchSt} {best outBest : Option Key} {r : Int}
    (h : NodeResult ctx tcLevel specFuel runFuel level cs st out numcells
      best outBest r) (hfuel : runFuel ≠ 0) :
    NodeSound ctx tcLevel specFuel level cs st numcells best outBest := by
  cases h with
  | complete sound => exact sound
  | unwind sound => exact sound
  | pruned sound => exact sound
  | exhausted empty => exact (hfuel empty).elim

/-- A located leaf-event unwind lifts directly through `otherNode`. -/
theorem otherNode_leaf_receipt {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells target : Nat}
    {cs : List Nat} {st : SearchSt} {best outBest : Option Key}
    {trail : FrameTrail}
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hreturn : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).1 = Int.ofNat target)
    (hbelow : target < level)
    (hsound : NodeSound ctx tcLevel (specFuel + 1) level cs st numcells
      best outBest)
    (payload : Unwind ctx tcLevel target
      (processnode ctx level ctx.n
        (otherLeafSt ctx level numcells st)).2 outBest)
    (hloc : payload.Located trail) :
    NodeReceipt trail ctx tcLevel (specFuel + 1) (fuel + 1) level cs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  have hearly : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level := by
    rw [hreturn]
    exact Int.ofNat_lt.mpr hbelow
  rw [otherNode_leaf_early ctx inf tcLevel fuel level numcells st hnum
    hearly]
  exact .unwind hsound target hreturn hbelow payload hloc

/-- A code-one admission at a reached active child has a located direct
unwind payload. -/
theorem Guide.firstLocated {ctx : Ctx} {tcLevel level numcells : Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (g : Guide ctx tcLevel st.gcaFirst best)
    (href : g.ref = st.firstlab) (hloc : g.Located trail)
    (htrail : TrailOk ctx level st trail) (hbelow : st.gcaFirst < level)
    (hgsz : ctx.g.size = ctx.n)
    (hsz₁ : st.firstlab.size = ctx.n)
    (hp₁ : st.firstlab.toList.Perm (List.range ctx.n))
    (hsz₂ : st.lab.size = ctx.n)
    (hp₂ : st.lab.toList.Perm (List.range ctx.n))
    (hsymm : ∀ i j, i < ctx.n → j < ctx.n →
      (ctx.g[i]!).testBit j = (ctx.g[j]!).testBit i)
    (hloop : ∀ i, i < ctx.n → (ctx.g[i]!).testBit i = false)
    (hbound : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (heq : (st.eqlevFirst == level) = true)
    (hsent : st.firstcode[level + 1]! = codeSentinel)
    (hnc : (numcells == ctx.n) = true)
    (hpass : isautom ctx (firstScatter ctx.n st.firstlab st.lab) = true) :
    ∃ payload : Unwind ctx tcLevel st.gcaFirst
        (processnode ctx level numcells st).2 best,
      payload.Located trail := by
  obtain ⟨o, hentry, ho, hat⟩ := g.active hloc htrail hbelow
  have hreach := g.reachAt hloc htrail hbelow
  have hcarrier := processnode_firstLabelCarrier hsz₁ hp₁ hsz₂ hp₂
    hsymm hloop hbound heq hsent hnc hpass
  have hcarrierG : LabelCarrier ctx g.ref st.lab
      (processnode ctx level numcells st).2.genTrace := by
    rw [href]
    exact hcarrier
  obtain ⟨γ, hγ, haut, hmap⟩ := hcarrierG
  have hrefReach : cellsPerm g.rsPtn st.gcaFirst g.rsLab st.firstlab := by
    rw [← href]
    exact g.refReach
  have hcell : CellCarrier ctx g.rsPtn st.gcaFirst g.rsLab g.ref st.lab
      (processnode ctx level numcells st).2.genTrace :=
    ⟨γ, hγ, haut, hmap,
      cellStab_of_scatter g.ptnSize g.labSize hsz₁ g.endClosed
        hrefReach hreach (by simpa only [href] using hmap)⟩
  have hinc : IncGrows best best := fun b hb ↦
    ⟨b, hb, keyLe_refl b⟩
  let anchor := g.anchorCell hgsz hinc hcell ho hat
  have hanchor : anchor.Located trail := by
    exact g.locateAnchorCell trail hentry hgsz hinc hcell ho hat
  obtain ⟨hlab, _, _, _, hfirst, _, _, _, _⟩ :=
    processnode_frames ctx level numcells st
  have hout : LabelCarrier ctx
      (processnode ctx level numcells st).2.firstlab
      (processnode ctx level numcells st).2.lab
      (processnode ctx level numcells st).2.genTrace := by
    rw [hfirst, hlab]
    exact hcarrier
  exact ⟨Unwind.first anchor hout, .first anchor hout hanchor⟩

/-- A code-two admission at a reached active child has a located direct
canonical unwind payload. -/
theorem Guide.canonLocated {ctx : Ctx} {tcLevel level numcells : Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (g : Guide ctx tcLevel st.gcaCanon best)
    (href : g.ref = st.canonlab) (hloc : g.Located trail)
    (htrail : TrailOk ctx level st trail) (hbelow : st.gcaCanon < level)
    (hgsz : ctx.g.size = ctx.n)
    (hsz₁ : st.canonlab.size = ctx.n)
    (hp₁ : st.canonlab.toList.Perm (List.range ctx.n))
    (hsz₂ : st.lab.size = ctx.n)
    (hp₂ : st.lab.toList.Perm (List.range ctx.n))
    (hbound : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hrows : leafRows ctx st.canonlab = leafRows ctx st.lab)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == ctx.n) = true)
    (hcc : st.compCanon = 0) (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0) :
    ∃ payload : Unwind ctx tcLevel st.gcaCanon
        (processnode ctx level numcells st).2 best,
      payload.Located trail := by
  obtain ⟨o, hentry, ho, hat⟩ := g.active hloc htrail hbelow
  have hreach := g.reachAt hloc htrail hbelow
  have hcarrier := processnode_canonLabelCarrier hsz₁ hp₁ hsz₂ hp₂
    hbound hrows hef hnc hcc hge htie
  have hcarrierG : LabelCarrier ctx g.ref st.lab
      (processnode ctx level numcells st).2.genTrace := by
    rw [href]
    exact hcarrier
  obtain ⟨γ, hγ, haut, hmap⟩ := hcarrierG
  have hrefReach : cellsPerm g.rsPtn st.gcaCanon g.rsLab st.canonlab := by
    rw [← href]
    exact g.refReach
  have hcell : CellCarrier ctx g.rsPtn st.gcaCanon g.rsLab g.ref st.lab
      (processnode ctx level numcells st).2.genTrace :=
    ⟨γ, hγ, haut, hmap,
      cellStab_of_scatter g.ptnSize g.labSize hsz₁ g.endClosed
        hrefReach hreach (by simpa only [href] using hmap)⟩
  have hinc : IncGrows best best := fun b hb ↦
    ⟨b, hb, keyLe_refl b⟩
  let anchor := g.anchorCell hgsz hinc hcell ho hat
  have hanchor : anchor.Located trail := by
    exact g.locateAnchorCell trail hentry hgsz hinc hcell ho hat
  obtain ⟨_, _, _, _, _, hcanon, _, _⟩ :=
    processnode_rowTie hef hnc hcc hge htie
  have hframes := processnode_frames ctx level numcells st
  have hout : LabelCarrier ctx
      (processnode ctx level numcells st).2.canonlab
      (processnode ctx level numcells st).2.lab
      (processnode ctx level numcells st).2.genTrace := by
    rw [hcanon, hframes.1]
    exact hcarrier
  exact ⟨Unwind.canon anchor hout, .canon anchor hout hanchor⟩

/-- A row-tied code-two event carries location evidence in both return
arms: the canonical arm uses its stored guide, while the first-ancestor
arm is the loop-local orbit return. -/
theorem Guide.tiedLocated {ctx : Ctx} {tcLevel level numcells : Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (g : Guide ctx tcLevel st.gcaCanon best)
    (href : g.ref = st.canonlab) (hloc : g.Located trail)
    (htrail : TrailOk ctx level st trail)
    (hgsz : ctx.g.size = ctx.n)
    (hsz₁ : st.canonlab.size = ctx.n)
    (hp₁ : st.canonlab.toList.Perm (List.range ctx.n))
    (hsz₂ : st.lab.size = ctx.n)
    (hp₂ : st.lab.toList.Perm (List.range ctx.n))
    (hbound : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hrows : leafRows ctx st.canonlab = leafRows ctx st.lab)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == ctx.n) = true)
    (hcc : st.compCanon = 0) (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0)
    (hcanonBelow : st.gcaCanon < level)
    (hfirstPos : 1 ≤ st.gcaFirst) (hfirstBelow : st.gcaFirst < level)
    (hcoset : (processnode ctx level numcells st).2.cosetindex < ctx.n)
    (horbit : OrbSound
      (OrbConn (processnode ctx level numcells st).2.genTrace.toList ctx.n)
      (processnode ctx level numcells st).2.orbits ctx.n) :
    ∃ target,
      (processnode ctx level numcells st).1 = Int.ofNat target ∧
      target < level ∧
      ∃ payload : Unwind ctx tcLevel target
          (processnode ctx level numcells st).2 best,
        payload.Located trail := by
  rcases processnode_rowTie_orbit hef hnc hcc hge htie with hcanon |
      ⟨hfirst, hsmaller⟩
  · obtain ⟨payload, hpayload⟩ := g.canonLocated href hloc htrail
      hcanonBelow hgsz hsz₁ hp₁ hsz₂ hp₂ hbound hrows hef hnc hcc hge htie
    exact ⟨st.gcaCanon, hcanon, hcanonBelow, payload, hpayload⟩
  · let payload : Unwind ctx tcLevel st.gcaFirst
        (processnode ctx level numcells st).2 best :=
      .orbit ⟨hfirstPos, hcoset, hsmaller, horbit⟩
    exact ⟨st.gcaFirst, hfirst, hfirstBelow, payload,
      .orbit ⟨hfirstPos, hcoset, hsmaller, horbit⟩⟩

/-- The located guide store discharges a code-one leaf return. -/
theorem GuideStore.firstUnwind {ctx : Ctx} {tcLevel level numcells : Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hstore : GuideStore ctx tcLevel level st best trail)
    (htrail : TrailOk ctx level st trail)
    (hfirstPos : 0 < st.gcaFirst) (hbelow : st.gcaFirst < level)
    (hgsz : ctx.g.size = ctx.n)
    (hsz₁ : st.firstlab.size = ctx.n)
    (hp₁ : st.firstlab.toList.Perm (List.range ctx.n))
    (hsz₂ : st.lab.size = ctx.n)
    (hp₂ : st.lab.toList.Perm (List.range ctx.n))
    (hsymm : ∀ i j, i < ctx.n → j < ctx.n →
      (ctx.g[i]!).testBit j = (ctx.g[j]!).testBit i)
    (hloop : ∀ i, i < ctx.n → (ctx.g[i]!).testBit i = false)
    (hbound : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (heq : (st.eqlevFirst == level) = true)
    (hsent : st.firstcode[level + 1]! = codeSentinel)
    (hnc : (numcells == ctx.n) = true)
    (hpass : isautom ctx (firstScatter ctx.n st.firstlab st.lab) = true) :
    ∃ payload : Unwind ctx tcLevel st.gcaFirst
        (processnode ctx level numcells st).2 best,
      payload.Located trail := by
  obtain ⟨g, href, hloc⟩ := hstore.first hfirstPos hbelow
  exact g.firstLocated href hloc htrail hbelow hgsz hsz₁ hp₁ hsz₂ hp₂
    hsymm hloop hbound heq hsent hnc hpass

/-- The located guide store discharges either arm of a row-tied code-two
leaf return. -/
theorem GuideStore.tiedUnwind {ctx : Ctx} {tcLevel level numcells : Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hstore : GuideStore ctx tcLevel level st best trail)
    (htrail : TrailOk ctx level st trail)
    (hcanonPos : 0 < st.gcaCanon) (hcanonBelow : st.gcaCanon < level)
    (hgsz : ctx.g.size = ctx.n)
    (hsz₁ : st.canonlab.size = ctx.n)
    (hp₁ : st.canonlab.toList.Perm (List.range ctx.n))
    (hsz₂ : st.lab.size = ctx.n)
    (hp₂ : st.lab.toList.Perm (List.range ctx.n))
    (hbound : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hrows : leafRows ctx st.canonlab = leafRows ctx st.lab)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == ctx.n) = true)
    (hcc : st.compCanon = 0) (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0)
    (hfirstPos : 1 ≤ st.gcaFirst) (hfirstBelow : st.gcaFirst < level)
    (hcoset : (processnode ctx level numcells st).2.cosetindex < ctx.n)
    (horbit : OrbSound
      (OrbConn (processnode ctx level numcells st).2.genTrace.toList ctx.n)
      (processnode ctx level numcells st).2.orbits ctx.n) :
    ∃ target,
      (processnode ctx level numcells st).1 = Int.ofNat target ∧
      target < level ∧
      ∃ payload : Unwind ctx tcLevel target
          (processnode ctx level numcells st).2 best,
        payload.Located trail := by
  obtain ⟨g, href, hloc⟩ := hstore.canon hcanonPos hcanonBelow
  exact g.tiedLocated href hloc htrail hgsz hsz₁ hp₁ hsz₂ hp₂ hbound
    hrows hef hnc hcc hge htie hcanonBelow hfirstPos hfirstBelow hcoset
    horbit

/-! # Direct leaf receipts -/

/-- A code-one leaf return is a located node receipt.  Its incumbent is
unchanged, so its `NodeSound` component needs no comparison with the
first leaf. -/
theorem otherNode_leaf_firstReceipt {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {cs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hstore : GuideStore ctx tcLevel level
      (otherLeafSt ctx level numcells st) best trail)
    (htrail : TrailOk ctx level (otherLeafSt ctx level numcells st) trail)
    (hfirstPos : 0 < (otherLeafSt ctx level numcells st).gcaFirst)
    (hbelow : (otherLeafSt ctx level numcells st).gcaFirst < level)
    (hgsz : ctx.g.size = ctx.n)
    (hfirstSize : (otherLeafSt ctx level numcells st).firstlab.size =
      ctx.n)
    (hfirstPerm : (otherLeafSt ctx level numcells st).firstlab.toList.Perm
      (List.range ctx.n))
    (hlabSize : (otherLeafSt ctx level numcells st).lab.size = ctx.n)
    (hlabPerm : (otherLeafSt ctx level numcells st).lab.toList.Perm
      (List.range ctx.n))
    (hsymm : ∀ i j, i < ctx.n → j < ctx.n →
      (ctx.g[i]!).testBit j = (ctx.g[j]!).testBit i)
    (hloop : ∀ i, i < ctx.n → (ctx.g[i]!).testBit i = false)
    (hbound : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true)
    (hsent : (otherLeafSt ctx level numcells st).firstcode[level + 1]! =
      codeSentinel)
    (hpass : isautom ctx (firstScatter ctx.n
      (otherLeafSt ctx level numcells st).firstlab
      (otherLeafSt ctx level numcells st).lab) = true) :
    NodeReceipt trail ctx tcLevel (specFuel + 1) (fuel + 1) level cs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  let leaf := otherLeafSt ctx level numcells st
  obtain ⟨payload, hloc⟩ := hstore.firstUnwind (numcells := ctx.n)
    htrail hfirstPos hbelow hgsz hfirstSize hfirstPerm hlabSize hlabPerm
    hsymm hloop hbound heq hsent (by simp) hpass
  have hreturn := (processnode_auto (level := level) (numcells := ctx.n)
    (st := leaf) heq hsent (by simp) hpass).1
  exact otherNode_leaf_receipt hnum hreturn hbelow
    (NodeSound.refl ctx tcLevel (specFuel + 1) level cs st numcells best)
    payload hloc

/-- A row-tied code-two leaf return is a located node receipt in both the
canonical-guide and first-ancestor orbit arms. -/
theorem otherNode_leaf_tiedReceipt {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {cs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hstore : GuideStore ctx tcLevel level
      (otherLeafSt ctx level numcells st) best trail)
    (htrail : TrailOk ctx level (otherLeafSt ctx level numcells st) trail)
    (hcanonPos : 0 < (otherLeafSt ctx level numcells st).gcaCanon)
    (hcanonBelow : (otherLeafSt ctx level numcells st).gcaCanon < level)
    (hgsz : ctx.g.size = ctx.n)
    (hcanonSize : (otherLeafSt ctx level numcells st).canonlab.size =
      ctx.n)
    (hcanonPerm : (otherLeafSt ctx level numcells st).canonlab.toList.Perm
      (List.range ctx.n))
    (hlabSize : (otherLeafSt ctx level numcells st).lab.size = ctx.n)
    (hlabPerm : (otherLeafSt ctx level numcells st).lab.toList.Perm
      (List.range ctx.n))
    (hbound : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hrows : leafRows ctx (otherLeafSt ctx level numcells st).canonlab =
      leafRows ctx (otherLeafSt ctx level numcells st).lab)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hcc : (otherLeafSt ctx level numcells st).compCanon = 0)
    (hge : ¬(level < (otherLeafSt ctx level numcells st).canonlevel))
    (htie : (testcanlab ctx (updatecan ctx
      (otherLeafSt ctx level numcells st).canong
      (otherLeafSt ctx level numcells st).canonlab
      (otherLeafSt ctx level numcells st).samerows)
      (otherLeafSt ctx level numcells st).lab).1 = 0)
    (hfirstPos : 1 ≤ (otherLeafSt ctx level numcells st).gcaFirst)
    (hfirstBelow : (otherLeafSt ctx level numcells st).gcaFirst < level)
    (hcoset : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).2.cosetindex < ctx.n)
    (horbit : OrbSound (OrbConn (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).2.genTrace.toList ctx.n)
      (processnode ctx level ctx.n
        (otherLeafSt ctx level numcells st)).2.orbits ctx.n) :
    NodeReceipt trail ctx tcLevel (specFuel + 1) (fuel + 1) level cs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  obtain ⟨target, hreturn, hbelow, payload, hloc⟩ :=
    hstore.tiedUnwind (numcells := ctx.n) htrail hcanonPos hcanonBelow
      hgsz hcanonSize hcanonPerm hlabSize hlabPerm hbound hrows hef (by simp)
      hcc hge htie hfirstPos hfirstBelow hcoset horbit
  exact otherNode_leaf_receipt hnum hreturn hbelow
    (NodeSound.refl ctx tcLevel (specFuel + 1) level cs st numcells best)
    payload hloc

end Hex.GraphIso.Nauty
