/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.ReferenceLeaf
public import HexGraphIso.Nauty.Generation.Cheap
public import HexGraphIso.Nauty.Generation.Tree
public import HexGraphIso.Nauty.Generation.Uniform
import all HexGraphIso.Nauty.Policy.ReferenceLeaf
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.MaxNode
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Generation.Matching
import all HexGraphIso.Nauty.Generation.Cheap
import all HexGraphIso.Nauty.Generation.Uniform
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- A matching occurrence prevents a first-target hint from changing
the selected cell or demoting the first-reference comparison. -/
theorem matching_target {ctx : Ctx n} {tcLevel level numcells tc : Nat}
    {st : Search n} {rs : RefineSt n} {targets : List Nat} {key : Key n}
    (hit : IterOk ctx level rs) (heqt : Equitable ctx level rs.lab rs.ptn)
    (hlab : st.lab = rs.lab) (hptn : st.ptn = rs.ptn) (hn : numcells < n)
    (hm : Generation.Matches ctx level st (tc :: targets) key)
    (hp : Generation.HasLeaf ctx tcLevel level rs (tc :: targets) key)
    (heq : st.eqlevFirst = level) :
    let t := specMaketargetcell ctx rs.lab rs.ptn level tcLevel
    chooseTarget false ctx tcLevel level numcells st =
      (Int.ofNat t.1, t.2.1, t.2.2, { st with tctotal := st.tctotal + t.2.2 }) := by
  have hplain := maketargetcell_eq_spec (tcLevel := tcLevel) heqt hit.ok.labOk
    hit.ok.labSize hit.ok.ptnSize hit.ok.ptnEnd
  have hhint := hm.target_spec hp hit heqt
  have hpos := hm.target hp hit heqt
  change Int.ofNat (maketargetcell ctx rs.lab rs.ptn level tcLevel st.firsttc[level]!).1 =
    st.firsttc[level]! at hpos
  change maketargetcell ctx rs.lab rs.ptn level tcLevel st.firsttc[level]! = _ at hhint
  unfold chooseTarget
  simp only [Bool.false_eq_true, ite_false, Bool.not_false, Bool.true_and, hn,
    decide_true, heq, beq_self_eq_true, Bool.true_or, Bool.and_self, ite_true, hlab, hptn]
  split
  · rw [hhint]
    rw [hhint] at hpos
    simp only [hpos, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ite_false, Id.run_pure]
  · rw [hplain]
    rw [hhint] at hpos
    simp only [hpos, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ite_false, Id.run_pure]

/-- A reference that continues through every target child makes the
actual first descent emit a carrier. The same recursion handles small
cells and uniform subtrees. -/
theorem descent_reference {ctx : Ctx n} (inf tcLevel : Nat)
    (hgsz : ctx.g.size = n)
    (P : Nat → RefineSt n → List Nat → Key n → Prop)
    (hvalid : ∀ {level rs targets key}, P level rs targets key →
      IterOk ctx level rs ∧ Equitable ctx level rs.lab rs.ptn ∧
        bcount rs.ptn level n = rs.numcells)
    (hchildren : ∀ {level rs tc e o targets key},
      P level rs (tc :: targets) ⟨rs.longcode :: key.codes, key.rows⟩ →
      level < n → (tc, e) ∈ cells rs.ptn level n → tc < e →
      tc = specTargetcell ctx rs.lab rs.ptn level tcLevel → o ≤ e - tc →
      Generation.HasLeaf ctx tcLevel (level + 1)
        (childSt ctx level rs tc rs.lab[tc + o]!) targets key →
      ∀ o', o' ≤ e - tc →
        P (level + 1) (childSt ctx level rs tc rs.lab[tc + o']!) targets key ∧
        Generation.HasLeaf ctx tcLevel (level + 1)
          (childSt ctx level rs tc rs.lab[tc + o']!) targets key) :
    ∀ fuel level numcells (st : Search n) targets key,
      P level (st.refined ctx level numcells) targets key →
      st.workperm.size = n → st.firstlab.size = n → st.firstlab.toList.Perm (List.range n) →
      Generation.Matches ctx level st targets key →
      Generation.HasLeaf ctx tcLevel level (st.refined ctx level numcells) targets key →
      st.eqlevFirst = level - 1 → st.gcaFirst < level → n < level + fuel →
      let out := node false ctx inf tcLevel fuel level numcells st
      out.1 = .unwind st.gcaFirst false ∧ LabelCarrier ctx st.firstlab out.2.lab out.2.genTrace := by
  intro fuel
  induction fuel with
  | zero =>
    intro level numcells st targets key hS hw hf hfp hm hp heq hg hbudget
    have := (hvalid hS).1.lvl
    omega
  | succ fuel ih =>
    intro level numcells st targets key hS hw hf hfp hm hp heq hg hbudget
    obtain ⟨hit, heqt, hacc⟩ := hvalid hS
    let rs := st.refined ctx level numcells
    by_cases hn : rs.numcells = n
    · apply matching_leaf hgsz hw hf hfp hit hn _ hm hp heq
      have hc : (List.range n).countP (fun q => decide (rs.ptn[q]! ≤ level)) =
          (List.range n).length := by
        rw [List.length_range]
        exact hacc.trans hn
      intro q hq
      exact of_decide_eq_true (List.countP_eq_length.mp hc q (List.mem_range.mpr hq))
    have hnc : rs.numcells < n := by
      have hc := hacc
      change bcount rs.ptn level n = rs.numcells at hc
      have hb := bcount_le rs.ptn level n
      omega
    rcases hp.cases with ⟨hd, _, _⟩ |
      ⟨tc, e, o, rest, tail, hl, hcell, hne, ho, htarget, hchildLeaf, rfl, rfl⟩
    · obtain ⟨q, hq, hopen⟩ := exists_open_of_bcount_lt (hacc ▸ hnc)
      have := hd q hq
      omega
    let compared := compareCodes level rs.longcode (visit ctx level numcells st).2.2
    have hfields : compared.lab = rs.lab ∧ compared.ptn = rs.ptn ∧
        compared.reference = st.reference ∧ compared.workperm = st.workperm ∧
        compared.gcaFirst = st.gcaFirst := by
      dsimp only [compared]
      unfold compareCodes
      simp only [Id.run_pure, apply_ite Id.run]
      repeat' split
      all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    have he : compared.eqlevFirst = level := by
      have h := (hm.stateEq (out := (visit ctx level numcells st).2.2) rfl rfl rfl).prep hp heq

      exact h
    have hmcomp : Generation.Matches ctx level compared (tc :: rest)
        ⟨rs.longcode :: tail.codes, tail.rows⟩ :=
      hm.stateEq (congrArg Prod.fst hfields.2.2.1)
        (congrArg (fun x => x.2.1) hfields.2.2.1) (congrArg (fun x => x.2.2) hfields.2.2.1)
    have hchoice := matching_target hit heqt hfields.1 hfields.2.1 hnc hmcomp hp he
    have hend := target_end_lt hit.ok.ptnSize hit.ok.ptnEnd hcell
    let len := e + 1 - tc
    let cell := windowSet n rs.lab tc len
    have hic : IsCell rs.ptn level tc len :=
      cells_isCell (by rw [hit.ok.ptnSize]; omega) hit.ok.ptnEnd _ hcell
    have hce : cellEnd rs.ptn level (tc + 1) = tc + len - 1 :=
      cellEnd_of_isCell hic (by dsimp only [len]; omega) (by rw [hit.ok.ptnSize]; dsimp only [len]; omega)
    have hmt : specMaketargetcell ctx rs.lab rs.ptn level tcLevel = (tc, cell, len) := by
      rw [specMaketargetcell, ← htarget, hce, worksetOf_eq_windowSet _ tc len (by dsimp only [len]; omega)]
      congr 2
      dsimp only [len]
      omega
    rw [hmt] at hchoice
    obtain ⟨tv, hnext⟩ := nextElem_windowSet_some (lab := rs.lab) (tc := tc) (len := len)
      (by dsimp only [len]; omega) (hit.ok.labOk _ (by rw [hit.ok.labSize]; omega))
    obtain ⟨o', ho', hat⟩ := mem_segN_iff.mp (mem_windowSet.mp (VSet.nextElem_mem hnext)).2
    have ho' : o' ≤ e - tc := by dsimp only [len] at ho'; omega
    obtain ⟨hsmall, hocc⟩ := hchildren hS hl hcell hne htarget ho hchildLeaf o' ho'
    rw [hat] at hsmall hocc
    let targeted := { compared with tctotal := compared.tctotal + len }
    let ready := cheapCheck false level targeted
    let child := Nauty.child false level tc tv ready
    have hcfields : child.reference = st.reference ∧ child.workperm = st.workperm ∧
        child.gcaFirst = st.gcaFirst ∧ child.eqlevFirst = level := by
      dsimp only [child, Nauty.child, ready]
      simp only [Bool.false_eq_true, ite_false]
      unfold cheapCheck
      split <;> exact ⟨hfields.2.2.1, hfields.2.2.2.1, hfields.2.2.2.2, he⟩
    have hcref : child.refined ctx (level + 1) (rs.numcells + 1) = childSt ctx level rs tc tv := by
      dsimp only [child, Nauty.child, ready]
      simp only [Bool.false_eq_true, ite_false]
      unfold cheapCheck
      split
      all_goals
        change refine ctx (level + 1) (breakout n compared.lab compared.ptn (level + 1) tc tv).1
          (breakout n compared.lab compared.ptn (level + 1) tc tv).2.1
          (breakout n compared.lab compared.ptn (level + 1) tc tv).2.2 (rs.numcells + 1) = _
        rw [hfields.1, hfields.2.1, breakout_ptn]
        rfl
    have hmchild : Generation.Matches ctx (level + 1) child rest tail :=
      hm.tail.stateEq (congrArg Prod.fst hcfields.1)
        (congrArg (fun x => x.2.1) hcfields.1) (congrArg (fun x => x.2.2) hcfields.1)
    have hfchild : child.firstlab = st.firstlab := congrArg (fun x => x.2.2) hcfields.1
    have hchild := ih (level + 1) (rs.numcells + 1) child rest tail
      (hcref ▸ hsmall) (hcfields.2.1 ▸ hw) (hfchild ▸ hf) (hfchild ▸ hfp)
      hmchild (hcref ▸ hocc) (by simpa only [Nat.add_sub_cancel] using hcfields.2.2.2)
      (by rw [hcfields.2.2.1]; omega) (by omega)
    let raw := node false ctx inf tcLevel fuel (level + 1) (rs.numcells + 1) child
    have hret : raw.1 = .unwind st.gcaFirst false := hchild.1.trans (by rw [hcfields.2.2.1])
    have hsweep : sweep false ctx inf tcLevel fuel (n + 1) level rs.numcells tc tv
        (some tv) cell 0 ready =
      (.unwind st.gcaFirst false, 0, { raw.2 with fixedpts := raw.2.fixedpts.erase tv }) := by
      rw [sweep]
      simp only [Bool.not_false, Bool.true_or, Bool.false_and, Bool.false_eq_true, ite_true, ite_false]
      have hr := hret
      dsimp only [raw, child] at hr
      rw [hr]
      simp only [hg, ite_true, Id.run_pure]
      rfl
    let l : Max.Loop n := ⟨⟨level, numcells, [], st⟩, false⟩
    have hlprep : l.prepare ctx tcLevel = (rs.numcells, Int.ofNat tc, cell, len, ready) := by
      change (let t := chooseTarget false ctx tcLevel level rs.numcells compared
        (rs.numcells, t.1, t.2.1, t.2.2.1, cheapCheck false level t.2.2.2)) = _
      rw [hchoice]
    have hclass : classify ctx level rs.numcells targeted = (.internal, targeted) := by
      rw [classify_eq]
      change (if _ then _ else if _ then _ else _) = _
      simp only [show targeted.eqlevFirst = level from he, bne_self_eq_false, Bool.false_and,
        Bool.false_eq_true, ite_false, bne_iff_ne.mpr hn, ite_true]
    have hstep := l.node_step (Generic.sweepCall ctx inf tcLevel fuel (n + 1))
      (fun h => by cases h) (fun _ => by
        change (classify ctx level rs.numcells (chooseTarget false ctx tcLevel level rs.numcells compared).2.2.2).1 = .internal
        rw [hchoice]
        exact congrArg Prod.fst hclass)
    change raw.1 = _ ∧ _ at hchild
    dsimp only [l, Generic.sweepCall] at hstep
    unfold Generic.sweepCall at hstep
    dsimp only
    rw [node_eq_generic, Generic.node, hstep, hlprep]
    dsimp only
    simp only [← sweep_eq_generic]
    rw [hnext]
    simp only [Int.ofNat_eq_natCast, Int.toNat_natCast, Option.getD_some]
    rw [hsweep]
    exact ⟨rfl, hfchild ▸ hchild.2⟩


/-- A matching small-cell node follows its actual first child to an
emitted automorphism, without assuming a generated carrier. -/
theorem cheap_reference {ctx : Ctx n} (inf tcLevel : Nat)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    ∀ fuel level numcells (st : Search n) targets key,
      SubtreeOk ctx level (st.refined ctx level numcells) →
      st.workperm.size = n → st.firstlab.size = n → st.firstlab.toList.Perm (List.range n) →
      Generation.Matches ctx level st targets key →
      Generation.HasLeaf ctx tcLevel level (st.refined ctx level numcells) targets key →
      st.eqlevFirst = level - 1 → st.gcaFirst < level → n < level + fuel →
      let out := node false ctx inf tcLevel fuel level numcells st
      out.1 = .unwind st.gcaFirst false ∧ LabelCarrier ctx st.firstlab out.2.lab out.2.genTrace := by
  apply descent_reference inf tcLevel hgsz
    (fun level rs _ _ => SubtreeOk ctx level rs)
    (fun h => ⟨h.it, h.eqt, h.acc⟩)
  intro level rs tc e o targets key hs hl hc hn _ ho hp o' ho'
  exact ⟨subtreeOk_child hs hl hsymm hc hn ho',
    hp.smallChild hs hl hgsz hsymm hloop hc hn ho ho'⟩

/-- Uniformity of a valid matching subtree forces a recorded generator
on the actual first descent. Validity supplies leaf existence. -/
theorem uniform_reference {ctx : Ctx n} {inf tcLevel fuel level numcells : Nat}
    {st : Search n} {targets : List Nat} {key : Key n}
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hT : Generation.TreeOk ctx level (st.refined ctx level numcells))
    (hU : Generation.Uniform ctx tcLevel level (st.refined ctx level numcells) targets key)
    (hw : st.workperm.size = n) (hf : st.firstlab.size = n)
    (hfp : st.firstlab.toList.Perm (List.range n))
    (hm : Generation.Matches ctx level st targets key)
    (heq : st.eqlevFirst = level - 1) (hg : st.gcaFirst < level) (hbudget : n < level + fuel) :
    let out := node false ctx inf tcLevel fuel level numcells st
    out.1 = .unwind st.gcaFirst false ∧ LabelCarrier ctx st.firstlab out.2.lab out.2.genTrace := by
  obtain ⟨targets', key', hp⟩ := hT.nonempty (by omega) hsymm
  have hocc : Generation.HasLeaf ctx tcLevel level (st.refined ctx level numcells) targets key := by
    obtain ⟨rfl, rfl⟩ := hU targets' key' hp
    exact hp
  apply descent_reference inf tcLevel hgsz
    (fun level rs targets key => Generation.TreeOk ctx level rs ∧
      Generation.Uniform ctx tcLevel level rs targets key)
    (fun h => ⟨h.1.it, h.1.eqt, h.1.acc⟩) ?_
    fuel level numcells st targets key ⟨hT, hU⟩ hw hf hfp hm hocc heq hg hbudget
  intro level rs tc e o targets key h hl hc hn ht ho _ o' ho'
  have hT' := h.1.child hl hsymm hc hn ho'
  have hU' := h.2.child hl hc hn ht ho'
  obtain ⟨targets', key', hp⟩ := hT'.nonempty (by omega) hsymm
  obtain ⟨rfl, rfl⟩ := hU' targets' key' hp
  exact ⟨⟨hT', hU'⟩, hp⟩

end Hex.GraphIso.Nauty
