/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Reference.Return
public import HexGraphIso.Nauty.Policy.Max.Resume
public import HexGraphIso.Nauty.Generation.PathCover
public import HexGraphIso.Nauty.Generation.Canon
import all HexGraphIso.Nauty.Generation.Reorder
import all HexGraphIso.Nauty.Policy.Max.Receive
import all HexGraphIso.Nauty.Policy.ChildFrame
import all HexGraphIso.Nauty.Policy.Max.Position
import all HexGraphIso.Nauty.Policy.Max.Suspend
import all HexGraphIso.Nauty.Policy.CallState
import all HexGraphIso.Nauty.Policy.Canon.Ref
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Max.Entry
import all HexGraphIso.Nauty.Policy.Max.Context
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Generation.Canon
import all HexGraphIso.Nauty.Search.State
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Receiving an actual child keeps the canonical source behind the next
cursor, whether the child retained or replaced the reference. -/
theorem SweepInput.canon_past {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv)
      cell index st l bs fs parents) {previous : Option Nat}
    (hp : Generation.CanonPast level tc previous st)
    (hnext : cell.nextElem previous = some tv) :
    let raw := (Nauty.node (first && tv == tv1) ctx (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (child first level tc tv st)).2
    let middle := if first && tv == tv1 then afterChildFirst level tv1 raw else raw
    let left := { middle with fixedpts := middle.fixedpts.erase tv }
    Generation.CanonPast level tc (some tv)
      (Nauty.recover (n + 2) level left) := by
  intro raw middle left
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  have hr := child_canon (first := first) (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
    h.partition hn0 hl h.target (h.cursor_mem tv rfl) (first && tv == tv1)
  change (raw.gcaCanon ≤ st.gcaCanon ∧ raw.canonlab = st.canonlab) ∨
    (raw.canonlab.size = st.lab.size ∧ cellsPerm st.ptn level st.lab raw.canonlab ∧
      raw.canonlab[tc]! = tv) at hr
  have hg : left.gcaCanon = raw.gcaCanon := by dsimp only [left, middle]; split <;> rfl
  have hc : left.canonlab = raw.canonlab := by dsimp only [left, middle]; split <;> rfl
  constructor
  · change (Nauty.recover (n + 2) level left).gcaCanon ≤ level
    rw [recover_canon]
    exact Nat.min_le_left _ _
  · intro he
    change (Nauty.recover (n + 2) level left).gcaCanon = level at he
    rw [recover_canon] at he
    change min level left.gcaCanon = level at he
    rw [hg] at he
    change ¬ tv < (Nauty.recover (n + 2) level left).canonlab[tc]!
    rw [recover_ref, hc]
    rcases hr with hold | hnew
    · have hlevel : st.gcaCanon = level := by have := hp.cap; change st.gcaCanon ≤ level at this; omega
      have hh := (hp.advance (nextElem_after hnext)).source hlevel
      change ¬ tv < st.canonlab[tc]! at hh
      rw [hold.2]
      exact hh
    · rw [hnew.2.2]
      omega

/-- A canonical return to this receiver names an earlier original child,
including when a previous filter removed that child from the live set. -/
theorem SweepInput.canon_earlier {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first childFirst : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv)
      cell index st l bs fs parents) {previous : Option Nat}
    (hp : Generation.CanonPast level tc previous st)
    (hnext : cell.nextElem previous = some tv) :
    let out := (Nauty.node childFirst ctx (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (child first level tc tv st)).2
    out.gcaCanon = level →
      ∃ o, o < (l.prepare ctx tcLevel).2.2.2.1 ∧
        out.canonlab[tc]! = (l.prepare ctx tcLevel).2.2.2.2.lab[tc + o]! ∧
        (l.prepare ctx tcLevel).2.2.2.2.lab[tc + o]! < tv ∧
        cellsPerm (l.prepare ctx tcLevel).2.2.2.2.ptn level
          (l.prepare ctx tcLevel).2.2.2.2.lab out.canonlab := by
  intro out he
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  have hold := child_canon_old (first := first) (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
    h.partition hn0 hl h.target (h.cursor_mem tv rfl) childFirst (Nat.le_of_eq he)
  have hg : st.gcaCanon = level := hold.1.symm.trans he
  have hh := hp.before hnext hg
  obtain ⟨v, _, hat, hperm⟩ := h.canonical hg
  have hmem : st.canonlab[tc]! ∈ segN (l.prepare ctx tcLevel).2.2.2.2.lab tc
      (l.prepare ctx tcLevel).2.2.2.1 := by
    apply (hperm tc _ h.window).mem_iff.mpr
    exact mem_segN_iff.mpr ⟨0, by have := h.len; omega, by simp⟩
  obtain ⟨o, ho, hoat⟩ := mem_segN_iff.mp hmem
  exact ⟨o, ho, by rw [hold.2]; exact hoat.symm,
    by rw [hoat]; exact hh, by rw [hold.2]; exact hperm⟩

/-- The actual returned child still labels its individualized singleton
by the chosen vertex, before partition recovery. -/
theorem SweepInput.return_chosen {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first childFirst : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv)
      cell index st l bs fs parents) :
    (Nauty.node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st)).2.lab[tc]! = tv := by
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  let p : Parent n := ⟨l, st, tv, bs, fs⟩
  have hp := p.picked h.suspend
  simp only [p, Parent.child, ← h.level_eq, ← h.numcells_eq, ← h.tc_eq, ← h.first_eq] at hp
  have hc := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
    hl h.partition h.target (h.cursor_mem tv rfl)
  have hout := node_out (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel) childFirst hn0
    (by omega) hc.1
  exact (cellsPerm_singleton hout.perm hp.1).symm.trans hp.2

/-- A received matching-reference return advances the absence ledger.
Canonical returns use an earlier reference; first-reference and orbit
returns cannot be received at an off-path frame. -/
theorem SweepInput.reference_visit {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel boundary : Nat}
    {level numcells tc tv1 tv index : Nat} {cell : VSet n} {short : Bool}
    {st out : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel false level numcells tc tv1 (some tv)
      cell index st l bs fs parents) {previous : Option Nat}
    {R : RefineSt n} {targets : List Nat} {key : Key n}
    (hit : IterOk ctx level R)
    (hlab : R.lab = (l.prepare ctx tcLevel).2.2.2.2.lab)
    (hptn : R.ptn = (l.prepare ctx tcLevel).2.2.2.2.ptn)
    (hcover : Generation.PathCover ctx tcLevel boundary level R tc
      (l.prepare ctx tcLevel).2.2.2.1 targets key cell previous)
    (hpast : Generation.CanonPast level tc previous st)
    (hnext : cell.nextElem previous = some tv)
    (hguide : st.gcaFirst < level)
    (hcall : Nauty.node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child false level tc tv st) = (.unwind level short, out))
    (hsize : out.canonlab.size = n) (hgsz : ctx.g.size = n)
    (hreceipt : ∀ o, o < (l.prepare ctx tcLevel).2.2.2.1 → R.lab[tc + o]! = tv →
      Generation.ChildPath ctx tcLevel boundary level R tc targets key o →
        RefReturn ctx level out) :
    Generation.PathCover ctx tcLevel boundary level R tc (l.prepare ctx tcLevel).2.2.2.1
      targets key cell (some tv) := by
  classical
  by_cases hex : ∃ o, o < (l.prepare ctx tcLevel).2.2.2.1 ∧ R.lab[tc + o]! = tv ∧
      Generation.ChildPath ctx tcLevel boundary level R tc targets key o
  · obtain ⟨o, ho, hat, href⟩ := hex
    have hr := hreceipt o ho hat href
    have hf := node_gca ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child false level tc tv st)
    rw [hcall] at hf
    change out.gcaFirst = st.gcaFirst at hf
    cases hr with
    | first returned carrier => omega
    | orbit returned smaller => omega
    | canon returned carrier =>
      have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
      have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
      have he := h.canon_earlier (childFirst := false) hpast hnext
      rw [hcall] at he
      obtain ⟨oRef, hoRef, hatRef, hbefore, hperm⟩ := he returned.symm
      have hout := child_frame (first := false) (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
        h.partition hn0 hl h.path.fixed h.target (h.cursor_mem tv rfl) false
      rw [hcall] at hout
      have hcurrent := (h.effect.trans hout.1).perm
      have hpicked := h.return_chosen (childFirst := false)
      rw [hcall] at hpicked
      have hcell : (tc, tc + (l.prepare ctx tcLevel).2.2.2.1 - 1) ∈ cells R.ptn level n := by
        apply isCell_mem_cells
        · rw [hptn]; exact h.window
        · rw [hit.ok.ptnSize]; exact Nat.le_refl _
        · exact hit.ok.ptnEnd
        · have := h.range; have := h.len; omega
      have hlt : level < n := by
        have hc := (reachPolicy G ctx tcLevel hn0).child false level numcells tc tv cell st
          hl h.partition h.target (h.cursor_mem tv rfl)
        dsimp only [policy, Generic.Policy.child] at hc
        have := hc.1.bc
        have := bcount_le (child false level tc tv st).ptn (level + 1) n
        omega
      have hcc : CellCarrier ctx R.ptn level R.lab out.canonlab out.lab out.genTrace := by
        obtain ⟨γ, hmem, hcheck, hmap⟩ := carrier
        refine ⟨γ, hmem, hcheck, hmap, ?_⟩
        apply cellStab_of_scatter hit.ok.ptnSize hit.ok.labSize hsize hit.ok.ptnEnd
        · rwa [hlab, hptn]
        · rw [hlab, hptn]; exact hcurrent
        · exact hmap
      exact hcover.reference hnext hit hlt hgsz hcell
        (by have := h.len; omega) (by have := h.len; omega) hoRef
        (by rw [hlab]; exact hbefore) hcc (by rw [hlab]; exact hatRef) hpicked
  · apply hcover.advance hnext
    intro o ho hat href
    exact hex ⟨o, ho, hat, href⟩

/-- Both executable pruning filters preserve the matching-reference
ledger using the checked workspace from the actual returned child. -/
theorem SweepInput.reference_filters {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel cfuel boundary : Nat} {first short : Bool}
    {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st out : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv)
      cell index st l bs fs parents)
    {R : RefineSt n} {targets : List Nat} {key : Key n}
    (hit : IterOk ctx level R)
    (hlab : R.lab = (l.prepare ctx tcLevel).2.2.2.2.lab)
    (hptn : R.ptn = (l.prepare ctx tcLevel).2.2.2.2.ptn)
    (hcover : Generation.PathCover ctx tcLevel boundary level R tc
      (l.prepare ctx tcLevel).2.2.2.1 targets key cell (some tv))
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcall : Nauty.node (first && tv == tv1) ctx (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (child first level tc tv st) = (.unwind level short, out)) :
    let middle := if first && tv == tv1 then afterChildFirst level tv1 out else out
    let left := { middle with fixedpts := middle.fixedpts.erase tv }
    let small := if short then shortprune cell left else cell
    let filtered := if !first && tv == tv1 then Nauty.longprune small left.fixedpts left.autos else small
    Generation.PathCover ctx tcLevel boundary level R tc (l.prepare ctx tcLevel).2.2.2.1
      targets key filtered (some tv) := by
  intro middle left small filtered
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  have hi := (h.push hgsz hsymm hloop).stored hgsz hsymm hloop
  dsimp only [Parent.child] at hi
  rw [← h.first_eq, ← h.level_eq, ← h.numcells_eq, ← h.tc_eq, hcall] at hi
  have hframe := child_frame (first := first) (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
    h.partition hn0 hl h.path.fixed h.target (h.cursor_mem tv rfl) (first && tv == tv1)
  rw [hcall] at hframe
  have hfixed : left.fixedpts = st.fixedpts := by
    dsimp only [left, middle]
    split <;> exact hframe.2
  have hauto : left.autos = out.autos := by dsimp only [left, middle]; split <;> rfl
  have hchild := h.push hgsz hsymm hloop
  have hlt : level < n := by
    have hd := hchild.frame.depth
    change l.node.level + 1 ≤ n at hd
    rw [← h.level_eq] at hd
    omega
  have hcell : (tc, tc + (l.prepare ctx tcLevel).2.2.2.1 - 1) ∈ cells R.ptn level n := by
    apply isCell_mem_cells
    · rw [hptn]; exact h.window
    · rw [hit.ok.ptnSize]; exact Nat.le_refl _
    · exact hit.ok.ptnEnd
    · have := h.range; have := h.len; omega
  have hs : Generation.PathCover ctx tcLevel boundary level R tc
      (l.prepare ctx tcLevel).2.2.2.1 targets key small (some tv) := by
    dsimp only [small]
    split
    · rename_i hshort
      have hc : short = true := hshort
      subst short
      change Generation.PathCover ctx tcLevel boundary level R tc
        (l.prepare ctx tcLevel).2.2.2.1 targets key (Nauty.shortprune cell left) (some tv)
      apply hcover.shortprune hit hlt hgsz hcell (by have := h.len; omega) (by have := h.len; omega)
      intro fix mcr hb
      have hb' : out.autos.back? = some (fix, mcr) := by
        change left.autos.back? = _ at hb
        rwa [hauto] at hb
      rw [hlab, hptn]
      exact h.short_pair hgsz hsymm hloop hcall fix mcr hb'
    · exact hcover
  dsimp only [filtered]
  split
  · apply hs.longprune hit hlt hgsz hcell (by have := h.len; omega) (by have := h.len; omega)
    intro pair hp hf
    rw [hlab, hptn]
    apply h.pair
    intro w hw hm
    rw [hauto] at hp
    obtain ⟨γ, ha, hfix, hroot, hless⟩ := hi.pairs pair hp w hw hm
    refine ⟨γ, ha, hfix, ?_, hless⟩
    apply h.path.stab γ ha hroot
    intro u hu hum
    apply hfix u hu
    rw [hfixed] at hf
    exact VSet.subset_iff.mp hf u hum
  · exact hs

/-- Reordering the receiving frame transports its frozen child reference
to the exact arrays individualized by the engine. -/
theorem SweepInput.reference_child {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel cfuel boundary : Nat} {first : Bool}
    {level numcells tc tv1 tv index o : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv)
      cell index st l bs fs parents)
    {R : RefineSt n} {targets : List Nat} {key : Key n}
    (hit : IterOk ctx level R)
    (hlab : R.lab = (l.prepare ctx tcLevel).2.2.2.2.lab)
    (hptn : R.ptn = (l.prepare ctx tcLevel).2.2.2.2.ptn) (hnc : R.numcells = numcells)
    (hgsz : ctx.g.size = n)
    (ho : o < (l.prepare ctx tcLevel).2.2.2.1) (hat : R.lab[tc + o]! = tv)
    (href : Generation.ChildPath ctx tcLevel boundary level R tc targets key o) :
    Generation.RefPath ctx tcLevel boundary (level + 1)
      ((child first level tc tv st).refined ctx (level + 1) (numcells + 1)) targets key := by
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  have hch := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
    hl h.partition h.target (h.cursor_mem tv rfl)
  have hlt : level < n := by
    have := hch.1.bc
    have := bcount_le (Generic.Policy.child (n := n) first level tc tv st).ptn (level + 1) n
    omega
  have hr := h.range
  have hlen := h.len
  have hcell : (tc, tc + (l.prepare ctx tcLevel).2.2.2.1 - 1) ∈ cells R.ptn level n := by
    apply isCell_mem_cells
    · rw [hptn]; exact h.window
    · rw [hit.ok.ptnSize]; exact Nat.le_refl _
    · exact hit.ok.ptnEnd
    · omega
  have hcurrent : st.ptn = R.ptn := (h.effect.ptn_eq h.base h.partition).trans hptn.symm
  have hperm : cellsPerm R.ptn level st.lab R.lab := by
    rw [hlab, hptn]
    exact cellsPerm_symm h.effect.perm
  have hmem := h.suspend.chosen
  simp only [← h.tc_eq] at hmem
  obtain ⟨o', ho', hat'⟩ := mem_segN_iff.mp (mem_windowSet.mp hmem).2
  change st.lab[tc + o']! = tv at hat'
  have hh := href.reorderChild hgsz hit hlt h.partition.labSize hperm hcell
    (by omega) (by omega) (by omega) (hat'.trans hat.symm)
  change Generation.RefPath ctx tcLevel boundary (level + 1)
    (childSt ctx level { R with lab := st.lab } tc st.lab[tc + o']!) targets key at hh
  rw [hat'] at hh
  have he : (child first level tc tv st).refined ctx (level + 1) (numcells + 1) =
      childSt ctx level { R with lab := st.lab } tc tv := by
    cases first <;> change refine ctx (level + 1) (breakout n st.lab st.ptn (level + 1) tc tv).1
      (st.ptn.set! tc (level + 1)) (VSet.empty.insert tc) (numcells + 1) = _
    all_goals simp only [childSt, ← hcurrent, hnc]
  rw [he]
  exact hh

end Hex.GraphIso.Nauty.Max
