/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Partition
public import HexGraphIso.Nauty.Policy.Controls
public import HexGraphIso.Nauty.Invariant.Singleton
import all HexGraphIso.Nauty.Policy.Reach
import all HexGraphIso.Nauty.Policy.Effect
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- A retained reference cannot acquire a deeper ancestor. An installed
reference belongs to the current partition and cannot return above it.
Recovery may lower either ancestor only as far as the current level. -/
structure CanonOut (level : Nat) (st out : Search n) : Prop where
  floor : min level st.gcaCanon ≤ out.gcaCanon
  source : (out.gcaCanon ≤ st.gcaCanon ∧ out.canonlab = st.canonlab) ∨
    (level ≤ out.gcaCanon ∧ out.canonlab.size = st.lab.size ∧
      cellsPerm st.ptn level st.lab out.canonlab)

/-- Retaining the canonical reference is a reflexive effect. -/
theorem CanonOut.refl (level : Nat) (st : Search n) : CanonOut level st st :=
  ⟨Nat.min_le_right _ _, Or.inl ⟨Nat.le_refl _, rfl⟩⟩

/-- Bookkeeping that retains the reference and ancestor preserves its effect. -/
theorem CanonOut.fields {level : Nat} {st out result : Search n}
    (h : CanonOut level st out) (hc : result.canonlab = out.canonlab)
    (hg : result.gcaCanon = out.gcaCanon) : CanonOut level st result := by
  constructor
  · rw [hg]; exact h.floor
  · rcases h.source with hs | hs
    · exact Or.inl ⟨by rw [hg]; exact hs.1, hc.trans hs.2⟩
    · exact Or.inr ⟨by rw [hg]; exact hs.1,
        by rw [hc]; exact hs.2.1, by rw [hc]; exact hs.2.2⟩

/-- Canonical effects compose using the partition effect of the first call. -/
theorem CanonOut.trans {G : Colored n k} {level : Nat} {st mid out : Search n}
    (h : CanonOut level st mid) (hnext : CanonOut level mid out)
    (he : SearchOut G level level st.view mid.view) : CanonOut level st out := by
  have hf := h.floor
  have hn := hnext.floor
  refine ⟨by omega, ?_⟩
  rcases hnext.source with hs | hs
  · rcases h.source with hb | hb
    · exact Or.inl ⟨Nat.le_trans hs.1 hb.1, hs.2.trans hb.2⟩
    · exact Or.inr ⟨by omega, by rw [hs.2]; exact hb.2.1,
        by rw [hs.2]; exact hb.2.2⟩
  · right
    refine ⟨hs.1, hs.2.1.trans he.labSize, cellsPerm_trans he.perm ?_⟩
    intro a len hc
    exact hs.2.2 a len (isCell_of_low he.low hc)

/-- Transport a reference through a finer partition while retaining its
ancestor bounds and the alternative of an unchanged reference. -/
theorem CanonOut.lift {level next : Nat} {st mid out : Search n}
    (h : CanonOut next mid out) (hlevel : level ≤ next)
    (hc : mid.canonlab = st.canonlab) (hg : mid.gcaCanon = st.gcaCanon)
    (hs : mid.lab.size = st.lab.size) (hp : cellsPerm st.ptn level st.lab mid.lab)
    (hlift : ∀ lab, lab.size = mid.lab.size → cellsPerm mid.ptn next mid.lab lab →
      cellsPerm st.ptn level mid.lab lab) : CanonOut level st out := by
  have hf := h.floor
  rw [hg] at hf
  refine ⟨by omega, ?_⟩
  rcases h.source with hb | hb
  · exact Or.inl ⟨by rw [← hg]; exact hb.1, hb.2.trans hc⟩
  · exact Or.inr ⟨Nat.le_trans hlevel hb.1, hb.2.1.trans hs,
      cellsPerm_trans hp (hlift _ hb.2.1 hb.2.2)⟩

/-- An ancestor deeper than the incoming one binds the reference to this call. -/
theorem CanonOut.within {level : Nat} {st out : Search n}
    (h : CanonOut level st out) (hg : st.gcaCanon < out.gcaCanon) :
    out.canonlab.size = st.lab.size ∧ cellsPerm st.ptn level st.lab out.canonlab := by
  rcases h.source with hs | hs
  · omega
  · exact hs.2

/-- A reference pointing above the call retains its incoming labelling
and ancestor, even when that labelling is also reachable in this subtree. -/
theorem CanonOut.old {level : Nat} {st out : Search n}
    (h : CanonOut level st out) (hg : out.gcaCanon < level) :
    out.gcaCanon = st.gcaCanon ∧ out.canonlab = st.canonlab := by
  have hf := h.floor
  rcases h.source with hs | hs
  · exact ⟨by omega, hs.2⟩
  · omega

/-- Refinement transports a canonical effect to the node's entry partition. -/
theorem CanonOut.visit {G : Colored n k} {ctx : Ctx n} {level numcells : Nat}
    {st out : Search n} (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st.view)
    (h : CanonOut level (visit ctx level numcells st).2.2 out) : CanonOut level st out := by
  let mid := (Engine.visit ctx level numcells st).2.2
  have hend := searchOk_end hn0 hok hlevel
  change st.ptn[st.ptn.size - 1]! ≤ level at hend
  have hs : st.lab.size = st.ptn.size := hok.labSize.trans hok.ptnSize.symm
  have hr := refine_refInv (ctx := ctx) (level := level)
    (lab := st.lab) (ptn := st.ptn) (active := st.active) (numcells := numcells)
    (Nat.le_of_eq hok.ptnSize.symm) hs hend
  have hp : mid.ptn.size = st.ptn.size := hr.ptnSize
  have hl : mid.lab.size = st.lab.size := hr.labSize
  have hclosed : ∀ q, st.ptn[q]! ≤ level → mid.ptn[q]! = st.ptn[q]! :=
    fun q hq => refine_frozen hok.ptnSize.symm hs hend hq
  have hend' : mid.ptn[mid.ptn.size - 1]! ≤ level := by
    rw [hp, hclosed _ hend]
    exact hend
  apply h.lift (st := st) (Nat.le_refl _) rfl rfl hl hr.perm
  intro lab hsize hperm
  apply cellsPerm_coarsen (ptnF := mid.ptn) (levF := level) hp.symm
    (hl.trans (hs.trans hp.symm)) (hsize.trans (hl.trans (hs.trans hp.symm))) hperm hend' hend
  intro q hq
  rw [hclosed q hq]
  exact hq

/-- A reference stored within the child retains the chosen vertex at
the target position and lies within the parent's cells. -/
theorem child_store {G : Colored n k} {ctx : Ctx n}
    {level numcells tc tv : Nat} {st : Search n} {lab : Array Nat} {cell : VSet n}
    (first : Bool) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st.view)
    (htarget : Generic.Target Search.view level tc cell st) (htv : cell.mem tv = true)
    (hsaved : lab.size = (Engine.child first level tc tv st).lab.size ∧
      cellsPerm (Engine.child first level tc tv st).ptn (level + 1)
        (Engine.child first level tc tv st).lab lab) :
    lab.size = st.lab.size ∧ cellsPerm st.ptn level st.lab lab ∧ lab[tc]! = tv := by
  let mid := Engine.child first level tc tv st
  have hc := (reachPolicy G ctx 0 hn0).child first level numcells tc tv cell st hlevel hok htarget htv
  have he := hc.2 mid (SearchOut.refl G level (level + 1) hc.1.reach)
  have hp : mid.ptn.size = st.ptn.size := he.ptnSize
  have hl : mid.lab.size = st.lab.size := he.labSize
  have hs : mid.lab.size = mid.ptn.size := hc.1.labSize.trans hc.1.ptnSize.symm
  refine ⟨hsaved.1.trans hl, cellsPerm_trans he.perm ?_, ?_⟩
  · apply cellsPerm_coarsen (ptnF := mid.ptn) (levF := level + 1) hp.symm
      hs (hsaved.1.trans hs) hsaved.2
      (searchOk_end hn0 hc.1 (by omega)) (searchOk_end hn0 hok hlevel)
    intro q hq
    have hsame := he.low q (Or.inl hq)
    change mid.ptn[q]! = st.ptn[q]! at hsame
    rw [hsame]
    omega
  · have hls : st.lab.size = n := hok.labSize
    have hps : st.ptn.size = n := hok.ptnSize
    obtain ⟨len, htcell, hm⟩ := htarget
    obtain ⟨hcell, hlen, hrange⟩ := htcell (mem_ne_empty htv)
    obtain ⟨o, ho, hv⟩ := mem_segN_iff.mp (hm tv htv)
    change st.lab[tc + o]! = tv at hv
    have hsingle : IsCell mid.ptn (level + 1) tc 1 := by
      have ht : tc < st.ptn.size := by rw [hps]; omega
      have hh := isCell_breakout_target (n := n) (lab := st.lab) (tv := tv) ht hcell.2.1
      cases first <;> exact hh
    rw [← cellsPerm_singleton hsaved.2 hsingle]
    have hinj : LabInj st.lab st.lab.size := by
      rw [hls]
      exact labInj_of_reach hok.labSize hn0 hok.reach
    have hat := breakout_at_target (n := n) (ptn := st.ptn) (level := level) hinj
      (show tc + o < st.lab.size by rw [hls]; omega)
    rw [hv] at hat
    cases first <;> exact hat

/-- A child's newly installed reference lies within its parent's cells. -/
theorem CanonOut.child {G : Colored n k} {ctx : Ctx n}
    {level numcells tc tv : Nat} {st out : Search n} {cell : VSet n}
    (first : Bool) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st.view)
    (htarget : Generic.Target Search.view level tc cell st) (htv : cell.mem tv = true)
    (h : CanonOut (level + 1) (Engine.child first level tc tv st) out) :
    CanonOut level st out := by
  have hf := h.floor
  have hg : (Engine.child first level tc tv st).gcaCanon = st.gcaCanon := by cases first <;> rfl
  rw [hg] at hf
  refine ⟨by omega, ?_⟩
  rcases h.source with hs | hs
  · left
    cases first <;> exact hs
  · have hc := child_store (ctx := ctx) first hn0 hlevel hok htarget htv hs.2
    exact Or.inr ⟨by omega, hc.1, hc.2.1⟩

/-- Leaf installation is the only leaf action that raises the canonical ancestor. -/
theorem canon_leaf (leaf : Leaf) (level : Nat) (st : Search n) :
    CanonOut level st (leafExit leaf level st).2 := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals first
    | exact ⟨Nat.min_le_right _ _, Or.inl ⟨Nat.le_refl _, rfl⟩⟩
    | exact ⟨by rw [admit_canon]; exact Nat.min_le_right _ _,
        Or.inl ⟨Nat.le_of_eq (admit_canon _), (admit_frame _).2.2.2⟩⟩
    | exact ⟨by rw [pruneReturn_canon]; exact Nat.min_le_right _ _,
        Or.inl ⟨Nat.le_of_eq (pruneReturn_canon level _), (pruneReturn_frame level _).2.2.2⟩⟩
    | exact ⟨by rw [pruneReturn_canon]; exact Nat.min_le_left _ _,
        Or.inr ⟨by rw [pruneReturn_canon]; exact Nat.le_refl _,
          congrArg Array.size (pruneReturn_frame level _).2.2.2,
          by rw [(pruneReturn_frame level _).2.2.2]; exact cellsPerm_refl _ _ _⟩⟩

/-- Recovery lowers the canonical ancestor and keeps its stored labelling. -/
theorem CanonOut.recover {level : Nat} {st out : Search n}
    (h : CanonOut level st out) (inf : Nat) :
    CanonOut level st (recoverLevels level (recoverPtn inf level out)) := by
  have hg : (recoverLevels level (recoverPtn inf level out)).gcaCanon = min level out.gcaCanon := by
    rw [recover_canon]
    rfl
  have hc := recover_ref inf level out
  have hf := h.floor
  constructor
  · rw [hg]; omega
  · rcases h.source with hs | hs
    · exact Or.inl ⟨by rw [hg]; omega, hc.trans hs.2⟩
    · exact Or.inr ⟨by rw [hg]; omega,
        by rw [hc]; exact hs.2.1, by rw [hc]; exact hs.2.2⟩

/-- Finishing a sweep changes only the all-same level. -/
theorem CanonOut.afterSweep {level : Nat} {st out : Search n}
    (h : CanonOut level st out) (first : Bool) (size index : Nat) :
    CanonOut level st (afterSweep first level size index out) := by
  unfold Engine.afterSweep
  split <;> exact h.fields rfl rfl

end Hex.GraphIso.Nauty.Engine
