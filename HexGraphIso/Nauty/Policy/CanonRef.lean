/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.CanonCalls
public import HexGraphIso.Nauty.Policy.CallState
public import HexGraphIso.Nauty.Policy.Maximum
import all HexGraphIso.Nauty.Policy.CanonCalls
import all HexGraphIso.Nauty.Policy.CanonFrame
import all HexGraphIso.Nauty.Policy.Maximum
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The actual child either retains the old reference and does not raise
its ancestor, or installs a reference through the chosen vertex. -/
theorem child_canon {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv : Nat} {first : Bool}
    {cell : VSet n} {st : Search n}
    (h : SearchOk G level numcells st)
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (htarget : Generic.Target (fun st => st) level tc cell st) (ht : cell.mem tv = true)
    (childFirst : Bool) :
    let out := (node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st)).2
    (out.gcaCanon ≤ st.gcaCanon ∧ out.canonlab = st.canonlab) ∨
      (out.canonlab.size = st.lab.size ∧ cellsPerm st.ptn level st.lab out.canonlab ∧
        out.canonlab[tc]! = tv) := by
  intro out
  have hc := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
    hlevel h htarget ht
  have hr := node_canon (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
    childFirst hn0 (by omega) hc.1
  rcases hr.source with hr | hr
  · left
    cases first <;> exact hr
  · exact Or.inr (child_store (ctx := ctx) first hn0 hlevel h htarget ht hr.2)

/-- A canonical reference pointing above the child is precisely the
reference held by the receiving parent before the child was entered. -/
theorem child_canon_old {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv : Nat} {first : Bool}
    {cell : VSet n} {st : Search n}
    (h : SearchOk G level numcells st)
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (htarget : Generic.Target (fun st => st) level tc cell st) (ht : cell.mem tv = true)
    (childFirst : Bool) :
    let out := (node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st)).2
    out.gcaCanon ≤ level → out.gcaCanon = st.gcaCanon ∧ out.canonlab = st.canonlab := by
  intro out he
  have hc := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
    hlevel h htarget ht
  have hr := node_canon (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
    childFirst hn0 (by omega) hc.1
  have hs := hr.old (by change out.gcaCanon < level + 1; omega)
  cases first <;> exact hs

/-- Later siblings use the partition-only canonical-return theorem. -/
theorem SweepPre.canon_return {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv1 tv : Nat} {first : Bool}
    {cell : VSet n} {st : Search n}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hn0 : 0 < n) (childFirst : Bool) :
    let out := (node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st)).2
    (out.gcaCanon ≤ st.gcaCanon ∧ out.canonlab = st.canonlab) ∨
      (out.canonlab.size = st.lab.size ∧ cellsPerm st.ptn level st.lab out.canonlab ∧
        out.canonlab[tc]! = tv) :=
  child_canon h.partition hn0 h.positive h.target (h.cursor_mem tv rfl) childFirst

/-- Later siblings retain precisely the reference above their child. -/
theorem SweepPre.canon_old {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv1 tv : Nat} {first : Bool}
    {cell : VSet n} {st : Search n}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hn0 : 0 < n) (childFirst : Bool) :
    let out := (node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st)).2
    out.gcaCanon ≤ level → out.gcaCanon = st.gcaCanon ∧ out.canonlab = st.canonlab :=
  child_canon_old h.partition hn0 h.positive h.target (h.cursor_mem tv rfl) childFirst

/-- At a frozen sweep frame, a canonical ancestor pointing to this level
names a child already bounded by the incumbent. -/
def CanonGuide (level tc : Nat) (base : Search n) (key : Nat → Key n)
    (best : Option (Key n)) (st : Search n) : Prop :=
  st.gcaCanon = level → ∃ v, Generic.Covers (key v) best ∧ st.canonlab[tc]! = v ∧
    cellsPerm base.ptn level base.lab st.canonlab

/-- Before any child has installed a reference at this level, the guide
has no coverage obligation. -/
theorem CanonGuide.vacuous {level tc : Nat} {base st : Search n}
    {key : Nat → Key n} {best : Option (Key n)} (h : st.gcaCanon < level) :
    CanonGuide level tc base key best st := by
  intro he
  omega

/-- A reference expressed in a frozen frame also belongs to the current
frame's cells after labels have been permuted within those cells. -/
theorem CanonGuide.rebase {G : Colored n k} {level tc : Nat} {base st : Search n}
    {key : Nat → Key n} {best : Option (Key n)}
    (h : CanonGuide level tc base key best st)
    (hf : SearchOut G level level base st) :
    CanonGuide level tc st key best st := by
  intro he
  obtain ⟨v, hv, hat, hp⟩ := h he
  refine ⟨v, hv, hat, ?_⟩
  have hperm := cellsPerm_trans (cellsPerm_symm hf.perm) hp
  intro a len hc
  apply hperm a len
  apply isCell_of_low (ptn := st.ptn) (ptn' := base.ptn) _ hc
  intro q hq
  exact (hf.low q hq.symm).symm

/-- The guide's reference vertex belongs to the original target window,
even if a filter has removed it from the mutable target set. -/
theorem CanonGuide.mem {level tc len : Nat} {base st : Search n}
    {key : Nat → Key n} {best : Option (Key n)}
    (h : CanonGuide level tc base key best st)
    (hok : LabOk base.lab n) (hc : IsCell base.ptn level tc len)
    (hr : tc + len ≤ base.lab.size) (he : st.gcaCanon = level) :
    ∃ v, Generic.Covers (key v) best ∧ st.canonlab[tc]! = v ∧
      (windowSet n base.lab tc len).mem v = true := by
  obtain ⟨v, hv, hat, hp⟩ := h he
  have hm : v ∈ segN base.lab tc len := by
    apply (hp tc len hc).mem_iff.mpr
    rw [← hat]
    exact mem_segN_iff.mpr ⟨0, hc.1, by simp⟩
  refine ⟨v, hv, hat, mem_windowSet.mpr ⟨?_, hm⟩⟩
  obtain ⟨o, ho, heq⟩ := mem_segN_iff.mp hm
  rw [← heq]
  exact hok _ (by omega)

/-- A canonical return to this loop names its previously covered
reference child, even before the returned partition is recovered. -/
theorem SweepPre.canon_locate {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv1 tv : Nat} {first : Bool}
    {cell : VSet n} {base st : Search n} {key : Nat → Key n} {best : Option (Key n)}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hn0 : 0 < n) (childFirst : Bool) (hguide : CanonGuide level tc base key best st) :
    let out := (node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st)).2
    out.gcaCanon = level → ∃ v, Generic.Covers (key v) best ∧ out.canonlab[tc]! = v ∧
      cellsPerm base.ptn level base.lab out.canonlab := by
  intro out he
  have hs := h.canon_old (fuel := fuel) hn0 childFirst (Nat.le_of_eq he)
  obtain ⟨v, hv, hat, hp⟩ := hguide (hs.1.symm.trans he)
  refine ⟨v, hv, ?_, ?_⟩
  · rw [hs.2]; exact hat
  · rw [hs.2]; exact hp

/-- The receiving loop uses either its old covered reference or the child
whose result was just absorbed, then clamps the reference's ancestor. -/
theorem CanonGuide.recover {G : Colored n k} {level tc tv : Nat}
    {base st out : Search n} {key : Nat → Key n} {before after : Option (Key n)}
    (h : CanonGuide level tc base key before st)
    (hbound : st.gcaCanon ≤ level) (hgrows : Generic.Grows before after)
    (hdone : Generic.Covers (key tv) after)
    (hframe : SearchOut G level level base st)
    (hreturn : (out.gcaCanon ≤ st.gcaCanon ∧ out.canonlab = st.canonlab) ∨
      (out.canonlab.size = st.lab.size ∧ cellsPerm st.ptn level st.lab out.canonlab ∧
        out.canonlab[tc]! = tv)) (inf : Nat) :
    CanonGuide level tc base key after (recoverLevels level (recoverPtn inf level out)) := by
  have hgc : (recoverLevels level (recoverPtn inf level out)).gcaCanon = min level out.gcaCanon := by
    rw [recover_canon]
    rfl
  have hcc := recover_ref inf level out
  intro he
  rw [hgc] at he
  rcases hreturn with hreturn | hreturn
  · have hi : st.gcaCanon = level := by omega
    obtain ⟨v, hv, hat, hp⟩ := h hi
    refine ⟨v, hv.grow hgrows, ?_, ?_⟩
    · rw [hcc, hreturn.2]; exact hat
    · rw [hcc, hreturn.2]; exact hp
  · refine ⟨tv, hdone, ?_, ?_⟩
    · rw [hcc]; exact hreturn.2.2
    · rw [hcc]
      apply cellsPerm_trans hframe.perm
      intro a len hc
      exact hreturn.2.1 a len (isCell_of_low hframe.low hc)

/-- A child's guide survives both first-child control updates and fixed-point
cleanup. Only the reached partition is required, so this also applies before
any first-path sibling has returned. -/
theorem child_canon_guide {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv1 tv : Nat} {first : Bool}
    {cell : VSet n} {base st : Search n} {key : Nat → Key n}
    {before after : Option (Key n)}
    (h : SearchOk G level numcells st)
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (htarget : Generic.Target (fun st => st) level tc cell st) (ht : cell.mem tv = true)
    (hbound : st.gcaCanon ≤ level)
    (hguide : CanonGuide level tc base key before st)
    (hframe : SearchOut G level level base st)
    (hgrows : Generic.Grows before after) (hdone : Generic.Covers (key tv) after) :
    let childFirst := first && tv == tv1
    let raw := (node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st)).2
    let left := if childFirst then afterChildFirst level tv1 raw else raw
    let out := { left with fixedpts := left.fixedpts.erase tv }
    CanonGuide level tc base key after (recoverLevels level (recoverPtn (n + 2) level out)) := by
  intro childFirst raw left out
  apply hguide.recover hbound hgrows hdone hframe
  have hr := child_canon (first := first) (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
    h hn0 hlevel htarget ht childFirst
  change (out.gcaCanon ≤ st.gcaCanon ∧ out.canonlab = st.canonlab) ∨
    (out.canonlab.size = st.lab.size ∧ cellsPerm st.ptn level st.lab out.canonlab ∧
      out.canonlab[tc]! = tv)
  dsimp only [out, left]
  cases childFirst <;> exact hr

end Hex.GraphIso.Nauty
