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
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- The actual child either retains the old reference and does not raise
its ancestor, or installs a reference through the chosen vertex. -/
theorem SweepPre.canon_return {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv1 tv : Nat} {first : Bool}
    {cell : VSet n} {st : Search n}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hn0 : 0 < n) (childFirst : Bool) :
    let out := (node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st)).2
    (out.gcaCanon ≤ st.gcaCanon ∧ out.canonlab = st.canonlab) ∨
      (out.canonlab.size = st.lab.size ∧ cellsPerm st.ptn level st.lab out.canonlab ∧
        out.canonlab[tc]! = tv) := by
  intro out
  have ht := h.cursor_mem tv rfl
  have hc := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
    h.positive h.partition h.target ht
  have hr := node_canon (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
    childFirst hn0 (by have := h.positive; omega) hc.1
  rcases hr.source with hr | hr
  · left
    cases first <;> exact hr
  · exact Or.inr (child_store (ctx := ctx) first hn0 h.positive h.partition h.target ht hr.2)

/-- A canonical reference pointing above the child is precisely the
reference held by the receiving parent before the child was entered. -/
theorem SweepPre.canon_old {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv1 tv : Nat} {first : Bool}
    {cell : VSet n} {st : Search n}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hn0 : 0 < n) (childFirst : Bool) :
    let out := (node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st)).2
    out.gcaCanon ≤ level → out.gcaCanon = st.gcaCanon ∧ out.canonlab = st.canonlab := by
  intro out he
  have ht := h.cursor_mem tv rfl
  have hc := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
    h.positive h.partition h.target ht
  have hr := node_canon (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
    childFirst hn0 (by have := h.positive; omega) hc.1
  have hs := hr.old (by change out.gcaCanon < level + 1; omega)
  cases first <;> exact hs

/-- At a frozen sweep frame, a canonical ancestor pointing to this level
names a child already bounded by the incumbent. -/
def CanonGuide (level tc : Nat) (base : Search n) (key : Nat → Key n)
    (best : Option (Key n)) (st : Search n) : Prop :=
  st.gcaCanon = level → ∃ v, Generic.Covers (key v) best ∧ st.canonlab[tc]! = v ∧
    cellsPerm base.ptn level base.lab st.canonlab

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
    (hframe : SearchOut G level level base.view st.view)
    (hreturn : (out.gcaCanon ≤ st.gcaCanon ∧ out.canonlab = st.canonlab) ∨
      (out.canonlab.size = st.lab.size ∧ cellsPerm st.ptn level st.lab out.canonlab ∧
        out.canonlab[tc]! = tv)) (inf : Nat) :
    CanonGuide level tc base key after (recoverLevels level (recoverPtn inf level out)) := by
  have hgc : (recoverLevels level (recoverPtn inf level out)).gcaCanon = min level out.gcaCanon := by
    rw [recover_canon]
    rfl
  have hcc : (recoverLevels level (recoverPtn inf level out)).canonlab = out.canonlab := by
    unfold recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite Search.canonlab]
    repeat' split
    all_goals rfl
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

/-- An actual child supplies the reference alternatives needed to restore
the receiving loop's canonical guide after fixed-point cleanup. -/
theorem SweepPre.canon_guide {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv1 tv : Nat} {first : Bool}
    {cell : VSet n} {base st : Search n} {key : Nat → Key n}
    {before after : Option (Key n)}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hn0 : 0 < n) (childFirst : Bool)
    (hguide : CanonGuide level tc base key before st)
    (hframe : SearchOut G level level base.view st.view)
    (hgrows : Generic.Grows before after) (hdone : Generic.Covers (key tv) after) :
    let raw := (node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st)).2
    let out := { raw with fixedpts := raw.fixedpts.erase tv }
    CanonGuide level tc base key after (recoverLevels level (recoverPtn (n + 2) level out)) := by
  intro raw out
  apply hguide.recover h.canonAncestor hgrows hdone hframe
  exact h.canon_return (fuel := fuel) hn0 childFirst

end Hex.GraphIso.Nauty.Engine
