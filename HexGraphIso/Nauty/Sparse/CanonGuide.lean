/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CanonSource
public import HexGraphIso.Nauty.Sparse.Coverage
import all HexGraphIso.Nauty.Sparse.CanonSource
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A canonical reference pointing to this sweep identifies a child whose
native specification key is already covered by its incumbent. The base is
the frozen parent frame, before sibling permutations and target filtering. -/
def CanonGuide (level tc : Nat) (base : State n) (key : Nat → Key n)
    (best : Option (Key n)) (st : State n) : Prop :=
  st.gcaCanon = level → ∃ v, Covers (key v) best ∧ st.canonlab[tc]! = v ∧
    cellsPerm base.ptn level base.lab st.canonlab

namespace CanonGuide

theorem vacuous {level tc : Nat} {base st : State n}
    {key : Nat → Key n} {best : Option (Key n)} (h : st.gcaCanon < level) :
    CanonGuide level tc base key best st := by
  intro he
  omega

/-- Completed sibling permutations preserve the reference's membership in
the current cells, while its covered key still refers to the frozen base. -/
theorem rebase {G : GraphIso.Sparse.Colored n k} {level tc : Nat} {base st : State n}
    {key : Nat → Key n} {best : Option (Key n)}
    (h : CanonGuide level tc base key best st) (hf : FrameOut G level level base st) :
    CanonGuide level tc st key best st := by
  intro he
  obtain ⟨v, hv, hat, hp⟩ := h he
  refine ⟨v, hv, hat, ?_⟩
  have hperm := cellsPerm_trans (cellsPerm_symm hf.effect.perm) hp
  intro a len hc
  apply hperm a len
  apply isCell_of_low (ptn := st.ptn) (ptn' := base.ptn) _ hc
  intro q hq
  exact (hf.effect.low q hq.symm).symm

/-- The reference remains in the original target window even when an
earlier filter has removed it from the mutable target set. -/
theorem mem {level tc len : Nat} {base st : State n}
    {key : Nat → Key n} {best : Option (Key n)}
    (h : CanonGuide level tc base key best st)
    (hok : LabOk base.lab n) (hc : IsCell base.ptn level tc len)
    (hr : tc + len ≤ base.lab.size) (he : st.gcaCanon = level) :
    ∃ v, Covers (key v) best ∧ st.canonlab[tc]! = v ∧
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

/-- Actual recovery either retains the old covered child or selects the
just-completed child, then clamps the canonical ancestor to this parent. -/
theorem recover {G : GraphIso.Sparse.Colored n k} {level tc tv : Nat}
    {base st out : State n} {key : Nat → Key n} {before after : Option (Key n)}
    (h : CanonGuide level tc base key before st)
    (hbound : st.gcaCanon ≤ level) (hgrows : Grows before after)
    (hdone : Covers (key tv) after) (hframe : FrameOut G level level base st)
    (hreturn : (out.gcaCanon ≤ st.gcaCanon ∧ out.canonlab = st.canonlab) ∨
      (out.canonlab.size = st.lab.size ∧ cellsPerm st.ptn level st.lab out.canonlab ∧
        out.canonlab[tc]! = tv)) (inf : Nat) :
    CanonGuide level tc base key after ((policy (n := n)).recover inf level out) := by
  have hgc : ((policy (n := n)).recover inf level out).gcaCanon = min level out.gcaCanon := by
    change (Nauty.recover inf level out).gcaCanon = _
    exact recover_canon level out
  have hcc := recover_ref inf level out
  intro he
  rw [hgc] at he
  rcases hreturn with hreturn | hreturn
  · have hi : st.gcaCanon = level := by omega
    obtain ⟨v, hv, hat, hp⟩ := h hi
    refine ⟨v, hv.grow hgrows, ?_, ?_⟩
    · change (Nauty.recover inf level out).canonlab[tc]! = v
      rw [hcc, hreturn.2]; exact hat
    · change cellsPerm base.ptn level base.lab (Nauty.recover inf level out).canonlab
      rw [hcc, hreturn.2]; exact hp
  · refine ⟨tv, hdone, ?_, ?_⟩
    · change (Nauty.recover inf level out).canonlab[tc]! = tv
      rw [hcc]; exact hreturn.2.2
    · change cellsPerm base.ptn level base.lab (Nauty.recover inf level out).canonlab
      rw [hcc]
      apply cellsPerm_trans hframe.effect.perm
      intro a len hc
      exact hreturn.2.1 a len (isCell_of_low hframe.effect.low hc)

end CanonGuide

/-- A return pointing to its receiving parent retains that parent's
previously covered reference, before any partition recovery occurs. -/
theorem child_canon_locate {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc tv : Nat} {cell : VSet n}
    {base st : State n} {key : Nat → Key n} {best : Option (Key n)}
    (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (first childFirst : Bool) (ht : Generic.Target State.frame level tc cell st)
    (hv : cell.mem tv = true) (hguide : CanonGuide level tc base key best st) :
    let out := (Generic.node childFirst (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2
    out.gcaCanon = level → ∃ v, Covers (key v) best ∧ out.canonlab[tc]! = v ∧
      cellsPerm base.ptn level base.lab out.canonlab := by
  intro out he
  have hs := child_canon_old (tcLevel := tcLevel) (fuel := fuel)
    h hn hl first childFirst ht hv (Nat.le_of_eq he)
  obtain ⟨v, hv, hat, hp⟩ := hguide (hs.1.symm.trans he)
  refine ⟨v, hv, ?_, ?_⟩
  · rw [hs.2]; exact hat
  · rw [hs.2]; exact hp

/-- The actual child return preserves the guide through first-child
bookkeeping, fixed-point cleanup and parent recovery. Child coverage is the
local induction premise; the reference provenance comes from the native call. -/
theorem child_canon_guide {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc tv1 tv : Nat} {first : Bool} {cell : VSet n}
    {base st : State n} {key : Nat → Key n} {before after : Option (Key n)}
    (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (hbound : st.gcaCanon ≤ level) (hguide : CanonGuide level tc base key before st)
    (hframe : FrameOut G level level base st)
    (hgrows : Grows before after) (hdone : Covers (key tv) after) :
    let childFirst := first && tv == tv1
    let raw := (Generic.node childFirst (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2
    let left := if childFirst then afterChildFirst level tv1 raw else raw
    let out := (policy (n := n)).leaveChild tv left
    CanonGuide level tc base key after ((policy (n := n)).recover (n + 2) level out) := by
  intro childFirst raw left out
  apply hguide.recover hbound hgrows hdone hframe
  have hr := child_canon (tcLevel := tcLevel) (fuel := fuel) h hn hl first childFirst ht hv
  change (out.gcaCanon ≤ st.gcaCanon ∧ out.canonlab = st.canonlab) ∨
    (out.canonlab.size = st.lab.size ∧ cellsPerm st.ptn level st.lab out.canonlab ∧
      out.canonlab[tc]! = tv)
  dsimp only [out, left]
  cases childFirst <;> exact hr

end Hex.GraphIso.Nauty.Sparse
