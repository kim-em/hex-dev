/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Exit.Classify
public import HexGraphIso.Nauty.Correct.State.Induction

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat}

/-- A canonical reference belonging to the current frame comes from a
child already behind its cursor. An older ancestor reference has no local
source obligation. -/
structure CanonPast (level pos : Nat) (cursor : Option Nat) (st : SearchSt n) : Prop where
  cap : st.gcaCanon ≤ level
  source : st.gcaCanon = level → ¬ After cursor st.canonlab[pos]!

/-- An ancestor reference imposes no source obligation at a fresh frame. -/
theorem CanonPast.start {level pos : Nat} {st : SearchSt n} (h : st.gcaCanon < level) :
    CanonPast level pos none st := ⟨Nat.le_of_lt h, fun he => by omega⟩

/-- Advancing a sweep cursor retains every older canonical source. -/
theorem CanonPast.advance {level pos tv : Nat} {cursor : Option Nat} {st : SearchSt n}
    (h : CanonPast level pos cursor st) (ha : After cursor tv) :
    CanonPast level pos (some tv) st := by
  refine ⟨h.cap, ?_⟩
  intro he
  have hs := h.source he
  cases cursor with
  | none => exact (hs trivial).elim
  | some c =>
    change c < tv at ha
    change ¬ c < st.canonlab[pos]! at hs
    change ¬ tv < st.canonlab[pos]!
    omega

/-- The reference child is strictly earlier than the next visited child. -/
theorem CanonPast.before {level pos tv : Nat} {cursor : Option Nat} {st : SearchSt n}
    {tcell : VSet n} (h : CanonPast level pos cursor st)
    (hnext : tcell.nextElem cursor = some tv) (he : st.gcaCanon = level) :
    st.canonlab[pos]! < tv := by
  have hs := h.source he
  have ha := nextElem_after hnext
  cases cursor with
  | none => exact (hs trivial).elim
  | some c =>
    change ¬ c < st.canonlab[pos]! at hs
    change c < tv at ha
    omega

/-- Updates to unrelated bookkeeping preserve the canonical source. -/
theorem CanonPast.stateEq {level pos : Nat} {cursor : Option Nat} {st out : SearchSt n}
    (h : CanonPast level pos cursor st) (hgca : out.gcaCanon = st.gcaCanon)
    (hlab : out.canonlab = st.canonlab) : CanonPast level pos cursor out := by
  exact ⟨hgca ▸ h.cap, fun he => by rw [hlab]; exact h.source (hgca.symm.trans he)⟩

/-- Recovering after a child visit keeps an old source or records the
visited child as the new source. The old/new disjunction is used directly;
no cell-location assertion is made about an old ancestor reference. -/
theorem CanonPast.recover {inf level pos tv : Nat} {cursor : Option Nat}
    {st child out : SearchSt n} (h : CanonPast level pos cursor st)
    (ha : After cursor tv) (hgca : child.gcaCanon = st.gcaCanon)
    (hlab : child.canonlab = st.canonlab)
    (hguide : GuideRel (level + 1) child out)
    (hcell : IsCell child.ptn (level + 1) pos 1) (hat : child.lab[pos]! = tv) :
    CanonPast level pos (some tv) (Nauty.recover n inf level out) := by
  have hrecGca := recover_gcaCanon n inf level out
  have hrecLab := (recover_frames n inf level out).1
  refine ⟨?_, ?_⟩
  · rw [hrecGca]
    split <;> omega
  · intro he
    rw [hrecLab]
    change ¬ tv < out.canonlab[pos]!
    rcases hguide.canon with hold | hnew
    · have hcap : out.gcaCanon ≤ level := by rw [hold.1, hgca]; exact h.cap
      rw [hrecGca, ite_eq_right (by omega)] at he
      have hs := (h.advance ha).source (hgca.symm.trans (hold.1.symm.trans he))
      rw [hold.2, hlab]
      exact hs
    · have hv := cellsPerm_singleton hnew.2 hcell
      rw [← hv, hat]
      omega

/-- A child return below its entry keeps the old canonical reference
whenever its canonical guide is also below that entry. -/
theorem canon_old {level : Nat} {st out : SearchSt n}
    (h : GuideRel level st out) (hbelow : out.gcaCanon < level) :
    out.gcaCanon = st.gcaCanon ∧ out.canonlab = st.canonlab := by
  rcases h.canon with hold | hnew
  · exact hold
  · omega

/-- A canonical return to this frame names an earlier original child.
The return tag and old-reference alternative recover its location from
the existing frame references, including after target-set pruning. -/
theorem CanonPast.locate {ctx : Ctx n} {tcLevel specFuel level tc len numcells tv : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {cursor : Option Nat} {tcell : VSet n}
    {st child out : SearchSt n} {best : Option (Key n)}
    (h : CanonPast level tc cursor st) (hnext : tcell.nextElem cursor = some tv)
    (hrefs : FrameRefs ctx tcLevel specFuel level codes rsLab rsPtn tc len numcells st best)
    (hgca : child.gcaCanon = st.gcaCanon) (hlab : child.canonlab = st.canonlab)
    (hguide : GuideRel (level + 1) child out) (hat : out.gcaCanon = level) :
    ∃ o, o < len ∧ out.canonlab[tc]! = rsLab[tc + o]! ∧
      rsLab[tc + o]! < tv ∧ cellsPerm rsPtn level rsLab out.canonlab := by
  have hold := canon_old hguide (by omega)
  have hlevel : st.gcaCanon = level := hgca.symm.trans (hold.1.symm.trans hat)
  obtain ⟨o, ho, _, hpos, hperm⟩ := hrefs.canon hlevel
  have hbefore := h.before hnext hlevel
  refine ⟨o, ho, ?_, ?_, ?_⟩
  · rw [hold.2, hlab]
    exact hpos
  · rw [← hpos]
    exact hbefore
  · rw [hold.2, hlab]
    exact hperm

end Hex.GraphIso.Nauty.Generation
