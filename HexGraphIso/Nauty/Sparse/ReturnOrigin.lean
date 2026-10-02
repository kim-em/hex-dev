/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CanonScatter
public import HexGraphIso.Nauty.Policy.Generic.Short
public import HexGraphIso.Nauty.Policy.Filters
public import HexGraphIso.Nauty.Policy.Workspace
import all HexGraphIso.Nauty.Policy.Generic.Short
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Bounds
import all HexGraphIso.Nauty.Policy.Effect
import all HexGraphIso.Nauty.Policy.Scratch
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

variable {n : Nat}

/-- A short return retains its emitting leaf's state, apart from the
fixed-point cleanup and first-path controls updated by enclosing loops. -/
def LeafReturn (target : Nat) (out : State n) : Prop :=
  ∃ leaf level st, (∃ g numcells before, classify g level numcells before = (leaf, st)) ∧
    (leafExit leaf level st).1 = .unwind target true ∧
    out = { (leafExit leaf level st).2 with
      fixedpts := out.fixedpts, gcaFirst := out.gcaFirst, stabvertex := out.stabvertex }

/-- The nauty cleanup operations retain the state of a short return's origin. -/
theorem shortPolicy : Generic.ShortPolicy (n := n) (LeafReturn (n := n)) where
  leaf := by
    intro g level numcells before c target he
    exact ⟨c.1, level, c.2, ⟨g, numcells, before, rfl⟩, he, rfl⟩
  afterFirst := by
    intro level tv target out h
    obtain ⟨leaf, depth, st, hc, he, hs⟩ := h
    refine ⟨leaf, depth, st, hc, he, ?_⟩
    change afterChildFirst level tv out = _
    rw [hs]
    rfl

  leave := by
    intro tv target out h
    obtain ⟨leaf, depth, st, hc, he, hs⟩ := h
    refine ⟨leaf, depth, st, hc, he, ?_⟩
    change { out with fixedpts := out.fixedpts.erase tv } = _
    rw [hs]
    rfl

/-- The receiving loop reads the emitting leaf's admitted pair in its
own fields. Its target is the canonical ancestor for an explicit pair,
and is bounded by the cheap boundary's parent for an implicit pair. -/
theorem LeafReturn.admission {target : Nat} {out : State n}
    (h : LeafReturn target out) (hcap : 0 < out.wsCap) :
    (out.autos.back? = some (fmperm out.workperm n) ∧ target = out.gcaCanon ∧
      out.workperm ∈ out.genTrace ∧
      (out.workperm.size = n → out.canonlab.size = n →
        out.canonlab.toList.Perm (List.range n) →
        ∀ i, i < n → out.workperm[out.canonlab[i]!]! = out.lab[i]!)) ∨
      (out.autos.back? = some (fmptn out.lab out.ptn out.noncheaplevel n) ∧
        target ≤ out.noncheaplevel - 1) := by
  obtain ⟨leaf, level, st, ⟨g, numcells, before, hclass⟩, he, hs⟩ := h
  have hc := congrArg SearchState.wsCap hs
  change out.wsCap = (leafExit leaf level st).2.wsCap at hc
  rw [leafExit_capacity] at hc
  have hb := congrArg SearchState.autos hs
  change out.autos = (leafExit leaf level st).2.autos at hb
  rcases leafExit_short_pair (hc ▸ hcap) he with ⟨rfl, hp⟩ | ⟨ha, hp⟩
  · have hw : out.workperm = st.workperm :=
      (congrArg SearchState.workperm hs).trans (leafExit_workperm .autoCanon level st)
    have hcanon : out.canonlab = st.canonlab :=
      (congrArg SearchState.canonlab hs).trans (autoCanon_ref level st)
    have hlab : out.lab = st.lab :=
      (congrArg SearchState.lab hs).trans (leafExit_frame .autoCanon level st).1
    refine Or.inl ⟨?_, ?_, ?_, ?_⟩
    · rwa [hb, hw]
    · exact (leafExit_canon_target he).trans (congrArg SearchState.gcaCanon hs).symm
    · have ht := congrArg SearchState.genTrace hs
      change out.genTrace = (leafExit .autoCanon level st).2.genTrace at ht
      rw [ht, leafExit_trace, hw]
      simp
    · intro hwork hsize hperm
      have hm := classify_canon_out (g := g) (level := level) (numcells := numcells)
        (st := before) (by rw [hclass])
      rw [hclass] at hm
      simp only [hw, hcanon, hlab] at hwork hsize hperm ⊢
      exact hm hwork hsize hperm
  · have hl : out.lab = st.lab := (congrArg SearchState.lab hs).trans (leafExit_frame leaf level st).1
    have hptn : out.ptn = st.ptn := (congrArg SearchState.ptn hs).trans (leafExit_frame leaf level st).2.1
    have hn : out.noncheaplevel = st.noncheaplevel :=
      (congrArg SearchState.noncheaplevel hs).trans (leafExit_noncheap leaf level st)
    refine Or.inr ⟨?_, ?_⟩
    · rwa [hb, hl, hptn, hn]
    · rw [hn]
      exact leafExit_cheap_bound ha he

/-- A node's short-prune payload comes from an actual leaf emission,
including when the return crosses several intermediate loops. -/
theorem node_origin (first : Bool) (g : Graph n) (inf tcLevel fuel level numcells : Nat)
    (st : State n) {target : Nat}
    (he : (Generic.node first g inf tcLevel fuel level numcells st).1 = .unwind target true) :
    LeafReturn target (Generic.node first g inf tcLevel fuel level numcells st).2 := by
  exact Generic.node_short shortPolicy first g inf tcLevel fuel level numcells st target he

/-- A sweep transports the emitting leaf's workspace and partition until
the target loop consumes the short-prune request. -/
theorem sweep_origin (first : Bool) (g : Graph n)
    (inf tcLevel fuel cfuel level numcells tc tv1 : Nat) (cursor : Option Nat)
    (cell : VSet n) (index : Nat) (st : State n) {target : Nat}
    (he : (Generic.sweep first g inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).1 =
      .unwind target true) :
    LeafReturn target
      (Generic.sweep first g inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2 := by
  exact Generic.sweep_short shortPolicy first g inf tcLevel fuel cfuel level numcells tc tv1
    cursor cell index st target he

end Hex.GraphIso.Nauty.Sparse
