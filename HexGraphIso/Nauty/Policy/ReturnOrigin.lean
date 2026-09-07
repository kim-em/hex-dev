/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Short
public import HexGraphIso.Nauty.Policy.Filters
import all HexGraphIso.Nauty.Policy.Short
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Workspace
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n : Nat}

/-- A short return retains its emitting leaf's state, apart from the
fixed-point cleanup and first-path controls updated by enclosing loops. -/
def LeafReturn (target : Nat) (out : Search n) : Prop :=
  ∃ leaf level st, (leafExit leaf level st).1 = .unwind target true ∧
    out = { (leafExit leaf level st).2 with
      fixedpts := out.fixedpts, gcaFirst := out.gcaFirst, stabvertex := out.stabvertex }

/-- The nauty cleanup operations retain the state of a short return's origin. -/
theorem shortPolicy : Generic.ShortPolicy (n := n) (LeafReturn (n := n)) where
  leaf leaf level st target he := ⟨leaf, level, st, he, rfl⟩
  afterFirst := by
    intro level tv target out h
    obtain ⟨leaf, depth, st, he, hs⟩ := h
    refine ⟨leaf, depth, st, he, ?_⟩
    change afterChildFirst level tv out = _
    rw [hs]
    rfl

  leave := by
    intro tv target out h
    obtain ⟨leaf, depth, st, he, hs⟩ := h
    refine ⟨leaf, depth, st, he, ?_⟩
    change { out with fixedpts := out.fixedpts.erase tv } = _
    rw [hs]
    rfl

/-- The receiving loop reads the emitting leaf's admitted pair. Capacity
can be supplied at the return: it has not changed since the emission. -/
theorem LeafReturn.admission {target : Nat} {out : Search n}
    (h : LeafReturn target out) (hcap : 0 < out.wsCap) :
    ∃ leaf level st, (leafExit leaf level st).1 = .unwind target true ∧
      out = { (leafExit leaf level st).2 with
        fixedpts := out.fixedpts, gcaFirst := out.gcaFirst, stabvertex := out.stabvertex } ∧
      ((leaf = .autoCanon ∧ out.autos.back? = some (fmperm st.workperm n)) ∨
        ((leaf = .bad ∨ ∃ sr, leaf = .better sr) ∧ level ≠ st.noncheaplevel ∧
          out.autos.back? = some (fmptn st.lab st.ptn st.noncheaplevel n))) := by
  obtain ⟨leaf, level, st, he, hs⟩ := h
  refine ⟨leaf, level, st, he, hs, ?_⟩
  have hc := congrArg Search.wsCap hs
  change out.wsCap = (leafExit leaf level st).2.wsCap at hc
  rw [leafExit_capacity] at hc
  have ha := congrArg Search.autos hs
  change out.autos = (leafExit leaf level st).2.autos at ha
  rw [ha]
  exact leafExit_short_pair (hc ▸ hcap) he

/-- A node's short-prune payload comes from an actual leaf emission,
including when the return crosses several intermediate loops. -/
theorem node_origin (first : Bool) (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat)
    (st : Search n) {target : Nat}
    (he : (node first ctx inf tcLevel fuel level numcells st).1 = .unwind target true) :
    LeafReturn target (node first ctx inf tcLevel fuel level numcells st).2 := by
  rw [node_eq_generic] at he ⊢
  exact Generic.node_short shortPolicy first ctx inf tcLevel fuel level numcells st target he

/-- A sweep transports the emitting leaf's workspace and partition until
the target loop consumes the short-prune request. -/
theorem sweep_origin (first : Bool) (ctx : Ctx n)
    (inf tcLevel fuel cfuel level numcells tc tv1 : Nat) (cursor : Option Nat)
    (cell : VSet n) (index : Nat) (st : Search n) {target : Nat}
    (he : (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).1 =
      .unwind target true) :
    LeafReturn target
      (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2 := by
  rw [sweep_eq_generic] at he ⊢
  exact Generic.sweep_short shortPolicy first ctx inf tcLevel fuel cfuel level numcells tc tv1
    cursor cell index st target he

end Hex.GraphIso.Nauty.Engine
