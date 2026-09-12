/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Generic.Stable
public import HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Generic.Stable
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- Every off-path operation retains each previously emitted generator. -/
theorem tracePolicy (ctx : Ctx n) (inf tcLevel : Nat) (γ : Array Nat) :
    Generic.StablePolicy ctx inf tcLevel (fun st : Search n => γ ∈ st.genTrace) where
  code := by intros; trivial
  visit := by intros; assumption
  compare := by
    intro level code st _ h
    change γ ∈ (compareCodes level code st).genTrace
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.genTrace, ite_self]
    exact h
  target := by
    intro level numcells st h
    change γ ∈ (chooseTarget false ctx tcLevel level numcells st).2.2.2.genTrace
    rw [chooseTarget_fields]
    exact h
  classify := by
    intro level numcells st h
    exact ⟨by change γ ∈ (classify ctx level numcells st).2.genTrace; rw [classify_trace]; exact h, trivial⟩
  leaf := by
    intro leaf level st _ h
    change γ ∈ (leafExit leaf level st).2.genTrace
    rw [leafExit_trace]
    cases leaf <;> first | exact h | exact Array.mem_push.mpr (Or.inl h)
  cheap := by
    intro first level st h
    change γ ∈ (cheapCheck first level st).genTrace
    unfold cheapCheck
    split <;> exact h
  child := by
    intro first level tc tv st h
    cases first <;> exact h
  leave := by intros; assumption
  recover := by
    intro level st h
    change γ ∈ (Nauty.recover inf level st).genTrace
    unfold Nauty.recover recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.genTrace, ite_self]
    exact h
  afterSweep := by
    intro level size index st h
    change γ ∈ (afterSweep false level size index st).genTrace
    unfold afterSweep
    split <;> exact h

/-- An off-path node retains its whole incoming trace. -/
theorem node_contains (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat) (st : Search n)
    {γ : Array Nat} (h : γ ∈ st.genTrace) :
    γ ∈ (node false ctx inf tcLevel fuel level numcells st).2.genTrace := by
  rw [node_eq_generic]
  exact Generic.node_stable (tracePolicy ctx inf tcLevel γ) fuel level numcells st h

/-- A sibling suffix retains every child generator already received. -/
theorem sweep_contains (ctx : Ctx n) (inf tcLevel fuel cfuel : Nat) (first : Bool)
    (level numcells tc tv1 index : Nat) (cursor : Option Nat) (cell : VSet n) (st : Search n)
    (hpast : Generic.Past first tv1 cursor) {γ : Array Nat} (h : γ ∈ st.genTrace) :
    γ ∈ (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.genTrace := by
  rw [sweep_eq_generic]
  exact Generic.sweep_stable (tracePolicy ctx inf tcLevel γ) first fuel cfuel level numcells tc tv1
    index cursor cell st hpast h

end Hex.GraphIso.Nauty
