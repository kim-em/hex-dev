/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Sparse.Search
public import HexGraphIso.Nauty.Policy.Emission
import all HexGraphIso.Nauty.Policy.Preserve
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.Scatter
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

open Emission

private theorem target_log (first : Bool) (g : Graph n) (tcLevel level numcells : Nat)
    (st : State n) : log (chooseTarget first g tcLevel level numcells st).2.2.2 = log st := by
  unfold chooseTarget
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, apply_ite log]
  repeat' first | rfl | split

private theorem classify_log (g : Graph n) (level numcells : Nat) (st : State n) :
    log (classify g level numcells st).2 = log st := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, apply_ite log, scatter_eq]
  simp only [log, ite_self]

theorem afterSweep_emission (first : Bool) (level size index : Nat) (st : State n) :
    log ((policy (n := n)).afterSweep first level size index st) = log st := by
  change log (if first then
    { (afterSweep first level size index st) with
      order := (afterSweep first level size index st).order * index }
    else afterSweep first level size index st) = log st
  split <;>
    change log (afterSweep first level size index st) = log st <;>
    exact afterSweep_log first level size index st

/-- Native refinement and target selection only update graph-specific
scratch. The common leaf action is the only writer of the emission log. -/
theorem emission_preserve (g : Graph n) (inf tcLevel : Nat) (P : Log → Prop)
    (leaf : ∀ v level (st : State n), P (log st) → P (log (leafExit v level st).2)) :
    Generic.Preserve g inf tcLevel (fun st : State n => P (log st)) where
  visit := fun _ _ _ h => h
  record := fun _ _ _ h => h
  compare := fun level code st h => (compare_log level code st).symm ▸ h
  target := fun first level numcells st h => (target_log first g tcLevel level numcells st).symm ▸ h
  terminal := fun _ _ h => h
  classify := fun level numcells st h => (classify_log g level numcells st).symm ▸ h
  leaf := leaf
  cheap := fun first level st h => (cheap_log first level st).symm ▸ h
  child := by
    intro first level tc tv st h
    change P (log (child first level tc tv st))
    rwa [child_log]
  afterChild := fun _ _ _ h => h
  leave := fun _ _ h => h
  recover := by
    intro level st h
    change P (log (Nauty.recover inf level st))
    rwa [recover_log]
  afterSweep := fun first level size index st h => (afterSweep_emission first level size index st).symm ▸ h

/-- Both parts of the log grow through a complete sparse search call. -/
theorem node_extends (first : Bool) (g : Graph n) (inf tcLevel fuel level numcells : Nat)
    (st : State n) :
    Extends (log st) (log (Generic.node first g inf tcLevel fuel level numcells st).2) :=
  Generic.node_sound
    (emission_preserve g inf tcLevel (Extends (log st)) (fun v l s h => h.trans (leaf_extends v l s))).sound
    first fuel level numcells st (.refl _)

theorem sweep_extends (first : Bool) (g : Graph n) (inf tcLevel fuel cfuel : Nat)
    (level numcells tc tv1 : Nat) (cursor : Option Nat) (cell : VSet n) (index : Nat)
    (st : State n) :
    Extends (log st) (log (Generic.sweep first g inf tcLevel fuel cfuel level numcells tc tv1
      cursor cell index st).2.2) :=
  Generic.sweep_sound
    (emission_preserve g inf tcLevel (Extends (log st)) (fun v l s h => h.trans (leaf_extends v l s))).sound
    first fuel cfuel level numcells tc tv1 cursor cell index st (.refl _)

theorem prepare_emission (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    log (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2 = log st :=
  target_log true g tcLevel level _ _

/-- The sparse search reports exactly the recorded count, in discovery order. -/
theorem emissions_valid (g : Graph n) (lab : Array Nat) (ends : List Nat) :
    Valid (log (run g lab ends)) := by
  change Valid (log (runState g lab ends).2)
  unfold runState
  split
  · exact ⟨.refl _, rfl⟩
  · exact Generic.node_sound (emission_preserve g (n + 2) 100 Valid Valid.leaf).sound
      true (n + 2) 1 ends.length _ ⟨.refl _, rfl⟩

end Hex.GraphIso.Nauty.Sparse
