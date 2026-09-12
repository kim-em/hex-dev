/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Search
public import HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generic.Stable
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.Scatter
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse.Order

open Std.Do
set_option mvcgen.warning false

theorem admit (st : SearchState n κ) : (Nauty.admit st).order = st.order := by
  unfold Nauty.admit pushAuto
  simp only [Id.run_pure]
  split <;> rfl

theorem leaf (leaf : Leaf) (level : Nat) (st : SearchState n κ) :
    (leafExit leaf level st).2.order = st.order := by
  cases leaf <;> unfold leafExit pruneReturn install pushAuto
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
    apply_ite SearchState.order, admit, ite_self]

theorem target (first : Bool) (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (chooseTarget first g tcLevel level numcells st).2.2.2.order = st.order := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n => out.2.2.2.order = st.order)
  mvcgen
  all_goals simp_all +zetaDelta

theorem classify (g : Graph n) (level numcells : Nat) (st : State n) :
    (Sparse.classify g level numcells st).2.order = st.order := by
  unfold Sparse.classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.order, ite_self]

theorem cheap (first : Bool) (level : Nat) (st : State n) :
    (cheapCheck first level st).order = st.order := by
  unfold cheapCheck
  split <;> rfl

theorem child (first : Bool) (level tc tv : Nat) (st : State n) :
    ((Sparse.policy (n := n)).child first level tc tv st).order = st.order := by
  cases first <;> rfl

theorem recover (inf level : Nat) (st : State n) :
    ((Sparse.policy (n := n)).recover inf level st).order = st.order := by
  change (recoverLevels level (recoverPtn inf level st)).order = st.order
  unfold recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.order, ite_self]

/-- Only closing a first-path sweep changes the accumulator. -/
theorem close (first : Bool) (level size index : Nat) (st : State n) :
    ((Sparse.policy (n := n)).afterSweep first level size index st).order =
      if first then st.order * index else st.order := by
  change (if first then { (Nauty.afterSweep first level size index st) with
    order := (Nauty.afterSweep first level size index st).order * index }
    else Nauty.afterSweep first level size index st).order = _
  cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals unfold Nauty.afterSweep; split <;> rfl

/-- Refinement, target selection and first-code installation retain the
incoming accumulator before the first child is individualized. -/
theorem prepare (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2.order = st.order := by
  unfold Generic.prepareFirst
  change (chooseTarget true g tcLevel level (visit g level numcells st).1
    (recordFirst level (visit g level numcells st).2.1 (visit g level numcells st).2.2)).2.2.2.order = _
  rw [target]
  rfl

/-- The off-path policy preserves the actual order accumulator through
every refinement, admission, pruning return and recovery. -/
theorem policy (g : Graph n) (inf tcLevel value : Nat) :
    Generic.StablePolicy g inf tcLevel (fun st : State n => st.order = value) where
  code := fun _ _ _ => trivial
  visit := fun _ _ _ h => h
  compare := by
    intro level code st _ h
    change (compareCodes level code st).order = value
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.order, ite_self]
    exact h
  target := fun level numcells st h => (target false g tcLevel level numcells st).trans h
  classify := fun level numcells st h => ⟨(classify g level numcells st).trans h, trivial⟩
  leaf := fun leaf level st _ h => (Order.leaf leaf level st).trans h
  cheap := fun first level st h => (cheap first level st).trans h
  child := fun first level tc tv st h => (child first level tc tv st).trans h
  leave := fun _ _ h => h
  recover := fun level st h => (recover inf level st).trans h
  afterSweep := fun level size index st h => (close false level size index st).trans h

theorem node (g : Graph n) (inf tcLevel fuel level numcells : Nat) (st : State n) :
    (Generic.node false g inf tcLevel fuel level numcells st).2.order = st.order :=
  Generic.node_stable (policy g inf tcLevel st.order) fuel level numcells st rfl

theorem sweep (first : Bool) (g : Graph n) (inf tcLevel fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : State n) (hpast : Generic.Past first tv1 cursor) :
    (Generic.sweep first g inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.order =
      st.order :=
  Generic.sweep_stable (policy g inf tcLevel st.order) first fuel cfuel level numcells tc tv1
    index cursor cell st hpast rfl

/-- The full first sweep retains exactly the guiding child's order
accumulator, before the receiver multiplies by its own index. -/
theorem first (g : Graph n) (inf tcLevel fuel cfuel level numcells tc tv index : Nat)
    (cell : VSet n) (st : State n) (horbit : st.orbits[tv]! = tv) :
    (Generic.sweep true g inf tcLevel fuel (cfuel + 1)
      level numcells tc tv (some tv) cell index st).2.2.order =
    (Generic.node true g inf tcLevel fuel (level + 1) (numcells + 1)
      ((Sparse.policy (n := n)).child true level tc tv st)).2.order :=
  Generic.sweep_first_stable (policy g inf tcLevel _) (fun _ _ _ h => h)
    fuel cfuel level numcells tc tv index cell st horbit rfl

end Hex.GraphIso.Nauty.Sparse.Order
