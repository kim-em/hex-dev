/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstPath
public import HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Off-path target selection may borrow scratch and update comparison
controls, but retains all saved first-path reference fields. -/
theorem chooseTarget_reference (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (chooseTarget false g tcLevel level numcells st).2.2.2.reference = st.reference := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n =>
    out.2.2.2.reference = st.reference)
  mvcgen
  all_goals simp_all +zetaDelta [SearchState.reference]

/-- Native row comparisons and automorphism scattering preserve the saved
first leaf, first codes and target hints. -/
theorem classify_reference (g : Graph n) (level numcells : Nat) (st : State n) :
    (classify g level numcells st).2.reference = st.reference := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    SearchState.reference, apply_ite SearchState.firstcode, apply_ite SearchState.firsttc,
    apply_ite SearchState.firstlab, ite_self]

/-- All actual sparse off-path operations preserve the first reference.
Common bookkeeping lemmas apply to arbitrary canonical storage. -/
theorem referencePolicy (g : Graph n) (inf tcLevel : Nat) :
    Generic.ReferencePolicy g inf tcLevel (SearchState.reference (n := n) (κ := Storage n)) where
  visit := fun _ _ _ => rfl
  compare := by
    intro level code st
    change (compareCodes level code st).reference = st.reference
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, SearchState.reference,
      apply_ite SearchState.firstcode, apply_ite SearchState.firsttc,
      apply_ite SearchState.firstlab, ite_self]
  target := chooseTarget_reference g tcLevel
  classify := classify_reference g
  leaf := leafExit_reference
  cheap := by
    intro first level st
    change (cheapCheck first level st).reference = st.reference
    unfold cheapCheck
    split <;> rfl
  child := by
    intro first level tc tv st
    cases first <;> rfl
  leave := fun _ _ => rfl
  recover := by
    intro level st
    change (recoverLevels level (recoverPtn inf level st)).reference = st.reference
    unfold recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, SearchState.reference,
      apply_ite SearchState.firstcode, apply_ite SearchState.firsttc,
      apply_ite SearchState.firstlab, ite_self]
  afterSweep := by
    intro first level size index st
    change (if first then { (Nauty.afterSweep first level size index st) with
      order := (Nauty.afterSweep first level size index st).order * index }
      else Nauty.afterSweep first level size index st).reference = st.reference
    cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals unfold Nauty.afterSweep; split <;> rfl

theorem node_reference (g : Graph n) (inf tcLevel fuel level numcells : Nat) (st : State n) :
    (Generic.node false g inf tcLevel fuel level numcells st).2.reference = st.reference :=
  Generic.node_reference (referencePolicy g inf tcLevel) fuel level numcells st

theorem sweep_reference (first : Bool) (g : Graph n)
    (inf tcLevel fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : State n) (hpast : Generic.Past first tv1 cursor) :
    (Generic.sweep first g inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.reference =
      st.reference :=
  Generic.sweep_reference (referencePolicy g inf tcLevel) first fuel cfuel level numcells tc tv1
    index cursor cell st hpast

/-- The saved reference of the completed first-path call is exactly the
reference installed at its actual first leaf. -/
theorem firstPath_reference {g : Graph n} {inf tcLevel fuel level numcells last : Nat}
    {st leaf : State n} (path : Generic.FirstPath g tcLevel fuel level numcells st last leaf) :
    (Generic.node true g inf tcLevel fuel level numcells st).2.reference =
      (firstterminal last leaf).reference :=
  path.reference (referencePolicy g inf tcLevel) (fun _ _ _ => rfl)

end Hex.GraphIso.Nauty.Sparse
