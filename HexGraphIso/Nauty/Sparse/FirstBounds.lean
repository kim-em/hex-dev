/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Depth
public import HexGraphIso.Nauty.Sparse.Alignment
public import HexGraphIso.Nauty.Policy.Generic.FirstBounded
import all HexGraphIso.Nauty.Policy.Generic.FirstBounded
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

theorem compare_same (level code : Nat) (st : State n) :
    (compareCodes level code st).allsamelevel = st.allsamelevel := by
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.allsamelevel, ite_self]

theorem target_same (first : Bool) (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (chooseTarget first g tcLevel level numcells st).2.2.2.allsamelevel = st.allsamelevel := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n =>
    out.2.2.2.allsamelevel = st.allsamelevel)
  mvcgen
  all_goals simp_all +zetaDelta

theorem classify_same (g : Graph n) (level numcells : Nat) (st : State n) :
    (classify g level numcells st).2.allsamelevel = st.allsamelevel := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.allsamelevel, ite_self]

theorem leafExit_same (leaf : Leaf) (level : Nat) (st : State n) :
    (leafExit leaf level st).2.allsamelevel = st.allsamelevel := by
  cases leaf <;> unfold leafExit pruneReturn install admit pushAuto
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals rfl

theorem recover_same (inf level : Nat) (st : State n) :
    (recoverLevels level (recoverPtn inf level st)).allsamelevel = st.allsamelevel := by
  unfold recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.allsamelevel, ite_self]

/-- Native calls below an ancestor retain its lower bounds on first-code
agreement and the all-same boundary, including cached target dispatch. -/
theorem firstFloor (g : Graph n) (inf tcLevel bound : Nat) :
    Generic.BoundedPolicy g inf tcLevel bound
      (fun st : State n => bound ≤ st.allsamelevel ∧ bound ≤ st.eqlevFirst) where
  visit := fun _ _ _ h => h
  compare := by
    intro level code st hl h
    change bound ≤ (compareCodes level code st).allsamelevel ∧
      bound ≤ (compareCodes level code st).eqlevFirst
    rw [compare_same, compareCodes_eqlev]
    split <;> exact ⟨h.1, by omega⟩
  target := by
    intro level numcells st hl h
    change bound ≤ (chooseTarget false g tcLevel level numcells st).2.2.2.allsamelevel ∧
      bound ≤ (chooseTarget false g tcLevel level numcells st).2.2.2.eqlevFirst
    unfold chooseTarget
    apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n =>
      bound ≤ out.2.2.2.allsamelevel ∧ bound ≤ out.2.2.2.eqlevFirst)
    mvcgen
    all_goals simp_all +zetaDelta
    all_goals omega
  classify := by
    intro level numcells st h
    change bound ≤ (classify g level numcells st).2.allsamelevel ∧
      bound ≤ (classify g level numcells st).2.eqlevFirst
    rwa [classify_same, classify_eqlev]
  leaf := by
    intro leaf level st _ h
    change bound ≤ (leafExit leaf level st).2.allsamelevel ∧
      bound ≤ (leafExit leaf level st).2.eqlevFirst
    rwa [leafExit_same, leafExit_eqlev]
  cheap := by
    intro first level st _ h
    change bound ≤ (cheapCheck first level st).allsamelevel ∧
      bound ≤ (cheapCheck first level st).eqlevFirst
    unfold cheapCheck
    split <;> exact h
  child := by intro first level tc tv st h; cases first <;> exact h
  leave := fun _ _ h => h
  recover := by
    intro level st hl h
    change bound ≤ (recoverLevels level (recoverPtn inf level st)).allsamelevel ∧
      bound ≤ (recoverLevels level (recoverPtn inf level st)).eqlevFirst
    have he := recover_eqlev inf level st
    change (recoverLevels level (recoverPtn inf level st)).eqlevFirst = _ at he
    rw [recover_same, he]
    exact ⟨h.1, by omega⟩
  afterSweep := by
    intro first level size index st hl h
    have hs : bound ≤ (Nauty.afterSweep first level size index st).allsamelevel ∧
        bound ≤ (Nauty.afterSweep first level size index st).eqlevFirst := by
      unfold Nauty.afterSweep
      split
      · rename_i hc
        have he : st.allsamelevel = level + 1 := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          exact hc.2
        exact ⟨by dsimp only; omega, h.2⟩
      · exact h
    change bound ≤ (if first then { Nauty.afterSweep first level size index st with
      order := (Nauty.afterSweep first level size index st).order * index }
      else Nauty.afterSweep first level size index st).allsamelevel ∧
      bound ≤ (if first then { Nauty.afterSweep first level size index st with
      order := (Nauty.afterSweep first level size index st).order * index }
      else Nauty.afterSweep first level size index st).eqlevFirst
    cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> exact hs

/-- The actual first terminal installs both boundaries at its depth;
every enclosing first call retains the bounds at its own entry level. -/
theorem firstPath_floor {g : Graph n} {inf tcLevel fuel level numcells last : Nat}
    {st leaf : State n} (path : Generic.FirstPath g tcLevel fuel level numcells st last leaf) :
    level ≤ (Generic.node true g inf tcLevel fuel level numcells st).2.allsamelevel ∧
      level ≤ (Generic.node true g inf tcLevel fuel level numcells st).2.eqlevFirst := by
  have hl : level ≤ last := by
    induction path with
    | leaf => exact Nat.le_refl _
    | step _ _ _ _ ih => omega
  exact path.bounded (firstFloor g inf tcLevel level) (fun _ _ _ h => h)
    (Nat.le_refl _) (show level ≤ (firstterminal last leaf).allsamelevel ∧
      level ≤ (firstterminal last leaf).eqlevFirst from ⟨hl, hl⟩)

end Hex.GraphIso.Nauty.Sparse
