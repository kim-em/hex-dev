/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Store
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse.Store

open Std.Do
set_option mvcgen.warning false

variable {G : Hex.SparseGraph n} {st : State n}

theorem target (h : Store G st) (first : Bool) (tcLevel level numcells : Nat) :
    Store G (chooseTarget first (.ofGraph G) tcLevel level numcells st).2.2.2 := by
  have hf : let out := (chooseTarget first (.ofGraph G) tcLevel level numcells st).2.2.2
      out.canong.toRows = st.canong.toRows ∧ out.canonlab = st.canonlab ∧ out.samerows = st.samerows := by
    unfold chooseTarget
    apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n =>
      out.2.2.2.canong.toRows = st.canong.toRows ∧
      out.2.2.2.canonlab = st.canonlab ∧ out.2.2.2.samerows = st.samerows)
    mvcgen
    all_goals simp_all +zetaDelta
  exact h.congr hf.1 hf.2.1 hf.2.2

theorem recover (h : Store G st) (inf level : Nat) :
    Store G ((policy (n := n)).recover inf level st) := by
  apply h.congr
  · change (recoverLevels level (recoverPtn inf level st)).canong.toRows = st.canong.toRows
    unfold recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.canong, ite_self]
  · change (recoverLevels level (recoverPtn inf level st)).canonlab = st.canonlab
    unfold recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.canonlab, ite_self]
  · change (recoverLevels level (recoverPtn inf level st)).samerows = st.samerows
    unfold recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.samerows, ite_self]

theorem push (h : Store G st) (pair : VSet n × VSet n) : Store G (pushAuto st pair) := by
  unfold pushAuto
  split <;> exact h.congr rfl rfl rfl

theorem admit (h : Store G st) : Store G (Nauty.admit st) := by
  have ht : Store G { st with genTrace := st.genTrace.push st.workperm } := h.congr rfl rfl rfl
  have hp : Store G (pushAuto { st with genTrace := st.genTrace.push st.workperm } (fmperm st.workperm n)) :=
    ht.push _
  unfold Nauty.admit
  exact hp.congr rfl rfl rfl

theorem prune (h : Store G st) (level : Nat) : Store G (pruneReturn level st).2 := by
  unfold pruneReturn
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  split
  · exact h.push _
  · exact h

/-- All five shared leaf actions preserve the native store; only a better
leaf replaces its label, using the prefix supplied by classification. -/
theorem leaf (h : Store G st) (leaf : Leaf) (level : Nat)
    (hc : ∀ sr, leaf = .better sr → Candidate G st sr) : Store G (leafExit leaf level st).2 := by
  cases leaf with
  | internal =>
    unfold leafExit
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split <;> exact h.congr rfl rfl rfl
  | autoFirst =>
    unfold leafExit
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact ((h.congr (out := { st with maxlevel := level }) rfl rfl rfl).admit).congr rfl rfl rfl
    · exact h.admit.congr rfl rfl rfl
  | autoCanon =>
    unfold leafExit
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    repeat' split
    all_goals first
      | exact ((h.congr (out := { st with maxlevel := level }) rfl rfl rfl).admit).congr rfl rfl rfl
      | exact h.admit.congr rfl rfl rfl
  | bad =>
    unfold leafExit
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    all_goals apply Store.prune
    all_goals exact h.congr rfl rfl rfl
  | better sr =>
    have hi := hc sr rfl
    unfold leafExit
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    all_goals apply Store.prune
    all_goals exact hi

end Hex.GraphIso.Nauty.Sparse.Store
