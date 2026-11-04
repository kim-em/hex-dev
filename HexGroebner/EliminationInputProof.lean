/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.MatrixState
import all HexGroebner.MatrixStateProof
import all HexGroebner.EliminationOutcome
import all HexGroebner.EliminationPhaseProof
public import HexGroebner.EliminationPhaseProof
import Init.Data.List.Monadic

public section

/-! Owning input correspondence proofs inspect private phase bodies. Public
State construction stays behind the executable API. -/

namespace Hex.Groebner

private def scatterRow (width : Width) (row : SparseRow) (dense : ByteArray) : ByteArray :=
  (List.range' 0 row.size).foldl (fun dense index =>
    Packed.set width dense (Packed.read .u32 row.columns index).toNat
      (Packed.read width row.coefficients index)) dense

private theorem scatter_loop [Monad m] [LawfulMonad m]
    (width : Width) (row : SparseRow) (dense : ByteArray) :
    (forIn [:row.size] dense (fun index dense =>
      pure (.yield (Packed.set width dense (Packed.read .u32 row.columns index).toNat
        (Packed.read width row.coefficients index)))) : m ByteArray) =
      pure (scatterRow width row dense) := by
  simp [scatterRow,Std.Legacy.Range.forIn_eq_forIn_range',List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]

private theorem scatter_list (width : Width) (row : SparseRow) (dense : ByteArray) :
    (forIn (List.range' 0 row.size) dense (fun index dense =>
      pure (.yield (Packed.set width dense (Packed.read .u32 row.columns index).toNat
        (Packed.read width row.coefficients index)))) : MatrixState.Work ByteArray) =
      pure (scatterRow width row dense) := by
  simp only [List.forIn_pure_yield_eq_foldl]
  rfl

private noncomputable def preparedScan (base : MatrixState.State) (row : SparseRow)
    (sugar : Nat) (stats : MatrixStats) : MatrixState.State :=
  { base with
    phase := .scan
    dense := {}
    sugar := sugar
    quanta := MatrixState.scanFuel base.columns
    scan := {
      dense := scatterRow base.field.width row base.dense
      column := (Packed.read .u32 row.columns 0).toNat
      last := (Packed.read .u32 row.columns (row.size-1)).toNat
      chargedUntil := (Packed.read .u32 row.columns 0).toNat
      sugar := sugar }
    stats := stats }

private noncomputable def installedInput (base : MatrixState.State) (row : SparseRow)
    (column : Nat) (inverse : UInt64) (sugar : Nat) (stats : MatrixStats) : MatrixState.State :=
  ((MatrixState.install row column inverse sugar).run { base with sugar,stats }).2

private noncomputable def zeroInput (base : MatrixState.State) (sugar : Nat)
    (stats : MatrixStats) : MatrixState.State :=
  (MatrixState.zeroRow.run { base with sugar,stats }).2

private noncomputable def inputTail (state : MatrixState.State) (row : SparseRow) (sugar : Nat)
    (stats : MatrixStats) : Except MatrixError (Echelon × Array RemainderRow) × MatrixStats :=
  if row.size == 0 then outcome (zeroInput state sugar stats) else
    let first := (Packed.read .u32 row.columns 0).toNat
    if !MatrixState.isTarget state && Packed.read .u32 state.slots first == 0 then
      match (Matrix.inverse state.field state.field.barrett state.limits
        (Packed.read state.field.width row.coefficients 0)).run stats with
      | (.error error,stats) => (.error error,stats)
      | (.ok inverse,stats) =>
        match (Matrix.scaleSparse state.field state.field.barrett state.limits row inverse).run stats with
        | (.error error,stats) => (.error error,stats)
        | (.ok row,stats) => outcome (installedInput state row first inverse sugar stats)
    else match (Matrix.work state.limits row.size).run stats with
      | (.error error,stats) => (.error error,stats)
      | (.ok _,stats) => outcome (preparedScan state row sugar stats)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
private theorem input_outcome (state : MatrixState.State) (hphase : state.phase = .input)
    (hgeometry : state.geometry) (hinput : state.input < state.reducers.size+state.targets.size) :
    outcome state = match (Matrix.work state.limits 1).run state.stats with
      | (.error error,stats) => (.error error,stats)
      | (.ok _,stats) => inputTail state
          (if MatrixState.isTarget state then state.targets[state.input-state.reducers.size]!
            else state.reducers[state.input]!) (state.sugars[state.input]?.getD 0) stats := by
  have installFormula := fun state row column inverse sugar => install_run state row column inverse sugar
  have zeroFormula := fun state => zero_run state
  have scatterFormula := fun row dense => scatter_list state.field.width row dense
  simp only [ExceptT.pure,ExceptT.mk,Pure.pure] at scatterFormula
  simp only [ExceptT.run] at installFormula zeroFormula
  rw [outcome_run state hgeometry (by simp [hphase])]
  unfold MatrixState.step
  simp [hphase,show ¬state.input ≥ state.reducers.size+state.targets.size by omega,
    scatter_loop,MatrixState.work,MatrixState.takeDense,preparedScan,installedInput,zeroInput,
    inputTail,ExceptT.run,ExceptT.mk,ExceptT.pure,ExceptT.bind,ExceptT.bindCont,ExceptT.lift,
    StateT.bind,StateT.get,StateT.set,StateT.pure,Bind.bind,MonadState.get,MonadStateOf.get,
    MonadStateOf.set,liftM,MonadLiftT.monadLift,MonadLift.monadLift,getThe,StateT.map,Functor.map,
    Pure.pure,Id.run,modify,modifyGet,modifyThe,MonadStateOf.modifyGet,StateT.modifyGet,
    MatrixState.liftWork]
  generalize hrow : (if MatrixState.isTarget state then
    state.targets[state.input-state.reducers.size]! else state.reducers[state.input]!) = row at *
  cases hw : (Matrix.work state.limits 1).run state.stats with
  | mk result stats =>
    simp only [ExceptT.run] at hw
    cases result
    all_goals simp [hw,hphase,scatter_loop,zeroFormula,installFormula,
      StateT.bind,StateT.pure,StateT.set,StateT.map,ExceptT.bindCont,ExceptT.mk,ExceptT.pure,Pure.pure,
      Bind.bind,Functor.map,MonadState.get,MonadStateOf.get,StateT.get,
      MonadStateOf.modifyGet,StateT.modifyGet,modifyGet,Id.run]
    all_goals (try split) <;> try simp_all
    all_goals (try split) <;> try simp_all
    all_goals (try split) <;> try simp_all
    all_goals (try split) <;> try simp_all
    all_goals (try split) <;> try simp_all
    all_goals (try split) <;> try simp_all
    all_goals (try split) <;> try simp_all
    all_goals (try split) <;> try simp_all
    all_goals try simp_all [StateT.bind,StateT.pure,StateT.set,StateT.map,ExceptT.bindCont,ExceptT.mk,
      ExceptT.pure,Pure.pure,Bind.bind,Functor.map,MonadState.get,MonadStateOf.get,StateT.get,
      MonadStateOf.modifyGet,StateT.modifyGet,modifyGet,Id.run,scatterFormula,scatter_list,scatter_loop,scatterRow,List.forIn_pure_yield_eq_foldl,zeroFormula,installFormula]
    all_goals grind

private theorem scatter_size (width : Width) (row : SparseRow) (dense : ByteArray) :
    (scatterRow width row dense).size = dense.size := by
  unfold scatterRow
  generalize List.range' 0 row.size = indices
  induction indices generalizing dense with
  | nil => rfl
  | cons index indices ih =>
    simp only [List.foldl_cons,ih,Packed.size_set]

private theorem prepared_geometry (state : MatrixState.State) (row : SparseRow) (sugar : Nat)
    (stats : MatrixStats) (hphase : state.phase = .input) (hgeometry : state.geometry)
    (hinput : state.input < state.reducers.size+state.targets.size) :
    (preparedScan state row sugar stats).geometry := by
  simp only [MatrixState.State.geometry,hphase] at hgeometry
  simpa [preparedScan,MatrixState.State.geometry,scatter_size,MatrixState.scanFuel]
    using (show state.dense.size = state.columns*state.field.width.bytes ∧
      state.input < state.reducers.size+state.targets.size ∧
      MatrixState.scanFuel state.columns ≤ MatrixState.scanFuel state.columns from
      ⟨hgeometry,hinput,Nat.le_refl _⟩)

private theorem input_end (state : MatrixState.State) (hphase : state.phase = .input)
    (hgeometry : state.geometry) (hinput : state.reducers.size+state.targets.size ≤ state.input) :
    outcome state = outcome { state with phase := .order } := by
  rw [outcome_run state hgeometry (by simp [hphase])]
  simp [MatrixState.step,hphase,hinput,ExceptT.run,ExceptT.mk,ExceptT.bind,ExceptT.bindCont,
    ExceptT.lift,StateT.bind,StateT.get,StateT.set,Bind.bind,MonadState.get,MonadStateOf.get,
    MonadStateOf.set,liftM,MonadLiftT.monadLift,MonadLift.monadLift,getThe,StateT.map,
    Functor.map,Pure.pure]

#print axioms prepared_geometry
#print axioms input_end
#print axioms input_outcome

end Hex.Groebner
