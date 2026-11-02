/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Matrix
import Init.Data.Range.Lemmas
import Init.Data.List.Monadic

public section

namespace Hex.Groebner.Matrix

/-- Residual validation follows the same input indices as the continuation. -/
def validateFrom (field : PrimeField) (limits : MatrixLimits)
    (columns : Nat) (reducers targets : Array SparseRow) (cursor : Nat) : Matrix.Work Unit := do
  for i in [cursor:reducers.size+targets.size] do
    Matrix.validate field limits columns i
      (if i < reducers.size then reducers[i]! else targets[i-reducers.size]!)

theorem validateFrom_succ (field : PrimeField) (limits : MatrixLimits)
    (columns : Nat) (reducers targets : Array SparseRow) (cursor : Nat)
    (h : cursor < reducers.size+targets.size) :
    validateFrom field limits columns reducers targets cursor = (do
      Matrix.validate field limits columns cursor
        (if cursor < reducers.size then reducers[cursor]! else targets[cursor-reducers.size]!)
      validateFrom field limits columns reducers targets (cursor+1)) := by
  simp only [validateFrom, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  have length : reducers.size+targets.size-cursor =
      (reducers.size+targets.size-(cursor+1))+1 := by omega
  rw [length, List.range'_succ]
  simp

theorem validateFrom_of_le (field : PrimeField) (limits : MatrixLimits)
    (columns : Nat) (reducers targets : Array SparseRow) (cursor : Nat)
    (h : reducers.size+targets.size ≤ cursor) :
    validateFrom field limits columns reducers targets cursor = pure () := by
  simp [validateFrom, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_eq_zero_of_le h]

theorem validateFrom_error (field : PrimeField) (limits : MatrixLimits)
    (columns : Nat) (reducers targets : Array SparseRow) (cursor : Nat)
    (stats nextStats : MatrixStats) (error : MatrixError)
    (h : cursor < reducers.size+targets.size)
    (hrow : (Matrix.validate field limits columns cursor
      (if cursor < reducers.size then reducers[cursor]! else targets[cursor-reducers.size]!)).run
        stats = (.error error,nextStats)) :
    (validateFrom field limits columns reducers targets cursor).run stats =
      (.error error,nextStats) := by
  rw [validateFrom_succ field limits columns reducers targets cursor h]
  dsimp [ExceptT.run, Bind.bind, ExceptT.bind, ExceptT.bindCont,
    ExceptT.mk, StateT.bind, Pure.pure, StateT.pure]
  simp only [ExceptT.run] at hrow
  rw [hrow] <;> rfl

theorem validateFrom_ok (field : PrimeField) (limits : MatrixLimits)
    (columns : Nat) (reducers targets : Array SparseRow) (cursor : Nat)
    (stats nextStats : MatrixStats)
    (h : cursor < reducers.size+targets.size)
    (hrow : (Matrix.validate field limits columns cursor
      (if cursor < reducers.size then reducers[cursor]! else targets[cursor-reducers.size]!)).run
        stats = (.ok (),nextStats)) :
    (validateFrom field limits columns reducers targets cursor).run stats =
      (validateFrom field limits columns reducers targets (cursor+1)).run nextStats := by
  rw [validateFrom_succ field limits columns reducers targets cursor h]
  dsimp [ExceptT.run, Bind.bind, ExceptT.bind, ExceptT.bindCont,
    ExceptT.mk, StateT.bind, Pure.pure, StateT.pure]
  simp only [ExceptT.run] at hrow
  rw [hrow] <;> rfl

private theorem forIn_unit (indices : List Nat) (action : Nat → Matrix.Work Unit) :
    forIn indices () (fun i _ => do action i; pure (.yield ())) =
      ForM.forM indices action := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    simp only [List.forIn_cons, List.forM_cons, bind_assoc, pure_bind, ih]


/-- Validate reducers followed by targets with their original input indices. -/
@[inline] def validateRows (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (native : Bool) : Matrix.Work Unit := do
  for i in [:reducers.size] do
    if native then validateWith field limits columns i reducers[i]!
    else validate field limits columns i reducers[i]!
  for i in [:targets.size] do
    if native then validateWith field limits columns (reducers.size+i) targets[i]!
    else validate field limits columns (reducers.size+i) targets[i]!

private theorem forM_congr (indices : List Nat) (f g : Nat → Matrix.Work Unit)
    (h : ∀ i ∈ indices, f i = g i) :
    ForM.forM indices f = ForM.forM indices g := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    simp only [List.forM_cons]
    rw [h i (by simp)]
    rw [ih (fun j hj => h j (by simp [hj]))]

/-- Combined-cursor validation equals the reference's reducer/target loops,
including every first error and charged prefix. -/
theorem validateFrom_zero (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (native : Bool) :
    validateFrom field limits columns reducers targets 0 =
      validateRows field limits columns reducers targets native := by
  simp only [validateFrom, validateRows, validateWith_spec, ite_self, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  simp only [forIn_unit]
  rw [← List.range'_append_1 (s := 0) (m := reducers.size) (n := targets.size)]
  simp only [List.forM_append, Nat.zero_add]
  have first :
      ForM.forM (List.range' 0 reducers.size) (fun i => validate field limits columns i
        (if i < reducers.size then reducers[i]! else targets[i-reducers.size]!)) =
      ForM.forM (List.range' 0 reducers.size) (fun i => validate field limits columns i reducers[i]!) := by
    apply forM_congr
    intro i hi
    have bound : i < reducers.size := by
      obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hi
      simpa using hj
    simp [bound]
  have second :
      ForM.forM (List.range' reducers.size targets.size) (fun i => validate field limits columns i
        (if i < reducers.size then reducers[i]! else targets[i-reducers.size]!)) =
      ForM.forM (List.range' 0 targets.size)
        (fun i => validate field limits columns (reducers.size+i) targets[i]!) := by
    rw [show List.range' reducers.size targets.size =
      (List.range' 0 targets.size).map (reducers.size+·) from by
        simpa using (List.map_add_range' (a := reducers.size) 0 targets.size 1).symm]
    simp only [List.forM_map]
    apply forM_congr
    intro i hi
    have bound : ¬ reducers.size+i < reducers.size := by omega
    simp [bound]
  rw [first,second]
  simp only [bind_assoc]

end Hex.Groebner.Matrix
