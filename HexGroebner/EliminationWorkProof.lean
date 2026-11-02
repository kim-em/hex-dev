/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.MatrixState
public import HexGroebner.MatrixState
public import HexGroebner.MatrixValidation
public import Std.Do

public section

/-! Owning correspondence proofs inspect private continuation bodies. Public
State construction stays behind the executable API; do not expose unchecked
State builders from this module. -/

namespace Hex.Groebner.MatrixState

/-- Lifting reference work into a continuation preserves pure results. -/
private theorem lift_pure (value : α) :
    liftWork (pure value : Matrix.Work α) = (pure value : Work α) := by
  funext state
  rfl

/-- Lifting commutes with sequential reference work, including the first error
and its exact charged statistics. -/
private theorem lift_bind (action : Matrix.Work α) (cont : α → Matrix.Work β) :
    liftWork (action >>= cont) = (do
      let value ← liftWork action
      liftWork (cont value)) := by
  funext state
  cases h : action.run state.stats with
  | mk result stats =>
    change action state.stats = (result,stats) at h
    cases result <;> simp [liftWork,ExceptT.mk,ExceptT.bind,ExceptT.bindCont,ExceptT.run,
      StateT.bind,StateT.pure,Pure.pure,Bind.bind,h]

/-- Reference row loops can be lifted without changing their early-return or
error semantics. The same statement applies to scan and gather quantum loops. -/
private theorem lift_forIn (items : List α) (initial : β)
    (body : α → β → Matrix.Work (ForInStep β)) :
    liftWork (forIn items initial body) =
      forIn items initial (fun item acc => liftWork (body item acc)) := by
  induction items generalizing initial with
  | nil => simp [List.forIn_nil,lift_pure]
  | cons item items ih =>
    rw [List.forIn_cons,List.forIn_cons,lift_bind]
    congr 1
    funext next
    cases next <;> simp [lift_pure,ih]

#print axioms lift_forIn

end Hex.Groebner.MatrixState

namespace Hex.Groebner.Matrix.Work

open Std.Do

private abbrev Post (α : Type) := PostCond α (.except MatrixError (.arg MatrixStats .pure))

private def pre (action : Matrix.Work α) (post : Post α) :
    Assertion (.except MatrixError (.arg MatrixStats .pure)) :=
  fun stats => match action.run stats with
    | (.ok value,out) => post.1 value out
    | (.error error,out) => post.2.1 error out

open Std.Do in
/-- Exact run semantics can be used as a specification without opening an
arithmetic helper's internal loops. Both error and successful statistics occur
in the precondition, so no charged prefix is discarded. -/
private theorem triple_run (action : Matrix.Work α)
    (post : Post α) : Triple (m := Matrix.Work) action (pre action post) post := by
  simp only [Triple.iff]
  intro stats h
  cases hr : action.run stats with
  | mk result out =>
    change action stats = (result,out) at hr
    cases result <;>
      simpa [Std.Do.WP.wp,ExceptT.run,StateT.run,Id.run,Pure.pure,pre,hr] using h

private theorem run_of_triple (action : Matrix.Work α) (initial : MatrixStats)
    (expected : Except MatrixError α × MatrixStats)
    (contract : Triple (m := Matrix.Work) (ps := .except MatrixError (.arg MatrixStats .pure)) action
      (fun stats => ⌜stats = initial⌝)
      (fun value stats => ⌜(.ok value,stats) = expected⌝,
        fun error stats => ⌜(.error error,stats) = expected⌝,PUnit.unit)) :
    action.run initial = expected := by
  simp only [Triple.iff] at contract
  have h := contract initial (by rfl)
  cases hr : action.run initial with
  | mk result out =>
    change action initial = (result,out) at hr
    cases result <;>
      simpa [Std.Do.WP.wp,ExceptT.run,StateT.run,Id.run,Pure.pure,hr] using h

@[spec] private theorem charge_run (resource : Resource) (amount limit : Nat)
    (read : MatrixStats → Nat) (write : MatrixStats → Nat → MatrixStats) (post : Post Unit) :
    Triple (Matrix.charge resource amount limit read write)
      (pre (Matrix.charge resource amount limit read write) post) post :=
  triple_run _ post

@[spec] private theorem work_run (limits : MatrixLimits) (amount : Nat) (post : Post Unit) :
    Triple (Matrix.work limits amount) (pre (Matrix.work limits amount) post) post :=
  triple_run _ post

@[spec] private theorem bytes_run (limits : MatrixLimits) (amount : Nat) (post : Post Unit) :
    Triple (Matrix.packedBytes limits amount) (pre (Matrix.packedBytes limits amount) post) post :=
  triple_run _ post

@[spec] private theorem inverse_run (field : PrimeField) (ctx : BarrettCtx field.modulus)
    (limits : MatrixLimits) (value : UInt64) (post : Post UInt64) :
    Triple (Matrix.inverse field ctx limits value)
      (pre (Matrix.inverse field ctx limits value) post) post :=
  triple_run _ post

@[spec] private theorem scale_run (field : PrimeField) (ctx : BarrettCtx field.modulus)
    (limits : MatrixLimits) (row : SparseRow) (value : UInt64) (post : Post SparseRow) :
    Triple (Matrix.scaleSparse field ctx limits row value)
      (pre (Matrix.scaleSparse field ctx limits row value) post) post :=
  triple_run _ post


@[spec] private theorem validation_run (field : PrimeField) (limits : MatrixLimits)
    (columns : Nat) (reducers targets : Array SparseRow) (native : Bool) (post : Post Unit) :
    Triple (Matrix.validateRows field limits columns reducers targets native)
      (pre (Matrix.validateRows field limits columns reducers targets native) post) post :=
  triple_run _ post


#print axioms triple_run

end Hex.Groebner.Matrix.Work
