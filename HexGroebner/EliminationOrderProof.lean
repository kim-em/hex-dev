/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.MatrixState
import all HexGroebner.MatrixStateProof
import all HexGroebner.EliminationOutcome
public import HexGroebner.EliminationOutcome
import Init.Data.List.Monadic

public section

/-! Owning final-order correspondence proofs inspect the private phase body.
State construction stays behind the executable API. -/

namespace Hex.Groebner

private def orderedPivots (columns : Nat) (slots : ByteArray) (pivots : Array Pivot) : Array Pivot :=
  (List.range' 0 columns).foldl (fun ordered column =>
    let slot := (Packed.read .u32 slots column).toNat
    if slot != 0 then ordered.push pivots[slot-1]! else ordered) #[]

private theorem order_loop [Monad m] [LawfulMonad m]
    (columns : Nat) (slots : ByteArray) (pivots : Array Pivot) :
    (forIn [:columns] #[] (fun column ordered =>
      let slot := (Packed.read .u32 slots column).toNat
      if slot != 0 then pure (.yield (ordered.push pivots[slot-1]!))
      else pure (.yield ordered)) : m (Array Pivot)) = pure (orderedPivots columns slots pivots) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  have body : ∀ column (ordered : Array Pivot),
      (if (Packed.read .u32 slots column).toNat != 0 then
        pure (.yield (ordered.push pivots[(Packed.read .u32 slots column).toNat-1]!))
      else pure (.yield ordered) : m (ForInStep (Array Pivot))) =
      pure (.yield (if (Packed.read .u32 slots column).toNat != 0 then
        ordered.push pivots[(Packed.read .u32 slots column).toNat-1]! else ordered)) := by
    intro column ordered
    split <;> rfl
  simp only [body,List.forIn_pure_yield_eq_foldl]
  simp [orderedPivots,Std.Legacy.Range.size]

set_option linter.unusedSimpArgs false in
private theorem order_outcome (state : MatrixState.State) (hphase : state.phase = .order)
    (hgeometry : state.geometry) :
    outcome state = if state.independent then (.ok (⟨#[],state.rank,#[]⟩,state.remainders),state.stats)
    else match (Matrix.work state.limits state.columns).run state.stats with
      | (.error error,stats) => (.error error,stats)
      | (.ok _,stats) => (.ok (⟨orderedPivots state.columns state.slots state.pivots,state.rank,#[]⟩,
          state.remainders),stats) := by
  cases independent : state.independent
  all_goals rw [outcome_run state hgeometry (by simp [hphase])]
  all_goals unfold MatrixState.step
  all_goals simp only [hphase,order_loop,independent]
  all_goals
    cases hw : (Matrix.work state.limits state.columns).run state.stats with
    | mk result stats =>
      simp only [ExceptT.run] at hw
      cases result
      all_goals simp [MatrixState.work,hphase,order_loop,independent,hw,
        ExceptT.run,ExceptT.mk,ExceptT.pure,ExceptT.bind,ExceptT.bindCont,ExceptT.lift,StateT.bind,
        StateT.get,StateT.set,StateT.pure,Bind.bind,MonadState.get,MonadStateOf.get,MonadStateOf.set,
        liftM,MonadLiftT.monadLift,MonadLift.monadLift,getThe,StateT.map,Functor.map,Pure.pure,
        Id.run,modify,modifyGet,modifyThe,MonadStateOf.modifyGet,StateT.modifyGet,MatrixState.liftWork,
        outcome,MatrixState.finish_done]

#print axioms order_outcome

end Hex.Groebner
