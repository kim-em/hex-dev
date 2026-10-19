/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.DagOperations

public section
namespace Hex.RealClosure.Replay
open Hex.SignDet

variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [ordinaryOne : One E] [ordinaryAdd : Add E] [ordinarySub : Sub E]
variable [ordinaryMul : Mul E] [ordinaryNatCast : NatCast E] [DecidableEq Ctx]

/-- Validate every supplied entry with equal cached operations and sign reads.
The literal memo is retained; only its erased acceptance proofs are restored to
the original dictionaries and callback. Missing records stop kernel replay. -/
@[expose] def validateOperations? (one : One E) (add : Add E) (sub : Sub E)
    (mul : Mul E) (natCast : NatCast E)
    (ho : one = ordinaryOne) (ha : add = ordinaryAdd) (hs : sub = ordinarySub)
    (hm : mul = ordinaryMul) (hn : natCast = ordinaryNatCast)
    (sign original : E → Int) (same : sign = original) (binding : Ctx)
    (head : DensePoly E) (lower upper : Endpoint E) (graph : Dag E Ctx) :
    Option (Array (@Dag.Checked E Ctx _ _ ordinaryOne ordinaryAdd ordinarySub ordinaryMul
      ordinaryNatCast _ original binding head lower upper)) :=
  let changed := @Dag.changeOps E Ctx _ _ ordinaryOne ordinaryAdd ordinarySub ordinaryMul
    ordinaryNatCast _ one add sub mul natCast ho ha hs hm hn sign binding head lower upper
    (@Dag.validate? E Ctx _ _ one add sub mul natCast _ sign binding head lower upper graph)
  letI := ordinaryOne
  letI := ordinaryAdd
  letI := ordinarySub
  letI := ordinaryMul
  letI := ordinaryNatCast
  changed.map fun entries => entries.map fun entry =>
    ⟨entry.value, (congrArg (fun callback =>
      @Hex.SignDet.Replay.check E Ctx _ _ ordinaryOne ordinaryAdd ordinarySub ordinaryMul
        ordinaryNatCast _ callback binding head lower upper entry.value.node.queries entry.value)
      same).symm.trans entry.accepted⟩

/-- The complete validation result is preserved for every supplied inventory,
including rejection. No completeness assumption supplies missing evidence. -/
theorem validateOperations_eq (one : One E) (add : Add E) (sub : Sub E)
    (mul : Mul E) (natCast : NatCast E)
    (ho : one = ordinaryOne) (ha : add = ordinaryAdd) (hs : sub = ordinarySub)
    (hm : mul = ordinaryMul) (hn : natCast = ordinaryNatCast)
    (sign original : E → Int) (same : sign = original) (binding : Ctx)
    (head : DensePoly E) (lower upper : Endpoint E) (graph : Dag E Ctx) :
    letI := ordinaryOne
    letI := ordinaryAdd
    letI := ordinarySub
    letI := ordinaryMul
    letI := ordinaryNatCast
    validateOperations? one add sub mul natCast ho ha hs hm hn sign original same binding
      head lower upper graph =
    @Dag.validate? E Ctx _ _ ordinaryOne ordinaryAdd ordinarySub ordinaryMul ordinaryNatCast _
      original binding head lower upper graph := by
  cases ho; cases ha; cases hs; cases hm; cases hn; cases same
  unfold validateOperations?
  rw [Dag.changeOps_validate]
  have identity : (fun entry : Dag.Checked sign binding head lower upper =>
      (⟨entry.value, entry.accepted⟩ : Dag.Checked sign binding head lower upper)) = id := by
    funext entry
    cases entry
    rfl
  simp only [identity, Array.map_id]
  cases graph.validate? sign binding head lower upper <;> rfl

end Hex.RealClosure.Replay
