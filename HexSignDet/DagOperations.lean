/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Dag

public section

namespace Hex.SignDet.Dag

variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [ordinaryOne : One E] [ordinaryAdd : Add E] [ordinarySub : Sub E]
variable [ordinaryMul : Mul E] [ordinaryNatCast : NatCast E] [DecidableEq Ctx]

/-- Restore one literal checked tree to the target operations. Equality
transport occurs only in the erased acceptance proof. -/
@[expose] def Checked.ofOperations (one : One E) (add : Add E) (sub : Sub E)
    (mul : Mul E) (natCast : NatCast E)
    (ho : one = ordinaryOne) (ha : add = ordinaryAdd) (hs : sub = ordinarySub)
    (hm : mul = ordinaryMul) (hn : natCast = ordinaryNatCast)
    (sign : E → Int) (binding : Ctx) (head : DensePoly E) (lower upper : Endpoint E)
    (value : Replay E Ctx)
    (accepted : @Replay.check E Ctx _ _ one add sub mul natCast _ sign binding
      head lower upper value.node.queries value = true) :
    @Checked E Ctx _ _ ordinaryOne ordinaryAdd ordinarySub ordinaryMul ordinaryNatCast _
      sign binding head lower upper :=
  @Checked.mk E Ctx _ _ ordinaryOne ordinaryAdd ordinarySub ordinaryMul ordinaryNatCast _
    sign binding head lower upper value (by
      rw [ho, ha, hs, hm, hn] at accepted
      exact accepted)

/-- Transport a checked memo along literal equalities of coefficient
operations. Its literal values remain reducible in the ordinary kernel. -/
@[expose] def changeOps (one : One E) (add : Add E) (sub : Sub E)
    (mul : Mul E) (natCast : NatCast E)
    (ho : one = ordinaryOne) (ha : add = ordinaryAdd) (hs : sub = ordinarySub)
    (hm : mul = ordinaryMul) (hn : natCast = ordinaryNatCast)
    (sign : E → Int) (binding : Ctx) (head : DensePoly E) (lower upper : Endpoint E)
    (memo : Option (Array (@Checked _ _ _ _ one add sub mul natCast _
      sign binding head lower upper))) :
    Option (Array (@Checked _ _ _ _ ordinaryOne ordinaryAdd ordinarySub ordinaryMul
      ordinaryNatCast _ sign binding head lower upper)) :=
  memo.map fun entries => entries.map fun entry =>
    @Checked.ofOperations E Ctx _ _ ordinaryOne ordinaryAdd ordinarySub ordinaryMul
      ordinaryNatCast _ one add sub mul natCast ho ha hs hm hn sign binding head lower upper
      (@Checked.value _ _ _ _ one add sub mul natCast _ sign binding head lower upper entry)
      (@Checked.accepted _ _ _ _ one add sub mul natCast _ sign binding head lower upper entry)

/-- Changing equal operations in the actual validator preserves its exact
result, including rejection. -/
theorem changeOps_validate (one : One E) (add : Add E) (sub : Sub E)
    (mul : Mul E) (natCast : NatCast E)
    (ho : one = ordinaryOne) (ha : add = ordinaryAdd) (hs : sub = ordinarySub)
    (hm : mul = ordinaryMul) (hn : natCast = ordinaryNatCast)
    (sign : E → Int) (binding : Ctx) (head : DensePoly E) (lower upper : Endpoint E)
    (graph : SignDet.Dag E Ctx) :
    @changeOps _ _ _ _ ordinaryOne ordinaryAdd ordinarySub ordinaryMul ordinaryNatCast _
      one add sub mul natCast ho ha hs hm hn sign binding head lower upper
      (@validate? _ _ _ _ one add sub mul natCast _ sign binding head lower upper graph) =
      @validate? _ _ _ _ ordinaryOne ordinaryAdd ordinarySub ordinaryMul ordinaryNatCast _
        sign binding head lower upper graph := by
  cases ho
  cases ha
  cases hs
  cases hm
  cases hn
  unfold changeOps
  have identity : (fun entry : Checked sign binding head lower upper =>
      Checked.ofOperations ordinaryOne ordinaryAdd ordinarySub ordinaryMul ordinaryNatCast
        rfl rfl rfl rfl rfl sign binding head lower upper entry.value entry.accepted) = id := by
    funext entry
    cases entry
    rfl
  simp only [identity, Array.map_id]
  cases validate? sign binding head lower upper graph <;> rfl

/-- The complete literal replay values are unchanged by operation transport. -/
theorem changeOps_values (one : One E) (add : Add E) (sub : Sub E)
    (mul : Mul E) (natCast : NatCast E)
    (ho : one = ordinaryOne) (ha : add = ordinaryAdd) (hs : sub = ordinarySub)
    (hm : mul = ordinaryMul) (hn : natCast = ordinaryNatCast)
    (sign : E → Int) (binding : Ctx) (head : DensePoly E) (lower upper : Endpoint E)
    (memo : Option (Array (@Checked _ _ _ _ one add sub mul natCast _
      sign binding head lower upper))) :
    (@changeOps _ _ _ _ ordinaryOne ordinaryAdd ordinarySub ordinaryMul ordinaryNatCast _
      one add sub mul natCast ho ha hs hm hn sign binding head lower upper memo).map
        (fun entries => entries.map (@Checked.value _ _ _ _ ordinaryOne ordinaryAdd
          ordinarySub ordinaryMul ordinaryNatCast _ sign binding head lower upper)) =
      memo.map (fun entries => entries.map (@Checked.value _ _ _ _ one add sub mul natCast _
        sign binding head lower upper)) := by
  unfold changeOps
  cases memo with
  | none => rfl
  | some entries =>
    simp only [Option.map_some, Option.some.injEq, Array.map_map]
    rfl

/-- Transport preserves both successful memos and rejection. -/
theorem changeOps_isSome (one : One E) (add : Add E) (sub : Sub E)
    (mul : Mul E) (natCast : NatCast E)
    (ho : one = ordinaryOne) (ha : add = ordinaryAdd) (hs : sub = ordinarySub)
    (hm : mul = ordinaryMul) (hn : natCast = ordinaryNatCast)
    (sign : E → Int) (binding : Ctx) (head : DensePoly E) (lower upper : Endpoint E)
    (memo : Option (Array (@Checked _ _ _ _ one add sub mul natCast _
      sign binding head lower upper))) :
    (@changeOps _ _ _ _ ordinaryOne ordinaryAdd ordinarySub ordinaryMul ordinaryNatCast _
      one add sub mul natCast ho ha hs hm hn sign binding head lower upper memo).isSome =
      memo.isSome := by
  cases memo <;> rfl

/-- The literal node list is unchanged by operation transport. -/
theorem changeOps_nodes (one : One E) (add : Add E) (sub : Sub E)
    (mul : Mul E) (natCast : NatCast E)
    (ho : one = ordinaryOne) (ha : add = ordinaryAdd) (hs : sub = ordinarySub)
    (hm : mul = ordinaryMul) (hn : natCast = ordinaryNatCast)
    (sign : E → Int) (binding : Ctx) (head : DensePoly E) (lower upper : Endpoint E)
    (memo : Option (Array (@Checked _ _ _ _ one add sub mul natCast _
      sign binding head lower upper))) :
    (@changeOps _ _ _ _ ordinaryOne ordinaryAdd ordinarySub ordinaryMul ordinaryNatCast _
      one add sub mul natCast ho ha hs hm hn sign binding head lower upper memo).map
        (fun entries => entries.map (fun entry =>
          (@Checked.value _ _ _ _ ordinaryOne ordinaryAdd ordinarySub ordinaryMul
            ordinaryNatCast _ sign binding head lower upper entry).node)) =
      memo.map (fun entries => entries.map (fun entry =>
        (@Checked.value _ _ _ _ one add sub mul natCast _
          sign binding head lower upper entry).node)) := by
  unfold changeOps
  cases memo with
  | none => rfl
  | some entries =>
    simp only [Option.map_some, Option.some.injEq, Array.map_map]
    rfl

end Hex.SignDet.Dag

/-- info: 'Hex.SignDet.Dag.changeOps_validate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Dag.changeOps_validate
/-- info: 'Hex.SignDet.Dag.changeOps_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Dag.changeOps_nodes

/-- info: 'Hex.SignDet.Dag.changeOps_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Dag.changeOps_values

/-- info: 'Hex.SignDet.Dag.changeOps_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Dag.changeOps_isSome
