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

/-- Transport a checked memo along literal equalities of coefficient
operations. The memo's values and indices remain unchanged. -/
@[expose] def changeOps (one : One E) (add : Add E) (sub : Sub E)
    (mul : Mul E) (natCast : NatCast E)
    (ho : one = ordinaryOne) (ha : add = ordinaryAdd) (hs : sub = ordinarySub)
    (hm : mul = ordinaryMul) (hn : natCast = ordinaryNatCast)
    (sign : E → Int) (binding : Ctx) (head : DensePoly E) (lower upper : Endpoint E)
    (memo : Option (Array (@Checked _ _ _ _ one add sub mul natCast _
      sign binding head lower upper))) :
    Option (Array (@Checked _ _ _ _ ordinaryOne ordinaryAdd ordinarySub ordinaryMul
      ordinaryNatCast _ sign binding head lower upper)) := by
  cases ho
  cases ha
  cases hs
  cases hm
  cases hn
  exact memo

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
  rfl

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
  cases ho
  cases ha
  cases hs
  cases hm
  cases hn
  rfl

end Hex.SignDet.Dag

/-- info: 'Hex.SignDet.Dag.changeOps_validate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Dag.changeOps_validate
/-- info: 'Hex.SignDet.Dag.changeOps_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Dag.changeOps_nodes
