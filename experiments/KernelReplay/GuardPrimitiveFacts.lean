/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardCoefficientControl
public meta import KernelReplay.GuardCoefficientControl
import all KernelReplay.GuardCoefficientControl
import all KernelReplay.GuardDescriptorReductions
import all KernelReplay.GuardDescriptorInputs

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPrimitiveFacts
open Lean Meta Elab Command GuardDescriptorInputs

private def arity : Expr → Nat
  | .forallE _ _ body _ => 1 + arity body
  | _ => 0

/-- Candidate selection ignores dictionary aliases. The complete requested
proposition must still pass the ordinary kernel when a proof is reused. -/
def key (type : Expr) : Option Expr := do
  let head ← type.getAppFn.constName?
  let count ← if #[``Transport.Sum, ``Transport.Product, ``Transport.Difference,
      ``Transport.Scaling, ``Transport.Evaluation, ``Transport.PowerData].contains head then
      some 2
    else if head == ``Transport.Differentiation then some 1 else none
  let arguments := type.getAppArgs
  if arguments.size < count + 1 then none
  else some (mkAppN (mkConst head) (arguments.extract (arguments.size - count - 1) arguments.size))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let targets := #[``Transport.Sum.of_closed, ``Transport.Product.of_closed,
    ``Transport.Difference.of_closed, ``Transport.Scaling.of_closed,
    ``Transport.Differentiation.of_closed, ``Transport.Evaluation.of_closed,
    ``Transport.PowerData.of_closed]
  let mut counts : NameMap Nat := {}
  for target in targets do counts := counts.insert target (arity (← getConstInfo target).type)
  let arities := counts
  let found ← IO.mkRef (#[] : Array Expr)
  let seen ← IO.mkRef ({} : ExprSet)
  for source in #[``GuardDescriptorInputs.derivatives, ``GuardDescriptorInputs.head,
      ``GuardDescriptorInputs.nodeHead, ``GuardDescriptorInputs.preparation,
      ``GuardDescriptorInputs.products, ``GuardDescriptorReductions.reductions] do
    let .thmInfo info ← getConstInfo source | throwError "missing fresh arithmetic source proof"
    let _ ← Core.transform info.value (post := fun expression => do
      let _ ← bounded began
      if expression.hasFVar || expression.hasMVar || expression.hasLooseBVars || expression.hasSorry then
        return .done expression
      if let some name := expression.getAppFn.constName? then
        if let some count := arities.find? name then
          if expression.getAppNumArgs == count && !(← seen.get).contains expression then
            seen.modify (·.insert expression)
            found.modify (·.push expression)
      return .done expression)
  let candidates ← found.get
  logInfo m!"fresh closed primitive arithmetic candidates: count={candidates.size} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
  let mut proofs : Array Expr := #[]
  let mut keys : ExprSet := {}
  for candidate in candidates do
    let type ← inferType candidate
    let some fingerprint := key type | throwError "arithmetic candidate changed its predicate"
    if keys.contains fingerprint then continue
    let tag ← mkFreshUserName `fact
    let proof ← retain began (`Hex.RealClosure.Algebraic.KernelReplay.GuardPrimitiveFacts ++ tag) candidate
    keys := keys.insert fingerprint
    proofs := proofs.push proof
  unless !proofs.isEmpty do throwError "fresh checked fields contain no closed primitive arithmetic proofs"
  logInfo m!"fresh primitive arithmetic module export: candidates={candidates.size} distinctReaderOperandKeys={proofs.size} dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardPrimitiveFacts
