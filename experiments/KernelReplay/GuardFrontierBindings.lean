/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardFrontier
public meta import KernelReplay.GuardFrontier
import all KernelReplay.GuardFrontier
import all KernelReplay.GuardFrontierStore
import all KernelReplay.FrameJoint
import all KernelReplay.GuardDescriptorInputs

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardFrontierBindings
open Lean Meta Elab FiniteData GuardDescriptorInputs

private def check (template expected : Expr) (oldReaders : Array Expr)
    (readers : Array Expr := #[]) (fuel : Nat := 3) : MetaM Unit := do
  if let fuel + 1 := fuel then
    let .lam name domain body info := template |
      throwError "stored discovery expression lost an original reader binder"
    withLocalDecl name info domain fun reader => do
      check (body.instantiate1 reader) expected oldReaders (readers.push reader) fuel
  else
    let expected := expected.replace fun expression => do
      let index ← oldReaders.findIdx? (· == expression)
      readers[index]?
    let equation ← mkEq template expected
    let type ← mkForallFVars readers equation (usedOnly := false)
    let proof ← mkLambdaFVars readers (← mkEqRefl expected) (usedOnly := false)
    kernelCheck `__originalSymbolicGuardSource type proof

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let expressions := GuardFrontier.templates.getState (← getEnv)
  unless expressions.size == 3773 do throwError "imported discovery expression count changed"
  let mut readers := #[]
  for name in #[``GuardCapture.read, ``GuardCapture.first.reader, ``GuardCapture.second.reader] do
    let some body := (← getConstInfo name).value? (allowOpaque := true) |
      throwError "original captured reader definition is missing"
    readers := readers.push body
  let .defnInfo request ← getConstInfo ``GuardCapture.request |
    throwError "original requested native product is missing"
  for (index, expected) in #[(131, (← getConstInfo ``GuardCapture.guard).type),
      (3772, request.value)] do
    let remaining ← bounded began
    withOptions (maxHeartbeats.set · remaining) do check expressions[index]! expected readers
    logInfo m!"original discovery source predicate checked: index={index} readers=3 actualGuardProof=false"
  logInfo m!"original discovery expressions reimported: count=3773 guard131AndNativeRequestKernelBound=true actualGuardProofs=0 aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardFrontierBindings
