/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRealClosureMathlib.NativeModels
public import HexRealClosureMathlib.SignReplay
public import HexRealClosure.InverseReplay

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

/-- Equal operation dictionaries on one original native carrier, in the order
one, addition, negation, subtraction, multiplication, inverse, division, cast.
The sign callback also retains its equality with the original stored tag. -/
structure NativeOperations where
  carrier : Expr
  operations : Array Expr
  equations : Array Expr
  sign : Expr
  signEquation : Expr

private def classes : Array Name :=
  #[``One, ``Add, ``Neg, ``Sub, ``Mul, ``Inv, ``Div, ``NatCast]

private def diagnostic (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_RECORD_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn message
      handle.flush

private def check (value expected : Expr) : MetaM Unit := do
  diagnostic "operation: begin type equality"
  unless ← withTransparency .all (isDefEq (← inferType value) expected) do
    throwError "native replay operation has a different carrier or dictionary"
  diagnostic "operation: type equality checked"
  let locals := (← getLCtx).getFVarIds.map mkFVar
  let binding ← mkAppOptM ``Eq.refl #[some expected, some value]
  let proof ← mkLambdaFVars locals binding (usedOnly := true)
  let type ← inferType proof
  let _ ← auditProof proof type
  kernelCheck `__nativeReplayOperation type proof
  diagnostic "operation: kernel check complete"

/-- The actual native base operations, without a field instance on raw syntax. -/
def NativeOperations.native (carrier sign : Expr) : MetaM NativeOperations := do
  let mut operations := #[]
  let mut equations := #[]
  for name in classes do
    let operation ← synthInstance (← mkAppM name #[carrier])
    operations := operations.push operation
    equations := equations.push (← mkEqRefl operation)
  check sign (← mkArrow carrier (mkConst ``Int))
  return ⟨carrier, operations, equations, sign, ← mkEqRefl sign⟩

/-- Build each extension's operations using its original-key packing, stored
sign and inverse inventories, recursively retaining predecessor dictionaries.
Inversion demands its checked inverse equation rather than executing xgcd. -/
def NativeOperations.extend (previous : NativeOperations) (owner entries signs inverses : Expr) :
    MetaM NativeOperations := do
  unless previous.operations.size == 8 && previous.equations.size == 8 do
    throwError "incomplete native predecessor operations"
  let ownerType ← withTransparency .all (whnf (← inferType owner))
  unless ownerType.getAppFn.isConstOf ``Context do
    throwError "native replay extension requires an actual algebraic owner"
  unless ← withTransparency .all (isDefEq ownerType.getAppArgs[0]! previous.carrier) do
    throwError "native replay extension has a different predecessor carrier"
  for (name, values) in #[(``Packing, entries), (``ValueSign, signs), (``InverseFact, inverses)] do
    check values (← mkAppM ``List #[← mkAppM name #[owner]])
  let carrier ← mkAppM ``Element #[owner]
  let nativeSign ← withLocalDeclD `value carrier fun value => do
    mkLambdaFVars #[value] (← mkAppM ``Element.sign #[value])
  let ordinary ← NativeOperations.native carrier nativeSign
  let mut operations := #[]
  let mut equations := #[]
  let recipes : Array (Name × Name × Array Nat × Array Expr) := #[
    (``Element.replayOne, ``Element.replayOne_eq, #[0], #[entries]),
    (``Element.replayAdd, ``Element.replayAdd_eq, #[1], #[entries]),
    (``Element.replayNeg, ``Element.replayNeg_eq, #[3], #[entries]),
    (``Element.replaySub, ``Element.replaySub_eq, #[3], #[entries]),
    (``Element.replayMul, ``Element.replayMul_eq, #[1, 4], #[entries]),
    (``Element.replayInverse, ``Element.replayInverse_eq, #[], #[inverses]),
    (``Element.replayQuotient, ``Element.replayQuotient_eq, #[1, 4], #[entries, inverses]),
    (``Element.replayNatCast, ``Element.replayNatCast_eq, #[7], #[entries])]
  for i in [:recipes.size] do
    let (implementation, theoremName, slots, records) := recipes[i]!
    let arguments := slots.map (previous.operations[·]!) ++
      slots.map (previous.equations[·]!) ++ records
    let operation ← mkAppM implementation arguments
    let equation ← mkAppM theoremName arguments
    check operation (← inferType ordinary.operations[i]!)
    check equation (← mkEq operation ordinary.operations[i]!)
    operations := operations.push operation
    equations := equations.push equation
  let callback ← mkAppM ``Element.replaySign #[signs]
  let callbackEquation ← mkAppM ``funext #[← mkAppM ``Element.replaySign_eq #[signs]]
  check callbackEquation (← mkEq callback nativeSign)
  return ⟨carrier, operations, equations, callback, callbackEquation⟩

/-- Instantiate the scalar reader with the actual predecessor model and its
cached operations. The supplied packet remains the only graph evidence. -/
def NativeModels.replaySignReader (data : NativeModels) (predecessor : Nat)
    (operations : NativeOperations) (owner value ctx polynomial claimed packet : Expr) :
    MetaM Expr := do
  let some model := data.models[predecessor]? |
    throwError "native replay reader has no predecessor model"
  unless operations.operations.size == 8 && operations.equations.size == 8 do
    throwError "incomplete native replay reader operations"
  let ownerType ← withTransparency .all (whnf (← inferType owner))
  unless ownerType.getAppFn.isConstOf ``Context &&
      (← withTransparency .all (isDefEq ownerType.getAppArgs[0]! operations.carrier)) do
    throwError "native replay reader has a different predecessor carrier"
  let nativeSign := ownerType.getAppArgs[ownerType.getAppArgs.size - 2]!
  let ordinary ← NativeOperations.native operations.carrier nativeSign
  for i in [:8] do
    unless ← withTransparency .all
        (isDefEq (← inferType operations.operations[i]!) (← inferType ordinary.operations[i]!)) do
      throwError "native replay operation has a different dictionary type"
    unless ← withTransparency .all (isDefEq (← inferType operations.equations[i]!)
        (← mkEq operations.operations[i]! ordinary.operations[i]!)) do
      throwError "native replay dictionary equation does not match its operation"
  unless ← withTransparency .all (isDefEq (← inferType operations.signEquation)
      (← mkEq operations.sign nativeSign)) do
    throwError "native replay sign equation does not match the original callback"
  diagnostic "model reader: dictionary checks complete"
  data.withInstances fun instances => do
    let mut laws := #[]
    for name in #[``Tower.Model.value, ``Tower.Model.zero_iff, ``Tower.Model.one,
        ``Tower.Model.add, ``Tower.Model.sub, ``Tower.Model.mul, ``Tower.Model.nat,
        ``Tower.Model.sign, ``Tower.Model.neg, ``Tower.Model.inv] do
      laws := laws.push (← mkAppM name #[model])
    diagnostic "model reader: model laws constructed"
    let reader ← mkAppM ``Context.readSignOperations?
      (laws ++ #[owner] ++ operations.operations ++ operations.equations ++
        #[operations.sign, operations.signEquation, value, ctx, polynomial, claimed, packet])
    diagnostic "model reader: expression constructed"
    let reader ← instantiateMVars (← mkLetFVars instances reader)
    if reader.hasMVar || reader.hasSorry then throwError "incomplete native replay reader"
    diagnostic "model reader: instances closed"
    check reader (← mkAppM ``Option #[← mkAppM ``SignFact #[owner]])
    diagnostic "model reader: expression checked"
    return reader

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
