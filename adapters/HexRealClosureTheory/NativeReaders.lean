/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRealClosureTheory.NativeReplay
public import HexRealClosure.QueryOperations

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta Hex.SignDet

/-- Reify equal cached operations as the core reader's typed dictionary
record. Its constructor checks every equation against the ordinary instances. -/
def NativeOperations.core (operations : NativeOperations) : MetaM Expr := do
  unless operations.operations.size == 8 && operations.equations.size == 8 do
    throwError "incomplete native record operations"
  let signEquation ← withTransparency .all (whnf (← inferType operations.signEquation))
  unless signEquation.getAppFn.isConstOf ``Eq do
    throwError "native record sign equation is not an equality"
  let core ← mkAppM ``Hex.RealClosure.Replay.Operations.mk
    (operations.operations ++ operations.equations ++ #[operations.sign, operations.signEquation])
  let expected ← mkAppM ``Hex.RealClosure.Replay.Operations #[signEquation.getAppArgs.back!]
  unless ← withTransparency .all (isDefEq (← inferType core) expected) do
    throwError "native record operations changed their original sign callback"
  let locals := (← getLCtx).getFVarIds.map mkFVar
  let binding ← mkAppOptM ``Eq.refl #[some expected, some core]
  let proof ← mkLambdaFVars locals binding (usedOnly := true)
  let type ← inferType proof
  let _ ← auditProof proof type
  kernelCheck `__nativeRecordOperations type proof
  return core

/-- The original owner's reduction computed with equal cached operations. -/
def NativeOperations.reduction (operations : NativeOperations) (owner : Expr) :
    MetaM (Expr × Expr) := do
  let core ← operations.core
  let original ← mkAppM ``Context.reduce #[owner]
  let polynomial := (← inferType original).bindingDomain!
  withLocalDeclD `polynomial polynomial fun p => do
    let reduced ← mkAppM ``Context.reduceOperations #[core, owner, p]
    let equation ← mkAppM ``Context.reduceOperations_eq #[core, owner, p]
    return (← mkLambdaFVars #[p] reduced,
      ← mkAppM ``funext #[← mkLambdaFVars #[p] equation])

/-- Assemble the packing reader expression with cached graph validation,
packing differences and derivative prefixes, retaining the original request. -/
def NativeOperations.packingReader (operations : NativeOperations)
    (owner codec ctx reduce reductionEquation facts polynomial packet : Expr) : MetaM Expr := do
  let core ← operations.core
  let queries ← mkAppM ``Packing.queriesOperations #[core, reduce, polynomial]
  let queriesEq ← mkAppM ``Packing.queriesOperations_eq #[core, reduce, polynomial]
  let preceding ← mkAppM ``Context.prefixOperations #[core, owner]
  let prefixEq ← mkAppM ``Context.prefixOperations_eq #[core, owner]
  mkAppM ``Packing.readPacketOperations?
    #[core, codec, ctx, reduce, reductionEquation, facts, polynomial,
      queries, queriesEq, preceding, prefixEq, packet]

/-- Assemble the reader for the exact stored operand and its original tag. -/
def NativeOperations.valueSignReader (operations : NativeOperations)
    (owner codec ctx value packet : Expr) : MetaM Expr := do
  let core ← operations.core
  let polynomial ← mkAppM ``Element.polynomial #[value]
  let queries ← mkListLit (← inferType polynomial) [polynomial]
  let preceding ← mkAppM ``Context.prefixOperations #[core, owner]
  let prefixEq ← mkAppM ``Context.prefixOperations_eq #[core, owner]
  mkAppM ``ValueSign.readPacketOperations?
    #[core, codec, ctx, value, queries, ← mkEqRefl queries, preceding, prefixEq, packet]

/-- Assemble the inverse reader with the actual supplied candidate computation
and the original operand's inverse equation. Every equality is a Lean proof. -/
def NativeOperations.inverseReader (operations : NativeOperations)
    (owner codec ctx argument entry packet : Expr) : MetaM Expr := do
  let core ← operations.core
  let candidate ← mkAppM ``Element.inverseOperations #[core, argument]
  let candidateEq ← mkAppM ``Element.inverseOperations_eq #[core, argument]
  let queries ← mkAppM ``Packing.Inverse.queriesOperations #[core, argument, entry]
  let queriesEq ← mkAppM ``Packing.Inverse.queriesOperations_eq #[core, argument, entry]
  let preceding ← mkAppM ``Context.prefixOperations #[core, owner]
  let prefixEq ← mkAppM ``Context.prefixOperations_eq #[core, owner]
  mkAppM ``InverseFact.readPacketOperations?
    #[core, codec, ctx, argument, entry, candidate, candidateEq,
      queries, queriesEq, preceding, prefixEq, packet]

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
