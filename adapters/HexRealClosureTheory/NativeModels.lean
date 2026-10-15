/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.FiniteChain
public meta import HexRealClosureTheory.FiniteChain
public import HexRealClosureTheory.BaseFactory
public import HexRealClosureTheory.TowerModel
public import HexRealClosureTheory.SignFacts

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

/-- Models of the actual retained prefixes in one ordered real-closed reference
field. The base history supplies the reference; no ordinary-real specialization
point or interpretation of raw expressions as a field is asserted here. -/
structure NativeModels where
  reference : Expr
  carrier : Expr
  prefixes : Array Expr
  models : Array Expr

private def check (value expected : Expr) : MetaM Unit := withExporting (isExporting := false) do
  let actualType ← withTransparency .all (whnf (← inferType value))
  let requestedType ← withTransparency .all (whnf expected)
  unless ← withTransparency .all (isDefEq actualType requestedType) do
    let actual := actualType.getAppArgs
    let requested := requestedType.getAppArgs
    for i in [:min actual.size requested.size] do
      unless ← withTransparency .all (isDefEq actual[i]! requested[i]!) do
        throwError "native model argument {i} differs: actual {actual[i]!}, expected {requested[i]!}"
    throwError "native prefix model has a different owner: actual {← inferType value}, expected {expected}"
  let locals := (← getLCtx).getFVarIds.map mkFVar
  let binding ← mkAppOptM ``Eq.refl #[some expected, some value]
  let equation ← inferType binding
  let proof ← mkLambdaFVars locals binding (usedOnly := true)
  let type ← mkForallFVars locals equation (usedOnly := true)
  let _ ← auditProof proof type
  kernelCheck `__nativePrefixModel type proof

private def withReferenceInstances (reference : Expr) (carrier : Expr)
    (action : Array Expr → MetaM α) : MetaM α :=
  go [``BaseContext.PackedContext.Reference.field, ``BaseContext.PackedContext.Reference.order,
    ``BaseContext.PackedContext.Reference.ordered, ``BaseContext.PackedContext.Reference.closed] #[]
where
  go (names : List Name) (instances : Array Expr) : MetaM α := do
    if let name :: remaining := names then
      let value ← mkAppM name #[reference]
      withLetDecl `referenceInstance (← inferType value) value fun inst =>
        go remaining (instances.push inst)
    else
      let equality ← mkAppOptM ``Classical.decEq #[some carrier]
      withLetDecl `equality (← inferType equality) equality fun equality =>
        action (instances.push equality)

/-- Scope the reference field instances while constructing a term, then let
the caller close those local instance declarations into the returned term. -/
def NativeModels.withInstances (data : NativeModels)
    (action : Array Expr → MetaM α) : MetaM α :=
  withReferenceInstances data.reference data.carrier action

/-- Follow the original staged constructors, propagating the validated base
model through each actual descriptor, frame and encoding proof. All prefixes
retain their native owners and share the same reference field. -/
def NativeChain.models (native : NativeChain) (following : Expr)
    (fuel : Nat := 256) : MetaM NativeModels := do
  let packedBase ← mkAppM ``BaseContext.PackedContext.pack #[native.base]
  let reference ← mkAppOptM ``BaseContext.PackedContext.Realization.reference
    #[none, some packedBase, some following]
  let carrier ← mkAppM ``BaseContext.PackedContext.Reference.Carrier #[reference]
  let packed ← withTransparency .all (whnf native.context)
  unless packed.getAppFn.isConstOf ``Tower.Context.pack do
    throwError "native models require the retained packed context"
  let chain := packed.getAppArgs.back!
  withReferenceInstances reference carrier fun instances => do
    let (prefixes, models) ← go reference carrier fuel chain
    unless models.size == native.owners.size + 1 do
      throwError "native models lost a retained prefix"
    for i in [:native.owners.size] do
      let actual ← mkAppM ``Tower.Context.Value #[prefixes[i + 1]!]
      let original ← mkAppM ``Element #[native.owners[i]!]
      check (← mkEqRefl actual) (← mkEq actual original)
    let mut closed := #[]
    for model in models do
      closed := closed.push (← mkLetFVars instances model)
    return ⟨reference, carrier, prefixes, closed⟩
where
  go (reference carrier : Expr) (remaining : Nat) (chain : Expr) :
      MetaM (Array Expr × Array Expr) := do
    let remaining + 1 := remaining |
      throwError "native model construction exhausted its depth bound"
    let constructor ← withTransparency .all (whnf chain)
    let context ← mkAppM ``Tower.Context.pack #[chain]
    let expected ← mkAppOptM ``Tower.Model #[none, some context, some carrier, none, none]
    if constructor.getAppFn.isConstOf ``Tower.Chain.base then
      let model ← mkAppM ``BaseContext.PackedContext.Reference.model #[reference]
      check model expected
      return (#[context], #[model])
    unless constructor.getAppFn.isConstOf ``Tower.Chain.root do
      throwError "native model prefix is not a retained base/root constructor"
    let args := constructor.getAppArgs
    let parent := args[args.size - 4]!
    let descriptor := args[args.size - 3]!
    let frame := args[args.size - 2]!
    let encoded := args.back!
    let (prefixes, models) ← go reference carrier remaining parent
    let model ← mkAppM ``Tower.Model.root #[parent, models.back!, descriptor, frame, encoded]
    check model expected
    return (prefixes.push context, models.push model)

/-- Instantiate the checked scalar packet reader with the actual predecessor
model's correspondence laws. The caller supplies literal packet data and the
original request; the model never produces evidence or a claimed sign. -/
def NativeModels.signReader (data : NativeModels) (predecessor : Nat)
    (owner value ctx polynomial claimed packet : Expr) : MetaM Expr := do
  let some model := data.models[predecessor]? |
    throwError "native scalar reader has no predecessor model"
  withReferenceInstances data.reference data.carrier fun instances => do
    let mut arguments := #[]
    for name in #[``Tower.Model.value, ``Tower.Model.zero_iff, ``Tower.Model.one,
        ``Tower.Model.add, ``Tower.Model.sub, ``Tower.Model.mul, ``Tower.Model.nat,
        ``Tower.Model.sign, ``Tower.Model.neg, ``Tower.Model.inv] do
      arguments := arguments.push (← mkAppM name #[model])
    let reader ← mkAppM ``Context.readSignPacket?
      (arguments ++ #[owner, value, ctx, polynomial, claimed, packet])
    return ← mkLetFVars instances reader

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
