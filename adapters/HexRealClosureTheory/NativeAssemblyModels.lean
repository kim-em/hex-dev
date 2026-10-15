/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRealClosureTheory.NativeAssembly

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

/-- Build record assembly from the actual retained chain and its validated
prefix models. Native codecs use each predecessor's original carrier; scalar
correspondence uses the common reference field, including infinitesimal bases.
No whole-field interpretation into the ordinary reals is selected here. -/
def NativeModels.assembly (models : NativeModels) (native : NativeChain)
    (fuel : Nat := 500) : MetaM NativeAssembly := do
  unless models.prefixes.size == native.owners.size + 1 &&
      models.models.size == models.prefixes.size do
    throwError "native assembly models lost a retained prefix"
  let mut owners := #[]
  for i in [:native.owners.size] do
    let some context := native.owners[i]? | throwError "native assembly owner missing"
    let some predecessor :=  models.prefixes[i]? | throwError "native assembly predecessor missing"
    let type ← withTransparency .all (whnf (← inferType context))
    unless type.getAppFn.isConstOf ``Context do throwError "native assembly owner is not algebraic"
    let carrier ← mkAppM ``Tower.Context.Value #[predecessor]
    unless ← withTransparency .all (isDefEq type.getAppArgs[0]! carrier) do
      throwError "native assembly model has a different predecessor carrier"
    let value ← mkAppM ``Tower.Context.codec #[predecessor]
    let ctx ← mkAppM ``Tower.contextCodec #[type.getAppArgs.back!]
    let reduce ← mkAppM ``Context.reduce #[context]
    owners := owners.push (models.owner i context value ctx reduce (← mkEqRefl reduce))
  let factory : NativeFactory := ⟨owners⟩
  return { factory, fuel, read := fun index operations codec polynomial claimed packet => do
    let some owner := factory.owners[index]? | throwError "native assembly scalar owner missing"
    models.replaySignReader index operations owner.context codec owner.contextCodec
      polynomial claimed packet }

/-- Supply the actual demanded records while dependency discovery still uses
unchosen local readers. Base support and all descendant support are collected
before the reconstruction selects simultaneous ordinary-real coordinates. -/
unsafe def NativeChain.reconstructModels (native : NativeChain) (models : NativeModels)
    (following extra : Expr) (statements : Expr → Array Level → MetaM (Array Expr))
    (decisions : Supplier) (fuel : Nat := 500) : MetaM Reconstruction := do
  let assembly ← models.assembly native fuel
  native.reconstruct following extra statements decisions
    (fun lookup _ => assembly.supply native.owners.size lookup.request #[]) fuel

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
