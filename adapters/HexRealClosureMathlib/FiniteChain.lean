/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerContext
public import HexRealClosureMathlib.FiniteReconstruction
public meta import HexRealClosureMathlib.FiniteReconstruction

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

/-- The staged base and actual algebraic owners retained by a native packed
tower, in predecessor order. Extraction does not rebuild root contexts. -/
structure NativeChain where
  context : Expr
  base : Expr
  owners : Array Expr

private def checkProof (type proof : Expr) : MetaM Unit := do
  let locals := (← getLCtx).getFVarIds.map mkFVar
  let proof ← mkLambdaFVars locals proof (usedOnly := true)
  let type ← mkForallFVars locals type (usedOnly := true)
  let _ ← auditProof proof type
  kernelCheck `__finiteNativeChain type proof

private def checkEquality (left right : Expr) : MetaM Unit := do
  checkProof (← mkEq left right) (← mkEqRefl left)

/-- Inspect the actual staged constructors and check each extracted owner
against the carrier and descriptor of that constructor. Opaque chains and
exhausted depth bounds fail; no origin or suffix reconstruction is used. -/
def NativeChain.ofContext (context : Expr) (fuel : Nat := 256) : MetaM NativeChain := do
  if context.hasMVar || context.hasSorry then throwError "incomplete native tower context"
  let packed ← withTransparency .all (whnf context)
  unless packed.getAppFn.isConstOf ``Tower.Context.pack do
    throwError "expected a native packed tower context"
  let mut chain := packed.getAppArgs.back!
  let mut owners := #[]
  for _ in [:fuel] do
    let constructor ← withTransparency .all (whnf chain)
    if constructor.getAppFn.isConstOf ``Tower.Chain.base then
      let base := constructor.getAppArgs.back!
      let carrier := (← inferType chain).getAppArgs[1]!
      checkEquality carrier (← mkAppM ``BaseContext.Element #[base])
      return ⟨context, base, owners.reverse⟩
    unless constructor.getAppFn.isConstOf ``Tower.Chain.root do
      throwError "native tower chain is not a retained base/root constructor"
    let arguments := constructor.getAppArgs
    unless arguments.size ≥ 4 do throwError "invalid native root constructor"
    let parent := arguments[arguments.size - 4]!
    let descriptor := arguments[arguments.size - 3]!
    let carrier := (← inferType chain).getAppArgs[1]!
    unless carrier.getAppFn.isConstOf ``Element do
      throwError "native root constructor has a different element carrier"
    let owner := carrier.getAppArgs.back!
    checkEquality carrier (← mkAppM ``Element #[owner])
    let predecessor := (← inferType parent).getAppArgs
    let clean := predecessor[predecessor.size - 3]!
    checkEquality owner (← mkAppM ``Context.adjoin #[descriptor, clean])
    checkProof (← mkEq (← mkAppM ``Context.root #[owner]) descriptor)
      (← mkAppM ``Context.root_adjoin #[descriptor, clean])
    owners := owners.push owner
    chain := parent
  throwError "native tower extraction exhausted its depth bound"

/-- Create empty typed inventories and unchosen local readers for every
retained native owner. Each level reads coefficients with the preceding
reader. The callback must discover support before selecting real points. -/
def NativeChain.withLevels (native : NativeChain) (read : Expr)
    (action : Array Level → MetaM α) : MetaM α := do
  let baseCarrier ← mkAppM ``BaseContext.Element #[native.base]
  unless ← withTransparency .all (isDefEq (← inferType read)
      (← mkArrow baseCarrier (mkConst ``Real))) do
    throwError "native tower base reader has a different carrier"
  go native.owners.toList read #[]
where
  go (owners : List Expr) (previous : Expr) (levels : Array Level) : MetaM α := do
    let owner :: remaining := owners | return ← action levels
    let carrier ← mkAppM ``Element #[owner]
    withLocalDeclD `reader (← mkArrow carrier (mkConst ``Real)) fun reader => do
      let level : Level := {
        context := owner
        entries := ← mkListLit (← mkAppM ``Packing #[owner]) []
        records := ← mkListLit (← mkAppM ``ValueSign #[owner]) []
        facts := ← mkListLit (← mkAppM ``InverseFact #[owner]) []
        read := previous
        reader := reader }
      go remaining reader (levels.push level)

/-- Discover all retained descriptor data, requested guards and scalar units
on the actual native chain, then reconstruct its simultaneous ordinary-real
conditions from the validated base history. Record suppliers contribute
checked native evidence; no interpretation or selected point is chosen
until dependency discovery has finished. -/
def NativeChain.reconstruct (native : NativeChain) (following extra : Expr)
    (statements : Expr → Array Level → MetaM (Array Expr)) (decisions : Supplier)
    (record : Lookup → Array Level → MetaM (Option Expr)) (fuel : Nat := 500) :
    MetaM Reconstruction := do
  let carrier ← mkAppM ``BaseContext.Element #[native.base]
  withLocalDeclD `baseReader (← mkArrow carrier (mkConst ``Real)) fun read => do
    native.withLevels read fun levels => do
      let types (current : Array Level) : MetaM (Array Expr) := do
        let mut required ← statements read current
        for level in current do
          required := required.push (← mkAppM ``Packing.Inventory.Data
            #[level.context, level.entries, level.records, level.facts, level.read])
          let element ← mkAppM ``Element #[level.context]
          for (nativeConstant, realConstant) in #[(``Zero.zero, ``Zero.zero), (``One.one, ``One.one)] do
            let input ← mkAppOptM nativeConstant #[some element, none]
            let output ← mkAppOptM realConstant #[some (mkConst ``Real), none]
            required := required.push (← mkEq (mkApp level.reader input) output)
        return required
      let discovery ← collectDependencies fuel levels types decisions record
      FiniteData.reconstruct native.base following read discovery extra decisions

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
