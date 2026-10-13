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

private def diagnostic (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn message
      handle.flush

/-- Use the original context's retained coefficient dictionaries when forming
one of its native record types. These constructors have the same parameters
as `Context`, followed by the context itself. -/
private def recordType (name : Name) (owner : Expr) : MetaM Expr := do
  let type ← withTransparency .all (whnf (← inferType owner))
  let .const constructor levels := type.getAppFn |
    throwError "native record owner has no context type"
  unless constructor == ``Context do throwError "native record owner is not algebraic"
  return mkAppN (mkConst name levels) (type.getAppArgs.push owner)

/-- Retain an actual closed owner once. Its caches and descriptor are kept
unchanged; the transparent definition is checked before it enters the
environment and is compiled for native data production. -/
private def retainOwner (owner : Expr) : MetaM Expr := do
  if owner.isConst || owner.hasFVar then return owner
  let type ← inferType owner
  let _ ← auditProof owner type
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `__nativeOwner)
  let levels := collectLevelParams (collectLevelParams {} type) owner |>.params.toList
  let declaration := Declaration.defnDecl {
    name, levelParams := levels, type, value := owner,
    hints := .regular 0, safety := .safe }
  diagnostic "chain: begin original owner definition check"
  let options := (← getOptions).setBool `debug.skipKernelTC false
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true))
  withOptions (Elab.async.set · false) do
    withOptions (fun options => options.setBool `compiler.postponeCompile false) do
      compileDecl declaration
  diagnostic "chain: original owner checked and compiled"
  return mkConst name (levels.map Lean.Level.param)

/-- The staged base and actual algebraic owners retained by a native packed
tower, in predecessor order. Extraction does not rebuild root contexts. -/
structure NativeChain where
  context : Expr
  base : Expr
  owners : Array Expr
  /-- Ordinary-kernel equalities linking the caller's context and every
  retained base/owner definition to the expressions extracted from it. -/
  bindings : Array Expr := #[]

private def checkProof (type proof : Expr) : MetaM Unit := do
  let locals := (← getLCtx).getFVarIds.map mkFVar
  let proof ← mkLambdaFVars locals proof (usedOnly := true)
  let type ← mkForallFVars locals type (usedOnly := true)
  let _ ← auditProof proof type
  kernelCheck `__finiteNativeChain type proof

private def checkEquality (left right : Expr) : MetaM Unit := do
  checkProof (← mkEq left right) (← mkEqRefl left)

private def retainBinding (left right : Expr) : MetaM Expr := do
  let statement ← mkEq left right
  -- Fix the advertised equality before checking reflexivity, so inference
  -- does not replace the source binding with a reflexive equality.
  let proof ← withTransparency .all do
    mkAppOptM ``id #[some statement, some (← mkEqRefl right)]
  checkProof statement proof
  return proof

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
  let mut bindings := #[← retainBinding context packed]
  for _ in [:fuel] do
    let constructor ← withTransparency .all (whnf chain)
    if constructor.getAppFn.isConstOf ``Tower.Chain.base then
      let base := constructor.getAppArgs.back!
      let carrier := (← inferType chain).getAppArgs[1]!
      checkEquality carrier (← mkAppM ``BaseContext.Element #[base])
      let retained ← retainOwner base
      bindings := bindings.push (← retainBinding retained base)
      return ⟨context, retained, owners.reverse, bindings⟩
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
    let retained ← retainOwner owner
    bindings := bindings.push (← retainBinding retained owner)
    owners := owners.push retained
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
    let carrier ← recordType ``Element owner
    diagnostic "chain: original level carrier constructed"
    withLocalDeclD `reader (← mkArrow carrier (mkConst ``Real)) fun reader => do
      let level : Level := {
        context := owner
        entries := ← mkListLit (← recordType ``Packing owner) []
        records := ← mkListLit (← recordType ``ValueSign owner) []
        facts := ← mkListLit (← recordType ``InverseFact owner) []
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
  diagnostic "chain: base carrier constructed"
  withLocalDeclD `baseReader (← mkArrow carrier (mkConst ``Real)) fun read => do
    native.withLevels read fun levels => do
      diagnostic "chain: original levels constructed"
      let types (current : Array Level) : MetaM (Array Expr) := do
        let mut required ← statements read current
        for level in current do
          required := required.push (← mkAppM ``Packing.Inventory.Data
            #[level.context, level.entries, level.records, level.facts, level.read])
          diagnostic "chain: inventory premises constructed"
          let contextType ← withTransparency .all (whnf (← inferType level.context))
          let parameters := contextType.getAppArgs
          let coefficientLevel := contextType.getAppFn.constLevels![0]!
          let coefficientOne := mkAppN (mkConst ``One.one [coefficientLevel])
            #[parameters[0]!, parameters[4]!]
          let constantOne := mkAppN (mkConst ``DensePoly.C [coefficientLevel])
            #[parameters[0]!, parameters[2]!, parameters[3]!, coefficientOne]
          let nativeZero ← recordType ``Element.zero level.context
          let nativeOne := mkApp (← recordType ``Element.ofPoly level.context) constantOne
          for (input, realConstant) in #[(nativeZero, ``Zero.zero), (nativeOne, ``One.one)] do
            let output ← mkAppOptM realConstant #[some (mkConst ``Real), none]
            required := required.push (← mkEq (mkApp level.reader input) output)
          diagnostic "chain: original zero/unit premises constructed"
        return required
      diagnostic "chain: begin dependency discovery"
      let discovery ← collectDependencies fuel levels types decisions record
      diagnostic "chain: dependency discovery returned"
      let requested ← statements read discovery.levels
      FiniteData.reconstruct native.base following read discovery extra decisions requested

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
