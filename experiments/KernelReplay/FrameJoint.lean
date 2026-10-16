/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FrameNested
public import KernelReplay.FrameOwners
public import KernelReplay.FrameOperand
public meta import KernelReplay.FrameOperand
public meta import KernelReplay.NativeAssemblyStaged
import all KernelReplay.NativeAssemblyNestedData
public meta import KernelReplay.FiniteChain
public meta import KernelReplay.FiniteBase
public meta import KernelReplay.FiniteData
public meta import HexRealClosureTheory.NativeAssemblyModels
import all HexRowReduce.Loop
import all HexRowReduce.Pivot
import all HexRowReduce.Api
-- Kernel replay inspects the actual validated producer result. Access to
-- preparation internals is restricted to this exact experiment by the DAG lint.
import all HexSturm.Basic
import all HexRealClosure.BaseContext
import all HexRealClosure.BaseJson
import all HexRealClosure.FrameFormat
import all HexRealClosure.TowerContext
import all HexRealClosure.InversePacking
import all HexRealClosure.Algebraic
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Value
import all HexSignDet.Table
import all HexSignDet.Descriptor
import all HexRealRoots.TarskiShared
import all HexPoly.Dense
import all HexPoly.Euclid.DivGcd
import all Std.Data.DHashMap.Basic
import all Std.Data.DHashMap.Raw
import all Std.Data.DHashMap.Internal.Defs
import all Std.Data.DHashMap.Internal.AssocList.Basic
import all Init.Prelude
import all Init.Util
import all Init.Data.Rat.Basic
import all Init.Data.Array.Basic
import all HexRealClosure.Packing
import all HexRealClosure.ValueSigns
import all HexRealClosure.RecordPackets
import all HexRealClosure.InversePackets
import all HexSignDet.Dag
import all HexSignDet.DagEncode
import all HexSignDet.Thom
import all HexSignDet.Replay
import all HexSignDet.MomentReplay
import all HexSignDet.QueryReduction
import all HexSignDet.Reduction
import all HexSignDet.Matrix
import all HexRank.Cert
import all HexMatrix.MatrixAlgebra
import all HexRealClosure.RecordReaders
import all HexRealClosure.QueryOperations
import all HexRealClosure.RecordQueries
import all HexRealClosureTheory.SignReplay
import all HexRealClosure.SignCodec

public meta import HexRealClosureTheory.FiniteReconstruction
import all HexRealClosureTheory.FiniteReconstruction
import all HexRealClosureTheory.FiniteChain

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

private def emitCapture (name : Name) (type value : Expr) : MetaM Unit := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  let (type, value) ← closeStatement type value
  for expression in #[type, value] do
    if expression.hasFVar || expression.hasMVar || expression.hasSorry || expression.hasLooseBVars then
      throwError "guard capture retained incomplete data"
  let _ ← auditProof value type
  let levels := collectLevelParams (collectLevelParams {} type) value |>.params.toList
  let declaration ← if ← isProp type then
      pure (Declaration.thmDecl { name, levelParams := levels, type, value })
    else pure (Declaration.defnDecl {
      name, levelParams := levels, type, value, hints := .regular 0, safety := .safe })
  withOptions (fun options => options.setBool `debug.skipKernelTC false) do
    addDecl declaration (forceExpose := true)

private def captureReconstruction (base following baseReader : Expr) (discovery : Discovery) (extra : Expr)
    (decisions : Supplier) (statements : Array Expr := #[]) : MetaM Unit := do
  unless discovery.saturated do throwError "unsaturated finite dependencies"
  let levels := discovery.levels
  let temporaryReaders := #[baseReader] ++ levels.flatMap (fun level => #[level.read, level.reader])
  let .app _ coefficient := (← inferType extra) |
    throwError "expected a base coefficient list"
  nativeOnly extra temporaryReaders
  let mut blocks := #[extra]
  for leaf in discovery.leaves do
    if let some coefficients ← leaf.coefficients? then
      nativeOnly coefficients temporaryReaders
      unless ← withTransparency .all (isDefEq (← inferType coefficients) (← inferType extra)) do
        throwError "dependency lowering did not reach the base coefficient carrier"
      blocks := blocks.push coefficients
  let additional ← appendSupport coefficient blocks
  nativeOnly additional temporaryReaders
  let firstSupport ← if let some first := levels[0]? then
      mkAppM ``Packing.Inventory.level #[first.context, first.entries, first.records, first.facts]
    else mkListLit coefficient []
  nativeOnly firstSupport temporaryReaders
  let support ← retain (← mkAppM ``List.append #[firstSupport, additional])
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn "reconstruction: support collected"
      handle.flush
  let existence ← retain (← instantiateMVars
    (← mkAppM ``BaseContext.Context.partial_exists #[base, following, support]))
  let existential ← inferType existence
  unless existential.getAppFn.isConstOf ``Exists do throwError "base bootstrap did not produce an existential"
  let args := existential.getAppArgs
  let interpretation ← retain (← mkAppOptM ``Classical.choose
    #[some args[0]!, some args[1]!, some existence])
  let specification ← mkAppOptM ``Classical.choose_spec #[some args[0]!, some args[1]!, some existence]
  let agreement ← mkAppM ``And.left #[specification]
  let fixed ← mkAppM ``And.right #[specification]
  let closed ← mkAppM ``BaseContext.Context.partialClosed #[base, interpretation]
  let origin ← Base.ofClosed closed
  let agreement ← origin.bindAgreement agreement
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn "reconstruction: guarded base reader constructed"
      handle.flush
  unless ← withTransparency .all (isDefEq (← inferType baseReader) (← inferType origin.read)) do
    throwError "discovery base reader has a different coefficient carrier"
  if let some first := levels[0]? then
    unless ← withTransparency .all (isDefEq first.read baseReader) do
      throwError "first finite level does not follow the base reader"
  -- Share only the deterministic walk of this closed inventory. Every
  -- coefficient proof still checks its original list position and predicate.
  let coefficientCache ← IO.mkRef (none : Option CoefficientWalk)
  let domains := origin.domains (agreementSupplier agreement (some coefficientCache))
  let known ← IO.mkRef discovery.known
  let retained := lookupSupplier known (fun _ => pure none)
  let checks : Supplier := fun type => do
    if type.getAppFn.isConstOf ``Eq && type.getAppArgs[0]!.isConstOf ``Bool then
      if let some proof ← retained type then return some proof
      decisions type
    else pure none
  let baseSupplier := origin.supply domains (fun type => do
    if type.getAppFn.isConstOf ``Eq && type.getAppArgs[0]!.isConstOf ``Bool then
      return ← checks type
    if let some proof ← domains type then return some proof
    checks type)
  let mut supplier := baseSupplier
  let mut verified : Array Prefix := #[]
  let mut readers := #[origin.read]
  let mut conditions := #[agreement, fixed]
  for level in levels do
    for value in #[level.context, level.entries, level.records, level.facts] do nativeOnly value temporaryReaders
    if verified.size > 0 then
      if let some preceding := levels[verified.size - 1]? then
        unless ← withTransparency .all (isDefEq level.read preceding.reader) do
          throwError "finite levels are not in predecessor order"
    let current ← if let some previous := verified.back? then
        previous.extend supplier level.context level.entries level.records level.facts
      else do
        let firstAgreement ← mkAppM ``Transport.Inventory.Agreement.append #[agreement]
        let firstAgreement ← mkAppM ``And.left #[firstAgreement]
        let data ← mkAppM ``Packing.Inventory.level_data
          #[level.context, level.entries, level.records, level.facts,
            origin.read, origin.domain, origin.closed, firstAgreement]
        let zero ← mkAppM ``Transport.Closed.read_zero #[closed]
        let unit ← mkAppM ``Transport.Closed.read_one #[closed]
        Prefix.ofData data zero unit
    conditions := conditions.push (← mkAppM ``Packing.Inventory.Data.conditions
      #[current.data, current.zero, current.unit])
    supplier := current.supplyFrom readers supplier
    readers := readers.push current.reader
    verified := verified.push current
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn "reconstruction: ordinary-real prefix constructed"
        handle.flush
  let oldReaders := #[baseReader] ++ levels.flatMap (fun level => #[level.read, level.reader])
  let realReaders := #[origin.read] ++ verified.flatMap (fun level => #[level.read, level.reader])
  let guardScope ← getLCtx
  let guardInstances ← getLocalInstances
  let globalLocals := guardScope.getFVarIds.map mkFVar
  for statement in statements do
    if statement.hasMVar || statement.hasSorry then
      throwError "incomplete requested reconstruction statement"
    unless ← isProp statement do
      throwError "requested reconstruction statement must be a proposition"
  let requestedLeaves := statements.map fun type => (⟨type, guardScope, guardInstances⟩ : Leaf)
  let leaves := discovery.leaves ++ requestedLeaves
  unless verified.size == 2 && requestedLeaves.size == 1 do
    throwError "actual guard capture changed its two owners or native product request"
  unless discovery.leaves.size == 3772 do throwError "expensive capture changed its discovery count"
  let some leaf := leaves[131]? | throwError "actual guard capture has no guard131"
  let (required, guard) ← leaf.withContext do
    let hypotheses := (← getLCtx).getFVarIds.filter fun id =>
      (guardScope.find? id).isNone
    let required ← mkForallFVars (hypotheses.map mkFVar) leaf.type (usedOnly := true)
    let required := required.replace fun expression => do
      let i ← oldReaders.findIdx? (· == expression)
      realReaders[i]?
    unless required.getAppFn.isConstOf ``Transport.Sum do
      throwError "guard131 changed its original operation"
    let guard ← withLCtx guardScope guardInstances do
      build required supplier
    return (required, guard)
  withLCtx guardScope guardInstances do
    let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardCapture
    let fullType ← mkForallFVars globalLocals required
    let fullProof ← mkLambdaFVars globalLocals guard
    emitCapture (root ++ `index) (mkConst ``Nat) (toExpr (131 : Nat))
    emitCapture (root ++ `withReaders) fullType fullProof
    emitCapture (root ++ `guard) required guard
    let some requestedLeaf := requestedLeaves[0]? | throwError "requested leaf missing"
    let requested := requestedLeaf.type.replace fun expression => do
      let i ← oldReaders.findIdx? (· == expression)
      realReaders[i]?
    emitCapture (root ++ `request) (mkSort .zero) requested
    for (name, value) in #[(`support, support), (`interpretation, interpretation),
        (`closed, origin.closed), (`read, origin.read), (`domain, origin.domain)] do
      emitCapture (root ++ name) (← inferType value) value
    let some first := verified[0]? | throwError "first captured prefix missing"
    let some second := verified[1]? | throwError "second captured prefix missing"
    for (tag, current) in #[(`first, first), (`second, second)] do
      for (field, value) in #[(`context, current.context), (`data, current.data),
          (`point, current.point), (`read, current.read), (`reader, current.reader),
          (`zero, current.zero), (`unit, current.unit)] do
        emitCapture (root ++ tag ++ field) (← inferType value) value

private def NativeChain.capture (native : NativeChain) (following extra : Expr)
    (statements : Expr → Array Level → MetaM (Array Expr)) (decisions : Supplier)
    (record : Lookup → Array Level → MetaM (Option Expr)) (fuel : Nat := 500)
    (prepare : Option LookupPreparation := none) :
    MetaM Unit := do
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
      let discovery ← collectDependencies fuel levels types decisions record prepare
      diagnostic "chain: dependency discovery returned"
      unless discovery.levels.size == native.owners.size do
        throwError "guard capture changed its original owner count"
      for i in [:native.owners.size] do
        let some actual := discovery.levels[i]? | throwError "captured owner missing"
        unless actual.context == native.owners[i]! do
          throwError "guard capture changed an original native owner"
      let requested ← statements read discovery.levels
      captureReconstruction native.base following read discovery extra decisions requested

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData

namespace Hex.RealClosure.Algebraic.KernelReplay.FrameJoint
open Lean Meta Elab Command FiniteData

private def diagnostic (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn message
      handle.flush

syntax (name := frameGuardCapture) "#frame_guard_capture" : command
@[command_elab frameGuardCapture]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <|
  withOptions (fun options => smartUnfolding.set options false) do
    diagnostic "nested: extract original owners"
    let native ← withOptions (fun options => smartUnfolding.set options false) do
      withExporting (isExporting := false) do
        NativeChain.ofContext (← mkAppM ``FrameNested.extend #[← mkAppM ``Context.root #[mkConst ``NativeAssemblyStaged.owner]])
    unless native.owners.size == 2 do throwError "nested native descriptor was rejected"
    diagnostic "nested: build original models"
    let following := mkConst ``FiniteChainProbe.following
    let models ← withExporting (isExporting := false) do
      native.models following
    let extra ← mkListLit (← mkAppM ``BaseContext.Element #[native.base]) []
    let polynomial := mkConst ``FrameOperand.requestPoly
    let element ← mkAppM ``Element #[native.owners[1]!]
    let expected ← mkAppOptM ``DensePoly #[some element, none, none]
    unless (← inferType expected).isSort do throwError "nested product has an unsaturated polynomial type"
    kernelCheck `__nestedProductOwner (← mkEq (← inferType polynomial) expected)
      (← mkEqRefl expected)
    diagnostic "nested: native product request retains original second owner"
    let statements (_ : Expr) (levels : Array FiniteData.Level) : MetaM (Array Expr) := do
      let some level := levels[1]? | throwError "nested product lost its second native level"
      unless level.context == native.owners[1]! do
        throwError "nested product changed its original second owner"
      return #[← mkAppM ``Transport.Product #[level.reader, polynomial, polynomial]]
    diagnostic "nested: reconstruct joint ordinary-real conditions and native generator product"
    let assembly ← models.assembly native
    let prepare : Option LookupPreparation :=
      if Hex.RealClosure.batchLookups.get (← getOptions) then some NativeBatch.prepare else none
    native.capture following extra statements FiniteDataProbe.supply
      (fun lookup _ => assembly.supply native.owners.size lookup.request #[]) 500 prepare
    logInfo "original two-prefix preparation and actual guard131 retained with ordinary kernel checking"

end Hex.RealClosure.Algebraic.KernelReplay.FrameJoint
end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
/-- info: original two-prefix preparation and actual guard131 retained with ordinary kernel checking -/
#guard_msgs in
#frame_guard_capture
