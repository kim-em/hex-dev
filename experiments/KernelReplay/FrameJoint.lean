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

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FrameJoint
open Lean Meta Elab Command FiniteData

private def diagnostic (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn message
      handle.flush

private def checkWitnesses : List Expr → Expr → MetaM Unit
  | [], type => do
    let type ← withTransparency .all (whnf type)
    if type.getAppFn.isConstOf ``Exists || type.isForall then
      throwError "nested reconstruction retained an unexpected witness or hypothesis"
  | expected :: remaining, type => do
    let type ← withTransparency .all (whnf type)
    unless type.getAppFn.isConstOf ``Exists do
      throwError "nested reconstruction lost a joint existential binder"
    let .lam name domain body _ := type.getAppArgs.back! |
      throwError "nested reconstruction has no explicit witness predicate"
    kernelCheck `__nestedWitnessDomain (← mkEq domain expected) (← mkEqRefl expected)
    unless body.hasLooseBVar 0 do
      throwError "nested reconstruction has an unused witness"
    withLocalDeclD name domain fun witness =>
      checkWitnesses remaining (body.instantiate1 witness)

syntax (name := frameJoint) "#frame_joint" : command
@[command_elab frameJoint]
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
    let result ← native.reconstructModels models following extra statements FiniteDataProbe.supply
    unless result.prefixes.size == 2 && !result.type.hasFVar && !result.proof.hasFVar do
      throwError "nested reconstruction lost its original levels or retained temporary readers"
    for i in [:2] do
      let some retained := result.prefixes[i]? | throwError "nested prefix missing"
      unless retained.context == native.owners[i]! do
        throwError "nested reconstruction changed an original owner"
    unless result.requested.size == 1 do
      throwError "nested reconstruction lost its requested native product"
    let expected ← statements result.interpretation (result.prefixes.map fun current => {
      context := current.context, entries := current.entries, records := current.records,
      facts := current.facts, read := current.read, reader := current.reader : FiniteData.Level })
    unless expected.size == 1 &&
        (← instantiateMVars result.requested[0]!) == (← instantiateMVars expected[0]!) do
      throwError "nested reconstruction changed its requested product or real reader"
    checkWitnesses [← inferType result.interpretation, mkConst ``Real, mkConst ``Real] result.type
    let _ ← auditProof result.proof result.type
    let statementName := `Hex.RealClosure.Algebraic.KernelReplay.FrameJoint.statement
    addDecl (.defnDecl {
      name := statementName, levelParams := [], type := mkSort .zero, value := result.type,
      hints := .regular 0, safety := .safe }) (forceExpose := true)
    let declaration := Declaration.thmDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.FrameJoint.exists_joint,
      levelParams := [], type := mkConst statementName, value := result.proof }
    let options := (← getOptions).setBool `debug.skipKernelTC false
    setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true))
    logInfo "two native selected extensions and the second generator product reconstructed jointly in the ordinary reals"

end Hex.RealClosure.Algebraic.KernelReplay.FrameJoint

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
/-- info: two native selected extensions and the second generator product reconstructed jointly in the ordinary reals -/
#guard_msgs in
#frame_joint

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FrameJoint.exists_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FrameJoint.exists_joint
