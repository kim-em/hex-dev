/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FrameNested
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
namespace Hex.RealClosure.Algebraic.KernelReplay.FrameOwners
open Lean Meta Elab Command FiniteData

private def definition (name : Name) (value : Expr) : MetaM Expr := do
  unless !value.hasFVar && !value.hasMVar && !value.hasSorry do
    throwError "native owner export contains an unresolved term"
  let type ← inferType value
  let _ ← auditProof value type
  let declaration := Declaration.defnDecl {
    name, levelParams := [], type, value, hints := .regular 0, safety := .safe }
  addDecl declaration (forceExpose := true)
  withOptions (Elab.async.set · false) do
    withOptions (fun options => options.setBool `compiler.postponeCompile false) do
      compileDecl declaration
  return mkConst name

/-- Export an actual owner's raw descriptor with its checked source equality. -/
private def descriptor (rawName bindingName : Name) (owner sourceOwner : Expr)
    (bindings : Array Expr) : MetaM Unit := do
  let original ← mkAppM ``Hex.SignDet.Descriptor.raw
    #[← mkAppM ``Context.root #[sourceOwner]]
  let mut retained : Option Expr := none
  for proof in bindings do
    let type ← inferType proof
    let arguments := type.getAppArgs
    if type.getAppFn.isConstOf ``Eq && arguments.size == 3 && arguments[1]! == original then
      if retained.isSome then throwError "duplicate raw descriptor source binding"
      retained := some proof
  let some proof := retained | throwError "actual raw descriptor source binding missing"
  let type ← inferType proof
  let raw ← definition rawName type.getAppArgs[2]!
  let original ← mkAppM ``Hex.SignDet.Descriptor.raw #[← mkAppM ``Context.root #[owner]]
  let statement ← mkEq original raw
  let proof ← withTransparency .all do
    mkAppOptM ``id #[some statement, some proof]
  let _ ← auditProof proof statement
  kernelCheck `__frameOwnerRaw statement proof
  addDecl (.thmDecl { name := bindingName, levelParams := [], type := statement, value := proof })

syntax (name := frameOwners) "#frame_owners" : command
@[command_elab frameOwners]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <|
  withOptions (fun options => smartUnfolding.set options false) do
    let original ← mkAppM ``FrameNested.extend
      #[← mkAppM ``Context.root #[mkConst ``NativeAssemblyStaged.owner]]
    let native ← withExporting (isExporting := false) do NativeChain.ofContext original
    unless native.owners.size == 2 && !native.bindings.isEmpty do
      throwError "native owner export lost its original two-level chain"
    let first ← definition
      `Hex.RealClosure.Algebraic.KernelReplay.FrameOwners.first native.owners[0]!
    let second ← definition
      `Hex.RealClosure.Algebraic.KernelReplay.FrameOwners.second native.owners[1]!
    for (retained, source) in #[(first, native.owners[0]!), (second, native.owners[1]!)] do
      kernelCheck `__frameOwner (← mkEq retained source) (← mkEqRefl source)
    descriptor `Hex.RealClosure.Algebraic.KernelReplay.FrameOwners.firstRaw
      `Hex.RealClosure.Algebraic.KernelReplay.FrameOwners.first_raw
      first native.owners[0]! native.bindings
    descriptor `Hex.RealClosure.Algebraic.KernelReplay.FrameOwners.secondRaw
      `Hex.RealClosure.Algebraic.KernelReplay.FrameOwners.second_raw
      second native.owners[1]! native.bindings
    let source := native.bindings[0]!
    let statement ← inferType source
    unless statement.getAppFn.isConstOf ``Eq && statement.getAppArgs[1]! == original do
      throwError "native owner export lost the original source context"
    let _ ← auditProof source statement
    kernelCheck `__frameOwnerSource statement source
    addDecl (.defnDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.FrameOwners.source,
      levelParams := [], type := mkSort .zero, value := statement,
      hints := .regular 0, safety := .safe }) (forceExpose := true)
    addDecl (.thmDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.FrameOwners.source_binding,
      levelParams := [], type := mkConst
        `Hex.RealClosure.Algebraic.KernelReplay.FrameOwners.source,
      value := source })
    let originalToStaged ← mkAppM ``Eq.trans
      #[← mkAppM ``Eq.symm #[mkConst ``FrameNested.context_eq],
        mkConst ``FrameNested.context_eq_first]
    let originalBinding ← mkAppM ``Eq.trans #[originalToStaged, source]
    let originalStatement ← inferType originalBinding
    unless originalStatement.getAppFn.isConstOf ``Eq &&
        originalStatement.getAppArgs[1]! == mkConst ``NativeAssemblyNested.context do
      throwError "native owner export lost the unmodified original source"
    let _ ← auditProof originalBinding originalStatement
    kernelCheck `__frameOriginalSource originalStatement originalBinding
    addDecl (.defnDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.FrameOwners.original,
      levelParams := [], type := mkSort .zero, value := originalStatement,
      hints := .regular 0, safety := .safe }) (forceExpose := true)
    addDecl (.thmDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.FrameOwners.original_binding,
      levelParams := [], type := mkConst
        `Hex.RealClosure.Algebraic.KernelReplay.FrameOwners.original,
      value := originalBinding })
    logInfo "both original nested owners checked and compiled; original source binding retained"

end Hex.RealClosure.Algebraic.KernelReplay.FrameOwners

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
/-- info: both original nested owners checked and compiled; original source binding retained -/
#guard_msgs in
#frame_owners

end

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FrameOwners

/-- The actual second selected generator, retaining production storage. -/
@[expose] def beta : Element second := Element.ofPoly (DensePoly.ofCoeffs #[0, 1])

/-- The operand whose native square is required by the nested consumer. -/
@[expose] def requestPoly := DensePoly.C beta

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FrameOwners.source_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_binding

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FrameOwners.original_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms original_binding

end Hex.RealClosure.Algebraic.KernelReplay.FrameOwners
