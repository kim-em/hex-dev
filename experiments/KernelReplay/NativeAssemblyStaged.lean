/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteChain
public meta import KernelReplay.FiniteChain
public meta import KernelReplay.FiniteBase
public meta import KernelReplay.FiniteData
public meta import HexRealClosureMathlib.NativeAssemblyModels
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
import all Init.Util
import all Init.Data.Rat.Basic
import all Init.Data.Array.Basic
import all HexRealClosure.Packing
import all HexRealClosure.ValueSigns
import all HexRealClosure.RecordPackets
import all HexRealClosure.InversePackets
import all HexSignDet.Dag
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
import all HexRealClosureMathlib.SignReplay
import all HexRealClosure.SignCodec

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged
open Hex.SignDet

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat

private abbrev base := Tower.Context.base FiniteBaseProbe.base
private def epsilon : base.Value := FiniteBaseProbe.epsilon
private def delta : base.Value := FiniteBaseProbe.delta
private def variablePoly : base.Poly := DensePoly.ofCoeffs #[0, 1]
private def raw : RawDescriptor base.Value Tower.Signature :=
  ⟨base.signature, variablePoly - DensePoly.C (R := base.Value) (epsilon + delta),
    .negInf, .posInf, [1], [1]⟩

/-- The actual linear selected extension of two successive infinitesimals.
The fallback retains the base and is explicitly rejected by the probe. -/
def context : Tower.Context FiniteBaseProbe.registry :=
  match Descriptor.validate base.sign base.signature raw with
  | none => base
  | some descriptor => (base.adjoin descriptor).context

end Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged
open Lean Meta Elab Command FiniteData

private def diagnostic (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn message
      handle.flush

private def checkWitnesses : List Expr → Expr → MetaM Unit
  | [], _ => pure ()
  | expected :: remaining, type => do
    let type ← withTransparency .all (whnf type)
    unless type.getAppFn.isConstOf ``Exists do
      throwError "staged reconstruction lost a joint existential binder"
    let .lam name domain body _ := type.getAppArgs.back! |
      throwError "staged reconstruction has no explicit witness predicate"
    let domainBinding ← mkEq domain expected
    let _ ← auditProof (← mkEqRefl expected) domainBinding
    kernelCheck `__stagedWitnessDomain domainBinding (← mkEqRefl expected)
    unless body.hasLooseBVar 0 do
      throwError "staged reconstruction has an unused witness"
    withLocalDeclD name domain fun witness =>
      checkWitnesses remaining (body.instantiate1 witness)

syntax (name := nativeAssemblyStaged) "#native_assembly_staged" : command
@[command_elab nativeAssemblyStaged]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM do
  let native ← withExporting (isExporting := false) do
    NativeChain.ofContext (mkConst ``context)
  unless native.owners.size == 1 do throwError "staged native descriptor was rejected"
  unless native.bindings.size == 3 do throwError "staged source bindings were lost"
  let sourceBinding ← inferType native.bindings[0]!
  unless sourceBinding.getAppFn.isConstOf ``Eq &&
      sourceBinding.getAppArgs[1]! == mkConst ``context do
    throwError "staged source binding lost the caller's original context"
  let following := mkConst ``FiniteChainProbe.following
  let models ← native.models following
  let assembly ← models.assembly native
  let fact ← assembly.scalar 0 (mkConst ``variablePoly)
  let reused ← assembly.scalar 0 (mkConst ``variablePoly)
  unless reused == fact do throwError "staged exact scalar request was produced again"
  let other ← assembly.scalar 0 (← mkAppM ``Hex.SignDet.RawDescriptor.head #[mkConst ``raw])
  unless other != fact do throwError "staged scalar cache reused a different operand"
  let otherEquation ← mkEq (Expr.proj ``SignFact 1 other) (toExpr (0 : Int))
  let otherProof ← mkEqRefl (toExpr (0 : Int))
  let _ ← auditProof otherProof otherEquation
  kernelCheck `__nativeStagedDistinctScalar otherEquation otherProof
  diagnostic "staged: scalar supplied"
  let equation ← mkEq (Expr.proj ``SignFact 1 fact) (toExpr (1 : Int))
  diagnostic "staged: scalar binding constructed"
  let proof ← mkEqRefl (toExpr (1 : Int))
  let _ ← auditProof proof equation
  kernelCheck `__nativeStagedScalar equation proof
  diagnostic "staged: scalar binding kernel checked"
  let extra ← mkListLit (← mkAppM ``BaseContext.Element #[native.base]) []
  let exhausted ← try
    let _ ← native.reconstruct following extra (fun _ _ => pure #[]) FiniteDataProbe.supply
      (fun _ _ => throwError "zero-fuel discovery called a record producer") 0
    pure false
  catch error =>
    unless (← error.toMessageData.toString).startsWith "unsaturated finite dependencies" do
      throw error
    pure true
  unless exhausted do throwError "staged reconstruction accepted unsaturated native inventories"
  diagnostic "staged: begin ordinary-real reconstruction"
  let firstType ← withTransparency .all (whnf (← inferType native.owners[0]!))
  let firstParameters := firstType.getAppArgs
  let firstUniverse := firstType.getAppFn.constLevels![0]!
  let one := mkAppN (mkConst ``One.one [firstUniverse])
    #[firstParameters[0]!, firstParameters[4]!]
  let constantOne := mkAppN (mkConst ``DensePoly.C [firstUniverse])
    #[firstParameters[0]!, firstParameters[2]!, firstParameters[3]!, one]
  let unitEntry ← assembly.packing 0 constantOne
  let unit ← mkAppM ``Packing.value #[unitEntry]
  let statements (_ : Expr) (levels : Array FiniteData.Level) : MetaM (Array Expr) := do
    let some level := levels[0]? | throwError "staged request lost its native level"
    let carrier ← inferType unit
    let polynomial ← mkAppM ``DensePoly.ofCoeffs #[← mkArrayLit carrier [unit, unit]]
    return #[← mkAppM ``Hex.RealClosure.Transport.Sum #[level.reader, polynomial, polynomial]]
  let result ← native.reconstructModels models following extra statements FiniteDataProbe.supply
  diagnostic "staged: ordinary-real reconstruction returned"
  unless result.prefixes.size == 1 && !result.type.hasFVar && !result.proof.hasFVar do
    throwError "staged reconstruction lost its original level or retained temporary readers"
  let some retained := result.prefixes[0]? |
    throwError "staged reconstruction lost its retained prefix"
  unless retained.context == native.owners[0]! do
    throwError "staged reconstruction changed its retained native owner"
  let entries ← withTransparency .all (whnf retained.entries)
  unless entries.getAppFn.isConstOf ``List.cons do
    throwError "staged reconstruction dropped its demanded packing inventory"
  unless result.guards.size == 8 && result.requested.size == 1 do
    throwError "staged reconstruction guard count {result.guards.size}, request count {result.requested.size}"
  let expected ← statements retained.read (result.prefixes.map fun current => {
    context := current.context, entries := current.entries, records := current.records,
    facts := current.facts, read := current.read, reader := current.reader : FiniteData.Level })
  unless expected.size == 1 &&
      (← instantiateMVars result.requested[0]!) == (← instantiateMVars expected[0]!) do
    throwError "staged reconstruction changed its requested real-reader statement"
  checkWitnesses [← inferType result.interpretation, mkConst ``Real] result.type
  let _ ← auditProof result.proof result.type
  let statementName := `Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged.statement
  addDecl (.defnDecl {
    name := statementName, levelParams := [], type := mkSort .zero, value := result.type,
    hints := .regular 0, safety := .safe })
  let declaration := Declaration.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged.exists_joint,
    levelParams := [], type := mkConst statementName, value := result.proof }
  let options := (← getOptions).setBool `debug.skipKernelTC false
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true))
  let mut bindings := mkConst ``True.intro
  for sourceEquality in native.bindings.reverse do
    bindings ← mkAppM ``And.intro #[sourceEquality, bindings]
  let sourceName := `Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged.source
  addDecl (.defnDecl {
    name := sourceName, levelParams := [], type := mkSort .zero, value := ← inferType bindings,
    hints := .regular 0, safety := .safe })
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged.source_binding,
    levelParams := [], type := mkConst sourceName, value := bindings })
  logInfo "native records and joint ordinary-real reconstruction checked for an actual selected root over two successive infinitesimals"

end Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
/-- info: native records and joint ordinary-real reconstruction checked for an actual selected root over two successive infinitesimals -/
#guard_msgs in
#native_assembly_staged

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged.exists_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged.exists_joint
