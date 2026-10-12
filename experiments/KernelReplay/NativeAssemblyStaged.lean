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
private def context : Tower.Context FiniteBaseProbe.registry :=
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

syntax (name := nativeAssemblyStaged) "#native_assembly_staged" : command
@[command_elab nativeAssemblyStaged]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM do
  let native ← withExporting (isExporting := false) do
    NativeChain.ofContext (mkConst ``context)
  unless native.owners.size == 1 do throwError "staged native descriptor was rejected"
  let following := mkConst ``FiniteChainProbe.following
  let models ← native.models following
  let assembly ← models.assembly native
  let fact ← assembly.scalar 0 (mkConst ``variablePoly)
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
  let result ← native.reconstructModels models following extra
    (fun _ _ => pure #[]) FiniteDataProbe.supply
  diagnostic "staged: ordinary-real reconstruction returned"
  unless result.prefixes.size == 1 && !result.type.hasFVar && !result.proof.hasFVar do
    throwError "staged reconstruction lost its original level or retained temporary readers"
  let _ ← auditProof result.proof result.type
  kernelCheck `__nativeStagedJoint result.type result.proof
  let declaration := Declaration.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged.exists_joint,
    levelParams := [], type := result.type, value := result.proof }
  let options := (← getOptions).setBool `debug.skipKernelTC false
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true))
  logInfo "native records and joint ordinary-real reconstruction checked for an actual selected root over two successive infinitesimals"

end Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
#native_assembly_staged

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged.exists_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged.exists_joint
