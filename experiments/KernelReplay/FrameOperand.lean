/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FrameNested
public import KernelReplay.FrameOwners
import all KernelReplay.FrameOwners
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

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FrameOperand
universe u

-- A verified literal for the constant polynomial of a known nonzero scalar.
@[expose] def constant {E : Type u} [Zero E] [DecidableEq E]
    (c : E) (nonzero : c ≠ 0) : DensePoly E :=
  ⟨#[c], by
    right
    change some c ≠ some (0 : E)
    exact fun same => nonzero (Option.some.inj same)⟩

private theorem constant_eq {E : Type u} [Zero E] [DecidableEq E]
    (c : E) (nonzero : c ≠ 0) : constant c nonzero = DensePoly.C c := by
  cases same : DensePoly.C c with
  | mk coeffs normalized =>
    have equal : coeffs = #[c] := by
      simpa only [same] using (DensePoly.coeffs_C_of_ne_zero nonzero)
    subst coeffs
    rfl

private theorem constant_coeff {E : Type u} [Zero E] [DecidableEq E]
    (c : E) (nonzero : c ≠ 0) : (constant c nonzero).coeff 0 = c := rfl

end Hex.RealClosure.Algebraic.KernelReplay.FrameOperand
end

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FrameOperand
open Lean Meta FiniteData

private def diagnostic (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"nested operand: {message} [heartbeats={(← IO.getNumHeartbeats)/1000}]"
      handle.flush

private def retain (name : Name) (type value : Expr) : MetaM Expr := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  for expression in #[type, value] do
    if expression.hasMVar || expression.hasFVar || expression.hasSorry then
      throwError "incomplete checked nested operand"
  let _ ← auditProof value type
  let levels := collectLevelParams (collectLevelParams {} type) value |>.params.toList
  let declaration ← if ← isProp type then
      pure (Declaration.thmDecl { name, levelParams := levels, type, value })
    else pure (Declaration.defnDecl {
      name, levelParams := levels, type, value, hints := .regular 0, safety := .safe })
  withOptions (Elab.async.set · false) do
    withOptions (fun options => options.setBool `debug.skipKernelTC false) do
      addDecl declaration (forceExpose := true)
  if let .defnDecl _ := declaration then
    withOptions (Elab.async.set · false) do
      withOptions (fun options => options.setBool `compiler.postponeCompile false) do
        compileDecl declaration
  return mkConst name (levels.map Level.param)

/-- Read the sign of the original reduced generator through a checked scalar
packet. `ofPoly_restore` identifies the cached value with the original native
`ofPoly` value before it is used in the request. Kernel-checked source, bound
and coefficient equations let ordinary consumers use that exact generator. -/
unsafe def request (native : NativeChain) (models : NativeModels) (scope : Name) : MetaM Expr := do
  unless native.owners.size == 2 do throwError "nested operand needs its two original owners"
  let original := mkConst ``FrameOwners.beta
  let .defnInfo definition ← getConstInfo ``FrameOwners.beta |
    throwError "original native generator definition missing"
  unless definition.value.getAppFn.isConstOf ``Element.ofPoly do
    throwError "original native generator changed its packing constructor"
  let generator := definition.value.getAppArgs.back!
  diagnostic "begin original reduced generator scalar sign"
  let assembly ← models.assembly native
  let reduced ← mkAppM ``Context.reduce #[native.owners[1]!, generator]
  let fact ← assembly.scalar 1 reduced
  diagnostic "original reduced generator scalar sign checked"
  let sign ← mkAppM ``SignFact.sign #[fact]
  let checked ← mkAppM ``SignFact.checked #[fact]
  let nonzeroType ← mkAppM ``Ne #[sign, toExpr (0 : Int)]
  let nonzero ← mkAppOptM ``of_decide_eq_true
    #[some nonzeroType, none, some (← mkEqRefl (mkConst ``Bool.true))]
  let nonzero ← retain (scope ++ `sign_nonzero) nonzeroType nonzero
  let value ← withTransparency .all do
    mkAppM ``Element.restore #[reduced, sign, checked, nonzero]
  let value ← withExporting (isExporting := false) do
    withTransparency .all (whnf value)
  let type ← inferType original
  let value ← withTransparency .all (mkAppOptM ``id #[some type, some value])
  let beta ← retain (scope ++ `beta) type value
  let restored ← withTransparency .all do
    mkAppM ``Element.ofPoly_restore #[generator, sign, checked, nonzero]
  let nativeProof ← mkAppM ``Eq.symm #[restored]
  let nativeType ← mkEq beta original
  let nativeProof ← withTransparency .all do
    mkAppOptM ``id #[some nativeType, some nativeProof]
  let nativeProof ← retain (scope ++ `beta_native) nativeType nativeProof
  diagnostic "cached generator equals original native generator, kernel checked"
  let .defnInfo originalPolynomial ← getConstInfo ``FrameOwners.requestPoly |
    throwError "original constant polynomial definition missing"
  unless originalPolynomial.value.getAppFn.isConstOf ``DensePoly.C do
    throwError "original request changed its constant polynomial constructor"
  let sourceConstant := originalPolynomial.value.appFn!
  let parameters := sourceConstant.getAppArgs
  let levels := sourceConstant.getAppFn.constLevels!
  let zero := mkAppN (mkConst ``Zero.zero levels) (parameters.extract 0 2)
  let nonzeroType ← mkAppM ``Ne #[beta, zero]
  let stored := mkAppN (mkConst ``Element.stored type.getAppFn.constLevels!) type.getAppArgs
  let nonzero ← withLocalDeclD `equal (← mkEq beta zero) fun equal => do
    let same ← mkAppM ``congrArg #[stored, equal]
    let contradiction ← withExporting (isExporting := false) do
      withTransparency .all (mkNoConfusion (mkConst ``False) same)
    mkLambdaFVars #[equal] contradiction
  let nonzero ← retain (scope ++ `beta_nonzero) nonzeroType nonzero
  let literal := mkAppN (mkConst ``constant levels) (parameters ++ #[beta, nonzero])
  let polynomial ← retain (scope ++ `requestPoly) (← inferType literal) literal
  let literalEq := mkAppN (mkConst ``constant_eq levels) (parameters ++ #[beta, nonzero])
  let sourceEq ← mkAppM ``congrArg #[sourceConstant, nativeProof]
  let sourceProof ← withTransparency .all (mkAppM ``Eq.trans #[literalEq, sourceEq])
  let bindingType ← mkEq polynomial (mkConst ``FrameOwners.requestPoly)
  let sourceProof ← withTransparency .all (mkAppOptM ``id #[some bindingType, some sourceProof])
  let _ ← retain (scope ++ `request_native) bindingType sourceProof
  diagnostic "literal polynomial equals original polynomial, kernel checked"
  let size ← mkAppM ``DensePoly.size #[polynomial]
  let bound ← mkAppM ``Nat.lt #[toExpr (0 : Nat), size]
  let proof := mkApp (mkConst ``Nat.zero_lt_succ) (toExpr (0 : Nat))
  let _ ← retain (scope ++ `request_bound) bound proof
  let coefficient ← mkAppM ``DensePoly.coeff #[polynomial, toExpr (0 : Nat)]
  let actual := mkAppN (mkConst ``constant_coeff levels) (parameters ++ #[beta, nonzero])
  let proof ← withTransparency .all (mkAppM ``Eq.trans #[actual, nativeProof])
  let _ ← retain (scope ++ `request_coeff) (← mkEq coefficient original) proof
  diagnostic "nonempty bound and original generator coefficient kernel checked"
  return polynomial

syntax (name := frameOperand) "#frame_operand" : command
@[command_elab frameOperand]
unsafe def elaborate : Lean.Elab.Command.CommandElab := fun _ => Lean.Elab.Command.liftTermElabM <|
  withOptions (fun options => smartUnfolding.set options false) do
    let source := mkConst ``FrameOwners.source_binding
    let sourceType ← withTransparency .all (whnf (← inferType source))
    unless sourceType.getAppFn.isConstOf ``Eq do throwError "original owner source binding missing"
    let context := sourceType.getAppArgs[1]!
    let first := mkConst ``FrameOwners.first
    let second := mkConst ``FrameOwners.second
    let firstType ← withTransparency .all (whnf (← inferType first))
    let coefficient ← withTransparency .all (whnf firstType.getAppArgs[0]!)
    unless coefficient.getAppFn.isConstOf ``BaseContext.Element do
      throwError "original first owner lost its staged base"
    let native : NativeChain := {
      context, base := coefficient.getAppArgs.back!, owners := #[first, second],
      bindings := #[source, mkConst ``FrameOwners.original_binding] }
    let following := mkConst ``FiniteChainProbe.following
    let models ← withExporting (isExporting := false) do native.models following
    let _ ← request native models `Hex.RealClosure.Algebraic.KernelReplay.FrameOperand
    logInfo "original native generator cached with kernel-checked identity, polynomial, bound and coefficient equations"

end Hex.RealClosure.Algebraic.KernelReplay.FrameOperand


set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
/-- info: original native generator cached with kernel-checked identity, polynomial, bound and coefficient equations -/
#guard_msgs in
#frame_operand
