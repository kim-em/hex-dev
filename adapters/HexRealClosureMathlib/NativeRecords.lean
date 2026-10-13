/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.KernelReplay
public import HexSignDet.Codec
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Value
import all HexSignDet.Descriptor
import all HexRealRoots.TarskiShared
import all HexPoly.Dense
import all HexPoly.Euclid.DivGcd
import all Init.Data.Rat.Basic
import all Init.Data.Array.Basic
import all HexRealClosure.Packing
import all HexRealClosure.ValueSigns
import all HexRealClosure.InversePacking
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
import all HexRealClosure.Algebraic

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay
open Lean Meta Hex.SignDet

mutual
/-- Quote untrusted integer-only JSON data as constructors. Acceptance still
requires checking the resulting expression and its literal subject bindings. -/
def jsonExpr : Codec.Json → Expr
  | .null => mkConst ``Codec.Json.Value.null
  | .bool value => mkApp (mkConst ``Codec.Json.Value.bool) (toExpr value)
  | .number value => mkApp (mkConst ``Codec.Json.Value.number) (toExpr value)
  | .string value => mkApp (mkConst ``Codec.Json.Value.string) (toExpr value)
  | .array values => mkApp (mkConst ``Codec.Json.Value.array) (valuesExpr values)
  | .object fields => mkApp (mkConst ``Codec.Json.Value.object) (fieldsExpr fields)
def valuesExpr : Codec.Json.Values → Expr
  | .nil => mkConst ``Codec.Json.Values.nil
  | .cons value rest => mkApp2 (mkConst ``Codec.Json.Values.cons) (jsonExpr value) (valuesExpr rest)
def fieldsExpr : Codec.Json.Fields → Expr
  | .nil => mkConst ``Codec.Json.Fields.nil
  | .cons key value rest => mkAppN (mkConst ``Codec.Json.Fields.cons)
      #[toExpr key, jsonExpr value, fieldsExpr rest]
end

private def blocked (expression : Expr) (fuel : Nat) : MetaM Expr := do
  let fuel + 1 := fuel | return expression
  let expression ← withTransparency .all (whnf expression)
  match expression with
  | .proj _ _ value => blocked value fuel
  | .mdata _ value => blocked value fuel
  | _ =>
    if let .const name _ := expression.getAppFn then
      if let .recInfo recursor ← getConstInfo name then
        if let some major := expression.getAppArgs[recursor.getMajorIdx]? then
          return ← blocked major fuel
    return expression

private def diagnostic (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_RECORD_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn message
      handle.flush

/-- Keep the original type parameters on a reduced constructor. In particular,
context parameters need not retain their expanded field and model expressions.
The constructor's data fields remain literal; the final kernel check validates
their types with these original parameters. -/
private def retainParameters (original record : Expr) : MetaM Expr := do
  let type ← withTransparency .reducible (whnf (← inferType original))
  unless type.getAppFn.isConstOf ``Option do return record
  let expected ← withTransparency .reducible (whnf type.getAppArgs.back!)
  let .const name _ := record.getAppFn | return record
  let .ctorInfo constructor ← getConstInfo name | return record
  unless expected.getAppFn.isConstOf constructor.induct do return record
  let parameters := expected.getAppArgs
  unless parameters.size >= constructor.numParams do return record
  let mut arguments := record.getAppArgs
  unless arguments.size >= constructor.numParams do return record
  for i in [:constructor.numParams] do
    arguments := arguments.set! i parameters[i]!
  return mkAppN record.getAppFn arguments

/-- Check a closed evidence record as one safe definition. Its literal data
remain transparent, while later binding and inventory checks reuse the checked
semantic proofs instead of inserting the whole reader result repeatedly. -/
private def retainRecord (record : Expr) : MetaM Expr := do
  let type ← inferType record
  let _ ← auditProof record type
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `__nativeRecord)
  let levels := collectLevelParams (collectLevelParams {} type) record |>.params.toList
  let declaration := Declaration.defnDecl {
    name, levelParams := levels, type, value := record,
    hints := .regular 0, safety := .safe }
  diagnostic s!"record: begin {type.getAppFn.constName!} definition check"
  let options := (← getOptions).setBool `debug.skipKernelTC false
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true))
  diagnostic "record: definition kernel checked"
  withOptions (Elab.async.set · false) do
    withOptions (fun options => options.setBool `compiler.postponeCompile false) do
      compileDecl declaration
  diagnostic "record: definition compiled"
  return mkConst name (levels.map Level.param)

/-- Reduce a supplied literal reader, retaining and kernel-checking its
conversion proof before exposing the checked record. -/
def checkedRecordProof (original : Expr) : MetaM (Expr × Expr) := withExporting (isExporting := false) do
  diagnostic "record: begin whnf"
  let result ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (whnf original)
  diagnostic "record: whnf complete"
  let mut rules : SimpTheorems := {}
  for name in #[``Dag.replay_eq, ``Dag.step_eq, ``Node.check_eq, ``checkMoment_eq,
      ``TarskiCertificate.check_eq, ``Array.toList_range] do
    rules ← rules.addConst name
  rules ← rules.addConst ``Array.all_toList (inv := true)
  rules ← rules.addConst ``Array.foldlM_toList (inv := true)
  let simpContext ← Simp.mkContext (simpTheorems := #[rules])
    (config := { decide := false }) (congrTheorems := ← getSimpCongrTheorems)
  let (simplified, _) ← Meta.simp result simpContext
  diagnostic "record: simplification complete"
  let proof ← simplified.getProof' result
  let result ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (reduce simplified.expr)
  diagnostic "record: data reduction complete"
  let equation ← mkEq original result
  let locals := (← getLCtx).getFVarIds.map mkFVar
  let closedProof ← mkLambdaFVars locals proof (usedOnly := true)
  let statement ← mkForallFVars locals equation (usedOnly := true)
  let _ ← auditProof closedProof statement
  kernelCheck `__nativeRecordPacket statement closedProof
  diagnostic "record: reader conversion kernel checked"
  unless result.getAppFn.isConstOf ``Option.some do
    throwError "literal reader rejected or remained at {← blocked result 128}"
  let record ← retainParameters original result.getAppArgs.back!
  let type ← inferType record
  if !record.hasFVar &&
      #[``SignFact, ``Packing, ``ValueSign, ``InverseFact].any type.getAppFn.isConstOf then
    let record ← retainRecord record
    let retainedEquation ← mkEq original (← mkAppM ``Option.some #[record])
    let retainedStatement ← mkForallFVars locals retainedEquation (usedOnly := true)
    let _ ← auditProof closedProof retainedStatement
    kernelCheck `__nativeRetainedRecordConversion retainedStatement closedProof
    return (record, proof)
  let retainedEquation ← mkEq original (← mkAppM ``Option.some #[record])
  let retainedStatement ← mkForallFVars locals retainedEquation (usedOnly := true)
  let _ ← auditProof closedProof retainedStatement
  kernelCheck `__nativeOpenRecordConversion retainedStatement closedProof
  diagnostic "record: retained reader conversion kernel checked"
  return (record, proof)

/-- Reduce a supplied literal reader and return its independently checked record. -/
def checkedRecord (original : Expr) : MetaM Expr := do
  return (← checkedRecordProof original).1

end Hex.RealClosure.Algebraic.KernelReplay
