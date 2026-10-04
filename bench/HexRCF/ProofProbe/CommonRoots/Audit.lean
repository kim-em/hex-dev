/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.CommonRoots.Simple
import all HexRCF.ProofProbe.CommonRoots.Simple
public import HexRCF.ProofProbe.CommonRoots.Repeated
import all HexRCF.ProofProbe.CommonRoots.Repeated
public import HexRCF.ProofProbe.CommonRoots.Shared
import all HexRCF.ProofProbe.CommonRoots.Shared
public meta import HexRCF.ProofProbe.Windows.Audit
import all HexRCF.ProofProbe.Windows.Audit
public meta section

namespace Hex.RCF.ProofProbe.CommonRoots
open Lean Meta

private partial def listSize (e : Expr) : MetaM Nat := do
  if e.isAppOfArity ``List.nil 1 then return 0
  unless e.isAppOfArity ``List.cons 3 do throwError "nonliteral certificate list"
  return 1 + (← listSize e.getAppArgs[2]!)

private def arraySize (e : Expr) : MetaM Nat := do
  unless e.isAppOfArity ``List.toArray 2 do throwError "nonliteral certificate array"
  listSize e.getAppArgs[1]!

private def describe (name : Name) : MetaM Json := do
  let some owner := (← getEnv).getModuleIdxFor? name | throwError "probe is not imported"
  let (_, counts) ← (Windows.Audit.declaration owner name).run {}
  let mut rows : List Json := []
  for (e, _) in counts.expressions.toList do
    if e.isAppOfArity ``RealCoefficients.FieldBuild.Result.mk 10 then
      let args := e.getAppArgs
      let radical := args[6]!
      unless radical.isAppOf ``RealCoefficients.RadicalCert.mk do
        throwError "nonliteral carrier certificate"
      let core := radical.getAppArgs[5]!
      unless core.isAppOf ``DensePoly.ofCoeffs do throwError "nonliteral carrier polynomial"
      let coefficients ← arraySize core.getAppArgs.back!
      let isolation := args[7]!
      unless isolation.isAppOf ``RealCoefficients.IsolationReplay.mk do
        throwError "nonliteral root isolation"
      let intervals := isolation.getAppArgs[4]!
      unless intervals.isAppOf ``IsolationCert.mk do throwError "nonliteral isolation intervals"
      let sections ← arraySize intervals.getAppArgs.back!
      unless coefficients = 5 && sections = 4 do
        throwError "probe changed its normalized carrier degree or root union size"
      let signs := args[8]!
      unless signs.isAppOf ``RealCoefficients.FieldRootSigns.Table.mk do
        throwError "nonliteral root sign table"
      let atoms ← listSize signs.getAppArgs.back!
      rows := Json.mkObj [("carrier_coefficients", toJson coefficients),
        ("sections", toJson sections), ("sectors", toJson (sections + 1)),
        ("root_sign_rows", toJson atoms)] :: rows
  unless rows.length = 1 do throwError "expected one complete solver envelope"
  let solver := counts.expressions.toList.any fun (e, _) =>
    e.isConstOf ``RealCoefficients.FieldBuild.Result.checkExists_sound
  unless solver do throwError "source proof bypassed the fixed-field algebraic solver"
  let common := counts.expressions.toList.any fun (e, _) =>
    e.isConstOf ``RealCoefficients.CommonPresentation.checkPolynomials_sound
  if common then throwError "named sqrt(2) probe changed its source authentication route"
  return Json.mkObj [("proof", toJson name.toString), ("common_presentation", toJson common), ("solver", toJson rows.head!),
    ("syntax", ← Windows.Audit.measure name)]

run_meta do logInfo m!"{(← describe ``Simple.witness).compress}"
run_meta do logInfo m!"{(← describe ``Repeated.witness).compress}"
run_meta do logInfo m!"{(← describe ``Shared.witness).compress}"

end Hex.RCF.ProofProbe.CommonRoots
