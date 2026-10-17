/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealClosure.RootReplay
public meta import HexRCF.RealCoefficients.RootQuote
public meta section
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.RealCoefficients.RootHeader

/-- Independently checked reconstruction of a root and its original raw subject.
The retained root result includes both reads and the final binding in its usage. -/
structure Result where
  root : RootQuote.Result
  raw : Expr
  parsed : Expr
  binding : Expr

/-- Derive the complete raw-header identity from the original checked root
reader and the independently quoted subject reader. Retain all original
implicit instances by taking the subject reader from the owner's theorem.
The caller supplies the transaction through `RootQuote.runWith`; all quotation,
source parsing and binding proof construction consume its shared budget.
This does not authenticate a real source alias or construct an origin history. -/
def quoteWith (reader : Expr) (decode : RootQuote.DecoderM := fun _ => pure none) :
    Hex.RealFormula.Reify.ReifyM Result := do
  let reader ← instantiateMVars reader
  unless reader.getAppFn.isConstOf ``Algebraic.RootReplay.readDescriptor do
    throwError "header quotation needs the complete original descriptor reader"
  let information ← getConstInfo ``Algebraic.RootReplay.readDescriptor
  let subjectInfo ← getConstInfo ``Algebraic.RootReplay.readDescriptor_subject
  unless reader.getAppNumArgs == information.type.getNumHeadForalls &&
      subjectInfo.type.getNumHeadForalls == reader.getAppNumArgs+2 &&
      information.levelParams.isEmpty && subjectInfo.levelParams.isEmpty do
    throwError "descriptor reader/header law signatures differ"
  let root ← RootQuote.quoteWith reader decode
  let strict ← mkAppM ``RootQuote.read_eq #[reader,root.value,root.proof]
  Hex.RealFormula.Reify.accountProof strict
  let consumed := mkAppN (mkConst ``Algebraic.RootReplay.readDescriptor_subject)
    (reader.getAppArgs ++ #[root.value,strict])
  Hex.RealFormula.Reify.accountProof consumed
  let kind ← inferType consumed
  unless kind.isAppOfArity ``Eq 3 do throwError "descriptor subject law is not an equation"
  let subjectReader := kind.getAppArgs[1]!
  let raw ← RootQuote.quoteWith subjectReader decode
  let parsed ← mkAppM ``RootQuote.read_eq #[subjectReader,raw.value,raw.proof]
  Hex.RealFormula.Reify.accountProof parsed
  let same ← mkEqTrans (← mkEqSymm consumed) parsed
  let binding ← mkAppM ``Except.ok.inj #[same]
  Hex.RealFormula.Reify.accountProof binding
  let statement ← mkEq (← mkAppM ``Descriptor.raw #[root.value]) raw.value
  let binding ← Hex.RCF.checkProof `quotedHeader statement binding
  return ⟨{root with usage := (← get).budget.consumed},raw.value,parsed,binding⟩

end Hex.RCF.RealCoefficients.RootHeader
