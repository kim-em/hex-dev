/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ScalarQuoteCases
public import HexSignDet.Conformance

public section

open Lean Meta Qq Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.SharedQuoteTests
open CellReplayTests.Algebraic Hex.RealFormula.Reify
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

def literal : Codec.Json := .array
  (.cons Hex.RCF.ScalarQuoteTests.literal (.cons Hex.RCF.ScalarQuoteTests.literal .nil))

def reader : Except String (DensePoly (Algebraic.Element Data.native)) :=
  Codec.readPoly (Algebraic.Element.codec (context := Data.native) Data.base.codec) literal

noncomputable def callbackReader : Except String Nat :=
  cond (Node.check Sturm.orderSign 7 Hex.Sturm.Fixtures.p (.finite (-2)) (.finite 2)
    [] Hex.SignDet.Conformance.literalNode) (.ok 7) (.error "false branch")

private meta def decoder (expression : Expr) : ReifyM (Option Expr) :=
  liftM (RationalQuote.decoder (mkConst ``Data.registry) expression)

private meta def quotePoly (decode : RootQuote.DecoderM)
    (config : Hex.RealFormula.Reify.Config := {})
    (usage : Hex.Reflect.BudgetUsage := Hex.Reflect.Budget.zero) := do
  let some expression ← unfoldDefinition? (mkConst ``reader)
    | throwError "polynomial reader definition unavailable"
  RootQuote.runWith
    (ScalarQuote.quotePolyWith expression (mkConst ``Records.facts) decode) config usage

private meta def config (limit : Nat) : Hex.RealFormula.Reify.Config :=
  {ring := {budget := {Hex.Reflect.Budget.default with proofNodes := limit}}}

private meta def unchanged (action : MetaM Unit) : MetaM Unit := do
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let count := (← getMCtx).decls.toList.length
  action
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names &&
      (← getMCtx).decls.toList.length == count do
    throwError "shared quotation failure retained declarations or metavariables"

run_meta do
  withExporting (isExporting := false) do
    let .ok result ← quotePoly decoder
      | throwError "shared scalar/poly quotation failed"
    unless result.usage.proofNodes == 1579 do
      throwError "documented polynomial proof-node count changed: {result.usage.proofNodes}"
    logInfo m!"shared scalar/poly quotation proofNodes={result.usage.proofNodes}"
    let some expanded ← unfoldDefinition? (mkConst ``reader)
      | throwError "polynomial source definition unavailable"
    let hidden ← mkFreshExprMVar (← inferType expanded)
    hidden.mvarId!.assign expanded
    let .ok assigned ← RootQuote.runWith
        (ScalarQuote.quotePolyWith hidden (mkConst ``Records.facts) decoder)
      | throwError "assigned polynomial reader failed"
    unless assigned.usage.proofNodes == result.usage.proofNodes do
      throwError "assigned polynomial reader hid its size from the request"
    withExporting (isExporting := true) do
      let declaration := Declaration.defnDecl {
        name := `Hex.RCF.SharedQuoteTests.restored,levelParams := [],
        type := ← inferType result.value,value := result.value,hints := .regular 0,safety := .safe}
      addDecl declaration
      compileDecl declaration (logErrors := true)
      let statement ← mkEq (← mkAppM ``Except.toOption #[mkConst ``reader])
        (← mkAppM ``Option.some #[mkConst `Hex.RCF.SharedQuoteTests.restored])
      addDecl (.thmDecl {
        name := `Hex.RCF.SharedQuoteTests.read_checked,levelParams := [],
        type := statement,value := mkExpectedPropHint result.proof statement})
    let .ok exact ← quotePoly decoder (config result.usage.proofNodes)
      | throwError "exact shared quotation budget failed"
    unless exact.usage.proofNodes == result.usage.proofNodes do
      throwError "shared quotation usage changed at the exact limit"
    unchanged do
      let .error (.budget exhausted) ← quotePoly decoder
          (config (result.usage.proofNodes-1))
        | throwError "one-below shared quotation budget did not exhaust"
      unless exhausted.dimension == .proofNodes do throwError "wrong shared budget dimension"
    let marked : RootQuote.DecoderM := fun expression => do
      charge .sourceNodes 13
      decoder expression
    let .ok charged ← RootQuote.run (mkConst ``callbackReader) marked
      | throwError "shared callback charge failed"
    unless charged.usage.sourceNodes ≥ 13 && charged.usage.sourceNodes % 13 == 0 do
      throwError "nested callbacks did not retain their shared source charges"
    let carried := {Hex.Reflect.Budget.zero with sourceNodes := 7,proofNodes := 11}
    let .ok continued ← RootQuote.run (mkConst ``callbackReader) marked {} carried
      | throwError "shared quotation rejected carried usage"
    unless continued.usage.sourceNodes == charged.usage.sourceNodes+7 &&
        continued.usage.proofNodes == charged.usage.proofNodes+11 do
      throwError "shared quotation reset a caller budget dimension"
    let declinedNames ← IO.mkRef (#[] : Array Name)
    let declining : RootQuote.DecoderM := fun expression => do
      let result ← decoder expression
      if result.isSome then return result
      charge .sourceNodes 3
      let name ← mkFreshUserName `declinedShared
      addDecl (.defnDecl {
        name,levelParams := [],type := mkConst ``Nat,
        value := mkNatLit 0,hints := .regular 0,safety := .safe})
      declinedNames.modify (·.push name)
      return none
    let .ok declined ← RootQuote.run (mkConst ``callbackReader) declining
      | throwError "a declined shared callback changed successful quotation"
    let names ← declinedNames.get
    unless !names.isEmpty && declined.usage.sourceNodes == names.size*3 do
      throwError "declined callback work was not charged to the request"
    for name in names do
      if (← getEnv).contains name then throwError "a declined callback retained its declaration"
    let calls ← IO.mkRef (0 : Nat)
    let terminal : RootQuote.DecoderM := fun _ => do
      calls.modify (·+1)
      let _ ← mkFreshExprMVar (mkConst ``Nat)
      let name ← mkFreshUserName `sharedTemporary
      addDecl (.defnDecl {
        name,levelParams := [],type := mkConst ``Nat,
        value := mkNatLit 0,hints := .regular 0,safety := .safe})
      abort (.providerFailure (.invalidProviderEvidence ⟨`sharedQuote,0⟩ "deliberate terminal input") #[])
    unchanged do
      let .error (.providerFailure (.invalidProviderEvidence ..) _) ←
          RootQuote.run (mkConst ``callbackReader) terminal
        | throwError "shared callback failure was swallowed"
    unless (← calls.get) == 1 do throwError "a terminal callback was retried"
    let some original ← unfoldDefinition? (mkConst ``reader)
      | throwError "polynomial source definition missing"
    let codec := original.getAppArgs[3]!
    let facts := mkConst ``Records.facts
    let stages : ReifyM RootQuote.Result := do
      let first ← ScalarQuote.quoteWith codec facts (mkConst ``Hex.RCF.ScalarQuoteTests.literal) decoder
      unless first.usage.proofNodes == 818 do
        throwError "documented scalar proof-node count changed: {first.usage.proofNodes}"
      let final ← ScalarQuote.quotePolyWith original facts decoder
      unless final.usage.proofNodes == first.usage.proofNodes+result.usage.proofNodes do
        throwError "polynomial quotation reset the preceding scalar request"
      charge .sourceNodes 7
      return final
    let .ok combined ← RootQuote.runWith stages
      | throwError "composed scalar and polynomial quotation failed"
    unless combined.usage.proofNodes == 2397 do
      throwError "documented composed proof-node count changed: {combined.usage.proofNodes}"
    unless combined.usage.sourceNodes == 7 do
      throwError "transaction runner returned stale usage after its final quote"
    unchanged do
      let .error (.budget exhausted) ← RootQuote.runWith stages (config (combined.usage.proofNodes-1))
        | throwError "composed quotation budget was reset"
      unless exhausted.dimension == .proofNodes do throwError "wrong composed budget dimension"
    unchanged do
      let .error (.providerFailure (.invalidProviderEvidence ..) _) ← RootQuote.runWith (do
          let _ ← ScalarQuote.quotePolyWith original facts decoder
          abort (.providerFailure (.invalidProviderEvidence ⟨`sharedLate,0⟩ "late rejection") #[]))
        | throwError "late rejection after a completed polynomial quote was swallowed"
    let factType ← mkAppM ``Algebraic.SignFact #[mkConst ``Data.native]
    let noFacts ← mkAppOptM ``List.nil #[some factType]
    unchanged do
      let .error (.providerFailure (.invalidProviderEvidence ..) _) ← RootQuote.runWith
          (ScalarQuote.quotePolyWith original noFacts decoder)
        | throwError "polynomial reader accepted a missing scalar fact"
    logInfo m!"composed scalar/poly quotation proofNodes={combined.usage.proofNodes}; final source charge and late refusal rollback checked"
    logInfo "shared callback budget, exact/below limits, continued usage, charged decline and terminal rollback checked"

theorem coefficient_zero : restored.coeff 0 = Hex.RCF.ScalarQuoteTests.restored := by rfl
theorem coefficient_one : restored.coeff 1 = Hex.RCF.ScalarQuoteTests.restored := by rfl

theorem value_zero : Data.original.value (restored.coeff 0) = -2 * Real.sqrt 2 := by
  rw [coefficient_zero]
  exact Hex.RCF.ScalarQuoteTests.restored_value

end Hex.RCF.SharedQuoteTests
