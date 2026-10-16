/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Records
import HexRCF.RealCoefficients.ScalarQuote
import HexRCF.RealCoefficients.RationalQuote
open Lean Meta Qq Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.ScalarQuoteTests
open CellReplayTests.Algebraic
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

def literal : Codec.Json := .array (.cons Scalars.p0 (.cons (.number (-1)) .nil))
def wrongSign : Codec.Json := .array (.cons Scalars.p0 (.cons (.number 1) .nil))
def empty : Codec.Json := .array .nil

private meta def config (limit : Nat) : Hex.RealFormula.Reify.Config :=
  {ring := {budget := {Hex.Reflect.Budget.default with proofNodes := limit}}}

private meta def unchanged (action : MetaM Unit) : MetaM Unit := do
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let count := (← getMCtx).decls.toList.length
  action
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "failed scalar quotation retained declarations"
  unless (← getMCtx).decls.toList.length == count do
    throwError "failed scalar quotation retained metavariables"

private meta def observeTerminal (action : MetaM α) (handler : Exception → MetaM α) : MetaM α :=
  fun metaContext metaState coreContext coreState => do
    try action metaContext metaState coreContext coreState
    catch error => handler error metaContext metaState coreContext coreState

private meta def rejected (action : MetaM α) : MetaM Unit := do
  let failed ← observeTerminal (action *> pure false) fun error => do
    match error with
    | .error _ _ => pure true
    | _ => throw error
  unless failed do throwError "scalar quotation accepted an invalid input"

run_meta do
  withExporting (isExporting := false) do
    let codec : Q(ValueCodec (Algebraic.Element Data.native)) :=
      q(Algebraic.Element.codec (context := Data.native) Data.base.codec)
    let facts := mkConst ``Records.facts
    let decode := RationalQuote.decoder (mkConst ``Data.registry)
    let strictCodec := mkAppN (mkConst ``Algebraic.Element.signCodec codec.getAppFn.constLevels!)
      (codec.getAppArgs.push facts)
    let strictReader := mkApp (.proj ``ValueCodec 1 strictCodec) (mkConst ``literal)
    let .ok strict ← RootQuote.quote strictReader decode
      | throwError "strict scalar control failed"
    let .ok result ← ScalarQuote.quote codec facts (mkConst ``literal) decode
      | throwError "extension scalar quotation rejected checked supplied signs"
    unless result.usage.proofNodes > strict.usage.proofNodes do
      throwError "canonical scalar transport was not charged after strict quotation"
    let _ ← Hex.RCF.checkProof `canonicalScalar (← inferType result.proof) result.proof
    logInfo m!"canonical extension scalar quotation proofNodes={result.usage.proofNodes}"
    withExporting (isExporting := true) do
      let name := `Hex.RCF.ScalarQuoteTests.restored
      addDecl (.defnDecl {
        name,levelParams := [],type := ← inferType result.value,value := result.value,
        hints := .regular 0,safety := .safe}) (forceExpose := true)
      let reader := (← inferType result.proof).getAppArgs[1]!
      let statement ← mkEq reader
        (← mkAppM ``Option.some #[mkConst name])
      addDecl (.thmDecl {
        name := `Hex.RCF.ScalarQuoteTests.canonical_read,levelParams := [],
        type := statement,value := mkExpectedPropHint result.proof statement})
    let .ok exact ← ScalarQuote.quote codec facts (mkConst ``literal) decode
        (config result.usage.proofNodes)
      | throwError "exact scalar proof budget failed"
    unless exact.usage.proofNodes == result.usage.proofNodes do
      throwError "exact scalar proof accounting changed"
    let carried := {Hex.Reflect.Budget.zero with proofNodes := 11,sourceNodes := 7}
    let .ok continued ← ScalarQuote.quote codec facts (mkConst ``literal) decode
        (config (result.usage.proofNodes+11)) carried
      | throwError "scalar quotation did not continue an existing budget"
    unless continued.usage.proofNodes == result.usage.proofNodes+11 &&
        continued.usage.sourceNodes == 7 do
      throwError "scalar quotation reset a carried resource dimension"
    unchanged do
      let .error (.budget exhausted) ← ScalarQuote.quote codec facts (mkConst ``literal) decode
          (config (result.usage.proofNodes-1))
        | throwError "one-below scalar proof budget was accepted"
      unless exhausted.dimension == .proofNodes do throwError "wrong scalar budget dimension"
      unless exhausted.consumed ≥ strict.usage.proofNodes do
        throwError "transport exhaustion happened before the strict quote completed"
    let factType ← mkAppM ``Algebraic.SignFact #[mkConst ``Data.native]
    let noFacts ← mkAppOptM ``List.nil #[some factType]
    for malformed in #[mkConst ``ValueCodec.rat,mkConst ``Algebraic.Element.codec] do
      unchanged <| rejected <| ScalarQuote.quote malformed facts (mkConst ``literal) decode
    let untrusted ← mkSorry (← inferType facts) false
    unchanged <| rejected <| ScalarQuote.quote codec untrusted (mkConst ``literal) decode
    for (available,payload) in #[(noFacts,mkConst ``literal),(facts,mkConst ``wrongSign)] do
      unchanged do
        let .error (.providerFailure (.invalidProviderEvidence ..) _) ←
            ScalarQuote.quote codec available payload decode
          | throwError "missing or mismatched scalar sign fact did not reject"
    let .ok zero ← ScalarQuote.quote codec noFacts (mkConst ``empty) decode
      | throwError "zero scalar required a nonzero sign fact"
    let _ ← Hex.RCF.checkProof `zeroScalar (← inferType zero.proof) zero.proof
    withExporting (isExporting := true) do
      let zeroValue ← mkAppOptM ``Zero.zero #[some (← inferType zero.value),none]
      let type ← inferType zero.proof
      let statement ← mkEq type.getAppArgs[1]!
        (← mkAppM ``Option.some #[zeroValue])
      addDecl (.thmDecl {
        name := `Hex.RCF.ScalarQuoteTests.zero_read,levelParams := [],
        type := statement,value := mkExpectedPropHint zero.proof statement})
    logInfo "scalar canonical transport: exact/below budgets, missing/wrong facts, state rollback and empty zero checked"

theorem restored_polynomial : restored.polynomial =
    DensePoly.ofCoeffs (#[⟨(0 : Rat)⟩,⟨(-2 : Rat)⟩] : Array Data.base.Value) := by
  rfl

theorem restored_sign : restored.sign = -1 := by rfl

theorem canonical_source :
    ((Algebraic.Element.codec (context := Data.native) Data.base.codec).decode literal).toOption =
      some restored := canonical_read

private theorem polynomial_value :
    HexPolyTheory.Interpret.interpret Data.rational.value Data.rational.zero_iff
      (DensePoly.ofCoeffs (#[⟨(0 : Rat)⟩,⟨(-2 : Rat)⟩] : Array Data.base.Value)) =
        Polynomial.C (-2 : ℝ) * Polynomial.X := by
  ext i
  rw [HexPolyTheory.Interpret.coeff_interpret]
  rcases i with _ | _ | i
  · change Data.rational.value (0 : Data.base.Value) = _
    rw [Data.rationalZero]
    norm_num
  · change Data.rational.value (-2 : Data.base.Value) = _
    rw [Data.rationalNegativeTwo]
    norm_num
  · rw [DensePoly.coeff_eq_zero_of_size_le _ (by change 2 ≤ i+1+1; omega)]
    change Data.rational.value (0 : Data.base.Value) = _
    rw [Data.rationalZero]
    simp

theorem restored_value : Data.original.value restored = -2 * Real.sqrt 2 := by
  change (Data.rational.root (.base (BaseContext.rational Data.registry))
    Data.lower Data.frozenFrame Data.frameEncoded).value restored = _
  erw [Tower.Model.root_value]
  unfold Algebraic.Element.denote
  erw [restored_polynomial]
  change (HexPolyTheory.Interpret.interpret Data.rational.value Data.rational.zero_iff
    (DensePoly.ofCoeffs (#[⟨(0 : Rat)⟩,⟨(-2 : Rat)⟩] : Array Data.base.Value))).eval
      Data.selectedReal = _
  rw [polynomial_value, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Data.selectedSqrt]

end Hex.RCF.ScalarQuoteTests
