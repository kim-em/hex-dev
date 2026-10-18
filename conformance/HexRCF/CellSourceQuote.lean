/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.RowQuote
import HexRCF.CellReplay.Operations
import HexRCF.RealCoefficients.RootQuote
import HexRCF.RealCoefficients.RationalQuote
import HexRCF.RealCoefficients.ScalarQuote
import HexRCF.RootTableQuote.Input
import HexRCF.RealCoefficients.CellQuote
import HexRCF.SourceIdentityPacket
open Lean Meta Qq Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.RealCoefficients.CellReplayTests
open Hex.RCF.RealCoefficients.CellReplayTests.Algebraic
/-! Quote the original source through independently restored literal cells over
one retained selected algebraic parent. Older complete-packet acceptance proofs
are excluded by the importing audit; coefficient seed facts remain checked inputs. This fixed-parent case does not reconstruct arbitrary source histories. -/
namespace Hex.RCF.CellSourceQuote
set_option maxHeartbeats 60000000
set_option maxRecDepth 32768
set_option smartUnfolding false
set_option trace.Hex.RCF.RowQuote true
def rational (value : Int) : Codec.Json := .arr #[.number 0,.number value,.number 1]
def scalar (polynomial : Array Codec.Json) (sign : Int) : Codec.Json :=
  .arr #[.arr polynomial,.number sign]
def polynomial : Codec.Json := .arr #[
  scalar #[rational 0,rational (-1)] (-1),.arr #[],scalar #[rational 1] 1]
run_meta do
  withoutExporting do
    let target : Q(Prop) := q(∃ x : ℝ, x ^ 2 - Real.sqrt 2 ≥ 0 ∧
      x ^ 2 - Real.sqrt 2 ≤ 0 ∧ (0 : ℝ) = 0)
    let basic : Hex.RealFormula.Reify.Config := {}
    let config := {basic with ring := {basic.ring with budget :=
      {basic.ring.budget with proofNodes := 24000000}}}
    let .ok source ← Reify.prepare target config
      | throwError "original complete-cell source was not recognized"
    unless source.coefficients.size == 1 && source.divisors.isEmpty do
      throwError "original complete-cell source changed its coefficient/guard inventory"
    let quantified ← whnf source.formula
    unless quantified.getAppFn.isConstOf ``Hex.RealFormula.Prenex.quant do
      throwError "original complete-cell source is not quantified"
    let matrix ← whnf quantified.appArg!
    unless matrix.getAppFn.isConstOf ``Hex.RealFormula.Prenex.matrix do
      throwError "original complete-cell source has no shared matrix"
    let formula := matrix.appArg!
    let codec : Q(ValueCodec (Algebraic.Element Hex.RCF.SelectedRootTests.Data.native)) :=
      q(Algebraic.Element.codec (context := Hex.RCF.SelectedRootTests.Data.native)
        Hex.RCF.SelectedRootTests.Data.base.codec)
    let reader ← mkAppM ``Codec.readPoly #[codec,mkConst ``polynomial]
    let result ← match ← RootQuote.runWith (do
        let p ← ScalarQuote.quotePolyWith reader (mkConst ``Records.facts) fun expression =>
          liftM (RationalQuote.decoder (mkConst ``Hex.RCF.SelectedRootTests.Data.registry) expression)
        logInfo m!"literal polynomial reconstructed; proofNodes={p.usage.proofNodes}"
        let polynomialType ← inferType p.value
        Hex.RealFormula.Reify.accountProof polynomialType
        Hex.RealFormula.Reify.accountProof p.value
        let polynomialName := mkPrivateName (← getEnv) (← mkFreshUserName `FrozenPolynomial)
        let polynomial ← mkAuxDefinition polynomialName polynomialType p.value (compile := false)
        let signature ← mkAppM ``Tower.Context.signature #[mkConst ``Schema.parent]
        let cert ← mkAppM ``RadicalCert.mk #[signature,polynomial,polynomial,polynomial,mkNatLit 1]
        let certificateType ← inferType cert
        Hex.RealFormula.Reify.accountProof certificateType
        Hex.RealFormula.Reify.accountProof cert
        let certificateName := mkPrivateName (← getEnv) (← mkFreshUserName `FrozenRadical)
        let cert ← mkAuxDefinition certificateName certificateType cert (compile := false)
        let cells := mkApp (mkConst ``Codec.Json.Value.array)
          (mkApp2 (mkConst ``Codec.Json.Values.cons) (mkConst ``Literals.sections)
            (mkApp2 (mkConst ``Codec.Json.Values.cons) (mkConst ``Literals.sectors)
              (mkConst ``Codec.Json.Values.nil)))
        let empty ← mkListLit (← mkAppM ``Tower.Context.Value #[mkConst ``Schema.parent]) []
        let some operations ← unfoldDefinition? (mkConst ``Operations.operations)
          | throwError "supplied operations have no accessible definition"
        let operations := operations.replace fun expression =>
          if expression.isConstOf ``Hex.RCF.SelectedRootTests.Data.reduction then
            some (mkConst ``Hex.RCF.RootTableQuoteTests.reduction)
          else if expression.isConstOf ``Hex.RCF.SelectedRootTests.Data.reduction_eq then
            some (mkConst ``Hex.RCF.RootTableQuoteTests.reduction_eq)
          else none
        Meta.check operations
        let operationsType ← inferType operations
        Hex.RealFormula.Reify.accountProof operationsType
        Hex.RealFormula.Reify.accountProof operations
        let name := mkPrivateName (← getEnv) (← mkFreshUserName `FrozenOperations)
        let operations ← mkAuxDefinition name operationsType operations (compile := false)
        let program ← mkAppM ``CellOperations.check
          #[operations,mkConst ``Operations.codec,mkConst ``Schema.values,
            formula,empty,cert,
            mkConst ``Hex.RealFormula.Quantifier.existsReal,mkConst ``Literals.roots,cells]
        let quoted ← CellQuote.replayWith program fun expression => do
          if let some proof ← RowQuote.decoder expression then return some proof
          if expression.getAppFn.isConstOf ``RootTable.read then
            let table ← RootQuote.quoteWith expression fun expression =>
              liftM (RationalQuote.decoder (mkConst ``Hex.RCF.SelectedRootTests.Data.registry) expression)
            let kind ← inferType table.value
            Hex.RealFormula.Reify.accountProof kind
            Hex.RealFormula.Reify.accountProof table.value
            let name := mkPrivateName (← getEnv) (← mkFreshUserName `FrozenRootTable)
            let value ← mkAuxDefinition name kind table.value (compile := false)
            let strict ← mkAppM ``RootQuote.read_eq #[expression,table.value,table.proof]
            let readerType ← whnf (← inferType expression)
            unless readerType.isAppOfArity ``Except 2 do
              throwError "nested root-table result changed its exception type"
            let accepted ← mkAppOptM ``Except.ok
              #[some readerType.getAppArgs[0]!,some readerType.getAppArgs[1]!,some value]
            let target ← mkEq expression accepted
            Hex.RealFormula.Reify.accountProof target
            Hex.RealFormula.Reify.accountProof strict
            return some (← Hex.RCF.checkProof `frozenTable target (mkExpectedPropHint strict target))
          return none
        let result := quoted
        let kind ← inferType result.proof
        unless kind.isAppOfArity ``Eq 3 do throwError "complete quotation did not return an equation"
        let optional := kind.getAppArgs[1]!
        unless optional.getAppFn.isConstOf ``Except.toOption do
          throwError "staged quotation omitted the optional reader boundary"
        let program := optional.getAppArgs.back!
        unless program.getAppFn.isConstOf ``CellOperations.check do
          throwError "complete quotation changed its original checker"
        let readerType ← whnf (← inferType program)
        let accepted ← mkAppOptM ``Except.ok
          #[some readerType.getAppArgs[0]!,some readerType.getAppArgs[1]!,some (mkConst ``Bool.true)]
        let target ← mkEq program accepted
        let checked ← mkAppM ``RootQuote.read_eq #[program,result.value,result.proof]
        Hex.RealFormula.Reify.accountProof target
        Hex.RealFormula.Reify.accountProof checked
        let proof ← Hex.RCF.checkProof `freshCompleteLiteral target (mkExpectedPropHint checked target)
        let axioms ← collectAxioms proof.getAppFn.constName!
        unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
          throwError "fresh complete literal quote has inadmissible dependencies"
        addDecl (.thmDecl {
          name := `Hex.RCF.CellSourceQuote.checked,levelParams := [],type := target,value := proof})
        let valuation ← withLocalDeclD `i (← mkAppM ``Fin #[mkNatLit 1]) fun i => do
          let value ← mkAppM ``Tower.Model.value
            #[mkConst ``Schema.original,mkApp (mkConst ``Schema.values) i]
          mkLambdaFVars #[i] value
        let identityType ← mkEq valuation source.valuation
        let identity ← mkFreshExprMVar identityType
        let remaining ← Lean.Elab.runTactic' identity.mvarId!
          (← `(tactic| funext i; fin_cases i; exact Hex.RCF.SourceIdentityPacket.coefficient))
        unless remaining.isEmpty do throwError "original coefficient identity left goals"
        let identity ← instantiateMVars identity
        Hex.RealFormula.Reify.accountProof identityType
        Hex.RealFormula.Reify.accountProof identity
        let identity ← Hex.RCF.checkProof `completeSourceIdentity identityType identity
        let realTarget := source.original
        let arguments := program.getAppArgs
        let info ← getFunInfoNArgs program.getAppFn arguments.size
        let inputs := arguments.zipIdx |>.filterMap fun (argument,index) =>
          if info.paramInfo[index]!.binderInfo.isExplicit then some argument else none
        let checker ← mkAppM ``CompleteReplay.check (inputs.extract 1 inputs.size)
        let law ← mkAppM ``CellOperations.check_eq inputs
        let accepted ← mkAppM ``Eq.trans #[← mkEqSymm law,mkConst `Hex.RCF.CellSourceQuote.checked]
        let completed ← CellQuote.finishPacketWith source realTarget checker accepted
          (mkConst ``Schema.original) identity
        let sourceProof := completed.proof
        Hex.RealFormula.Reify.accountProof realTarget
        Hex.RealFormula.Reify.accountProof sourceProof
        let sourceProof ← Hex.RCF.checkProof `freshCompleteSource realTarget sourceProof
        addDecl (.thmDecl {
          name := `Hex.RCF.CellSourceQuote.source,levelParams := [],type := realTarget,value := sourceProof})
        let sourceAxioms ← collectAxioms `Hex.RCF.CellSourceQuote.source
        unless sourceAxioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
          throwError "complete original source quotation has inadmissible dependencies"
        logInfo m!"original algebraic source quotation proofNodes={result.usage.proofNodes}; axioms={axioms}"
        logInfo m!"original algebraic source complete proofNodes={completed.usage.proofNodes}"
        return {completed with usage := (← get).budget.consumed}
      ) config source.usage with
      | .ok result => pure result
      | .error error => throwError "fresh complete literal quote refused: {Hex.RealFormula.Reify.Error.toMessageData error}"
    logInfo m!"complete original-source attempt consumed proofNodes={result.usage.proofNodes}"
end Hex.RCF.CellSourceQuote
