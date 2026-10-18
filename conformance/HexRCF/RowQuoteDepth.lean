/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RowQuoteData
public meta import HexRCF.RealCoefficients.RowQuote
public section
namespace Hex.RCF.RowQuoteDepthTests
open Lean Meta Hex.RealFormula.Reify Hex.RCF.RealCoefficients Hex.RCF.RowQuoteTests
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
private meta def reader (input : Expr) (depth : Nat) : MetaM Expr := do
  let same ← mkAppM ``Input.queryEq #[input]
  let reverse ← mkEqSymm same
  let mut row ← mkAppM ``source #[input]
  for i in [:depth] do
    let equality := if i % 2 == 0 then same else reverse
    let kind ← withTransparency .reducible (whnf (← inferType row))
    unless kind.getAppFn.isConstOf ``Hex.SignDet.SelectedSigns do
      throwError "depth control lost its selected-sign record"
    let parameters := kind.getAppArgs
    let before := parameters.back!
    let motive ← withLocalDeclD `queries (← inferType before) fun queries => do
      withLocalDeclD `same (← mkEq before queries) fun same => do
        let after := mkAppN kind.getAppFn (parameters.set! (parameters.size-1) queries)
        mkLambdaFVars #[queries,same] after
    row ← mkEqRec motive row equality
  let value ← mkAppM ``Hex.SignDet.SelectedSigns.value #[row]
  let decision ← mkDecide (← mkEq value (toExpr (1 : Int)))
  mkAppM ``gate #[decision]
run_meta do
  withLocalDeclD `input (mkApp (mkConst ``Input) (toExpr (1 : Int))) fun input => do
    for depth in [1,16,24] do
      let subject ← reader input depth
      let .ok result ← RootQuote.run subject RowQuote.decoder
        | throwError "projection quotation refused a valid {depth}-transport chain"
      let expected := if depth == 1 then 2001 else if depth == 16 then 4962 else 6758
      unless result.usage.proofNodes == expected do
        throwError "projection depth accounting changed: {depth}/{result.usage.proofNodes}"
      let target ← mkEq (← mkAppM ``Except.toOption #[subject])
        (← mkAppM ``Option.some #[mkNatLit 17])
      let checked ← Hex.RCF.checkProof `depthControl target (mkExpectedPropHint result.proof target)
      if depth == 24 then
        let target ← mkForallFVars #[input] target
        let proof ← mkLambdaFVars #[input] checked
        let name := `Hex.RCF.RowQuoteDepthTests.depth24
        addDecl (.thmDecl {name,levelParams := [],type := target,value := proof})
      let basic : Hex.RealFormula.Reify.Config := {}
      let small := {basic with ring := {basic.ring with budget :=
        {basic.ring.budget with proofNodes := result.usage.proofNodes-1}}}
      let .error (.budget exhausted) ← RootQuote.run subject RowQuote.decoder small
        | throwError "projection depth control accepted below its consumed budget"
      unless exhausted.dimension == .proofNodes do
        throwError "projection depth control exhausted the wrong resource"
      logInfo m!"projection depth={depth}; proofNodes={result.usage.proofNodes}; below refused"
end Hex.RCF.RowQuoteDepthTests
