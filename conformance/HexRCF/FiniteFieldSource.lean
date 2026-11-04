/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.FiniteFieldFormula
public meta import HexRCF.FiniteFieldFormula
public meta import HexRCF.RealCoefficients.Tactic
public meta import HexRCF.RealCoefficients.CommonPresentation
public meta import Lean.Elab.Command
public section
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
set_option debug.skipKernelTC false
set_option Elab.async false
open Hex Hex.RCF Hex.RCF.RealCoefficients Lean Meta Qq

private theorem selectedQuartic :
    (Field.literalRep CertificationInputs.polynomial CertificationInputs.square
      (by decide) (by decide)).root.re = CertificationInputs.realAlgebraic.toReal :=
  (Selected.real_toReal CertificationInputs.polynomial CertificationInputs.square
    (by decide) (by decide) (by rfl) (by decide) (by decide)
    CertificationInputs.checked CertificationInputs.squarefree (by decide)).symm

run_meta do
  let (_,_,quadratic) ← FieldRuntime.coefficient q(Real.sqrt 2)
  let common := QAdjoin.common #[CertificationInputs.realAlgebraic.toAlgebraic,quadratic.toAlgebraic]
  let p := common.generator.p
  let s := common.generator.rep.1.square
  if hw : atomWitness p s then do
    if hp : (mahlerPrec p : Int) ≤ s.prec then do
      let root := SimpleRoot.ofSquare p s hw hp
      let a ← match common.entries[0]? with
        | none => throwError "missing quartic coordinate"
        | some entry => pure (PolyQuot.ofSquare p s entry.coeffs hw hp)
      let b ← match common.entries[1]? with
        | none => throwError "missing quadratic coordinate"
        | some entry => pure (PolyQuot.ofSquare p s entry.coeffs hw hp)
      let values : Fin 2 → PolyQuot p root := fun i => if i.val = 0 then a else b
      let firstP := CertificationInputs.polynomial
      let firstS := CertificationInputs.square
      let secondP := SquareRoot.polynomial 2
      let secondS := quadratic.toAlgebraic.rep.1.square
      let table ← match FieldBuild.buildTable p s hw hp
          [CommonPresentation.discSlack firstS a,CommonPresentation.discSlack secondS b,
            CommonPresentation.discSlack secondS (-b)] with
        | none => throwError "source sign table failed"
        | some result => pure result
      unless CommonPresentation.checkEntry hw hp table (ZPoly.toRatPoly firstP) firstS a do
        throwError "quartic source authentication failed"
      unless CommonPresentation.checkEntry hw hp table (ZPoly.toRatPoly secondP) secondS b do
        throwError "quadratic source authentication failed"
      unless CommonPresentation.checkEquation (ZPoly.toRatPoly secondP) (-b) do
        throwError "negative conjugate was not an equation root"
      if CommonPresentation.checkEntry hw hp table (ZPoly.toRatPoly secondP) secondS (-b) then
        throwError "wrong selected conjugate accepted"
      let pExpr : Q(ZPoly) ← FieldLiteral.zpolyExpr p
      let sExpr : Q(DyadicSquare) ← FieldLiteral.squareExpr s
      let hwExpr ← mkDecideProof q(atomWitness $pExpr $sExpr)
      let hpExpr ← mkDecideProof q((mahlerPrec $pExpr : Int) ≤ ($sExpr).prec)
      let rootExpr ← mkAppM ``SimpleRoot.ofSquare #[pExpr,sExpr,hwExpr,hpExpr]
      let repExpr ← mkAppM ``Field.literalRep #[pExpr,sExpr,hwExpr,hpExpr]
      let tableExpr ← FieldLiteral.signTableExpr pExpr rootExpr table
      let valuesExpr ← FieldLiteral.valuesExpr pExpr rootExpr values
      let coords ← #[a,b].mapM (FieldLiteral.fieldExpr pExpr rootExpr)
      let sourcePExprs := #[q(CertificationInputs.polynomial),q(SquareRoot.polynomial 2)]
      let sourceSExprs := #[q(CertificationInputs.square),(← FieldLiteral.squareExpr secondS)]
      let sourceValues : Array Expr := #[q(CertificationInputs.realAlgebraic.toReal),q(Real.sqrt 2)]
      let mut identities : Array Expr := #[]
      for i in [:2] do
        let sourceP : Q(ZPoly) := sourcePExprs[i]!
        let sourceS : Q(DyadicSquare) := sourceSExprs[i]!
        let sourcePoly ← mkAppM ``ZPoly.toRatPoly #[sourceP]
        let sourceWitness ← mkDecideProof q(atomWitness $sourceP $sourceS)
        let sourcePrecision ← mkDecideProof q((mahlerPrec $sourceP : Int) ≤ ($sourceS).prec)
        let selected ← if i = 0 then pure q(selectedQuartic) else do
          let real ← mkDecideProof q(($sourceS).meetsRealAxis = true)
          let positive ← Tactic.positiveLowerBound sourceS
          mkAppM ``SquareRoot.selected #[mkNatLit 2,sourceS,sourceWitness,sourcePrecision,real,positive]
        let check ← mkAppM ``CommonPresentation.checkEntry
          #[hwExpr,hpExpr,tableExpr,sourcePoly,sourceS,coords[i]!]
        let goal ← mkFreshExprMVar (← mkEq check q(true))
        let lemmas ← FieldLiteral.evidenceLemmas
        let remaining ← Elab.runTactic' goal.mvarId! (← `(tactic|
          (simp only [CommonPresentation.checkEntry,CommonPresentation.checkDisc,$lemmas,*,Bool.and_eq_true];
           repeat' (any_goals (apply And.intro)); all_goals try (decide +kernel))))
        unless remaining.isEmpty do throwError "source identity replay left goals"
        let checked ← instantiateMVars goal
        let identity ← mkAppM ``CommonPresentation.checkEntry_sound_of_selected
          #[hwExpr,hpExpr,tableExpr,sourcePoly,sourceS,sourceP,sourceWitness,sourcePrecision,
            ← mkEqRefl sourcePoly,sourceValues[i]!,selected,coords[i]!,checked]
        identities := identities.push identity
      let realValues ← withLocalDeclD `i q(Fin 2) fun i => do
        mkLambdaFVars #[i] (← mkAppM ``Field.value #[repExpr,mkApp valuesExpr i])
      let alpha : Q(ℝ) := q(CertificationInputs.realAlgebraic.toReal)
      let beta : Q(ℝ) := q(Real.sqrt 2)
      let originalValues : Q(Fin 2 → ℝ) := q(fun i => if i.val = 0 then $alpha else $beta)
      let equalityGoal ← withLocalDeclD `i q(Fin 2) fun i => do
        mkForallFVars #[i] (← mkEq (mkApp realValues i) (mkApp originalValues i))
      let equality ← FieldLiteral.proveFinCases equalityGoal identities
      let equality ← mkAppM ``funext #[equality]
      let statement ← withLocalDeclD `values q(Fin 2 → ℝ) fun vals => do
        let body ← withLocalDeclD `x q(ℝ) fun x => do
          let body ← mkAppM ``RealFormula.QF.toProp
            #[q(Hex.RCF.FiniteFieldCells.formula),← mkAppM ``RealFormula.append #[vals,x]]
          mkForallFVars #[x] body
        mkLambdaFVars #[vals] body
      let geometry := mkConst ``Hex.RCF.FiniteFieldCells.universal
      unless ← isDefEq (← inferType geometry) (mkApp statement realValues) do
        throwError "retained cell proof belongs to different independently reconstructed coordinates"
      let transport ← mkAppM ``congrArg #[statement,equality]
      let specialized ← mkAppM ``Eq.mp #[transport,geometry]
      let proof ← withLocalDeclD `x q(ℝ) fun x => do
        let meaning ← mkAppM ``Hex.RCF.FiniteFieldCells.meaning #[alpha,beta,x]
        let body ← mkAppM ``Iff.mp #[meaning,mkApp specialized x]
        mkLambdaFVars #[x] body
      let target : Q(Prop) := q(∀ x : ℝ,
        x^2-($alpha+$beta)*x+$alpha*$beta<0 → 1<x ∧ x<2)
      let proof ← Hex.RCF.checkProof `OcticSource.original target proof
      addDecl (.thmDecl {
        name := `Hex.RCF.FiniteFieldSource.original
        levelParams := []
        type := target
        value := proof })
      logInfo m!"ORIGINAL_CAS_GOAL: selected quartic and sqrt(2) authenticated; wrong conjugate rejected"
    else throwError "common root precision failed"
  else throwError "common root witness failed"
#print axioms Hex.RCF.FiniteFieldSource.original
