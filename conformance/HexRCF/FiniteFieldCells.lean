/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.FieldCells
public meta import HexRCF.RealCoefficients.FieldCells
public import HexRCF.CertificationInputs
public meta import HexRCF.CertificationInputs
public meta import HexRCF.RealCoefficients.FieldRuntime
public meta import HexRCF.RealCoefficients.FieldLiteral
public meta import HexRCF.ProofEvidence
public meta import Lean.Elab.Command
public section
set_option maxRecDepth 32768
set_option maxHeartbeats 40000000
set_option debug.skipKernelTC false
set_option Elab.async false
open Hex Hex.RCF Hex.RCF.RealCoefficients Lean Meta Qq

namespace Hex.RCF.FiniteFieldCells
@[expose] def formula : RealFormula.QF 3 :=
  let a : RealFormula.Poly 3 := MvPoly.X 0
  let b : RealFormula.Poly 3 := MvPoly.X 1
  let x : RealFormula.Poly 3 := MvPoly.X 2
  .or (.not (.atom ⟨x*x - (a+b)*x+a*b, .lt⟩))
    (.and (.atom ⟨x - MvPoly.C 1, .gt⟩) (.atom ⟨x - MvPoly.C 2, .lt⟩))
end Hex.RCF.FiniteFieldCells

run_meta do
  let (_,_,quadratic) ← FieldRuntime.coefficient q(Real.sqrt 2)
  let common := QAdjoin.common #[CertificationInputs.realAlgebraic.toAlgebraic, quadratic.toAlgebraic]
  let p := common.generator.p
  let s := common.generator.rep.1.square
  unless p.natDegree == 8 do throwError "expected degree-eight common presentation"
  if hw : atomWitness p s then do
    if hp : (mahlerPrec p : Int) ≤ s.prec then do
      let : ZPoly.CheckedIrreducible p := common.generator.checked
      let root := SimpleRoot.ofSquare p s hw hp
      let a ← match common.entries[0]? with
        | none => throwError "missing quartic coordinate"
        | some entry => pure (PolyQuot.ofSquare p s entry.coeffs hw hp)
      let b ← match common.entries[1]? with
        | none => throwError "missing quadratic coordinate"
        | some entry => pure (PolyQuot.ofSquare p s entry.coeffs hw hp)
      let values : Fin 2 → PolyQuot p root := fun i => if i.val = 0 then a else b
      let query := RepresentationSpecialize.polynomial values
      let formula := Hex.RCF.FiniteFieldCells.formula
      let product := RepresentationCarrier.product (formula.polys.map query)
      let radical ← match RadicalCert.build () product with
        | none => throwError "carrier proposal failed"
        | some result => pure result
      let prepared ← if real : s.meetsRealAxis = true then
          pure (Field.prepareSign p s hw hp real)
        else throwError "common generator was not real"
      let sign := fun value : PolyQuot p root => Sturm.queryPrepared prepared.val value.coeffs
      let isolation ← match FieldBuild.isolateAtWith (Field.literalRep p s hw hp)
          (Field.literalRep_mk p s hw hp) sign () radical.core 16 with
        | none => throwError "four-root isolation proposal failed"
        | some result => pure result
      unless isolation.isolations.intervals.size == 4 do throwError "expected four carrier roots"
      let rows ← match FieldRootSigns.Table.build sign FieldDecision.point () radical.core
          isolation query formula with
        | none => throwError "atom/root query construction failed"
        | some result => pure result
      let keys := FieldCells.keys query formula radical.core isolation rows
      let table ← match FieldBuild.buildTable p s hw hp keys with
        | none => throwError "finite sign table failed"
        | some result => pure result
      unless FieldCells.check table () query formula radical isolation rows do
        throwError "complete cell replay failed"
      if FieldCells.check table () query formula radical isolation {rows with entries := []} then
        throwError "missing atom/root rows accepted"
      if FieldCells.check {table with entries := []} () query formula radical isolation rows then
        throwError "missing finite signs accepted"
      let badRows := {rows with entries := rows.entries.map fun row =>
        {row with evidence := row.evidence.map fun cert => {cert with value := cert.value+1}}}
      if FieldCells.check table () query formula radical isolation badRows then
        throwError "corrupted root signs accepted"
      let extraRows := {rows with entries := rows.entries ++ badRows.entries}
      if FieldCells.check table () query formula radical isolation extraRows then
        throwError "extra root rows accepted"
      if extraRows.checkTransport table () radical.core isolation.isolations.intervals.toVector
          query (.and formula formula) then
        throwError "corrupt repeated-atom rows accepted"
      let verdict := OptionFold.allArray (Cell.all isolation.isolations.intervals.size)
        (fun cell => formula.evalSigns (Decision.cellSign (FieldQuery.cached table)
          FieldDecision.point query isolation (rows.value isolation.total) cell))
      unless verdict == some true do throwError "expected true strict universal verdict"
      logInfo m!"OCTIC_CELLS_PRODUCED roots=4; atoms={formula.polys.length}; signs={table.entries.length}"
      let pExpr : Q(ZPoly) ← FieldLiteral.zpolyExpr p
      let sExpr : Q(DyadicSquare) ← FieldLiteral.squareExpr s
      let hwExpr ← mkDecideProof q(atomWitness $pExpr $sExpr)
      let hpExpr ← mkDecideProof q((mahlerPrec $pExpr : Int) ≤ ($sExpr).prec)
      let rootExpr ← mkAppM ``SimpleRoot.ofSquare #[pExpr,sExpr,hwExpr,hpExpr]
      let valuesExpr ← FieldLiteral.valuesExpr pExpr rootExpr values
      let formulaExpr := q(Hex.RCF.FiniteFieldCells.formula)
      let data : FieldBuild.Result p s hw hp Unit 3 := ⟨radical,isolation,rows,table⟩
      let dataExpr ← FieldLiteral.resultExpr pExpr rootExpr formulaExpr formula data
      let radicalExpr ← mkAppM ``FieldBuild.Result.radical #[dataExpr]
      let isoExpr ← mkAppM ``FieldBuild.Result.isolation #[dataExpr]
      let rowsExpr ← mkAppM ``FieldBuild.Result.rootSigns #[dataExpr]
      let signsExpr ← mkAppM ``FieldBuild.Result.signs #[dataExpr]
      let queryExpr ← mkAppM ``RepresentationSpecialize.polynomial #[valuesExpr]
      let checkExpr ← mkAppM ``FieldCells.check #[signsExpr,q(()),queryExpr,formulaExpr,
        radicalExpr,isoExpr,rowsExpr]
      let candidate ← mkFreshExprMVar (← mkEq checkExpr q(true))
      let lemmas ← FieldLiteral.evidenceLemmas
      let remaining ← Elab.runTactic' candidate.mvarId! (← `(tactic|
        (simp only [FieldCells.check,FieldCells.checkWith,QueryCells.check,QueryCells.checkRows,IsolationTransport.check,FieldIsolation.check,FieldQuery.check,FieldQuery.covered,
          FieldRootSigns.Table.checkTransport,FieldRootSigns.Table.checkRows,FieldRootSigns.Table.checkWith,
          FieldTransport.leadingCheck,$lemmas,*,Bool.and_eq_true];
         repeat' (any_goals (apply And.intro)); all_goals try (decide +kernel))))
      unless remaining.isEmpty do
        for goal in remaining do goal.withContext do logInfo m!"CELL_REPLAY_REMAINING: {(← ppExpr (← goal.getType))}"
        throwError "cell replay left {remaining.length} goals"
      let accepted ← instantiateMVars candidate
      let header ← mkAppM ``FieldCells.signs_checked #[signsExpr,q(()),queryExpr,formulaExpr,
        radicalExpr,isoExpr,rowsExpr,accepted]
      let specialization ← mkAppM ``FieldCells.specialize #[signsExpr,header,valuesExpr]
      let valuation ← withLocalDeclD `x q(ℝ) fun x => do
        let k ← inferType (← FieldLiteral.fieldExpr pExpr rootExpr a)
        let realValues ← withLocalDeclD `i q(Fin 2) fun i => do
          let value ← mkAppM ``Field.value #[← mkAppM ``Field.literalRep #[pExpr,sExpr,hwExpr,hpExpr],
            mkApp valuesExpr i]
          mkLambdaFVars #[i] value
        let v ← mkAppM ``RealFormula.append #[realValues,x]
        let _ := k
        mkLambdaFVars #[x] v
      let equivalence ← mkAppM ``FieldCells.forall_formula #[signsExpr,q(()),queryExpr,formulaExpr,
        radicalExpr,isoExpr,rowsExpr,valuation,specialization,accepted]
      let verdictType := (← inferType equivalence).getAppArgs[0]!
      let verdictGoal ← mkFreshExprMVar verdictType
      let remaining ← Elab.runTactic' verdictGoal.mvarId! (← `(tactic| decide +kernel))
      unless remaining.isEmpty do throwError "strict fold proof left goals"
      let verdictProof ← instantiateMVars verdictGoal
      let proof ← mkAppM ``Iff.mp #[equivalence,verdictProof]
      let expected ← withLocalDeclD `x q(ℝ) fun x => do
        let body ← mkAppM ``RealFormula.QF.toProp #[formulaExpr,mkApp valuation x]
        mkForallFVars #[x] body
      let proof ← Hex.RCF.checkProof `OcticCells.checked expected proof
      let proofType ← inferType proof
      addDecl (.thmDecl {
        name := `Hex.RCF.FiniteFieldCells.universal
        levelParams := []
        type := proofType
        value := proof })
      logInfo m!"FINITE_FIELD_CELLS: ordinary-kernel universal proof checked"
    else throwError "common root precision failed"
  else throwError "common root witness failed"
#print axioms Hex.RCF.FiniteFieldCells.universal
