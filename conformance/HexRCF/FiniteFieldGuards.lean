/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.FieldCells
public meta import HexRCF.RealCoefficients.FieldCells
public meta import HexRCF.RealCoefficients.FieldRuntime
public meta import HexRCF.RealCoefficients.FieldLiteral
public meta import HexRCF.ProofEvidence
public meta import Lean.Elab.Command
public section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option debug.skipKernelTC false
set_option Elab.async false
open Hex Hex.RCF Hex.RCF.RealCoefficients Lean Meta Qq
@[expose] def Hex.RCF.FiniteFieldGuards.formula : RealFormula.QF 2 :=
  let difference : RealFormula.Poly 2 := MvPoly.X 1 - MvPoly.X 0
  .atom ⟨difference * difference, .ge⟩

@[expose] def Hex.RCF.FiniteFieldGuards.rootFormula : RealFormula.QF 2 :=
  let difference : RealFormula.Poly 2 := MvPoly.X 1 - MvPoly.X 0
  .atom ⟨difference * difference, .eq⟩

run_meta do
  let (_,_,quadratic) ← FieldRuntime.coefficient q(Real.sqrt 2)
  let p : ZPoly := DensePoly.ofList [6,0,-5,0,1]
  let s : DyadicSquare := ⟨quadratic.approx 256,0,128⟩
  if hw : atomWitness p s then do
    if hp : (mahlerPrec p : Int) ≤ s.prec then do
      let root := SimpleRoot.ofSquare p s hw hp
      let z : PolyQuot p root := PolyQuot.ofSquare p s (DensePoly.ofList [-2,0,1]) hw hp
      if z == 0 then throwError "expected nonzero stored coordinate"
      let table ← match FieldBuild.buildTable p s hw hp [z] with
        | none => throwError "selected-root sign evidence failed"
        | some result => pure result
      unless table.lookup? z == some 0 do throwError "selected coordinate was not exactly zero"
      if FieldTransport.leadingCheck table (DensePoly.C z) then
        throwError "semantically zero leading coefficient accepted"
      let pExpr : Q(ZPoly) ← FieldLiteral.zpolyExpr p
      let sExpr : Q(DyadicSquare) ← FieldLiteral.squareExpr s
      let hwExpr ← mkDecideProof q(atomWitness $pExpr $sExpr)
      let hpExpr ← mkDecideProof q((mahlerPrec $pExpr : Int) ≤ ($sExpr).prec)
      let rootExpr ← mkAppM ``SimpleRoot.ofSquare #[pExpr,sExpr,hwExpr,hpExpr]
      let tableExpr ← FieldLiteral.signTableExpr pExpr rootExpr table
      let zExpr ← FieldLiteral.fieldExpr pExpr rootExpr z
      let zeroExpr ← FieldLiteral.fieldExpr pExpr rootExpr (0 : PolyQuot p root)
      let nonzero ← mkDecideProof (← mkAppM ``Ne #[zExpr,zeroExpr])
      let hit ← mkAppM ``LiteralSign.Table.lookup? #[tableExpr,zExpr]
      let recorded ← mkDecideProof (← mkEq hit (← mkAppM ``Option.some #[mkIntLit 0]))
      let checkedExpr ← mkAppM ``Field.checkSignTable #[pExpr,sExpr,hwExpr,hpExpr,tableExpr]
      let goal ← mkFreshExprMVar (← mkEq checkedExpr q(true))
      let lemmas ← FieldLiteral.evidenceLemmas
      let remaining ← Elab.runTactic' goal.mvarId! (← `(tactic|
        (simp only [$lemmas,*,Bool.and_eq_true];
         repeat' (any_goals (apply And.intro)); all_goals try (decide +kernel))))
      unless remaining.isEmpty do throwError "selected sign table did not replay"
      let checked ← instantiateMVars goal
      let valueZero ← mkAppM ``Field.checkSignTable_lookup
        #[pExpr,sExpr,hwExpr,hpExpr,tableExpr,checked,zExpr,mkIntLit 0,recorded]
      let negative ← mkAppM ``FieldTransport.leadingCheck #[tableExpr,← mkAppM ``DensePoly.C #[zExpr]]
      let refused ← mkDecideProof (← mkEq negative q(false))
      for (label,proof) in #[(`Hex.RCF.FiniteFieldGuards.nonzero,nonzero),(`Hex.RCF.FiniteFieldGuards.zeroSign,valueZero),
          (`Hex.RCF.FiniteFieldGuards.leadingRefused,refused)] do
        let proof ← Hex.RCF.checkProof label (← inferType proof) proof
        let type ← inferType proof
        addDecl (.thmDecl {name := label,levelParams := [],type,value := proof})
      let generator : PolyQuot p root :=
        PolyQuot.ofSquare p s (DensePoly.ofList [0,1]) hw hp
      let values : Fin 1 → PolyQuot p root := fun _ => generator
      let formula := Hex.RCF.FiniteFieldGuards.formula
      let query := RepresentationSpecialize.polynomial values
      let head : DensePoly (PolyQuot p root) := DensePoly.ofList [-generator,1]
      let prepared ← match Sturm.prepare Sturm.orderSign (ZPoly.toRatPoly p)
          (.finite (s.re - s.radiusHi).toRat) (.finite (s.re + s.radiusHi).toRat) with
        | none => throwError "reducible rational sign domain failed"
        | some result => pure result
      let sign := fun value : PolyQuot p root => Sturm.queryPrepared prepared value.coeffs
      -- Pseudoremainder production needs no inverse or field instance here.
      -- Leaving the positive normalization factor at one is an exact backend choice.
      let squarefree := SignedRemainderChain.build sign SignedRemainderChain.normalizeId head 1
      let make (test : DensePoly (PolyQuot p root)) lower upper :=
        TarskiCertificate.fromChains sign (EndpointSigns.ofSign sign) () head test lower upper
          squarefree (SignedRemainderChain.build sign SignedRemainderChain.normalizeId head test)
      let interval : DyadicInterval := ⟨Dyadic.ofInt 1,Dyadic.ofInt 2,by decide⟩
      let isolation : IsolationReplay (PolyQuot p root) Unit := {
        isolations := ⟨#[interval]⟩
        total := make 1 .negInf .posInf
        counts := Vector.ofFn fun _ => make 1
          (.finite (PolyQuot.ofRat interval.lower.toRat))
          (.finite (PolyQuot.ofRat interval.upper.toRat)) }
      let rows : FieldRootSigns.Table (PolyQuot p root) Unit 2
          isolation.isolations.intervals.size := ⟨formula.polys.map fun atom =>
        ⟨atom,Vector.ofFn fun _ => make (query atom)
          (.finite (PolyQuot.ofRat interval.lower.toRat))
          (.finite (PolyQuot.ofRat interval.upper.toRat))⟩⟩
      let radical : RadicalCert (PolyQuot p root) Unit := ⟨(),head,head,1,0⟩
      let signs ← match FieldBuild.buildTable p s hw hp
          (FieldCells.keys query formula head isolation rows ++ [z]) with
        | none => throwError "reducible cell sign table failed"
        | some result => pure result
      unless FieldCells.check signs () query formula radical isolation rows do
        throwError "valid complete cells over a noninjective presentation rejected"
      let formulaExpr := q(Hex.RCF.FiniteFieldGuards.formula)
      let valuesExpr ← FieldLiteral.valuesExpr pExpr rootExpr values
      let data : FieldBuild.Result p s hw hp Unit 2 := ⟨radical,isolation,rows,signs⟩
      let dataExpr ← FieldLiteral.resultExpr pExpr rootExpr formulaExpr formula data
      let radicalExpr ← mkAppM ``FieldBuild.Result.radical #[dataExpr]
      let isoExpr ← mkAppM ``FieldBuild.Result.isolation #[dataExpr]
      let rowsExpr ← mkAppM ``FieldBuild.Result.rootSigns #[dataExpr]
      let signsExpr ← mkAppM ``FieldBuild.Result.signs #[dataExpr]
      let queryExpr ← mkAppM ``RepresentationSpecialize.polynomial #[valuesExpr]
      let checkExpr ← mkAppM ``FieldCells.check #[signsExpr,q(()),queryExpr,formulaExpr,
        radicalExpr,isoExpr,rowsExpr]
      let candidate ← mkFreshExprMVar (← mkEq checkExpr q(true))
      let remaining ← Elab.runTactic' candidate.mvarId! (← `(tactic|
        (simp only [FieldCells.check,FieldIsolation.check,FieldQuery.check,FieldQuery.covered,
          FieldRootSigns.Table.checkTransport,FieldRootSigns.Table.checkRows,
          FieldTransport.leadingCheck,$lemmas,*,Bool.and_eq_true];
         repeat' (any_goals (apply And.intro)); all_goals try (decide +kernel))))
      unless remaining.isEmpty do throwError "complete reducible cell replay left goals"
      let accepted ← instantiateMVars candidate
      let header ← mkAppM ``FieldCells.signs_checked #[signsExpr,q(()),queryExpr,formulaExpr,
        radicalExpr,isoExpr,rowsExpr,accepted]
      let specialization ← mkAppM ``FieldCells.specialize #[signsExpr,header,valuesExpr]
      let valuation ← withLocalDeclD `x q(ℝ) fun x => do
        let realValues ← withLocalDeclD `i q(Fin 1) fun i => do
          mkLambdaFVars #[i] (← mkAppM ``Field.value
            #[← mkAppM ``Field.literalRep #[pExpr,sExpr,hwExpr,hpExpr],mkApp valuesExpr i])
        mkLambdaFVars #[x] (← mkAppM ``RealFormula.append #[realValues,x])
      let equivalence ← mkAppM ``FieldCells.forall_formula #[signsExpr,q(()),queryExpr,formulaExpr,
        radicalExpr,isoExpr,rowsExpr,valuation,specialization,accepted]
      let verdictType := (← inferType equivalence).getAppArgs[0]!
      let verdict ← mkFreshExprMVar verdictType
      let remaining ← Elab.runTactic' verdict.mvarId! (← `(tactic| decide +kernel))
      unless remaining.isEmpty do throwError "reducible universal fold left goals"
      let proof ← mkAppM ``Iff.mp #[equivalence,← instantiateMVars verdict]
      let expected ← withLocalDeclD `x q(ℝ) fun x => do
        mkForallFVars #[x] (← mkAppM ``RealFormula.QF.toProp #[formulaExpr,mkApp valuation x])
      let proof ← Hex.RCF.checkProof `FiniteFieldGuards.accepted expected proof
      addDecl (.thmDecl {
        name := `Hex.RCF.FiniteFieldGuards.accepted
        levelParams := []
        type := expected
        value := proof })
      for (label,method,isExists) in #[
          (`Hex.RCF.FiniteFieldGuards.existsRoot,``FieldCells.exists_formula,true),
          (`Hex.RCF.FiniteFieldGuards.falseUniversal,``FieldCells.forall_formula,false)] do
        let rootFormula := q(Hex.RCF.FiniteFieldGuards.rootFormula)
        let equivalence ← mkAppM method #[signsExpr,q(()),queryExpr,rootFormula,
          radicalExpr,isoExpr,rowsExpr,valuation,specialization,accepted]
        let folded := (← inferType equivalence).getAppArgs[0]!
        let premise ← if isExists then pure folded else mkAppM ``Not #[folded]
        let goal ← mkFreshExprMVar premise
        let remaining ← Elab.runTactic' goal.mvarId! (← `(tactic| decide +kernel))
        unless remaining.isEmpty do throwError "reducible quantifier verdict left goals"
        let verdict ← instantiateMVars goal
        let proof ← if isExists then mkAppM ``Iff.mp #[equivalence,verdict] else
          mkAppM ``Iff.mp #[← mkAppM ``not_congr #[equivalence],verdict]
        let statement ← withLocalDeclD `x q(ℝ) fun x => do
          let body ← mkAppM ``RealFormula.QF.toProp #[rootFormula,mkApp valuation x]
          if isExists then mkAppM ``Exists #[← mkLambdaFVars #[x] body]
          else mkForallFVars #[x] body
        let expected ← if isExists then pure statement else mkAppM ``Not #[statement]
        let proof ← Hex.RCF.checkProof label expected proof
        addDecl (.thmDecl {name := label,levelParams := [],type := expected,value := proof})
      logInfo "REDUCIBLE_ACCEPTED: complete nonlinear universal replay without a field instance"
      logInfo "REDUCIBLE_PRESENTATION: nonzero coordinate has checked zero sign; semantic leading guard rejects"
    else throwError "reducible root precision failed"
  else throwError "reducible root witness failed"
#print axioms Hex.RCF.FiniteFieldGuards.zeroSign

#print axioms Hex.RCF.FiniteFieldGuards.accepted
#print axioms Hex.RCF.FiniteFieldGuards.existsRoot
#print axioms Hex.RCF.FiniteFieldGuards.falseUniversal
