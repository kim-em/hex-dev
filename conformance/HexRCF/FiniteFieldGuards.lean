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
      logInfo "REDUCIBLE_PRESENTATION: nonzero coordinate has checked zero sign; semantic leading guard rejects"
    else throwError "reducible root precision failed"
  else throwError "reducible root witness failed"
#print axioms Hex.RCF.FiniteFieldGuards.zeroSign
