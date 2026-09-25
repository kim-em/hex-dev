/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRCF.Tactic
public meta import HexRCF.RealCoefficients.FieldRuntime
public meta import HexRCF.RealCoefficients.SquareTwo
public meta import HexRCF.RealCoefficients.CubeTwo

public meta section

/-! Checked real-coefficient handler for the existing `rcf` tactic. -/

namespace Hex.RCF.RealCoefficients.Tactic

open Hex Lean Meta Qq

private meta def same (left right : Expr) : MetaM Bool := do
  let saved ← saveState
  let result ← isDefEq left right
  saved.restore
  return result

private meta def positiveLowerBound (s : Q(DyadicSquare)) : MetaM Expr := do
  let goal : Q(Prop) := q(0 < ((($s).re - ($s).radiusHi).toRat : ℝ))
  let proof ← mkFreshExprMVar goal
  let remaining ← Lean.Elab.runTactic' proof.mvarId! (← `(tactic| norm_num; decide))
  unless remaining.isEmpty do
    throwError "rcf: selected square has no checked positive lower bound"
  return ← instantiateMVars proof

private meta def checkGuards (source : Reify.Source) : MetaM Unit := do
  for divisor in source.divisors do
    let divisor : Q(ℝ) := divisor
    let goal : Q(Prop) := q($divisor ≠ 0)
    let proof ← mkFreshExprMVar goal
    let remaining ← Lean.Elab.runTactic' proof.mvarId! (← `(tactic| norm_num))
    unless remaining.isEmpty do
      throwError "rcf: could not prove a closed divisor nonzero"
    check (← instantiateMVars proof)

private meta def selectedArgs? (source : Reify.Source) :
    MetaM (Option (Array Expr × Option Expr)) := do
  if source.coefficients.size != 1 then return none
  let coefficient := source.coefficients[0]!
  unless coefficient.isAppOfArity ``RealAlgebraicNumber.toReal 1 do return none
  let selected ← withTransparency .reducible (whnf coefficient.appArg!)
  if selected.isAppOfArity ``Selected.real 10 then
    return some (selected.getAppArgs, none)
  if selected.isAppOfArity ``Selected.field 11 then
    let args := selected.getAppArgs
    return some (args.extract 0 10, some args[10]!)
  return none

private meta def proveSelected (source : Reify.Source) (args : Array Expr)
    (fieldValue? : Option Expr) : MetaM Expr := do
  checkGuards source
  let p ← FieldRuntime.evalZPoly args[0]!
  let s ← FieldRuntime.evalSquare args[1]!
  let formula ← FieldRuntime.evalFormula 1 source.formula
  let (quantifier, qf) ← match formula with
    | .quant q (.matrix qf) => pure (q, qf)
    | _ => throwError "rcf: expected one real quantifier over a matrix"
  let pExpr : Q(ZPoly) ← FieldLiteral.zpolyExpr p
  let sExpr : Q(DyadicSquare) ← FieldLiteral.squareExpr s
  let hwExpr ← mkDecideProof (q(atomWitness $pExpr $sExpr) : Q(Prop))
  let hpExpr ← mkDecideProof
    (q((mahlerPrec $pExpr : Int) ≤ ($sExpr).prec) : Q(Prop))
  let rootExpr ← mkAppM ``SimpleRoot.ofSquare #[pExpr, sExpr, hwExpr, hpExpr]
  if hw : atomWitness p s then
    if hp : (mahlerPrec p : Int) ≤ s.prec then
      let f ← match fieldValue? with
        | some v => FieldRuntime.evalRatPoly (← mkAppM ``PolyQuot.coeffs #[v])
        | none => pure (DensePoly.ofList [0, 1])
      let value : PolyQuot p (SimpleRoot.ofSquare p s hw hp) :=
        PolyQuot.ofSquare p s f hw hp
      let valuesExpr ← FieldLiteral.valuesExpr pExpr rootExpr (fun _ : Fin 1 => value)
      let formulaWhnf ← whnf source.formula
      let matrixExpr ← whnf formulaWhnf.getAppArgs.back!
      let qfExpr := matrixExpr.getAppArgs.back!
      let checkedIrred := args[7]!
      let instType ← mkAppM ``ZPoly.CheckedIrreducible #[pExpr]
      let proof ← if hi : ZPoly.isIrreducible p = true then
          if hd : 0 < p.natDegree then
            letI : p.CheckedIrreducible := ⟨hi, hd⟩
            withLocalDecl `inst .instImplicit instType fun inst => do
              let result ← FieldLiteral.prove pExpr rootExpr valuesExpr qfExpr
                (fun _ : Fin 1 => value) qf quantifier
              pure (mkApp (← mkLambdaFVars #[inst] result) checkedIrred)
          else throwError "rcf: selected polynomial has zero degree"
        else throwError "rcf: selected polynomial is not irreducible"
      let valueZero := mkApp valuesExpr q((0 : Fin 1))
      let fExpr ← FieldLiteral.ratPolyExpr f
      let coordinate ← mkAppM ``PolyQuot.ofSquare
        #[pExpr, sExpr, fExpr, hwExpr, hpExpr]
      let hvalue ← mkEqRefl valueZero
      unless ← isDefEq (← inferType hvalue) (← mkAppM ``Eq #[valueZero, coordinate]) do
        throwError "rcf: literal generator coordinate differs from its selected root"
      let hreal ← mkDecideProof (q(($sExpr).meetsRealAxis = true) : Q(Prop))
      let eqVal ← match fieldValue? with
        | none => do
          mkAppM ``Selected.valuation
            #[pExpr, sExpr, hwExpr, hpExpr, args[4]!, args[5]!, args[6]!,
              checkedIrred, args[8]!, hreal, valuesExpr, hvalue]
        | some v => do
          let coeffs ← mkAppM ``PolyQuot.coeffs #[v]
          let goal ← mkAppM ``Eq #[coeffs, fExpr]
          let hcoeffMVar ← mkFreshExprMVar goal
          let remaining ← Lean.Elab.runTactic' hcoeffMVar.mvarId!
            (← `(tactic| decide +kernel))
          unless remaining.isEmpty do
            throwError "rcf: field coordinate coefficients differ from their literal encoding"
          let hcoeff ← instantiateMVars hcoeffMVar
          mkAppM ``Selected.field_valuation
            #[pExpr, sExpr, hwExpr, hpExpr, args[4]!, args[5]!, args[6]!,
              checkedIrred, args[8]!, hreal, v, fExpr, hcoeff, valuesExpr, hvalue]
      let congr ← withLocalDeclD `ρ (← inferType source.valuation) fun ρ => do
        let body ← mkAppM ``Hex.RealFormula.Prenex.toProp #[source.formula, ρ]
        mkAppM ``congrArg #[← mkLambdaFVars #[ρ] body, eqVal]
      let specialized ← mkAppM ``Eq.mp #[congr, proof]
      let final ← mkAppM ``Iff.mp #[source.proof, specialized]
      return final
    else throwError "rcf: selected square has insufficient precision"
  else throwError "rcf: selected square failed its root witness"

private meta def proveNamedRoot (source : Reify.Source) : MetaM Expr := do
  unless source.coefficients.size == 1 do
    throwError "rcf: this algebraic-coefficient path needs one coefficient"
  checkGuards source
  let isSquare ← same source.coefficients[0]! q(Real.sqrt 2)
  let isCube ← same source.coefficients[0]! q((2 : ℝ) ^ (1 / 3 : ℝ))
  let isHexCube ← same source.coefficients[0]! q(CubeTwo.realAlgebraic.toReal)
  let isFieldCube ← same source.coefficients[0]! q(CubeTwo.shifted.toReal)
  unless isSquare || isCube || isHexCube || isFieldCube do
    throwError "rcf: this coefficient is not supported by the selected-root adapter"
  let formula ← FieldRuntime.evalFormula 1 source.formula
  let (quantifier, qf) ← match formula with
    | .quant q (.matrix qf) => pure (q, qf)
    | _ => throwError "rcf: expected one real quantifier over a matrix"
  let (_, _, coefficient) ← FieldRuntime.coefficient
    (if isFieldCube then q(CubeTwo.realAlgebraic.toReal) else source.coefficients[0]!)
  let a := coefficient.toAlgebraic
  let s := a.rep.1.square
  let expected := if isSquare then SquareTwo.polynomial else CubeTwo.polynomial
  unless a.p == expected do
    throwError "rcf: coefficient has a different defining polynomial"
  if hw : atomWitness a.p s then
    if hp : (mahlerPrec a.p : Int) ≤ s.prec then
      let generator : PolyQuot a.p (SimpleRoot.ofSquare a.p s hw hp) :=
        PolyQuot.ofSquare a.p s (DensePoly.ofList [0, 1]) hw hp
      let value := if isFieldCube then 1 + generator else generator
      let pExpr : Q(ZPoly) ← FieldLiteral.zpolyExpr a.p
      let sExpr : Q(DyadicSquare) ← FieldLiteral.squareExpr s
      let hwExpr ← mkDecideProof (q(atomWitness $pExpr $sExpr) : Q(Prop))
      let hpExpr ← mkDecideProof
        (q((mahlerPrec $pExpr : Int) ≤ ($sExpr).prec) : Q(Prop))
      let rootExpr ← mkAppM ``SimpleRoot.ofSquare #[pExpr, sExpr, hwExpr, hpExpr]
      let valuesExpr ← FieldLiteral.valuesExpr pExpr rootExpr (fun _ : Fin 1 => value)
      let formulaWhnf ← whnf source.formula
      let matrixExpr ← whnf formulaWhnf.getAppArgs.back!
      let qfExpr := matrixExpr.getAppArgs.back!
      let witness ← mkAppM ``ZPoly.IrredWitness.eisenstein #[mkNatLit 2, mkIntLit 0]
      let irred ← mkDecideProof
        (q(ZPoly.checkIrredWitness $pExpr (.eisenstein 2 0) = true) : Q(Prop))
      let degree ← mkDecideProof (q(0 < ($pExpr).natDegree) : Q(Prop))
      let irreducible ← mkAppM ``Field.checkedIrreducible
        #[pExpr, witness, irred, degree]
      let instType ← mkAppM ``ZPoly.CheckedIrreducible #[pExpr]
      let proof ← withLocalDecl `inst .instImplicit instType fun inst => do
        let result ← FieldLiteral.prove pExpr rootExpr valuesExpr qfExpr
          (fun _ : Fin 1 => value) qf quantifier
        return mkApp (← mkLambdaFVars #[inst] result) irreducible
      let hreal ← mkDecideProof (q(($sExpr).meetsRealAxis = true) : Q(Prop))
      let coordinate ← mkAppM
        (if isSquare then ``SquareTwo.coordinate else if isFieldCube then
          ``CubeTwo.shiftedCoordinate else ``CubeTwo.coordinate)
        #[sExpr, hwExpr, hpExpr]
      let valueZero := mkApp valuesExpr q((0 : Fin 1))
      let hvalue ← if isFieldCube then
          let left ← mkAppM ``PolyQuot.coeffs #[valueZero]
          let right ← mkAppM ``PolyQuot.coeffs #[coordinate]
          let coeffs ← mkDecideProof (← mkAppM ``Eq #[left, right])
          mkAppM ``PolyQuot.ext #[coeffs]
        else do
          let coordinateProof ← mkEqRefl valueZero
          unless ← isDefEq (← inferType coordinateProof) (← mkAppM ``Eq #[valueZero, coordinate]) do
            throwError "rcf: literal coefficient differs from its selected-root coordinate"
          pure coordinateProof
      let eqVal ← if isSquare then
          let hpositive ← positiveLowerBound sExpr
          mkAppM ``SquareTwo.valuation
            #[sExpr, hwExpr, hpExpr, hreal, hpositive, valuesExpr, hvalue]
        else if isFieldCube then
          mkAppM ``CubeTwo.valuationShifted
            #[sExpr, hwExpr, hpExpr, hreal, valuesExpr, hvalue]
        else if isHexCube then
          mkAppM ``CubeTwo.valuationAlgebraic
            #[sExpr, hwExpr, hpExpr, hreal, valuesExpr, hvalue]
        else
          mkAppM ``CubeTwo.valuation
            #[sExpr, hwExpr, hpExpr, hreal, valuesExpr, hvalue]
      let congr ← withLocalDeclD `ρ (← inferType source.valuation) fun ρ => do
        let body ← mkAppM ``Hex.RealFormula.Prenex.toProp #[source.formula, ρ]
        mkAppM ``congrArg #[← mkLambdaFVars #[ρ] body, eqVal]
      let specialized ← mkAppM ``Eq.mp #[congr, proof]
      let final ← mkAppM ``Iff.mp #[source.proof, specialized]
      return final
    else throwError "rcf: selected square has insufficient precision"
  else throwError "rcf: selected square failed its root witness"

@[rcf_handler] meta def handle : Handler := fun target => do
  let .ok source ← Reify.prepare target | return .declined
  if let some (args, fieldValue?) ← selectedArgs? source then
    return .proved (← proveSelected source args fieldValue?)
  if source.coefficients.size != 1 then return .declined
  let isSquare ← same source.coefficients[0]! q(Real.sqrt 2)
  let isCube ← same source.coefficients[0]! q((2 : ℝ) ^ (1 / 3 : ℝ))
  let isHexCube ← same source.coefficients[0]! q(CubeTwo.realAlgebraic.toReal)
  let isFieldCube ← same source.coefficients[0]! q(CubeTwo.shifted.toReal)
  if !(isSquare || isCube || isHexCube || isFieldCube) then return .declined
  return .proved (← proveNamedRoot source)

end Hex.RCF.RealCoefficients.Tactic
