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

private meta def proveNamedRoot (source : Reify.Source) : MetaM Expr := do
  unless source.coefficients.size == 1 do
    throwError "rcf: this algebraic-coefficient path needs one coefficient"
  checkGuards source
  let isSquare ← same source.coefficients[0]! q(Real.sqrt 2)
  let isCube ← same source.coefficients[0]! q((2 : ℝ) ^ (1 / 3 : ℝ))
  unless isSquare || isCube do
    throwError "rcf: this coefficient is not supported by the selected-root adapter"
  let formula ← FieldRuntime.evalFormula 1 source.formula
  let (quantifier, qf) ← match formula with
    | .quant q (.matrix qf) => pure (q, qf)
    | _ => throwError "rcf: expected one real quantifier over a matrix"
  let (_, _, coefficient) ← FieldRuntime.coefficient source.coefficients[0]!
  let a := coefficient.toAlgebraic
  let s := a.rep.1.square
  let expected := if isSquare then SquareTwo.polynomial else CubeTwo.polynomial
  unless a.p == expected do
    throwError "rcf: coefficient has a different defining polynomial"
  if hw : atomWitness a.p s then
    if hp : (mahlerPrec a.p : Int) ≤ s.prec then
      let value : PolyQuot a.p (SimpleRoot.ofSquare a.p s hw hp) :=
        PolyQuot.ofSquare a.p s (DensePoly.ofList [0, 1]) hw hp
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
        (if isSquare then ``SquareTwo.coordinate else ``CubeTwo.coordinate)
        #[sExpr, hwExpr, hpExpr]
      let valueZero := mkApp valuesExpr q((0 : Fin 1))
      let hvalue ← mkEqRefl valueZero
      unless ← isDefEq (← inferType hvalue) (← mkAppM ``Eq #[valueZero, coordinate]) do
        throwError "rcf: literal coefficient differs from its selected-root coordinate"
      let eqVal ← if isSquare then
          let hpositive ← positiveLowerBound sExpr
          mkAppM ``SquareTwo.valuation
            #[sExpr, hwExpr, hpExpr, hreal, hpositive, valuesExpr, hvalue]
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
  if source.coefficients.size != 1 then return .declined
  let isSquare ← same source.coefficients[0]! q(Real.sqrt 2)
  let isCube ← same source.coefficients[0]! q((2 : ℝ) ^ (1 / 3 : ℝ))
  if !(isSquare || isCube) then return .declined
  return .proved (← proveNamedRoot source)

end Hex.RCF.RealCoefficients.Tactic
