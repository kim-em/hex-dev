/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealClosureTheory.TowerModel
public meta import HexRCF.RealCoefficients.RootQuote
public meta import HexRCF.RealCoefficients.Interpret
public meta import HexRCF.RealCoefficients.Reify
public section

namespace Hex.RCF.RealCoefficients.TowerCompile
open Hex.RealClosure

/-- Interpret the ordinary repeated-product operation without installing a
field instance on the stored carrier. -/
theorem pow_value {registry : BaseContext.Registry} {parent : Tower.Context registry}
    (model : Tower.Model parent ℝ) (a : parent.Value) (n : Nat) :
    model.value (npowRec n a) = model.value a ^ n := by
  induction n with
  | zero => simpa only [npowRec, pow_zero] using model.one
  | succ n ih => rw [npowRec, model.mul, ih, pow_succ]

end Hex.RCF.RealCoefficients.TowerCompile

public meta section

namespace Hex.RCF.RealCoefficients.TowerCompile
open Lean Meta Qq Hex.RealFormula.Reify

/-- A stored expression and an ordinary proof of its original real value.
No compiled proposal is used as proof evidence. -/
structure Term where
  expression : Expr
  proof : Expr

private meta def checked (model source : Expr) (term : Term) : ReifyM Term := do
  let expression ← instantiateMVars term.expression
  if expression.hasFVar || expression.hasMVar || expression.hasLooseBVars then
    abort (.unsupported source "stored coefficient is not closed")
  accountProof expression
  let expression ← Hex.RCF.checkExpr `TowerCompile.value expression
  Meta.check expression
  let target ← mkEq (← mkAppM ``Hex.RealClosure.Tower.Model.value #[model,expression]) source
  accountProof target
  accountProof term.proof
  let proof ← Hex.RCF.checkProof `TowerCompile.identity target term.proof
  return ⟨expression,proof⟩

private meta def operand (proof : Expr) : MetaM Expr := do
  let kind ← whnf (← inferType proof)
  unless kind.isAppOfArity ``Eq 3 do
    throwError "rcf: expected a tower interpretation equation"
  let lhs := kind.getAppArgs[1]!
  unless lhs.getAppFn.isConstOf ``Hex.RealClosure.Tower.Model.value && lhs.isApp do
    throwError "rcf: expected the retained model's interpreted operand"
  return lhs.getAppArgs.back!

private meta def natural (model : Expr) (n : Nat) : ReifyM Term := do
  let proof ← mkAppM ``Hex.RealClosure.Tower.Model.nat #[model,toExpr n]
  return ⟨← operand proof,proof⟩

private meta def rational (model source : Expr) : ReifyM Term := do
  Coefficients.admitRational source
  let sourceQ : Q(ℝ) ← pure source
  let ⟨value,_,_,_⟩ ← liftM <|
    Mathlib.Meta.NormNum.deriveRat sourceQ (_inst := q(inferInstance))
  let a ← natural model value.num.natAbs
  let b ← natural model value.den
  let mut numerator := a.expression
  let mut numeratorProof := a.proof
  if value.num < 0 then
    let mapped ← mkAppM ``Hex.RealClosure.Tower.Model.neg #[model,a.expression]
    numerator ← operand mapped
    let ax : Q(ℝ) ← pure (← whnf (← inferType a.proof)).getAppArgs[2]!
    let av : Q(ℝ) ← mkAppM ``Hex.RealClosure.Tower.Model.value #[model,a.expression]
    let ha : Q($av = $ax) ← pure a.proof
    numeratorProof ← mkEqTrans mapped
      q(congrArg (fun x : ℝ => -x) $ha)
  let mapped ← mkAppM ``Hex.RealClosure.Tower.Model.div #[model,numerator,b.expression]
  let expression ← operand mapped
  let left : Q(ℝ) ← pure (← whnf (← inferType numeratorProof)).getAppArgs[2]!
  let right : Q(ℝ) ← pure (← whnf (← inferType b.proof)).getAppArgs[2]!
  let va : Q(ℝ) ← mkAppM ``Hex.RealClosure.Tower.Model.value #[model,numerator]
  let vb : Q(ℝ) ← mkAppM ``Hex.RealClosure.Tower.Model.value #[model,b.expression]
  let ha : Q($va = $left) ← pure numeratorProof
  let hb : Q($vb = $right) ← pure b.proof
  let mapped ← mkEqTrans mapped q(congrArg₂ (fun x y : ℝ => x / y) $ha $hb)
  let target ← mkEq q($left / $right) source
  let equal ← liftM <| withNewMCtxDepth do
    let candidate ← mkFreshExprMVar target
    let remaining ← Elab.runTactic' candidate.mvarId! (← `(tactic| norm_num))
    unless remaining.isEmpty do throwError "rcf: rational source equality was not proved"
    instantiateMVars candidate
  checked model source ⟨expression,← mkEqTrans mapped equal⟩

/-- Compile closed source arithmetic into the operations of the retained tower.
Leaves are authenticated by exact target checking. Use an enclosing
`RootQuote.runWith` request for failure rollback and aggregate accounting.
Original source divisors must still be independently retained and discharged. -/
private meta partial def compileCore (model : Expr) (leaf : Expr → ReifyM (Option Term))
    (source : Expr) : ReifyM Term := do
  Core.checkSystem "tower coefficient compilation"
  charge .proofNodes 1
  let e := source.consumeMData
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then
    abort (.unsupported source "coefficient must be closed")
  unless ← isDefEq (← inferType e) q(ℝ) do
    abort (.unsupported source "coefficient must have type Real")
  let saved : Meta.SavedState ← liftM (saveState : MetaM Meta.SavedState)
  match ← leaf source with
  | some term => return ← checked model source term
  | none => liftM (saved.restore : MetaM Unit)
  let args := e.getAppArgs
  let op := e.getAppFn.constName?
  if [``HAdd.hAdd,``HSub.hSub,``HMul.hMul,``HDiv.hDiv].any (op == some ·) &&
      args.size == 6 then
    let x : Q(ℝ) ← pure args[4]!
    let y : Q(ℝ) ← pure args[5]!
    let canonical := if op == some ``HAdd.hAdd then q($x + $y)
      else if op == some ``HSub.hSub then q($x - $y)
      else if op == some ``HMul.hMul then q($x * $y) else q($x / $y)
    unless ← isDefEq e canonical do
      abort (.unsupported source "nonstandard real arithmetic instance")
    let a ← compileCore model leaf x
    let b ← compileCore model leaf y
    let va : Q(ℝ) ← mkAppM ``Hex.RealClosure.Tower.Model.value #[model,a.expression]
    let vb : Q(ℝ) ← mkAppM ``Hex.RealClosure.Tower.Model.value #[model,b.expression]
    let ha : Q($va = $x) ← pure a.proof
    let hb : Q($vb = $y) ← pure b.proof
    let (law,congr) := if op == some ``HAdd.hAdd then
        (``Hex.RealClosure.Tower.Model.add,q(congrArg₂ (fun x y : ℝ => x + y) $ha $hb))
      else if op == some ``HSub.hSub then
        (``Hex.RealClosure.Tower.Model.sub,q(congrArg₂ (fun x y : ℝ => x - y) $ha $hb))
      else if op == some ``HMul.hMul then
        (``Hex.RealClosure.Tower.Model.mul,q(congrArg₂ (fun x y : ℝ => x * y) $ha $hb))
      else (``Hex.RealClosure.Tower.Model.div,q(congrArg₂ (fun x y : ℝ => x / y) $ha $hb))
    let mapped ← mkAppM law #[model,a.expression,b.expression]
    let expression ← operand mapped
    return ← checked model source ⟨expression,← mkEqTrans mapped congr⟩
  if [``Neg.neg,``Inv.inv].any (op == some ·) && args.size == 3 then
    let x : Q(ℝ) ← pure args[2]!
    let canonical := if op == some ``Neg.neg then q(-$x) else q($x⁻¹)
    unless ← isDefEq e canonical do
      abort (.unsupported source "nonstandard real unary instance")
    let a ← compileCore model leaf x
    let va : Q(ℝ) ← mkAppM ``Hex.RealClosure.Tower.Model.value #[model,a.expression]
    let ha : Q($va = $x) ← pure a.proof
    let (law,congr) := if op == some ``Neg.neg then
        (``Hex.RealClosure.Tower.Model.neg,q(congrArg (fun x : ℝ => -x) $ha))
      else (``Hex.RealClosure.Tower.Model.inv,q(congrArg (fun x : ℝ => x⁻¹) $ha))
    let mapped ← mkAppM law #[model,a.expression]
    let expression ← operand mapped
    return ← checked model source ⟨expression,← mkEqTrans mapped congr⟩
  let naturalPower ← if e.isAppOfArity ``HPow.hPow 6 then
      pure ((← inferType args[5]!).isConstOf ``Nat) else pure false
  if naturalPower then
    let x : Q(ℝ) ← pure args[4]!
    let k : Q(ℕ) ← pure args[5]!
    unless ← isDefEq e q($x ^ $k) do
      abort (.unsupported source "nonstandard real power instance")
    let some n ← getNatValue? k |
      abort (.unsupported source "coefficient power requires a natural literal")
    charge .exponent n
    let a ← compileCore model leaf x
    let mapped ← mkAppM ``pow_value #[model,a.expression,toExpr n]
    let expression ← operand mapped
    let va : Q(ℝ) ← mkAppM ``Hex.RealClosure.Tower.Model.value #[model,a.expression]
    let ha : Q($va = $x) ← pure a.proof
    return ← checked model source
      ⟨expression,← mkEqTrans mapped q(congrArg (fun x : ℝ => x ^ $k) $ha)⟩
  rational model source

private meta def admitModel (model : Expr) : ReifyM Expr := do
  let budget := (← get).budget
  for dimension in #[.sourceNodes,.atoms,.reflectedNodes,.exponent,.terms,
      .coefficientBits,.proofNodes] do
    match (Hex.Reflect.BudgetState.ofBudget budget.initial).check dimension
        (budget.consumed.get dimension) with
    | .error exhausted => abort (.budget exhausted)
    | .ok _ => pure ()
  let model ← instantiateMVars model
  if model.hasFVar || model.hasMVar || model.hasLooseBVars then
    throwError "rcf: coefficient compilation requires a closed tower model"
  accountProof model
  let model ← Hex.RCF.checkExpr `TowerCompile.model model
  Meta.check model
  let kind ← whnf (← inferType model)
  accountProof kind
  unless kind.isAppOfArity ``Hex.RealClosure.Tower.Model 5 do
    throwError "rcf: coefficient compilation requires a tower model"
  let expected ← mkAppM ``Hex.RealClosure.Tower.Model
    #[kind.getAppArgs[1]!,mkConst ``Real]
  let expected := mkApp2 expected q(inferInstance : Field ℝ)
    q(inferInstance : LinearOrder ℝ)
  unless ← isDefEq kind expected do
    throwError "rcf: coefficient compilation requires the ordinary real model instances"
  return model

/-- Interpret one closed arithmetic expression under a checked retained model.
Run inside the enclosing quotation transaction; this does not discharge guards. -/
meta def compile (model : Expr) (leaf : Expr → ReifyM (Option Term))
    (source : Expr) : ReifyM Term := do
  compileCore (← admitModel model) leaf source

/-- Compile the existing source's coefficient and original-divisor inventories
in their original order, including guards hidden by cancellation or zero
multiplication. The second array remains a separate nonvanishing obligation.
Continue the source preparation's budget in the enclosing request. -/
meta def prepareWith (source : Reify.Source) (model : Expr)
    (leaf : Expr → ReifyM (Option Term)) : ReifyM (Array Term × Array Term) := do
  let consumed := (← get).budget.consumed
  for dimension in #[.sourceNodes,.atoms,.reflectedNodes,.exponent,.terms,
      .coefficientBits,.proofNodes] do
    unless source.usage.get dimension ≤ consumed.get dimension do
      abort (.internal "tower compilation must continue source preparation accounting")
  let model ← admitModel model
  let coefficients ← source.coefficients.mapM (compileCore model leaf)
  let divisors ← source.divisors.mapM (compileCore model leaf)
  return (coefficients,divisors)

end Hex.RCF.RealCoefficients.TowerCompile
