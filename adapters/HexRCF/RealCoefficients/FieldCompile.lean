/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRCF.RealCoefficients.FieldLiteral
public meta import HexRCF.RealCoefficients.Interpret
public meta import HexRCF.RealCoefficients.Conversion

public meta section

/-! Compile closed arithmetic from authenticated fixed-field source leaves. -/

namespace Hex.RCF.RealCoefficients.FieldCompile
open Lean Meta Qq Hex

structure Result (p : ZPoly) (root : SimpleRoot p) where
  value : PolyQuot p root
  expression : Expr
  /-- Ordinary proof that the coordinate has the original scalar value. -/
  proof : Expr

private meta def checked {p : ZPoly} {root : SimpleRoot p}
    (rep source : Expr) (result : Result p root) : MetaM (Result p root) := do
  let interpreted ← mkAppM ``Field.value #[rep, result.expression]
  let goal ← mkEq interpreted source
  unless ← isDefEq (← inferType result.proof) goal do
    throwError "rcf: fixed-field arithmetic proof has the wrong source"
  return result

private meta def quotient {p : ZPoly} {root : SimpleRoot p}
    [ZPoly.CheckedIrreducible p] (pExpr rootExpr rep hrep hr : Expr)
    (a b : Result p root) (source : Expr) : MetaM (Result p root) := do
  let value := a.value / b.value
  let expression ← FieldLiteral.fieldExpr pExpr rootExpr value
  let reflect ← mkAppM ``Field.value_quotient
    #[rep, hrep, hr, a.expression, b.expression, expression]
  let goal := (← whnf (← inferType reflect)).bindingDomain!
  let certificate ← mkDecideProof goal
  let mapped := mkApp reflect certificate
  let left : Q(ℝ) ← pure (← inferType a.proof).getAppArgs[2]!
  let right : Q(ℝ) ← pure (← inferType b.proof).getAppArgs[2]!
  let va : Q(ℝ) ← mkAppM ``Field.value #[rep, a.expression]
  let vb : Q(ℝ) ← mkAppM ``Field.value #[rep, b.expression]
  let ha : Q($va = $left) ← pure a.proof
  let hb : Q($vb = $right) ← pure b.proof
  let proof ← mkEqTrans mapped q(congrArg₂ (fun x y : ℝ => x / y) $ha $hb)
  return ← checked rep source ⟨value, expression, proof⟩

/-- Compile source arithmetic from already authenticated leaves. This traversal
uses the existing field operations and constructs ordinary homomorphism proofs;
it neither selects roots nor simplifies away original divisor obligations. -/
meta partial def compile {p : ZPoly} {root : SimpleRoot p}
    [ZPoly.CheckedIrreducible p] (pExpr rootExpr rep hrep hr : Expr)
    (leaf : Expr → MetaM (Option (Result p root))) (source : Expr) :
    MetaM (Result p root) := do
  if let some result ← leaf source then return ← checked rep source result
  let e := source.consumeMData
  let args := e.getAppArgs
  let op := e.getAppFn.constName?
  let sourceQ : Q(ℝ) ← pure source
  if let some (value, equality) ← Conversion.step? source then
    let compiled ← compile pExpr rootExpr rep hrep hr leaf value
    let proof ← mkEqTrans compiled.proof (← mkEqSymm equality)
    return ← checked rep source ⟨compiled.value, compiled.expression, proof⟩
  if e.isAppOfArity ``RealAlgebraicNumber.toReal 1 &&
      e.appArg!.isAppOfArity ``RealAlgebraicNumber.ofRat 1 then
    let rational : Q(ℚ) := e.appArg!.appArg!
    let compiled ← compile pExpr rootExpr rep hrep hr leaf q(($rational : ℝ))
    let interpretation ← mkAppM ``RealAlgebraicNumber.ofRat_toReal #[rational]
    let proof ← mkEqTrans compiled.proof (← mkEqSymm interpretation)
    return ← checked rep source ⟨compiled.value, compiled.expression, proof⟩
  if [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv].any (op == some ·) &&
      args.size == 6 then
    let left : Q(ℝ) ← pure args[4]!
    let right : Q(ℝ) ← pure args[5]!
    let canonical := if op == some ``HAdd.hAdd then q($left + $right)
      else if op == some ``HSub.hSub then q($left - $right)
      else if op == some ``HMul.hMul then q($left * $right) else q($left / $right)
    unless ← isDefEq e canonical do
      throwError "rcf: nonstandard fixed-field arithmetic instance"
    let a ← compile pExpr rootExpr rep hrep hr leaf args[4]!
    let b ← compile pExpr rootExpr rep hrep hr leaf args[5]!
    if op == some ``HDiv.hDiv then
      return ← quotient pExpr rootExpr rep hrep hr a b source
    let va : Q(ℝ) ← mkAppM ``Field.value #[rep, a.expression]
    let vb : Q(ℝ) ← mkAppM ``Field.value #[rep, b.expression]
    let ha : Q($va = $left) ← pure a.proof
    let hb : Q($vb = $right) ← pure b.proof
    let (value, name, congr) := if op == some ``HAdd.hAdd then
        (a.value + b.value, ``Field.value_add,
          q(congrArg₂ (fun x y : ℝ => x + y) $ha $hb))
      else if op == some ``HSub.hSub then
        (a.value - b.value, ``Field.value_sub,
          q(congrArg₂ (fun x y : ℝ => x - y) $ha $hb))
      else (a.value * b.value, ``Field.value_mul,
          q(congrArg₂ (fun x y : ℝ => x * y) $ha $hb))
    let expression ← mkAppM op.get! #[a.expression, b.expression]
    let mapped ← mkAppM name #[rep, hrep, hr, a.expression, b.expression]
    return ← checked rep source ⟨value, expression, ← mkEqTrans mapped congr⟩
  if [``Neg.neg, ``Inv.inv].any (op == some ·) && args.size == 3 then
    let operand : Q(ℝ) ← pure args[2]!
    let canonical := if op == some ``Neg.neg then q(-$operand) else q($operand⁻¹)
    unless ← isDefEq e canonical do
      throwError "rcf: nonstandard fixed-field unary instance"
    let a ← compile pExpr rootExpr rep hrep hr leaf args[2]!
    if op == some ``Inv.inv then
      let one : Q(ℝ) := q((1 : ℝ))
      let unit ← compile pExpr rootExpr rep hrep hr leaf one
      let divided ← quotient pExpr rootExpr rep hrep hr unit a q(1 / $operand)
      let proof ← mkEqTrans divided.proof q(one_div $operand)
      return ← checked rep source ⟨divided.value, divided.expression, proof⟩
    let va : Q(ℝ) ← mkAppM ``Field.value #[rep, a.expression]
    let ha : Q($va = $operand) ← pure a.proof
    let expression ← mkAppM ``Neg.neg #[a.expression]
    let mapped ← mkAppM ``Field.value_neg #[rep, hrep, hr, a.expression]
    let proof ← mkEqTrans mapped q(congrArg (fun x : ℝ => -x) $ha)
    return ← checked rep source ⟨-a.value, expression, proof⟩
  let isNatPower ← if e.isAppOfArity ``HPow.hPow 6 then
      pure ((← inferType args[5]!).isConstOf ``Nat) else pure false
  if isNatPower then
    let base : Q(ℝ) ← pure args[4]!
    let exponent : Q(ℕ) ← pure args[5]!
    unless ← isDefEq e q($base ^ $exponent) do
      throwError "rcf: nonstandard fixed-field power instance"
    let some n ← getNatValue? exponent |
      throwError "rcf: fixed-field power requires a natural literal"
    let a ← compile pExpr rootExpr rep hrep hr leaf args[4]!
    let va : Q(ℝ) ← mkAppM ``Field.value #[rep, a.expression]
    let ha : Q($va = $base) ← pure a.proof
    let expression ← mkAppM ``HPow.hPow #[a.expression, exponent]
    let mapped ← mkAppM ``Field.value_pow #[rep, hrep, hr, a.expression, exponent]
    let proof ← mkEqTrans mapped q(congrArg (fun x : ℝ => x ^ $exponent) $ha)
    return ← checked rep source ⟨a.value ^ n, expression, proof⟩
  let ⟨value, n, d, h⟩ ← Mathlib.Meta.NormNum.deriveRat sourceQ
    (_inst := q(inferInstance))
  let rational : Q(ℚ) := q(($n : ℚ) / $d)
  let expression := mkApp3 (mkConst ``PolyQuot.ofRat) pExpr rootExpr rational
  let hom ← mkAppM ``FieldSpecialize.value_ofRat #[rep, hrep, hr, rational]
  let raw : Q(((($n : ℚ) / $d : ℚ) : ℝ) = ($n : ℝ) / $d) :=
    q(by push_cast; rfl)
  let proof ← mkEqTrans hom (← mkEqTrans raw q(($h).to_raw_eq.symm))
  return ← checked rep source ⟨PolyQuot.ofRat value, expression, proof⟩

end Hex.RCF.RealCoefficients.FieldCompile
