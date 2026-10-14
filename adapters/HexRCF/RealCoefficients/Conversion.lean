/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealAlgebraicTheory.Complex
public import HexRCF.RealCoefficients.Coefficients
public meta import Lean.Meta
public meta import Qq

public section

/-! Exact source conversions for checked construction and explicit projection.
These equalities retain the actual `getD` branch. They do not interpret a
nonreal algebraic number as a real coefficient. -/

namespace Hex.RCF.RealCoefficients.Conversion

open Hex

theorem checked_value (a fallback : RealAlgebraicNumber) :
    (RealAlgebraicNumber.ofAlgebraic? a.toAlgebraic).getD fallback = a := by
  rw [(RealAlgebraicNumber.ofAlgebraic?_eq_some _ _).mpr rfl]
  rfl

theorem checked_I (fallback : RealAlgebraicNumber) :
    (RealAlgebraicNumber.ofAlgebraic? AlgebraicNumber.I).getD fallback = fallback := by
  have h : ¬ AlgebraicNumber.I.isReal = true := by
    rw [AlgebraicNumber.isReal_iff, AlgebraicNumber.I_toComplex]
    norm_num
  simp only [RealAlgebraicNumber.ofAlgebraic?, dite_eq_right h, Option.getD_none]

theorem checked_rat (q : Rat) (fallback : RealAlgebraicNumber) :
    (RealAlgebraicNumber.ofAlgebraic? (AlgebraicNumber.ofRat q)).getD fallback =
      RealAlgebraicNumber.ofRat q := by
  rw [(RealAlgebraicNumber.ofAlgebraic?_eq_some _ _).mpr
    (RealAlgebraicNumber.ofRat_toAlgebraic q).symm]
  rfl

theorem checked_field (a : RealAlgebraicNumber) (v : QAdjoin a.toAlgebraic)
    (fallback : RealAlgebraicNumber) :
    (RealAlgebraicNumber.ofAlgebraic? v.toAlgebraicNumber).getD fallback =
      Coefficients.ofField a v := by
  have h : RealAlgebraicNumber.ofAlgebraic? v.toAlgebraicNumber =
      some (Coefficients.ofField a v) :=
    (RealAlgebraicNumber.ofAlgebraic?_eq_some _ _).mpr rfl
  rw [h]
  rfl

theorem project_value (a : RealAlgebraicNumber) : a.toAlgebraic.re = a :=
  AlgebraicNumber.re_ofReal a

theorem project_I : AlgebraicNumber.I.re = RealAlgebraicNumber.ofRat 0 := by
  apply RealAlgebraicNumber.toReal_injective
  simp

theorem project_rat (q : Rat) :
    (AlgebraicNumber.ofRat q).re = RealAlgebraicNumber.ofRat q := by
  apply RealAlgebraicNumber.toReal_injective
  simp

theorem project_field (a : RealAlgebraicNumber) (v : QAdjoin a.toAlgebraic) :
    v.toAlgebraicNumber.re = Coefficients.ofField a v :=
  AlgebraicNumber.re_ofReal (Coefficients.ofField a v)

theorem project_add (a b : AlgebraicNumber) :
    (a + b).re.toReal = a.re.toReal + b.re.toReal := by
  rw [AlgebraicNumber.re_add, RealAlgebraicNumber.add_toReal]

theorem cast_nat (n : Nat) : (n : RealAlgebraicNumber).toReal = (n : ℝ) := by
  change (RealAlgebraicNumber.ofRat (n : Rat)).toReal = _
  rw [RealAlgebraicNumber.ofRat_toReal, Rat.cast_natCast]

theorem cast_int (n : Int) : (n : RealAlgebraicNumber).toReal = (n : ℝ) := by
  change (RealAlgebraicNumber.ofRat (n : Rat)).toReal = _
  rw [RealAlgebraicNumber.ofRat_toReal, Rat.cast_intCast]

public meta section

open Lean Meta Qq

private def realArgument? (source : Expr) : Option Expr :=
  if source.isAppOfArity ``RealAlgebraicNumber.toAlgebraic 1 ||
      source.isAppOfArity ``AlgebraicNumber.ofReal 1 then some source.appArg!
  else none

private def fieldArguments? (source : Expr) : Option (Expr × Expr) := do
  unless source.isAppOfArity ``QAdjoin.toAlgebraicNumber 2 do none
  let args := source.getAppArgs
  let value ← realArgument? args[0]!
  return (value, args[1]!)

private def binaryArguments? (source : Expr) : MetaM (Option (Name × Expr × Expr)) := do
  let (op, args) := source.getAppFnArgs
  let pairs := #[(``HAdd.hAdd, ``RealAlgebraicNumber.add),
    (``HSub.hSub, ``RealAlgebraicNumber.sub), (``HMul.hMul, ``RealAlgebraicNumber.mul),
    (``HDiv.hDiv, ``RealAlgebraicNumber.div)]
  for (operatorName, constructor) in pairs do
    if op == constructor && args.size == 2 then return some (operatorName, args[0]!, args[1]!)
    if op == operatorName && args.size == 6 then
      unless ← isDefEq (← inferType args[4]!) (mkConst ``RealAlgebraicNumber) do return none
      let a : Q(RealAlgebraicNumber) := args[4]!
      let b : Q(RealAlgebraicNumber) := args[5]!
      let canonical := if op == ``HAdd.hAdd then q($a + $b)
        else if op == ``HSub.hSub then q($a - $b)
        else if op == ``HMul.hMul then q($a * $b) else q($a / $b)
      unless ← isDefEq source canonical do return none
      return some (op, a, b)
  return none

private def unaryArgument? (source : Expr) : MetaM (Option (Name × Expr)) := do
  let (op, args) := source.getAppFnArgs
  for (operatorName, constructor) in #[(``Neg.neg, ``RealAlgebraicNumber.neg),
      (``Inv.inv, ``RealAlgebraicNumber.inv)] do
    if op == constructor && args.size == 1 then return some (operatorName, args[0]!)
    if op == operatorName && args.size == 3 then
      unless ← isDefEq (← inferType args[2]!) (mkConst ``RealAlgebraicNumber) do return none
      let a : Q(RealAlgebraicNumber) := args[2]!
      let canonical := if op == ``Neg.neg then q(-$a) else q($a⁻¹)
      unless ← isDefEq source canonical do return none
      return some (op, a)
  return none

/-- The original denominator of visible real-algebraic arithmetic, interpreted
at its real value. Consumers must prove it nonzero before source simplification. -/
def divisor? (value : Expr) : MetaM (Option Expr) := do
  if let some (op, _, denominator) ← binaryArguments? value then
    if op == ``HDiv.hDiv then
      return some (← mkAppM ``RealAlgebraicNumber.toReal #[denominator])
  if let some (op, denominator) ← unaryArgument? value then
    if op == ``Inv.inv then
      return some (← mkAppM ``RealAlgebraicNumber.toReal #[denominator])
  return none

/-- Recognize one visible constructor conversion. The returned equality has
the exact original real expression on its left. No approximation or native
conversion result supplies proof evidence. -/
def step? (source : Expr) : MetaM (Option (Expr × Expr)) := do
  unless !source.hasFVar && !source.hasMVar && !source.hasLooseBVars &&
      source.isAppOfArity ``RealAlgebraicNumber.toReal 1 do return none
  let argument := source.appArg!
  let interpretation := mkConst ``RealAlgebraicNumber.toReal
  if argument.isConstOf ``RealAlgebraicNumber.zero then
    return some (q((0 : ℝ)), mkConst ``RealAlgebraicNumber.zero_toReal)
  if argument.isAppOfArity ``OfNat.ofNat 3 then
    let some number := getRawNatValue? argument.getAppArgs[1]! | return none
    if number == 0 then
      unless ← isDefEq argument q((0 : RealAlgebraicNumber)) do return none
      return some (q((0 : ℝ)), mkConst ``RealAlgebraicNumber.zero_toReal)
    if number == 1 then
      unless ← isDefEq argument q((1 : RealAlgebraicNumber)) do return none
      return some (q((1 : ℝ)), mkConst ``RealAlgebraicNumber.one_toReal)
    let n : Q(ℕ) := mkNatLit number
    unless ← isDefEq argument q(($n : RealAlgebraicNumber)) do return none
    return some (q(($n : ℝ)), ← mkAppM ``cast_nat #[n])
  if argument.isAppOfArity ``Nat.cast 3 then
    let n : Q(ℕ) := argument.getAppArgs[2]!
    unless ← isDefEq argument q(($n : RealAlgebraicNumber)) do return none
    return some (q(($n : ℝ)), ← mkAppM ``cast_nat #[n])
  if argument.isAppOfArity ``Int.cast 3 then
    let n : Q(ℤ) := argument.getAppArgs[2]!
    unless ← isDefEq argument q(($n : RealAlgebraicNumber)) do return none
    return some (q(($n : ℝ)), ← mkAppM ``cast_int #[n])
  if let some (op, left, right) ← binaryArguments? argument then
    let a : Q(RealAlgebraicNumber) := left
    let b : Q(RealAlgebraicNumber) := right
    let (value, theoremName) := if op == ``HAdd.hAdd then
        (q(($a).toReal + ($b).toReal), ``RealAlgebraicNumber.add_toReal)
      else if op == ``HSub.hSub then
        (q(($a).toReal - ($b).toReal), ``RealAlgebraicNumber.sub_toReal)
      else if op == ``HMul.hMul then
        (q(($a).toReal * ($b).toReal), ``RealAlgebraicNumber.mul_toReal)
      else (q(($a).toReal / ($b).toReal), ``RealAlgebraicNumber.div_toReal)
    return some (value, ← mkAppM theoremName #[a, b])
  if let some (op, value) ← unaryArgument? argument then
    let a : Q(RealAlgebraicNumber) := value
    if op == ``Neg.neg then
      return some (q(-($a).toReal), ← mkAppM ``RealAlgebraicNumber.neg_toReal #[a])
    return some (q(($a).toReal⁻¹), ← mkAppM ``RealAlgebraicNumber.inv_toReal #[a])
  let power := if argument.isAppOfArity ``RealAlgebraicNumber.natPow 2 then
      some (argument.getAppArgs[0]!, argument.getAppArgs[1]!)
    else if argument.isAppOfArity ``HPow.hPow 6 then
      some (argument.getAppArgs[4]!, argument.getAppArgs[5]!) else none
  if let some (base, exponent) := power then
    unless (← inferType exponent).isConstOf ``Nat do return none
    let a : Q(RealAlgebraicNumber) := base
    let n : Q(ℕ) := exponent
    unless ← isDefEq argument q($a ^ $n) do return none
    return some (q(($a).toReal ^ $n), ← mkAppM ``RealAlgebraicNumber.pow_toReal #[a, n])
  if argument.isAppOfArity ``Option.getD 3 then
    let args := argument.getAppArgs
    let input := args[1]!
    unless input.isAppOfArity ``RealAlgebraicNumber.ofAlgebraic? 1 do return none
    let algebraic := input.appArg!
    let fallback := args[2]!
    if let some value := realArgument? algebraic then
      let proof ← mkAppM ``checked_value #[value, fallback]
      return some (← mkAppM ``RealAlgebraicNumber.toReal #[value],
        ← mkAppM ``congrArg #[interpretation, proof])
    if algebraic.isConstOf ``AlgebraicNumber.I then
      let proof ← mkAppM ``checked_I #[fallback]
      return some (← mkAppM ``RealAlgebraicNumber.toReal #[fallback],
        ← mkAppM ``congrArg #[interpretation, proof])
    if algebraic.isAppOfArity ``AlgebraicNumber.ofRat 1 then
      let rational := algebraic.appArg!
      let value ← mkAppM ``RealAlgebraicNumber.ofRat #[rational]
      let proof ← mkAppM ``checked_rat #[rational, fallback]
      return some (← mkAppM ``RealAlgebraicNumber.toReal #[value],
        ← mkAppM ``congrArg #[interpretation, proof])
    if let some (a, v) := fieldArguments? algebraic then
      let value ← mkAppM ``Coefficients.ofField #[a, v]
      let proof ← mkAppM ``checked_field #[a, v, fallback]
      return some (← mkAppM ``RealAlgebraicNumber.toReal #[value],
        ← mkAppM ``congrArg #[interpretation, proof])
  if argument.isAppOfArity ``AlgebraicNumber.re 1 then
    let algebraic := argument.appArg!
    if let some value := realArgument? algebraic then
      let proof ← mkAppM ``project_value #[value]
      return some (← mkAppM ``RealAlgebraicNumber.toReal #[value],
        ← mkAppM ``congrArg #[interpretation, proof])
    if algebraic.isConstOf ``AlgebraicNumber.I then
      let value : Q(RealAlgebraicNumber) := q(RealAlgebraicNumber.ofRat 0)
      return some (← mkAppM ``RealAlgebraicNumber.toReal #[value],
        ← mkAppM ``congrArg #[interpretation, mkConst ``project_I])
    if algebraic.isAppOfArity ``AlgebraicNumber.ofRat 1 then
      let rational := algebraic.appArg!
      let value ← mkAppM ``RealAlgebraicNumber.ofRat #[rational]
      let proof ← mkAppM ``project_rat #[rational]
      return some (← mkAppM ``RealAlgebraicNumber.toReal #[value],
        ← mkAppM ``congrArg #[interpretation, proof])
    if let some (a, v) := fieldArguments? algebraic then
      let value ← mkAppM ``Coefficients.ofField #[a, v]
      let proof ← mkAppM ``project_field #[a, v]
      return some (← mkAppM ``RealAlgebraicNumber.toReal #[value],
        ← mkAppM ``congrArg #[interpretation, proof])
    if algebraic.isAppOfArity ``HAdd.hAdd 6 then
      let args := algebraic.getAppArgs
      unless ← isDefEq (← inferType args[4]!) (mkConst ``AlgebraicNumber) do
        return none
      let a : Q(AlgebraicNumber) := args[4]!
      let b : Q(AlgebraicNumber) := args[5]!
      unless ← isDefEq algebraic q($a + $b) do return none
      return some (q(($a).re.toReal + ($b).re.toReal),
        ← mkAppM ``project_add #[a, b])
  return none

end
end Hex.RCF.RealCoefficients.Conversion
