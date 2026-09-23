/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.RootAliases
public meta import HexRealFormulaMathlib.Reify.Arithmetic

public section

namespace Hex.RCF.RealCoefficients.Coefficients

private theorem rational_value (n : Int) (d : Nat) :
    (RealAlgebraicNumber.ofRat ((n : Rat) / d)).toReal = (n : ℝ) / d := by
  simp

private theorem nonneg_value (a : RealAlgebraicNumber) (source : ℝ)
    (h : a.toReal = source) (hs : 0 ≤ source) : 0 ≤ a := by
  simpa only [RealAlgebraicNumber.le_iff, RealAlgebraicNumber.zero_toReal, h] using hs

end Hex.RCF.RealCoefficients.Coefficients

public meta section

namespace Hex.RCF.RealCoefficients.Coefficients

open Lean Meta Qq Hex.RealFormula.Reify

/-- An algebraic expression with its exact source interpretation. This is not
an encoding of a computed value: certificate replay must still authenticate its
literal data without evaluating algebraic root search in the kernel. -/
structure Prepared where
  value : Expr
  /-- Ordinary proof of `RealAlgebraicNumber.toReal value = source`. -/
  proof : Expr

/-- Recognize a positive reciprocal integer exponent using checked rational
normalization. The caller retains the source exponent's divisor obligations. -/
def rootDegree (source : Expr) : ReifyM Nat := do
  let _ ← arithmetic #[] source
  let source : Q(ℝ) ← pure source
  let result ← liftM <| observing? do
    let ⟨value, _, _, _⟩ ← Mathlib.Meta.NormNum.deriveRat source (_inst := q(inferInstance))
    pure value
  let some value := result | abort (.unsupported source "expected a reciprocal root degree")
  unless value.num == 1 do
    abort (.unsupported source "root exponent must be 1/n for a positive integer n")
  charge .exponent value.den
  return value.den

private def checked (source : Expr) (value proof : Expr) : ReifyM Prepared := do
  let target ← mkEq (← mkAppM ``RealAlgebraicNumber.toReal #[value]) source
  unless ← isDefEq (← inferType proof) target do
    abort (.internal "coefficient interpretation has the wrong target")
  accountProof proof
  return ⟨value, proof⟩

private partial def interpretCore (source : Expr)
    (nonnegative : Expr → MetaM Expr) : ReifyM Prepared := do
  let e := source.consumeMData
  unless !e.hasFVar && !e.hasMVar && !e.hasLooseBVars do
    abort (.unsupported source "coefficient must be closed")
  unless ← isDefEq (← inferType e) q(ℝ) do
    abort (.unsupported source "coefficient must have type Real")
  if e.isAppOfArity ``RealAlgebraicNumber.toReal 1 then
    return ← checked source e.appArg! (← mkEqRefl e)
  let args := e.getAppArgs
  let op := e.getAppFn.constName?
  if [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv].any (op == some ·) &&
      args.size == 6 then
    let ra ← interpretCore args[4]! nonnegative
    let rb ← interpretCore args[5]! nonnegative
    let a : Q(RealAlgebraicNumber) ← pure ra.value
    let b : Q(RealAlgebraicNumber) ← pure rb.value
    let x : Q(ℝ) ← pure args[4]!
    let y : Q(ℝ) ← pure args[5]!
    let ha : Q(($a).toReal = $x) ← pure ra.proof
    let hb : Q(($b).toReal = $y) ← pure rb.proof
    let (value, proof) := if op == some ``HAdd.hAdd then
        (q($a + $b), q((RealAlgebraicNumber.add_toReal $a $b).trans
          (congrArg₂ (fun x y : ℝ => x + y) $ha $hb)))
      else if op == some ``HSub.hSub then
        (q($a - $b), q((RealAlgebraicNumber.sub_toReal $a $b).trans
          (congrArg₂ (fun x y : ℝ => x - y) $ha $hb)))
      else if op == some ``HMul.hMul then
        (q($a * $b), q((RealAlgebraicNumber.mul_toReal $a $b).trans
          (congrArg₂ (fun x y : ℝ => x * y) $ha $hb)))
      else (q($a / $b), q((RealAlgebraicNumber.div_toReal $a $b).trans
          (congrArg₂ (fun x y : ℝ => x / y) $ha $hb)))
    return ← checked source value proof
  if [``Neg.neg, ``Inv.inv].any (op == some ·) && args.size == 3 then
    let ra ← interpretCore args[2]! nonnegative
    let a : Q(RealAlgebraicNumber) ← pure ra.value
    let x : Q(ℝ) ← pure args[2]!
    let ha : Q(($a).toReal = $x) ← pure ra.proof
    if op == some ``Neg.neg then
      return ← checked source q(-$a) q((RealAlgebraicNumber.neg_toReal $a).trans
        (congrArg (fun x : ℝ => -x) $ha))
    return ← checked source q($a⁻¹) q((RealAlgebraicNumber.inv_toReal $a).trans
      (congrArg (fun x : ℝ => x⁻¹) $ha))
  let isNatPower ← if e.isAppOfArity ``HPow.hPow 6 then
      pure ((← inferType args[5]!).isConstOf ``Nat) else pure false
  if isNatPower then
    let some n ← getNatValue? args[5]!
      | abort (.unsupported source "coefficient power requires a natural literal")
    charge .exponent n
    let ra ← interpretCore args[4]! nonnegative
    let a : Q(RealAlgebraicNumber) ← pure ra.value
    let x : Q(ℝ) ← pure args[4]!
    let n : Q(ℕ) ← pure args[5]!
    let ha : Q(($a).toReal = $x) ← pure ra.proof
    return ← checked source q(RealAlgebraicNumber.natPow $a $n)
      q((RealAlgebraicNumber.natPow_toReal $a $n).trans
        (congrArg (fun x : ℝ => x ^ $n) $ha))
  let isRealPower ← if e.isAppOfArity ``HPow.hPow 6 then
      pure ((← inferType args[5]!).isConstOf ``Real) else pure false
  let radical := if e.isAppOfArity ``Real.sqrt 1 then some (e.appArg!, none)
    else if e.isAppOfArity ``Real.rpow 2 then some (args[0]!, some args[1]!)
    else if isRealPower then
      some (args[4]!, some args[5]!) else none
  if let some (base, exponent) := radical then
    let n ← match exponent with | none => pure 2 | some p => rootDegree p
    charge .exponent n
    let ra ← interpretCore base nonnegative
    let a : Q(RealAlgebraicNumber) ← pure ra.value
    let x : Q(ℝ) ← pure base
    let ha : Q(($a).toReal = $x) ← pure ra.proof
    let hx : Q(0 ≤ $x) ← nonnegative base
    unless ← isDefEq (← inferType hx) q(0 ≤ $x) do
      abort (.internal "nonnegativity provider returned the wrong proposition")
    let h : Q(0 ≤ $a) ← pure q(nonneg_value $a $x $ha $hx)
    let degree : Q(ℕ) ← pure (mkNatLit n)
    let value := q(root $a $degree $h)
    if exponent.isNone then
      return ← checked source value q((root_two $a $h).trans (congrArg Real.sqrt $ha))
    let p : Q(ℝ) ← pure exponent.get!
    let canonical : Q(ℝ) ← pure q(1 / ($degree : ℝ))
    let ⟨_, _, _, hp⟩ ← Mathlib.Meta.NormNum.deriveRat p (_inst := q(inferInstance))
    let ⟨_, _, _, hc⟩ ← Mathlib.Meta.NormNum.deriveRat canonical (_inst := q(inferInstance))
    let he ← mkAppM ``Mathlib.Meta.NormNum.isRat_eq_true #[hc, hp]
    let he : Q(1 / ($degree : ℝ) = $p) ← pure he
    return ← checked source value q((root_toReal $a $degree $h).trans
      (congrArg₂ (fun x y : ℝ => x ^ y) $ha $he))
  -- Validate literal syntax and its size before calling the rational normalizer.
  let _ ← arithmetic #[] e
  let x : Q(ℝ) ← pure e
  let ⟨_, n, d, h⟩ ← Mathlib.Meta.NormNum.deriveRat x (_inst := q(inferInstance))
  return ← checked source q(RealAlgebraicNumber.ofRat (($n : ℚ) / $d))
    q((rational_value $n $d).trans ($h).to_raw_eq.symm)

/-- Translate a closed real coefficient using the existing algebraic arithmetic
and checked radical aliases. `nonnegative` supplies proofs for radical bases;
all assembled proofs are checked by the ordinary kernel. Original divisor
obligations belong to `Reify.Source` and must still be discharged separately.
No compiled value or chosen-root certificate is trusted by this translation. -/
def interpret (source : Expr) (nonnegative : Expr → MetaM Expr) : ReifyM Prepared := do
  let cap := (← get).budget.remaining.sourceNodes
  charge .sourceNodes (Hex.Reflect.sourceNodeCount source (cap + 1))
  let result ← interpretCore source nonnegative
  checkWithKernel result.proof
  return result

end Hex.RCF.RealCoefficients.Coefficients
