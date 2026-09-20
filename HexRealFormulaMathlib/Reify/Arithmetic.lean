/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealFormulaMathlib.ReifyProof
public meta import HexReflect.Session
public meta import Mathlib.Tactic.NormNum
public meta import Qq

public meta section

/-! Rational source views, resource accounting, and structured frontend declines. -/

namespace Hex.RealFormula.Reify

open Lean Meta Qq

/-- Consumer limits include the expanded formula tree as well as ring budgets. -/
structure Config where
  ring : Reflect.Config := {}
  formulaNodes : Nat := 20000
  reference : Syntax := .missing

/-- Provider diagnostics retain their original structured reason and usage. -/
inductive Error where
  | unsupported (source : Expr) (reason : String)
  | budget (reason : Reflect.BudgetExhausted)
  | formulaBudget (limit requested : Nat)
  | providerDeclined (reason : Reflect.Decline) (usage : Reflect.BudgetUsage)
      (conditions : Array Reflect.Condition)
  | providerFailure (reason : Reflect.Failure) (conditions : Array Reflect.Condition)
  | providerConditions (conditions : Array Reflect.Condition)
  | internal (reason : String)

structure State where
  config : Config
  budget : Reflect.BudgetState
  inputs : Array Expr := #[]
  binders : Array Expr := #[]

abbrev ReifyM := StateRefT State (ExceptT Error MetaM)

def abort (e : Error) : ReifyM α := throwThe Error e

def charge (dimension : Reflect.BudgetDimension) (amount : Nat) : ReifyM Unit := do
  match (← get).budget.charge dimension amount with
  | .error e => abort (.budget e)
  | .ok b => modify fun s => { s with budget := b }

def formulaBudget (nodes : Nat) : ReifyM Unit := do
  let limit := (← get).config.formulaNodes
  if nodes > limit then abort (.formulaBudget limit nodes)

def accountProof (proof : Expr) : ReifyM Unit := do
  let cap := (← get).budget.remaining.proofNodes
  charge .proofNodes (Reflect.proofNodeCount #[proof] (cap + 1))

def realNat (n : Nat) : Expr :=
  let n : Q(ℕ) := toExpr n
  q(($n : ℝ))

def realInt (n : Int) : Expr :=
  let n : Q(ℤ) := toExpr n
  q(($n : ℝ))

def realMul (a b : Expr) : Expr :=
  let a : Q(ℝ) := a; let b : Q(ℝ) := b
  q($a * $b)

def realSub (a b : Expr) : Expr :=
  let a : Q(ℝ) := a; let b : Q(ℝ) := b
  q($a - $b)

def realNeg (a : Expr) : Expr :=
  let a : Q(ℝ) := a
  q(-$a)

/-- A proof of `source * denominator = numerator`, with a positive natural denominator. -/
structure Arithmetic where
  numerator : Expr
  denominator : Nat
  proof : Expr

private def bounded (numerator denominator : Nat) : ReifyM (Nat × Nat) := do
  charge .coefficientBits (max numerator denominator)
  return (numerator, denominator)

/-- Bound scalar numerator and denominator sizes before normalization. The
accepted scalar grammar is rational arithmetic and literal casts, not arbitrary
closed functions that a simplifier might happen to evaluate. -/
private partial def scalarSize (source : Expr) : ReifyM (Nat × Nat) := do
  let e := source.consumeMData
  if let some n := getRawNatValue? e then return ← bounded (n.log2 + 1) 1
  let args := e.getAppArgs
  let op := e.getAppFn.constName?
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let some n := getRawNatValue? args[1]!
      | abort (.unsupported source "coefficient numeral is not literal")
    return ← bounded (n.log2 + 1) 1
  if op == some ``Neg.neg && args.size == 3 then return ← scalarSize args[2]!
  if [``Int.cast, ``Nat.cast, ``Rat.cast, ``RatCast.ratCast, ``Int.ofNat,
      ``Int.negOfNat, ``Rat.ofInt].any (fun name => op == some name) && !args.isEmpty then
    return ← scalarSize args.back!
  if e.isAppOfArity ``Int.negSucc 1 then
    let (n, d) ← scalarSize args[0]!
    return ← bounded (n + 1) d
  if [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv].any
      (fun name => op == some name) && args.size == 6 then
    let (a, d) ← scalarSize args[4]!
    let (b, e) ← scalarSize args[5]!
    if op == some ``HMul.hMul then return ← bounded (a + b) (d + e)
    if op == some ``HDiv.hDiv then return ← bounded (a + e) (d + b)
    return ← bounded (max (a + e) (b + d) + 1) (d + e)
  if e.isAppOfArity ``HPow.hPow 6 then
    let some k ← getNatValue? args[5]!
      | abort (.unsupported source "scalar powers require literal natural exponents")
    charge .exponent k
    let (n, d) ← scalarSize args[4]!
    return ← bounded (n * k + 1) (d * k + 1)
  if e.isAppOfArity ``OfScientific.ofScientific 5 then
    let some k ← getNatValue? args[4]!
      | abort (.unsupported source "scientific notation requires a literal exponent")
    charge .exponent k
    let (n, _) ← scalarSize args[2]!
    return ← bounded (n + 4 * k + 1) (4 * k + 1)
  abort (.unsupported source "expected rational literal arithmetic")

private def scalar (e : Expr) : ReifyM (Rat × Arithmetic) := do
  let _ ← scalarSize e
  let eQ : Q(ℝ) := e
  let result : Option (Rat × Expr) ← liftM <| observing? do
    let ⟨value, _, _, proof⟩ ← Mathlib.Meta.NormNum.deriveRat eQ (_inst := q(inferInstance))
    pure (value, proof)
  let some (value, proof) := result
    | abort (.unsupported e "expected a rational literal")
  charge .coefficientBits (max (value.num.natAbs.log2 + 1) (value.den.log2 + 1))
  return (value, ⟨realInt value.num, value.den,
    ← mkAppM ``Denominator.scalar #[proof]⟩)

private def positive (n : Nat) : MetaM Expr := do
  let n : Q(ℕ) := toExpr n
  mkDecideProof q(0 < $n)

/-- Recognize only polynomial operations and literal scalar casts. Unknown
functions are rejected before ring reflection can hide them as opaque atoms. -/
partial def arithmetic (coords : Array Expr) (source : Expr) : ReifyM Arithmetic := do
  let e := source.consumeMData
  if e.isFVar then
    unless coords.contains e do
      abort (.unsupported source "undeclared real parameter")
    return ⟨e, 1, ← mkAppM ``Denominator.leaf #[e]⟩
  let args := e.getAppArgs
  let op := e.getAppFn.constName?
  if op == some ``HAdd.hAdd || op == some ``HSub.hSub || op == some ``HMul.hMul then
    unless args.size == 6 do abort (.unsupported source "malformed arithmetic application")
    let a ← arithmetic coords args[4]!
    let b ← arithmetic coords args[5]!
    charge .coefficientBits (a.denominator.log2 + b.denominator.log2 + 2)
    let (num, rule) := if op == some ``HMul.hMul then
        (realMul a.numerator b.numerator, ``Denominator.mul)
      else if op == some ``HSub.hSub then
        (realSub (realMul a.numerator (realNat b.denominator))
          (realMul b.numerator (realNat a.denominator)), ``Denominator.sub)
      else
        let l : Q(ℝ) := realMul a.numerator (realNat b.denominator)
        let r : Q(ℝ) := realMul b.numerator (realNat a.denominator)
        (q($l + $r), ``Denominator.add)
    return ⟨num, a.denominator * b.denominator, ← mkAppM rule #[a.proof, b.proof]⟩
  if op == some ``Neg.neg then
    unless args.size == 3 do abort (.unsupported source "malformed negation")
    let a ← arithmetic coords args[2]!
    return ⟨realNeg a.numerator, a.denominator, ← mkAppM ``Denominator.neg #[a.proof]⟩
  if op == some ``HPow.hPow then
    unless args.size == 6 do abort (.unsupported source "malformed power")
    unless ← isDefEq (← inferType args[5]!) (mkConst ``Nat) do
      abort (.unsupported source "power exponent must have type Nat")
    let some k ← getNatValue? args[5]!
      | abort (.unsupported source "power exponent must be a literal natural number")
    charge .exponent k
    let a ← arithmetic coords args[4]!
    charge .coefficientBits (if a.denominator ≤ 1 then 1 else (a.denominator.log2 + 1) * k)
    let num : Q(ℝ) := a.numerator
    let kQ : Q(ℕ) := toExpr k
    return ⟨q($num ^ $kQ), a.denominator ^ k, ← mkAppM ``Denominator.pow #[a.proof, kQ]⟩
  if op == some ``HDiv.hDiv then
    unless args.size == 6 do abort (.unsupported source "malformed division")
    let a ← arithmetic coords args[4]!
    -- Validate the divisor's syntax too: a closed non-polynomial expression
    -- is not accepted merely because a simplifier knows its value.
    let _ ← arithmetic #[] args[5]!
    let (value, b) ← scalar args[5]!
    if value == 0 then abort (.unsupported source "division by zero is unsupported")
    let k := value.num.natAbs
    charge .coefficientBits (a.denominator.log2 + k.log2 + 2)
    let num := realMul (if value < 0 then realNeg a.numerator else a.numerator)
      (realNat value.den)
    let divisorProof ← mkAppM
      (if value < 0 then ``Denominator.negative else ``Denominator.natural) #[b.proof]
    let proof ← mkAppM (if value < 0 then ``Denominator.div_neg else ``Denominator.div_pos)
      #[a.proof, divisorProof, ← positive k]
    return ⟨num, a.denominator * k, proof⟩
  if op == some ``OfNat.ofNat || op == some ``Int.cast || op == some ``Nat.cast ||
      op == some ``Rat.cast || op == some ``RatCast.ratCast || op == some ``OfScientific.ofScientific then
    if e.hasFVar || e.hasMVar then
      abort (.unsupported source "scalar casts must contain literal coefficients")
    return (← scalar e).2
  abort (.unsupported source "unsupported polynomial expression")

end Hex.RealFormula.Reify
