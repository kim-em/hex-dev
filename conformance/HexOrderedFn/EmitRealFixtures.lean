/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexOrderedFn.Tests
import Lean.Data.Json

open Hex Hex.OrderedFn Hex.OrderedFn.Oracle Lean

namespace Hex.OrderedFn.EmitReal

private def rational (q : Rat) : Json := .arr #[toJson q.num, toJson q.den]
private def bounds (b : Bounds) : Json := .arr #[rational b.lower, rational b.upper]
private def signJson : Option Int → Json
  | none => .null
  | some s => toJson s
private def boundsJson : Option Bounds → Json
  | none => .null
  | some b => bounds b

/-- Source syntax remains available independently of canonical cancellation. -/
private inductive Expr where
  | rat : Rat → Expr
  | x : Expr
  | sub : Expr → Expr → Expr
  | div : Expr → Expr → Expr
  | pow : Expr → Nat → Expr

private def Expr.eval : Expr → RationalFn Rat
  | .rat q => RationalFn.C q
  | .x => RationalFn.X
  | .sub a b => a.eval - b.eval
  | .div a b => a.eval / b.eval
  | .pow a n => a.eval ^ n

private def Expr.json : Expr → Json
  | .rat q => .arr #[toJson "rat", rational q]
  | .x => .arr #[toJson "x"]
  | .sub a b => .arr #[toJson "sub", a.json, b.json]
  | .div a b => .arr #[toJson "div", a.json, b.json]
  | .pow a n => .arr #[toJson "pow", a.json, toJson n]

/-- Original divisor checks precede normalization, including cancelled divisors. -/
private def Expr.at? (q : Rat) : Expr → Option Rat
  | .rat c => some c
  | .x => some q
  | .sub a b => return (← a.at? q) - (← b.at? q)
  | .div a b => do
    let x ← a.at? q
    let y ← b.at? q
    if y = 0 then none else some (x / y)
  | .pow a n => return (← a.at? q) ^ n

private def emit (name : String) (q : Rat) (joint : Bool) (expression : Expr)
    (n : Nat) : IO Unit := do
  let f := expression.eval
  let a : Approximation Rat :=
    ⟨fun c δ => if joint then Tests.window c δ else .singleton c, Tests.window q⟩
  let δ := Real.precision n
  let nb := Real.enclose a f.num δ
  let db := Real.enclose a f.den δ
  let trial := Real.attempt a f n
  let total := match ht : Real.attempt a f n with
    | none => Json.null
    | some s => toJson (Real.sign a f (acc_of_success _ n s ht 0 (by omega)))
  let approximation := Real.approxAttempt a f (1/16) n
  let totalApprox := match ht : Real.approxAttempt a f (1/16) n with
    | none => Json.null
    | some b => bounds (Real.approx a f (1/16)
        (by
          rw [Real.requestWidth_of_pos (δ := 1/16) (by decide +kernel)]
          exact acc_of_success _ n b ht 0 (by omega)))
  let record := Json.mkObj [
    ("kind", toJson "ordered-fn-real"), ("lib", toJson "HexOrderedFn"),
    ("case", toJson s!"{name}/{n}"), ("subject", rational q),
    ("expression", expression.json),
    ("source_regular", toJson (expression.at? q).isSome),
    ("guarded_sign", signJson (if (expression.at? q).isSome then Real.finiteAttempt a f n else none)),
    ("joint", toJson joint), ("precision", toJson n), ("request", rational δ),
    ("num", .arr (f.num.coeffs.map rational)), ("den", .arr (f.den.coeffs.map rational)),
    ("coeff_num", .arr (f.num.coeffs.map (fun c => bounds (a.coeff c δ)))),
    ("coeff_den", .arr (f.den.coeffs.map (fun c => bounds (a.coeff c δ)))),
    ("constant", bounds (a.constant δ)), ("num_bound", bounds nb), ("den_bound", bounds db),
    ("attempt", signJson trial), ("finite", signJson (Real.finiteAttempt a f n)),
    ("total_sign", total), ("approx_request", rational (1/16)),
    ("approx_attempt", boundsJson approximation), ("total_approx", totalApprox)]
  (← IO.getStdout).putStrLn record.compress

def run : IO Unit := do
  let linear (c : Rat) := Expr.sub .x (.rat c)
  for (name, q, f) in #[
      ("positive", (2 : Rat), linear 1),
      ("negative-denominator", 2, .div (linear 1) (linear 3)),
      ("pole", 2, .div (.rat 1) (linear 2)),
      ("cancelled-pole", 2, .div (linear 2) (linear 2)),
      ("near-zero", 2, linear (127/64)),
      ("zero", 2, .sub .x .x),
      ("non-dyadic", 1/3, linear (1/4)),
      ("degree", 3/2, .sub (.sub (.pow .x 4) (.pow .x 2)) (.rat 1)),
      ("quotient", 3/2, .div (.sub (.pow .x 2) (.rat 2)) (.sub (.pow .x 2) (.rat 3)))] do
    for joint in [false, true] do
      for n in [0, 1, 2, 4, 8, 12] do
        emit s!"{name}/{joint}" q joint f n

end Hex.OrderedFn.EmitReal

def main : IO Unit := Hex.OrderedFn.EmitReal.run
