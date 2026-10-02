/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealFormulaMathlib.Reify.Arithmetic
import Mathlib.Lean.Elab.Tactic.Meta
import Lean.Elab.Command

/-! Kernel-checked arithmetic views, including signed rational denominators. -/

open Lean Meta Qq Hex.RealFormula Hex.RealFormula.Reify

private meta def checkView (coords : Array Expr) (e : Expr) (den : Nat) : MetaM Unit := do
  let result ← ((arithmetic coords e).run { config := {}, budget := .ofBudget Hex.Reflect.Budget.default }).run
  let .ok (a, _) := result | throwError "arithmetic view unexpectedly declined: {e}"
  unless a.denominator == den do
    throwError "denominator {a.denominator}, expected {den}"
  let e : Q(ℝ) := e
  let d : Q(ℝ) := realNat den
  let p : Q(ℝ) := a.numerator
  unless ← isDefEq (← inferType a.proof) q($e * $d = $p) do
    throwError "incorrect arithmetic proof statement"
  check a.proof

run_meta do
  checkView #[] q((3 : ℝ)) 1
  checkView #[] q((3 : ℝ) / -2) 2
  checkView #[] q((1 : ℝ) / (3 / 2)) 3
  checkView #[] q(((1 : ℝ) / 2 + 1 / 3) ^ 4) (6 ^ 4)
  withLocalDeclD `x q(ℝ) fun x => do
    let x : Q(ℝ) := x
    checkView #[x] q(($x / 2 - 3 / 4) * ($x + 1)) 8
    checkView #[x] q($x / (-2 / 3)) 2
    let .error (.unsupported _ _) ←
      ((arithmetic #[x] q(1 / $x)).run { config := {}, budget := .ofBudget Hex.Reflect.Budget.default }).run
      | throwError "symbolic divisor was accepted"
    pure ()

run_meta do
  let .error (.unsupported _ _) ←
    ((arithmetic #[] q((1 : ℝ) / 0)).run { config := {}, budget := .ofBudget Hex.Reflect.Budget.default }).run
    | throwError "zero divisor was accepted"
  pure ()
