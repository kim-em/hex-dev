/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyMathlib.Literal
public meta import HexPolyMathlib.Literal
public meta import Lean.Elab.Tactic.Basic

open Polynomial HexPolyMathlib Lean Elab Tactic

elab "check_poly_literal" : tactic => withMainContext do
  let some (_, lhs, _) := (← getMainTarget).eq? | throwError "expected equality"
  let p ← HexPolyMathlib.Literal.recognize lhs
  closeMainGoal `check_poly_literal p.proof

theorem rationalLiteral : (X ^ 2 - C (1 / 2) * X + C (3 / 7) : Polynomial ℚ) =
    polynomialOfList [3 / 7, -1 / 2, 1] := by check_poly_literal

theorem factoredLiteral : ((X - C (1 / 2)) * (X + C (1 / 2)) : Polynomial ℚ) =
    polynomialOfList [-1 / 4, 0, 1] := by check_poly_literal

example : (0 : Polynomial ℚ) = polynomialOfList [0] := by check_poly_literal
example : (1 : Polynomial ℚ) = polynomialOfList [1] := by check_poly_literal

/-- error: polynomial literal exceeds the coefficient budget of 1024 -/
#guard_msgs in
example : ((X ^ 64) ^ 64 : Polynomial ℚ) = polynomialOfList (List.replicate 4096 0 ++ [1]) := by
  check_poly_literal

/-- info: '_private.HexPolyMathlib.LiteralTests.0.rationalLiteral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rationalLiteral
/-- info: '_private.HexPolyMathlib.LiteralTests.0.factoredLiteral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms factoredLiteral
