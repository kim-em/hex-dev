/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexKroneckerMathlib
import HexKroneckerMathlib.Residue
import Mathlib.Data.ZMod.Basic

theorem cubeUniform {R : Type*} [CommRing R] (x y : R) :
    (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 := by
  kronecker

example (x y : ℚ) : (x+y)^3 = x^3+3*x^2*y+3*x*y^2+y^3 := by kronecker
example (x y : ℤ) : (x+y)^3 = x^3+3*x^2*y+3*x*y^2+y^3 := by kronecker
example (x y : ZMod 7) : (x+y)^3 = x^3+3*x^2*y+3*x*y^2+y^3 := by kronecker

example {R : Type*} [CommRing R] (x y : R) : (x+y)^2 = x^2+2*x*y+y^2 :=
  kronecker% ((x+y)^2 = x^2+2*x*y+y^2)

/-- error: kronecker: goal is not a polynomial identity in the sealed atoms -/
#guard_msgs in
example (x : ZMod 7) : x^7 = x := by kronecker

/-- error: kronecker declined: dense box requires at least 2 digits and 8 packed bits (limits 1 digits, 16777216 bits); per-atom degree bounds [2] -/
#guard_msgs in
example (x : ℤ) : x^2 = x*x := by kronecker (config := { maxDenseDigits := 1 })

#guard HexKroneckerMathlib.fromGrind? 1 (.var 1) |>.isNone
#guard HexKroneckerMathlib.fromGrind? 1 (.var 0) |>.isSome

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

theorem frobeniusSeven {R : Type*} [CommRing R] [CharP R 7] (x : R) :
    (x+1)^7 = x^7+1 := by
  let l : Hex.Kronecker.Expr := .pow (.add (.atom 0) (.int 1)) 7
  let r : Hex.Kronecker.Expr := .add (.pow (.atom 0) 7) (.int 1)
  let q : Hex.MvPoly.Kernel.PolyList Int :=
    [([6],1),([5],3),([4],5),([3],5),([2],3),([1],1)]
  have hc : Hex.Kronecker.checkExprEqMod ⟨65536,4096⟩ 1 7 l r q = true := by decide +kernel
  have hs := Hex.Kronecker.checkExprEqMod_sound hc (fun _ => x)
  simpa only [l, r, Hex.Kronecker.Expr.denote, Int.cast_one] using hs

#print axioms cubeUniform
#print axioms frobeniusSeven
#print axioms Hex.Kronecker.checkExprEq_sound
#print axioms Hex.Kronecker.checkTermsEq_sound
#print axioms Hex.Kronecker.checkMulTerms_sound
#print axioms Hex.Kronecker.checkExprEqMod_sound
#print axioms Hex.Kronecker.checkTermsEqMod_sound
#print axioms Hex.Kronecker.checkMulTermsMod_sound

-- A huge literal exponent still takes logarithmically many kernel multiplications.
example : Hex.Kronecker.checkExprEq ⟨65536,16⟩ 0
    (.pow (.int 1) 1000000000) (.int 1) = true := by
  decide +kernel
