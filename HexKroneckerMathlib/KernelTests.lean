/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import HexKroneckerMathlib

open Hex.Kronecker

set_option maxRecDepth 4096

-- Index validity is required even in a subtree erased by a zero power.
example : Kernel.exprEq 0 (.pow (.atom 0) 0) (.int 1) = false := by decide +kernel
example : Kernel.exprEq 1 (.mul (.pow (.atom 0) 8) (.int 0)) (.int 0) = true := by decide +kernel
example : Kernel.exprEq 1 (.atom 0) (.int 1) = false := by decide +kernel
example : Kernel.exprEqPlan 1 (.atom 0) (.int 1) [0] 4 = false := by decide +kernel
example : Kernel.exprEqPlan 1 (.atom 0) (.int 1) [1] 0 = false := by decide +kernel
example : Kernel.exprEqPlan 1 (.add (.atom 0) (.atom 0)) (.mul (.int 2) (.atom 0)) [1] 4 = true := by
  decide +kernel

-- Ordinary term streams need shape validation, but need not be normalized.
example : Kernel.termsEq 1 [([1],1),([1],1)] [([1],2)] = true := by decide +kernel
example : Kernel.termsEq 1 [([],1)] [([0],1)] = false := by decide +kernel
example : Kernel.termsEq 1 [([1],1)] [([0],1)] = false := by decide +kernel

-- Integer quotient equality, rather than equality of integers modulo the base.
example : Kernel.exprEqMod 0 2 (.add (.int 1) (.int 1)) (.int 0) [([],1)] = true := by
  decide +kernel
example : Kernel.exprEqMod 0 2 (.add (.int 1) (.int 1)) (.int 0) [] = false := by decide +kernel
example : Kernel.termsEqMod 0 2 [([],1),([],1)] [] [([],1)] = true := by decide +kernel
example : Kernel.termsEqMod 0 0 [] [] [] = false := by decide +kernel
example : Kernel.termsEqMod 0 2 [([],2)] [] [([],1)] = false := by decide +kernel

private def x : Hex.MvPoly.Kernel.PolyList Int := [([1],1)]
private def x2 : Hex.MvPoly.Kernel.PolyList Int := [([2],1)]
private def one : Hex.MvPoly.Kernel.PolyList Int := [([0],1)]

-- Product degrees must add before the common box is formed.
example : Kernel.mulTerms .plain 1 1 1 1 [[x]] [[x]] [[x2]] = true := by decide +kernel
example : Kernel.mulTerms .plain 1 1 1 1 [[x]] [[x]] [[one]] = false := by decide +kernel
example : Kernel.mulTerms .plain 1 1 1 1 [[x]] [[]] [[x2]] = false := by decide +kernel
example : Kernel.mulTerms .plain 0 0 0 0 [] [] [] = true := by decide +kernel
example : Kernel.mulTerms .signedPacked 1 1 1 1 [[x]] [[x]] [[x2]] 16 32 = true := by decide +kernel
example : Kernel.mulTerms .signedPacked 1 1 1 1 [[x]] [[x]] [[x2]] 1 1 = false := by decide +kernel

-- Characteristic-two dot product [1,1] * [1,1]ᵀ has quotient 1.
example : Kernel.mulTermsMod .plain 1 1 2 1 2 [[one,one]] [[one],[one]] [[[]]] [[one]] = true := by
  decide +kernel
example : Kernel.mulTermsMod .plain 1 1 2 1 2 [[one,one]] [[one],[one]] [[[]]] [[[]]] = false := by
  decide +kernel
example : Kernel.mulTermsMod .signedPacked 1 1 2 1 2 [[one,one]] [[one],[one]] [[[]]] [[one]] 8 16 = true := by
  decide +kernel

-- Bit-length guards retain exact reports, including zero-budget boundaries,
-- cancellation, exceptional descendants, and powers with huge exponents.
example (b : Budget) (k : Nat) (l r : Expr) :
    Preflight.exprEq b k l r = sizeExprEq b k l r := Preflight.exprEq_eq b k l r
#guard Preflight.clip 0 0 == 0
#guard Preflight.clip 0 1 == 1
#guard Preflight.mul 4 3 5 == 15
#guard Preflight.mul 4 3 6 == 16
#guard Preflight.mul 4 0 1000000000 == 0
#guard Preflight.pow 4 0 0 == 1
#guard Preflight.pow 4 1 1000000000 == 1
#guard Preflight.pow 4 2 1000000000 == 16

/-- info: 'Hex.Kronecker.Kernel.exprEq_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Kronecker.Kernel.exprEq_sound
/-- info: 'Hex.Kronecker.Kernel.exprEqPlan_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Kronecker.Kernel.exprEqPlan_sound
/-- info: 'Hex.Kronecker.Kernel.termsEq_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Kronecker.Kernel.termsEq_sound
/-- info: 'Hex.Kronecker.Kernel.exprEqMod_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Kronecker.Kernel.exprEqMod_sound
/-- info: 'Hex.Kronecker.Kernel.termsEqMod_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Kronecker.Kernel.termsEqMod_sound
/-- info: 'Hex.Kronecker.Kernel.mulTerms_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Kronecker.Kernel.mulTerms_sound
/-- info: 'Hex.Kronecker.Kernel.mulTermsMod_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Kronecker.Kernel.mulTermsMod_sound
/-- info: 'Hex.Kronecker.Preflight.exprEq_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Kronecker.Preflight.exprEq_eq
