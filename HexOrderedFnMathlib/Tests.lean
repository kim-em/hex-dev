/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFnMathlib.Real
public import HexOrderedFn.Tests
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith

open Hex Hex.OrderedFn Hex.OrderedFn.Oracle
open Hex.OrderedFn.Tests (source window)

public section

namespace Hex.OrderedFn.SemanticTests

attribute [local instance 2000] Field.toGrindField

-- Share the computational polynomial input, but form a separate fraction under
-- the companion's fixed field dictionary. The core fractions have a different type.
def linear (q : Rat) : RationalFn Rat := RationalFn.ofPoly (Tests.linearPoly q)

theorem separated : Real.attempt (source 2) (linear (31/16)) 4 = some 1 := by decide +kernel

def totalSign : Int := Real.sign (source 2) (linear (31/16))
  (acc_of_success _ 4 1 separated 0 (by decide))

theorem narrow : Real.approxAttempt (source 2) (linear 1) (1/16) 4 =
    some ⟨31/32, 33/32, by norm_num⟩ := by decide +kernel

def totalApprox : Bounds := Real.approx (source 2) (linear 1) (1/16)
  (by
    rw [Real.requestWidth_of_pos (δ := 1/16) (by decide +kernel)]
    exact acc_of_success _ 4 _ narrow 0 (by decide))

def coarseApprox : Bounds := Real.approx (source 2) (linear 1) 0
  (acc_of_success _ 0 Tests.coarseBounds (by decide +kernel) 0 (by decide))

theorem window_contains (q δ : Rat) : Contains (window q δ) (q : ℝ) := by
  unfold window
  split
  next h =>
    have : (0 : ℝ) < δ := by exact_mod_cast h
    simp only [Contains, Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]
    constructor <;> linarith
  next h => exact Contains.singleton q

theorem source_correct (q : Rat) : ApproximationCorrect (Rat.castHom ℝ) (q : ℝ) (source q) :=
  .ofConstant _ _ (fun δ _ => window_contains q δ)

theorem source_width (q : Rat) : ApproximationWidth (source q) :=
  .ofConstant _ (by
    intro δ hδ
    simp only [window, dite_eq_left hδ, Bounds.width]
    linarith)

-- Ordinary theorem application checks a sign whose progress theorem is opaque.
theorem totalSign_correct : totalSign = 1 :=
  Real.sign_of_attempt (source_correct 2) _ _ separated

example : Contains totalApprox (Real.eval (Rat.castHom ℝ) 2 (linear 1)) :=
  Real.approx_contains (source_correct 2) _ _ _

example : totalApprox.width ≤ 1/16 := Real.approx_width _ _ _ _ (by decide +kernel)

example : Contains coarseApprox (Real.eval (Rat.castHom ℝ) 2 (linear 1)) :=
  Real.approx_contains (source_correct 2) _ _ _

example : coarseApprox.width ≤ 1 := Real.approx_width_le _ _ _ _

-- Containment cannot be reused for a different semantic subject.
example : ¬Contains (Bounds.singleton 2) (3 : ℝ) := by norm_num [Contains, Bounds.singleton]

def sqrtSource : Approximation Rat :=
  .ofConstant (fun _ => ⟨7/5, 3/2, by norm_num⟩)

theorem sqrt_correct : ApproximationCorrect (Rat.castHom ℝ) (Real.sqrt 2) sqrtSource where
  coeff c _ _ := Contains.singleton c
  constant δ _ := by
    change ((7/5 : Rat) : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ ((3/2 : Rat) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    constructor <;> nlinarith

example : Real.sign? sqrtSource (linear 1) 1 = some 1 := by decide +kernel
example : Real.sign? sqrtSource (linear 2) 1 = some (-1) := by decide +kernel
example : Real.sign? sqrtSource (RationalFn.ofPoly (DensePoly.ofList [-2, 0, 1])) 4 = none :=
  by decide +kernel

-- These are semantic conclusions from proved irrational containment, not a
-- false transcendental registration for the algebraic subject sqrt(2).
example : (1 : Int) = sgn (Real.eval (Rat.castHom ℝ) (Real.sqrt 2) (linear 1)) :=
  (Real.sign?_sound sqrt_correct _ 1 (by decide +kernel)).1

example : (-1 : Int) = sgn (Real.eval (Rat.castHom ℝ) (Real.sqrt 2) (linear 2)) :=
  (Real.sign?_sound sqrt_correct _ 1 (by decide +kernel)).1

-- Evaluating a cancelled formal fraction does not preserve an original divisor
-- premise at its root: source consumers must retain that premise themselves.
example : (Real.sqrt 2 - Real.sqrt 2) / (Real.sqrt 2 - Real.sqrt 2) ≠ (1 : ℝ) := by simp

/-- info: 'Hex.OrderedFn.Real.sign_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Real.sign_sound
/-- info: 'Hex.OrderedFn.Real.approx_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Real.approx_contains
/-- info: 'Hex.OrderedFn.Real.sign?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Real.sign?_sound
/-- info: 'Hex.OrderedFn.SemanticTests.totalSign_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms totalSign_correct

end Hex.OrderedFn.SemanticTests
