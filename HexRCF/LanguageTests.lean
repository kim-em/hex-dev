/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Language

public section

/-!
# Tests for the reflected RCF language

These examples exercise every comparison, Boolean connective, and sentence
constructor through the public semantics.
-/

namespace Hex.RCF.Tests

open Hex.RCF

/-- The atom `0 = 0`. -/
def zeroEq : Atom := ⟨0, .eq⟩

/-- The atom `0 ≠ 0`. -/
def zeroNe : Atom := ⟨0, .ne⟩

/-- The real evaluation of the executable zero polynomial is zero. -/
theorem eval_zero (x : ℝ) :
    Polynomial.aeval x (HexPolyZMathlib.toPolynomial (0 : ZPoly)) = 0 := by
  rw [HexPolyZMathlib.toPolynomial_zero]
  simp

example : Cmp.lt.toProp (1 : ℝ) 2 := by norm_num [Cmp.toProp]
example : Cmp.le.toProp (1 : ℝ) 1 := by norm_num [Cmp.toProp]
example : Cmp.eq.toProp (1 : ℝ) 1 := by norm_num [Cmp.toProp]
example : Cmp.ge.toProp (2 : ℝ) 1 := by norm_num [Cmp.toProp]
example : Cmp.gt.toProp (2 : ℝ) 1 := by norm_num [Cmp.toProp]
example : Cmp.ne.toProp (1 : ℝ) 2 := by norm_num [Cmp.toProp]

example (p : ZPoly) (x : ℝ) :
    (Atom.mk p .gt).toProp x ↔
      0 < Polynomial.aeval x (HexPolyZMathlib.toPolynomial p) :=
  Iff.rfl

example : zeroEq.toProp 2 := by
  change Polynomial.aeval 2 (HexPolyZMathlib.toPolynomial (0 : ZPoly)) = 0
  exact eval_zero 2

example : (Formula.atom zeroEq |>.and (.not (.atom zeroNe)) |>.toProp) (1 / 2) := by
  simp only [Formula.toProp, zeroEq, zeroNe, Atom.toProp, Cmp.toProp]
  rw [eval_zero]
  simp

example : (Formula.not .ff).toProp 0 := by simp [Formula.toProp]
example : (Formula.or .ff .tt).toProp 0 := by simp [Formula.toProp]
example : (Formula.imp .ff .ff).toProp 0 := by simp [Formula.toProp]

example : (Sentence.forallReal (.atom zeroEq)).toProp := by
  simp only [Sentence.toProp, Formula.toProp]
  intro x
  change Polynomial.aeval x (HexPolyZMathlib.toPolynomial (0 : ZPoly)) = 0
  exact eval_zero x

example : (Sentence.existsReal (.atom zeroEq)).toProp := by
  simp only [Sentence.toProp, Formula.toProp]
  refine ⟨1, ?_⟩
  change Polynomial.aeval 1 (HexPolyZMathlib.toPolynomial (0 : ZPoly)) = 0
  exact eval_zero 1

example : (Sentence.forallIoc (Dyadic.ofInt 0) (Dyadic.ofInt 1) .tt).toProp := by
  simp [Sentence.toProp, Formula.toProp]

example : (Sentence.existsIoc (Dyadic.ofInt 0) (Dyadic.ofInt 1) (.atom zeroEq)).toProp := by
  simp only [Sentence.toProp, Formula.toProp]
  refine ⟨1, ?_, ?_⟩
  · rw [HexRealRootsMathlib.toReal_ofInt, HexRealRootsMathlib.toReal_ofInt]
    norm_num [Set.mem_Ioc]
  · change Polynomial.aeval 1 (HexPolyZMathlib.toPolynomial (0 : ZPoly)) = 0
    exact eval_zero 1

/-- Reversed endpoints make the half-open interval empty. -/
example : (Sentence.forallIoc (Dyadic.ofInt 1) (Dyadic.ofInt 0) .ff).toProp := by
  simp only [Sentence.toProp, Formula.toProp]
  intro x hx
  have hle : HexRealRootsMathlib.Dyadic.toReal (Dyadic.ofInt 1) ≤
      HexRealRootsMathlib.Dyadic.toReal (Dyadic.ofInt 0) :=
    le_trans (le_of_lt hx.1) hx.2
  rw [HexRealRootsMathlib.toReal_ofInt, HexRealRootsMathlib.toReal_ofInt] at hle
  norm_num at hle

end Hex.RCF.Tests
