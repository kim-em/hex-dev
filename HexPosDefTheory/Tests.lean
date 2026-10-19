/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDefTheory.Tactic
public import HexPosDefTheory.Completeness
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! Closed positivity and refutation examples, including direct Cartan expressions. -/

open Matrix
open scoped ComplexOrder

example : (CartanMatrix.E 6).PosDef := by pos_def
example : (CartanMatrix.E 7).PosDef := by pos_def
public theorem posDefE8 : (CartanMatrix.E 8).PosDef := by pos_def
example : (CartanMatrix.E 8).PosDef := by pos_def (method := .positiveVector)
example : ¬ (CartanMatrix.E 9).PosDef := by pos_def
example : ¬ (CartanMatrix.E 10).PosDef := by pos_def

example : ∃ d : Fin 8 → ℤ, (∀ i, 0 < d i) ∧
    (Matrix.diagonal d * CartanMatrix.E 8).PosDef := by
  refine ⟨fun _ => 1, by simp, ?_⟩
  simpa using (show (CartanMatrix.E 8).PosDef from by pos_def)

example : (Matrix.of fun (_ _ : Fin 0) => (0 : ℤ)).PosDef := by pos_def
example : (!![(3 : ℤ)]).PosDef := by pos_def
example : ¬ (!![(0 : ℤ)]).PosDef := by pos_def
example : (!![(2 : ℤ), 1, 1; 1, 2, 1; 1, 1, 2]).PosDef := by pos_def
example : (!![(1 / 2 : ℚ), 1 / 3; 1 / 3, 2 / 5]).PosDef := by pos_def
public theorem posDefReal : (!![(1 / 2 : ℝ), 1 / 3; 1 / 3, 2 / 5]).PosDef := by pos_def
example : (Matrix.ofArray #[(2 : ℤ), -1, -1, 2] rfl : Matrix (Fin 2) (Fin 2) ℤ).PosDef := by pos_def
example : (!![(1 / 2 : ℂ), Complex.I / 3; -Complex.I / 3, 2 / 5]).PosDef := by
  pos_def
public theorem posDefComplex : (!![(2 : ℂ), Complex.I; -Complex.I, 2]).PosDef := by pos_def
public theorem notPosDefComplex : ¬ (!![(1 : ℂ), Complex.I; -Complex.I, 1]).PosDef := by pos_def
example : ¬ (!![(1 : ℂ), 2 * Complex.I; -2 * Complex.I, 1]).PosDef := by pos_def
example : ¬ (!![(2 : ℂ), Complex.I; Complex.I, 2]).PosDef := by pos_def
example : (!![(2 : ℂ), -1; -1, 2]).PosDef := by pos_def (method := .positiveVector)

/-- error: pos_def: the matrix has a checked positive certificate -/
#guard_msgs in
example : ¬ (!![(1 : ℤ)]).PosDef := by pos_def

/-- error: pos_def: declined: the positive-vector method accepts positive goals only -/
#guard_msgs in
example : ¬ (!![(0 : ℤ)]).PosDef := by pos_def (method := .positiveVector)

/-- error: pos_def: declined: the matrix has no accepted positive-vector certificate from the solve -/
#guard_msgs in
example : (!![(2 : ℤ), 1; 1, 2]).PosDef := by pos_def (method := .positiveVector)

/-- info: 'posDefE8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms posDefE8

/-- info: 'posDefComplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms posDefComplex

example : (!![(2 : ℂ), Complex.I; -Complex.I, 2]).PosDef := by
  fail_if_success pos_def (method := .positiveVector)
  pos_def

example : ¬ (!![(0 : ℤ)]).PosDef := by
  fail_if_success have : (!![(0 : ℤ)]).PosDef := by pos_def
  pos_def

/-- info: 'Hex.PosDefTheory.Int.certify_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PosDefTheory.Int.certify_complete

/-- info: 'Hex.PosDefTheory.Gaussian.certify_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PosDefTheory.Gaussian.certify_complete

/-- error: pos_def: not applicable: expected `A.PosDef` or `¬ A.PosDef` -/
#guard_msgs in
example : True := by pos_def

/-- error: pos_def: not applicable: the matrix must be closed -/
#guard_msgs in
example (A : Matrix (Fin 1) (Fin 1) Int) : A.PosDef := by pos_def

/-- error: pos_def: not applicable: unsupported carrier ℤ × ℤ -/
#guard_msgs in
example : (!![((1, 1) : Int × Int)]).PosDef := by pos_def

/-- error: pos_def: declined: entry quotation: entry (0, 0) over ℝ: √2: no norm_nums apply -/
#guard_msgs in
example : (!![(Real.sqrt 2 : Real)]).PosDef := by pos_def

/-- error: pos_def: the matrix has a checked refutation: Hex.PosDef.NegativeCert.nonpositive [1] -/
#guard_msgs in
example : (!![(0 : Int)]).PosDef := by pos_def

/-- info: 'posDefReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms posDefReal

/-- info: 'notPosDefComplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms notPosDefComplex

example : (!![(2 : Int), 0, -1, 0, 0, 0, 0, 0;
  0, 2, 0, -1, 0, 0, 0, 0;
  -1, 0, 2, -1, 0, 0, 0, 0;
  0, -1, -1, 2, -1, 0, 0, 0;
  0, 0, 0, -1, 2, -1, 0, 0;
  0, 0, 0, 0, -1, 2, -1, 0;
  0, 0, 0, 0, 0, -1, 2, -1;
  0, 0, 0, 0, 0, 0, -1, 2]).PosDef := by pos_def

example : (!![(⌊(5 / 2 : Real)⌋ : Int)]).PosDef := by pos_def
example : (Matrix.of fun i j : Fin 2 => if (i.val : Real) = (j.val : Real) then (2 : Int) else 0).PosDef := by
  pos_def

example : (!![(⌊(5 / 2 : Real)⌋ : Rat)]).PosDef := by pos_def

/-- error: pos_def: declined: entry quotation: entry (0, 0) over ℂ: √2: no norm_nums apply -/
#guard_msgs in
example : (!![((Real.sqrt 2 : Real) : Complex)]).PosDef := by pos_def
