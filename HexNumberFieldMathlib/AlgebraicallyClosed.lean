/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberFieldMathlib.Algebraic
public import HexNumberFieldMathlib.Polynomial
public import HexNumberFieldMathlib.AlgebraicRoots
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public section

/-! Algebraic closedness follows from completeness of the executable root solver. -/
namespace Hex.AlgebraicNumber

/-- Canonical algebraic numbers form an algebraically closed field. -/
instance instIsAlgClosed : IsAlgClosed AlgebraicNumber := by
  apply IsAlgClosed.of_exists_root
  intro p _ hp
  let f := AlgebraicPoly.ofPolynomial p
  have hf : f.toPolynomial = p.map toComplexHom := AlgebraicPoly.toPolynomial_ofPolynomial p
  have hd : 0 < f.toPolynomial.degree := by
    rw [hf, Polynomial.degree_map]
    exact Polynomial.degree_pos_of_irreducible hp
  obtain ⟨z, hz⟩ := Complex.exists_root hd
  have hm := (AlgebraicPoly.contains_roots_iff f z).mpr hz
  cases hroots : f.roots with
  | all =>
    have hfzero := (AlgebraicPoly.roots_all_iff f).mp hroots
    have hne : p.map toComplexHom ≠ 0 := Polynomial.map_ne_zero hp.ne_zero
    exact False.elim (hne (hf.symm.trans hfzero))
  | finite entries =>
    rw [hroots] at hm
    obtain ⟨r, _, hr⟩ := hm
    refine ⟨r.root.exact, toComplex_injective ?_⟩
    change toComplexHom (p.eval r.root.exact) = toComplexHom 0
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← hf]
    change f.toPolynomial.eval r.root.exact.toComplex = 0
    rwa [AlgebraicRoot.exact_toComplex, hr]

/-- This executable field is an algebraic closure of the rationals. -/
instance instIsAlgClosure : IsAlgClosure ℚ AlgebraicNumber where
  isAlgClosed := inferInstance
  isAlgebraic := inferInstance

/-- info: 'Hex.AlgebraicNumber.instIsAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instIsAlgClosed

example : IsAlgClosure ℚ AlgebraicNumber := inferInstance

end Hex.AlgebraicNumber
