/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SelectedRoot
public import HexRealAlgebraicMathlib.IntegerRoots
public import HexRealAlgebraicMathlib.Field
public import HexSturmMathlib.Rational
public import HexRealRootsMathlib.Drivers

public section

namespace Hex.RealClosure

/-- Every checked rational selected root has the value of a canonical real
algebraic number. Denominator clearing and the existing integer root list
handle reducible rational defining polynomials. -/
theorem Root.exists_canonical {context : Nat} (d : Root context) :
    ∃ a : Hex.RealAlgebraicNumber,
      a ∈ (Hex.ZPoly.clearDenominators d.raw.head).2.realAlgebraicRoots ∧
      a.toReal = d.real := by
  let p := (Hex.ZPoly.clearDenominators d.raw.head).2
  have hvalue : (realPoly d.raw.head).eval d.real = 0 := by
    simpa using Expression.denote_head (d := d)
  have hscale : (HexRealRootsMathlib.toPolyℝ p) =
      Polynomial.C ((Hex.ZPoly.clearDenominators d.raw.head).1 : ℝ) *
        realPoly d.raw.head := by
    exact HexSturmMathlib.toPolyℝ_clearDenominators d.raw.head
  have hne : HexRealRootsMathlib.toPolyℝ p ≠ 0 := by
    rw [hscale]
    apply mul_ne_zero
    · exact Polynomial.C_ne_zero.mpr (by
        exact_mod_cast ne_of_gt (Hex.ZPoly.clearDenominators_pos d.raw.head))
    · exact d.head_ne_zero ratCast ratZero
  have hp : p ≠ 0 := by
    intro hz
    apply hne
    simp [hz]
  have hroot : (HexRealRootsMathlib.toPolyℝ p).IsRoot d.real := by
    rw [Polynomial.IsRoot.def, hscale, Polynomial.eval_mul, hvalue, mul_zero]
  have hcomplex : (HexRootsMathlib.toPolyℂ p).IsRoot (d.real : ℂ) :=
    HexRealRootsMathlib.isRoot_toPolyℂ (p := p) hroot
  obtain ⟨a, hmem, ha⟩ :=
    (Hex.ZPoly.mem_algebraicRoots_iff p hp (d.real : ℂ)).mpr hcomplex
  have hreal : a.isReal = true := by
    rw [Hex.AlgebraicNumber.isReal_iff, ha]
    simp
  let b := Hex.RealAlgebraicNumber.ofAlgebraic a hreal
  refine ⟨b, ?_, ?_⟩
  · apply (Hex.ZPoly.mem_realAlgebraicRoots p b).mpr
    change a ∈ p.algebraicRoots
    exact Array.mem_toList_iff.mp hmem
  · change a.toComplex.re = d.real
    rw [ha]
    simp

/-- A semantic canonical witness for the selected root. The executable
conversion still has to select the matching entry of the finite root list. -/
noncomputable def Root.canonical {context : Nat} (d : Root context) :
    Hex.RealAlgebraicNumber := d.exists_canonical.choose

theorem Root.canonical_real {context : Nat} (d : Root context) :
    d.canonical.toReal = d.real := d.exists_canonical.choose_spec.2

theorem Root.canonical_mem {context : Nat} (d : Root context) :
    d.canonical ∈ (Hex.ZPoly.clearDenominators d.raw.head).2.realAlgebraicRoots :=
  d.exists_canonical.choose_spec.1

namespace Expression

/-- Interpret a rational expression with the existing canonical algebraic
field operations at the matching selected root. -/
noncomputable def canonicalValue {context : Nat} {d : Root context}
    (a : Expression d) : Hex.RealAlgebraicNumber :=
  (HexPolyMathlib.toPolynomial a.polynomial).eval₂
    (algebraMap Rat Hex.RealAlgebraicNumber) d.canonical

/-- The canonical arithmetic and checked selected-root expression have the
same real interpretation, even for a reducible defining polynomial. -/
theorem canonicalValue_real {context : Nat} {d : Root context}
    (a : Expression d) : a.canonicalValue.toReal = a.denote := by
  have hpoly : realPoly a.polynomial =
      (HexPolyMathlib.toPolynomial a.polynomial).map (Rat.castHom ℝ) := by
    ext i
    simp [realPoly, ratCast]
  have hcomp : Hex.RealAlgebraicNumber.toRealHom.comp
      (algebraMap Rat Hex.RealAlgebraicNumber) = Rat.castHom ℝ := by
    ext q
    simp [Hex.RealAlgebraicNumber.toRealHom]
  change Hex.RealAlgebraicNumber.toRealHom
      ((HexPolyMathlib.toPolynomial a.polynomial).eval₂
        (algebraMap Rat Hex.RealAlgebraicNumber) d.canonical) = _
  rw [Polynomial.hom_eval₂, hcomp]
  rw [show Hex.RealAlgebraicNumber.toRealHom d.canonical = d.real from d.canonical_real]
  simp [denote, hpoly, Polynomial.eval_map]

theorem canonicalValue_add {context : Nat} {d : Root context}
    (a b : Expression d) :
    (add a b).canonicalValue = a.canonicalValue + b.canonicalValue := by
  apply Hex.RealAlgebraicNumber.toReal_injective
  simp only [canonicalValue_real, denote_add, Hex.RealAlgebraicNumber.add_toReal]

theorem canonicalValue_mul {context : Nat} {d : Root context}
    (a b : Expression d) :
    (mul a b).canonicalValue = a.canonicalValue * b.canonicalValue := by
  apply Hex.RealAlgebraicNumber.toReal_injective
  simp only [canonicalValue_real, denote_mul, Hex.RealAlgebraicNumber.mul_toReal]

theorem canonicalValue_inverse? {context : Nat} {d : Root context}
    (a b : Expression d) (h : a.inverse? = .ok (some b)) :
    b.canonicalValue = a.canonicalValue⁻¹ := by
  apply Hex.RealAlgebraicNumber.toReal_injective
  rw [canonicalValue_real, Hex.RealAlgebraicNumber.inv_toReal, canonicalValue_real]
  exact eq_inv_of_mul_eq_one_right (inverse?_sound a b h)

end Expression

end Hex.RealClosure

/- The inherited `sorryAx` is `HexRealRootsMathlib.Tarski.check_rootSum` (#10389). -/
/-- info: 'Hex.RealClosure.Root.exists_canonical' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Root.exists_canonical
/-- info: 'Hex.RealClosure.Expression.canonicalValue_inverse?' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Expression.canonicalValue_inverse?
