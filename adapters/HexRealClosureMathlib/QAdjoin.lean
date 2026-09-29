/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Element
public import HexRealClosure.QAdjoin
public import HexNumberFieldMathlib.Exact

public section

namespace Hex.RealClosure.Root.Handle

/-- Packing exact fixed-field coordinates preserves the chosen generator's
complex value and therefore its selected real embedding. -/
theorem packQAdjoin_complex {context : Nat} {d : Root context} (h : Root.Handle d)
    (c : Hex.QAdjoin h.canonical.toAlgebraic) :
    (h.packQAdjoin c).value.toAlgebraic.toComplex =
      c.toAlgebraicNumber.toComplex := by
  have source := Hex.PolyQuot.toAlgebraicNumber_toComplex
    (a := c) h.canonical.toAlgebraic.rep h.canonical.toAlgebraic.rep_mk
  have value := Hex.RealClosure.evalCanonical_real c.coeffs h.canonical
  rw [packQAdjoin, Hex.RealClosure.Element.ofPolyWith_eq,
    Hex.RealClosure.Element.ofPoly_value]
  rw [← h.canonical_eq]
  rw [← Hex.RealAlgebraicNumber.ofReal_toReal]
  rw [value]
  rw [Hex.QAdjoin.toAlgebraicNumber, source]
  change (((Hex.RealClosure.realPoly c.coeffs).eval h.canonical.toReal : ℝ) : ℂ) =
    (HexPolyMathlib.toPolynomial c.coeffs).eval₂ (algebraMap Rat ℂ)
      h.canonical.toAlgebraic.rep.root
  have mapped : (Hex.RealClosure.realPoly c.coeffs).map Complex.ofRealHom =
      (HexPolyMathlib.toPolynomial c.coeffs).map (algebraMap Rat ℂ) := by
    ext i
    simp [Hex.RealClosure.realPoly, Hex.RealClosure.ratCast]
  rw [Polynomial.eval₂_eq_eval_map, ← mapped]
  rw [show h.canonical.toAlgebraic.rep.root = (h.canonical.toReal : ℂ) from
    h.canonical.ofReal_toReal.symm]
  change Complex.ofRealHom ((Hex.RealClosure.realPoly c.coeffs).eval h.canonical.toReal) =
    ((Hex.RealClosure.realPoly c.coeffs).map Complex.ofRealHom).eval
      (Complex.ofRealHom h.canonical.toReal)
  exact (Polynomial.eval_map_apply _ _).symm

/-- The checked real conversion of the exact fixed-field result returns the
same real-algebraic value as the packed Hex element. -/
theorem packQAdjoin_checked {context : Nat} {d : Root context} (h : Root.Handle d)
    (c : Hex.QAdjoin h.canonical.toAlgebraic) :
    Hex.RealAlgebraicNumber.ofAlgebraic? c.toAlgebraicNumber =
      some (h.packQAdjoin c).value := by
  apply (Hex.RealAlgebraicNumber.ofAlgebraic?_eq_some _ _).2
  apply Hex.AlgebraicNumber.toComplex_injective
  exact (h.packQAdjoin_complex c).symm

/-- Fixed-field addition and packed addition have the same selected value. -/
theorem packQAdjoin_add {context : Nat} {d : Root context} (h : Root.Handle d)
    (a b : Hex.QAdjoin h.canonical.toAlgebraic) :
    (h.packQAdjoin (a + b)).value =
      (h.packQAdjoin a + h.packQAdjoin b).value := by
  apply Hex.RealAlgebraicNumber.ext
  apply Hex.AlgebraicNumber.toComplex_injective
  change (h.packQAdjoin (a + b)).value.toAlgebraic.toComplex =
    (Hex.RealClosure.Element.add (h.packQAdjoin a) (h.packQAdjoin b)).value.toAlgebraic.toComplex
  rw [Hex.RealClosure.Element.value_add,
    Hex.RealAlgebraicNumber.add_toAlgebraic,
    Hex.AlgebraicNumber.add_toComplex,
    h.packQAdjoin_complex, h.packQAdjoin_complex, h.packQAdjoin_complex]
  simpa only [Hex.QAdjoin.toAlgebraicNumber,
    Hex.PolyQuot.toAlgebraicNumber_toComplex] using
    Hex.PolyQuot.map_add a b h.canonical.toAlgebraic.rep
      h.canonical.toAlgebraic.rep_mk

/-- Fixed-field multiplication and packed multiplication have the same selected value. -/
theorem packQAdjoin_mul {context : Nat} {d : Root context} (h : Root.Handle d)
    (a b : Hex.QAdjoin h.canonical.toAlgebraic) :
    (h.packQAdjoin (a * b)).value =
      (h.packQAdjoin a * h.packQAdjoin b).value := by
  apply Hex.RealAlgebraicNumber.ext
  apply Hex.AlgebraicNumber.toComplex_injective
  change (h.packQAdjoin (a * b)).value.toAlgebraic.toComplex =
    (Hex.RealClosure.Element.mul (h.packQAdjoin a) (h.packQAdjoin b)).value.toAlgebraic.toComplex
  rw [Hex.RealClosure.Element.value_mul,
    Hex.RealAlgebraicNumber.mul_toAlgebraic,
    Hex.AlgebraicNumber.mul_toComplex,
    h.packQAdjoin_complex, h.packQAdjoin_complex, h.packQAdjoin_complex]
  simpa only [Hex.QAdjoin.toAlgebraicNumber,
    Hex.PolyQuot.toAlgebraicNumber_toComplex] using
    Hex.PolyQuot.map_mul a b h.canonical.toAlgebraic.rep
      h.canonical.toAlgebraic.rep_mk

end Hex.RealClosure.Root.Handle

/-- info: 'Hex.RealClosure.Root.Handle.packQAdjoin_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Root.Handle.packQAdjoin_complex
/-- info: 'Hex.RealClosure.Root.Handle.packQAdjoin_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Root.Handle.packQAdjoin_checked
/-- info: 'Hex.RealClosure.Root.Handle.packQAdjoin_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Root.Handle.packQAdjoin_add
/-- info: 'Hex.RealClosure.Root.Handle.packQAdjoin_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Root.Handle.packQAdjoin_mul
