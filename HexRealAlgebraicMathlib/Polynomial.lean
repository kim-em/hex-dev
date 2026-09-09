/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraic.Roots
public import HexRealAlgebraicMathlib.Order
public import HexNumberFieldMathlib.AlgebraicRoots

public section

/-! Real polynomial interpretation and normalization correspondence. -/

namespace Hex.AlgebraicPoly

private theorem horner_normalize (l : List AlgebraicNumber) :
    ((l.reverse.dropWhile AlgebraicNumber.isZero).reverse.foldr
      (fun (a : AlgebraicNumber) (p : Polynomial ℂ) => Polynomial.C a.toComplex + Polynomial.X * p) 0) =
    l.foldr (fun (a : AlgebraicNumber) (p : Polynomial ℂ) => Polynomial.C a.toComplex + Polynomial.X * p) 0 := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    by_cases ha : a.isZero = true
    · have hz := (AlgebraicNumber.isZero_iff a).mp ha
      simpa [List.reverse_append, ha, List.foldr_append, hz] using ih
    · simp [List.reverse_append, ha]

/-- Removing trailing canonical zero coefficients preserves the polynomial. -/
theorem toPolynomial_ofArray (coeffs : Array AlgebraicNumber) :
    (ofArray coeffs).toPolynomial = coeffs.foldr
      (fun (a : AlgebraicNumber) (p : Polynomial ℂ) => Polynomial.C a.toComplex + Polynomial.X * p) 0 := by
  rw [toPolynomial, coeffs_ofArray]
  rcases coeffs with ⟨l⟩
  simpa only [List.popWhile_toArray, ← Array.foldr_toList, List.toList_toArray]
    using horner_normalize l

end Hex.AlgebraicPoly

namespace Hex.RealAlgebraicPoly

/-- Interpret the stored real coefficients in the real polynomial ring. -/
@[expose] noncomputable def toPolynomial (f : RealAlgebraicPoly) : Polynomial ℝ :=
  f.toAlgebraic.coeffs.foldr
    (fun a p => Polynomial.C a.toComplex.re + Polynomial.X * p) 0

private theorem map_horner (l : List AlgebraicNumber)
    (hl : ∀ a ∈ l, a.isReal = true) :
    (l.foldr (fun (a : AlgebraicNumber) (p : Polynomial ℝ) => Polynomial.C a.toComplex.re + Polynomial.X * p) 0).map
        Complex.ofRealHom =
      l.foldr (fun (a : AlgebraicNumber) (p : Polynomial ℂ) => Polynomial.C a.toComplex + Polynomial.X * p) 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, Polynomial.map_add, Polynomial.map_C,
      Polynomial.map_mul, Polynomial.map_X]
    rw [ih (fun b hb => hl b (List.mem_cons_of_mem a hb))]
    rw [show Complex.ofRealHom a.toComplex.re = a.toComplex from
      AlgebraicNumber.ofReal_re a (hl a (by simp))]

/-- Complex inclusion agrees with the existing algebraic polynomial interpretation. -/
theorem map_toPolynomial (f : RealAlgebraicPoly) :
    f.toPolynomial.map Complex.ofRealHom = f.toAlgebraic.toPolynomial := by
  unfold toPolynomial AlgebraicPoly.toPolynomial
  rw [← Array.foldr_toList, ← Array.foldr_toList]
  exact map_horner _ (fun a ha => f.property a (by simpa only [Array.mem_toList_iff, toAlgebraic] using ha))

/-- Evaluation commutes with the inclusion into the complex numbers. -/
theorem ofReal_eval (f : RealAlgebraicPoly) (r : ℝ) :
    ((f.toPolynomial.eval r : ℝ) : ℂ) = f.toAlgebraic.toPolynomial.eval (r : ℂ) := by
  rw [← map_toPolynomial, Polynomial.eval_map]
  change Complex.ofRealHom (f.toPolynomial.eval r) =
    Polynomial.eval₂ Complex.ofRealHom (Complex.ofRealHom r) f.toPolynomial
  rw [Polynomial.eval₂_at_apply]

private theorem map_real_horner (l : List RealAlgebraicNumber) :
    (l.foldr (fun a p => Polynomial.C a.toReal + Polynomial.X * p) (0 : Polynomial ℝ)).map
        Complex.ofRealHom =
      l.foldr (fun a p => Polynomial.C a.toAlgebraic.toComplex + Polynomial.X * p)
        (0 : Polynomial ℂ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, Polynomial.map_add, Polynomial.map_C,
      Polynomial.map_mul, Polynomial.map_X, ih]
    rw [show Complex.ofRealHom a.toReal = a.toAlgebraic.toComplex from
      RealAlgebraicNumber.ofReal_toReal a]

/-- Real coefficient-array normalization preserves the Horner polynomial. -/
theorem toPolynomial_ofArray (coeffs : Array RealAlgebraicNumber) :
    (ofArray coeffs).toPolynomial = coeffs.foldr
      (fun a p => Polynomial.C a.toReal + Polynomial.X * p) 0 := by
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  rw [map_toPolynomial]
  change (AlgebraicPoly.ofArray (coeffs.map RealAlgebraicNumber.toAlgebraic)).toPolynomial = _
  rw [AlgebraicPoly.toPolynomial_ofArray, Array.foldr_map]
  simpa only [← Array.foldr_toList] using (map_real_horner coeffs.toList).symm

/-- The zero polynomial is preserved and reflected by complex inclusion. -/
theorem toPolynomial_eq_zero (f : RealAlgebraicPoly) :
    f.toPolynomial = 0 ↔ f.toAlgebraic.toPolynomial = 0 := by
  rw [← map_toPolynomial, Polynomial.map_eq_zero_iff Complex.ofReal_injective]

/-- The natural degree agrees with the existing complex polynomial. -/
theorem natDegree_toPolynomial (f : RealAlgebraicPoly) :
    f.toPolynomial.natDegree = f.toAlgebraic.toPolynomial.natDegree := by
  rw [← map_toPolynomial, Polynomial.natDegree_map]

private theorem coeff_real_horner (l : List RealAlgebraicNumber) (n : Nat) :
    (l.foldr (fun a p => Polynomial.C a.toReal + Polynomial.X * p)
      (0 : Polynomial ℝ)).coeff n = (l.getD n 0).toReal := by
  induction l generalizing n with
  | nil => simp [RealAlgebraicNumber.zero_toReal]
  | cons a l ih =>
    cases n with
    | zero => simp
    | succ n => simpa using ih n

/-- Normalized array construction preserves each coefficient, with zero beyond the array. -/
theorem coeff_ofArray (coeffs : Array RealAlgebraicNumber) (n : Nat) :
    (ofArray coeffs).toPolynomial.coeff n = (coeffs.getD n 0).toReal := by
  rw [toPolynomial_ofArray, ← Array.foldr_toList, coeff_real_horner,
    List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- Represent a Mathlib polynomial by its finite coefficient array. -/
@[expose] noncomputable def ofPolynomial (p : Polynomial RealAlgebraicNumber) : RealAlgebraicPoly :=
  ofArray (Array.ofFn (fun i : Fin (p.natDegree + 1) => p.coeff i))

/-- Conversion from a Mathlib polynomial preserves its real interpretation. -/
theorem toPolynomial_ofPolynomial (p : Polynomial RealAlgebraicNumber) :
    (ofPolynomial p).toPolynomial = p.map RealAlgebraicNumber.toRealHom := by
  apply Polynomial.ext
  intro n
  rw [ofPolynomial, coeff_ofArray, Polynomial.coeff_map, Array.getD_eq_getD_getElem?,
    Array.getElem?_ofFn]
  split
  · rfl
  · rename_i hn
    have hc : p.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [Option.getD_none, RealAlgebraicNumber.zero_toReal, hc, map_zero]

end Hex.RealAlgebraicPoly
