/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberFieldMathlib.Embedding
public import HexNumberFieldMathlib.AlgebraicPoly
public section

/-! Coefficient-array normalization and conversion of Mathlib polynomials. -/
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

namespace Hex.AlgebraicPoly

private theorem coeff_horner (l : List AlgebraicNumber) (n : Nat) :
    (l.foldr (fun a p => Polynomial.C a.toComplex + Polynomial.X * p)
      (0 : Polynomial ℂ)).coeff n = (l.getD n 0).toComplex := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih => cases n <;> simp [ih]

/-- Normalization preserves every coefficient, including implicit trailing zeros. -/
theorem coeff_ofArray (coeffs : Array AlgebraicNumber) (n : Nat) :
    (ofArray coeffs).toPolynomial.coeff n = (coeffs.getD n 0).toComplex := by
  rw [toPolynomial_ofArray, ← Array.foldr_toList, coeff_horner,
    List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- Represent a Mathlib polynomial by its finite coefficient array. -/
@[expose] noncomputable def ofPolynomial (p : Polynomial AlgebraicNumber) : AlgebraicPoly :=
  ofArray (Array.ofFn (fun i : Fin (p.natDegree + 1) => p.coeff i))

/-- Conversion preserves the complex interpretation of the polynomial. -/
theorem toPolynomial_ofPolynomial (p : Polynomial AlgebraicNumber) :
    (ofPolynomial p).toPolynomial = p.map AlgebraicNumber.toComplexHom := by
  apply Polynomial.ext
  intro n
  rw [ofPolynomial, coeff_ofArray, Polynomial.coeff_map, Array.getD_eq_getD_getElem?,
    Array.getElem?_ofFn]
  split
  · rfl
  · rename_i hn
    have hc : p.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [Option.getD_none, AlgebraicNumber.zero_toComplex, hc, map_zero]

end Hex.AlgebraicPoly
