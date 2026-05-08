import HexPolyZMathlib.Mignotte
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
Resultant bridge lemmas for the Berlekamp-Zassenhaus Mathlib layer.

This module packages the upstream resultant API in the integer-polynomial
forms needed by the BHKS bad-vector proof route.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/--
The upstream resultant nonvanishing theorem specialized to integer
polynomials.
-/
theorem int_resultant_ne_zero_of_coprime
    (f g : Polynomial ℤ) (h : IsCoprime f g) :
    Polynomial.resultant f g ≠ 0 :=
  Polynomial.resultant_ne_zero f g h

/--
Mapping an integer resultant to `ℚ` agrees with taking the resultant after
mapping both input polynomials to `ℚ`.
-/
theorem resultant_map_intCast_rat
    (f g : Polynomial ℤ) :
    Polynomial.resultant (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ)) =
      ((@Polynomial.resultant ℤ _ f g f.natDegree g.natDegree) : ℚ) := by
  rw [Polynomial.natDegree_map_eq_of_injective
        (RingHom.injective_int (Int.castRingHom ℚ)) f,
      Polynomial.natDegree_map_eq_of_injective
        (RingHom.injective_int (Int.castRingHom ℚ)) g]
  exact Polynomial.resultant_map_map f g f.natDegree g.natDegree
    (Int.castRingHom ℚ)

/--
The integer resultant vanishes exactly when the rationally transported
polynomials are nontrivially non-coprime.
-/
theorem int_resultant_eq_zero_iff_not_coprime_over_rat
    (f g : Polynomial ℤ) :
    Polynomial.resultant f g = 0 ↔
      ((f.map (Int.castRingHom ℚ) ≠ 0 ∨ g.map (Int.castRingHom ℚ) ≠ 0) ∧
        ¬ IsCoprime (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ))) := by
  constructor
  · intro hres
    have hresQ :
        Polynomial.resultant (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ)) = 0 := by
      rw [resultant_map_intCast_rat]
      exact_mod_cast hres
    exact (Polynomial.resultant_eq_zero_iff).mp hresQ
  · intro h
    have hresQ :
        Polynomial.resultant (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ)) = 0 :=
      (Polynomial.resultant_eq_zero_iff).mpr h
    have hcast : ((@Polynomial.resultant ℤ _ f g f.natDegree g.natDegree) : ℚ) = 0 := by
      rw [← resultant_map_intCast_rat]
      exact hresQ
    exact_mod_cast hcast

/--
Contrapositive form useful when the BHKS route proves coprimality after
transporting an integer-polynomial pair to `ℚ`.
-/
theorem int_resultant_ne_zero_of_coprime_over_rat
    (f g : Polynomial ℤ)
    (hcoprime : IsCoprime (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ))) :
    Polynomial.resultant f g ≠ 0 := by
  intro hres
  have h :=
    (int_resultant_eq_zero_iff_not_coprime_over_rat f g).mp hres
  exact h.2 hcoprime

end

end HexBerlekampZassenhausMathlib
