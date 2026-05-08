import HexPolyZMathlib.Mignotte
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
Resultant bridge lemmas for the Berlekamp-Zassenhaus Mathlib layer.

This module packages the upstream resultant API in the integer-polynomial
forms needed by the BHKS bad-vector proof route.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open scoped BigOperators

open Polynomial

/--
Hadamard's determinant bound specialized to integer matrices and Euclidean
row norms.
-/
theorem abs_det_le_row_l2norm_prod
    {N : Nat} (A : Matrix (Fin N) (Fin N) ℤ) :
    |((A.det : ℤ) : ℝ)| ≤
      ∏ i : Fin N, Real.sqrt (∑ j : Fin N, (A i j : ℝ) ^ 2) := by
  let b := EuclideanSpace.basisFun (Fin N) ℝ
  let o := b.toBasis.orientation
  let rows : Fin N → EuclideanSpace ℝ (Fin N) :=
    fun i => WithLp.toLp 2 (fun j => (A i j : ℝ))
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N) := ⟨by simp⟩
  have hvol : |o.volumeForm rows| ≤ ∏ i : Fin N, ‖rows i‖ :=
    o.abs_volumeForm_apply_le rows
  have hrob : |o.volumeForm rows| = |b.toBasis.det rows| :=
    o.volumeForm_robust' b rows
  have hdet : b.toBasis.det rows = (A.map (Int.castRingHom ℝ)).det := by
    rw [EuclideanSpace.basisFun_toBasis, PiLp.basisFun_eq_pi_basisFun,
      Module.Basis.det_map]
    rw [Pi.basisFun_det_apply]
    rfl
  have hrow (i : Fin N) :
      ‖rows i‖ = Real.sqrt (∑ j : Fin N, (A i j : ℝ) ^ 2) := by
    simp [rows, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
  have hdet_cast : (A.map (Int.castRingHom ℝ)).det = ((A.det : ℤ) : ℝ) := by
    exact ((Int.castRingHom ℝ).map_det A).symm
  rw [hrob, hdet, hdet_cast] at hvol
  simpa [hrow] using hvol

/--
Hadamard's bound applied to the Sylvester matrix defining the integer
resultant.
-/
theorem abs_resultant_le_sylvester_row_l2norm_prod
    (f g : Polynomial ℤ) :
    |((Polynomial.resultant f g : ℤ) : ℝ)| ≤
      ∏ i : Fin (f.natDegree + g.natDegree),
        Real.sqrt
          (∑ j : Fin (f.natDegree + g.natDegree),
            (Polynomial.sylvester f g f.natDegree g.natDegree i j : ℝ) ^ 2) := by
  simpa [Polynomial.resultant] using
    abs_det_le_row_l2norm_prod
      (Polynomial.sylvester f g f.natDegree g.natDegree)

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
