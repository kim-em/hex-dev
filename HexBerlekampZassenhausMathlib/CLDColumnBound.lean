import HexPolyZMathlib.Mignotte
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Nat.Choose.Bounds

/-!
BHKS CLD-column coefficient bounds.

This file isolates the exact integer-polynomial `Phi` column used in BHKS
Lemma 5.1.  The main coefficient theorem is deliberately conditional on a
Mahler-measure bound for `Phi`; this is the replacement analytic obligation for
the invalid unconditional derivative estimate.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

namespace BHKS

/-- The exact integer-polynomial CLD column `Phi(g) = f * g' / g`. -/
def phi (f g : Polynomial ℤ) : Polynomial ℤ :=
  (f * g.derivative).divByMonic g

/--
If `f = g * h` and `g` is monic, the quotient definition of `Phi(g)` is the
integer polynomial `h * g'`.
-/
theorem phi_eq_factor_mul_derivative
    (f g h : Polynomial ℤ) (hg_monic : g.Monic) (hfac : f = g * h) :
    phi f g = h * g.derivative := by
  rw [phi, hfac]
  calc
    ((g * h) * g.derivative).divByMonic g =
        (g * (h * g.derivative)).divByMonic g := by
      ring_nf
    _ = h * g.derivative :=
      Polynomial.mul_divByMonic_cancel_left (h * g.derivative) hg_monic

/--
Coefficient bound for the BHKS `Phi` column from the valid replacement
analytic estimate `M(Phi) <= n * ||f||_2`.

The hypotheses `hphi_degree` and `hphi_mahler` are the precise downstream
analytic obligations: the theorem does not use, imply, or reintroduce the false
unconditional derivative Mahler bound.
-/
theorem abs_phi_coeff_le
    (f g h : Polynomial ℤ) (_hg_monic : g.Monic) (_hfac : f = g * h)
    (j : Nat)
    (hphi_degree : (phi f g).natDegree ≤ f.natDegree - 1)
    (hphi_mahler :
      ((phi f g).map (Int.castRingHom ℂ)).mahlerMeasure ≤
        (f.natDegree : ℝ) * HexPolyZMathlib.l2norm f) :
    (Int.natAbs ((phi f g).coeff j) : ℝ) ≤
      (Nat.choose (f.natDegree - 1) j : ℝ) *
        (f.natDegree : ℝ) * HexPolyZMathlib.l2norm f := by
  have hcoeff :=
    Polynomial.norm_coeff_le_choose_mul_mahlerMeasure
      (n := j) (p := (phi f g).map (Int.castRingHom ℂ))
  have hchoose :
      (Nat.choose ((phi f g).map (Int.castRingHom ℂ)).natDegree j : ℝ) ≤
        (Nat.choose (f.natDegree - 1) j : ℝ) := by
    rw [HexPolyZMathlib.natDegree_map_intCast]
    exact_mod_cast Nat.choose_le_choose j hphi_degree
  calc
    (Int.natAbs ((phi f g).coeff j) : ℝ) =
        ‖((phi f g).map (Int.castRingHom ℂ)).coeff j‖ := by
      exact (HexPolyZMathlib.norm_coeff_map_intCast (f := phi f g) (n := j)).symm
    _ ≤ Nat.choose ((phi f g).map (Int.castRingHom ℂ)).natDegree j *
        ((phi f g).map (Int.castRingHom ℂ)).mahlerMeasure := hcoeff
    _ ≤ (Nat.choose (f.natDegree - 1) j : ℝ) *
        ((f.natDegree : ℝ) * HexPolyZMathlib.l2norm f) := by
      exact mul_le_mul hchoose hphi_mahler
        (Polynomial.mahlerMeasure_nonneg _)
        (Nat.cast_nonneg _)
    _ =
        (Nat.choose (f.natDegree - 1) j : ℝ) *
          (f.natDegree : ℝ) * HexPolyZMathlib.l2norm f := by
      ring

end BHKS

end

end HexBerlekampZassenhausMathlib
