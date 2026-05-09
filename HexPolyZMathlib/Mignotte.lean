import HexPolyZMathlib.Basic
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.NumberTheory.MahlerMeasure

/-!
Mignotte-bound infrastructure for integer polynomials.

This module packages the real-valued coefficient `l2norm` used by the
classical Mignotte bound together with the transport lemmas needed to move
between `Polynomial ℤ` and the complex-coefficient Mahler-measure API in
Mathlib.
-/

open scoped BigOperators

namespace HexPolyZMathlib

noncomputable section

/-- The Euclidean norm of the coefficient vector of an integer polynomial. -/
def l2norm (f : Polynomial ℤ) : ℝ :=
  Real.sqrt (∑ i ∈ f.support, (f.coeff i : ℝ) ^ 2)

@[simp]
theorem coeff_map_intCast (f : Polynomial ℤ) (n : Nat) :
    (f.map (Int.castRingHom ℂ)).coeff n = (f.coeff n : ℂ) := by
  simp

@[simp]
theorem natDegree_map_intCast (f : Polynomial ℤ) :
    (f.map (Int.castRingHom ℂ)).natDegree = f.natDegree := by
  simpa using
    (Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℂ)
      (hf := RingHom.injective_int (Int.castRingHom ℂ)) f)

@[simp]
theorem support_map_intCast (f : Polynomial ℤ) :
    (f.map (Int.castRingHom ℂ)).support = f.support := by
  simpa using
    (Polynomial.support_map_of_injective (f := Int.castRingHom ℂ) f
      (RingHom.injective_int (Int.castRingHom ℂ)))

@[simp]
theorem norm_coeff_map_intCast (f : Polynomial ℤ) (n : Nat) :
    ‖(f.map (Int.castRingHom ℂ)).coeff n‖ = (Int.natAbs (f.coeff n) : ℝ) := by
  simp [Complex.norm_intCast]

theorem sq_norm_coeff_map_intCast (f : Polynomial ℤ) (n : Nat) :
    ‖(f.map (Int.castRingHom ℂ)).coeff n‖ ^ 2 = (f.coeff n : ℝ) ^ 2 := by
  simp [Complex.norm_intCast, pow_two]

private theorem range_foldl_add_eq_finset_sum_nat (f : Nat → Nat) (m : Nat) :
    (List.range m).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, Finset.sum_range_succ]

private theorem coeffNormSq_eq_finset_sum_real (f : Hex.ZPoly) :
    (Hex.ZPoly.coeffNormSq f : ℝ) =
      ∑ i ∈ Finset.range f.size, ((f.coeff i).natAbs : ℝ) ^ 2 := by
  rw [Hex.ZPoly.coeffNormSq_eq_sum, range_foldl_add_eq_finset_sum_nat]
  simp

private theorem l2norm_toPolynomial_sq_eq_sum_size (f : Hex.ZPoly) :
    (l2norm (toPolynomial f)) ^ 2 =
      ∑ i ∈ Finset.range f.size, ((f.coeff i : ℤ) : ℝ) ^ 2 := by
  unfold l2norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  trans ∑ i ∈ Finset.range f.size, (((toPolynomial f).coeff i : ℤ) : ℝ) ^ 2
  · apply Finset.sum_subset
    · intro x hx
      rw [Finset.mem_range]
      by_contra hlt
      have hcoeff : (toPolynomial f).coeff x = 0 := by
        rw [coeff_toPolynomial]
        exact Hex.DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hlt)
      exact (Polynomial.mem_support_iff.mp hx) hcoeff
    · intro x _ hx
      have hcoeff : (toPolynomial f).coeff x = 0 := by
        by_contra hne
        exact hx (Polynomial.mem_support_iff.mpr hne)
      rw [hcoeff]
      simp
  · simp

/-- The squared Mathlib coefficient `l2norm` of an executable integer
polynomial is exactly the executable squared coefficient norm. -/
theorem l2norm_toPolynomial_sq_eq_coeffNormSq (f : Hex.ZPoly) :
    (l2norm (toPolynomial f)) ^ 2 = (Hex.ZPoly.coeffNormSq f : ℝ) := by
  rw [l2norm_toPolynomial_sq_eq_sum_size, coeffNormSq_eq_finset_sum_real]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- A relaxed form of `l2norm_toPolynomial_sq_eq_coeffNormSq` matching the
BHKS cap's `(sumSquared + 1)` coefficient factor. -/
theorem l2norm_toPolynomial_sq_le_coeffNormSq_add_one (f : Hex.ZPoly) :
    (l2norm (toPolynomial f)) ^ 2 ≤ (Hex.ZPoly.coeffNormSq f + 1 : ℝ) := by
  rw [l2norm_toPolynomial_sq_eq_coeffNormSq]
  norm_num

/-- Landau's inequality specialized to `Polynomial ℤ` via the complex cast. -/
theorem mahlerMeasure_le_l2norm (f : Polynomial ℤ) :
    (f.map (Int.castRingHom ℂ)).mahlerMeasure ≤ l2norm f := by
  simpa [l2norm, support_map_intCast, sq_norm_coeff_map_intCast] using
    Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff (f.map (Int.castRingHom ℂ))

/-- Mignotte's coefficient bound for integer polynomial factors, obtained by
combining Mathlib's Mahler-measure coefficient estimate with Landau's
inequality. -/
theorem mignotte_bound (f g : Polynomial ℤ) (hf : f ≠ 0) (hg : g ∣ f) (j : ℕ) :
    (Int.natAbs (g.coeff j) : ℝ) ≤ Nat.choose g.natDegree j * l2norm f := by
  rcases hg with ⟨h, rfl⟩
  have hh0 : h ≠ 0 := by
    intro hh
    apply hf
    simp [hh]
  have hcoeff :=
      Polynomial.norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure
        (n := j) (g := g.map (Int.castRingHom ℂ)) (h := h.map (Int.castRingHom ℂ))
        (Polynomial.one_le_mahlerMeasure_of_ne_zero hh0)
  calc
    (Int.natAbs (g.coeff j) : ℝ) = ‖(g.map (Int.castRingHom ℂ)).coeff j‖ := by
      exact (norm_coeff_map_intCast (f := g) (n := j)).symm
    _ ≤ Nat.choose (g.map (Int.castRingHom ℂ)).natDegree j *
          ((g.map (Int.castRingHom ℂ)) * (h.map (Int.castRingHom ℂ))).mahlerMeasure := hcoeff
    _ = Nat.choose g.natDegree j * (((g * h).map (Int.castRingHom ℂ)).mahlerMeasure) := by
      simp [Polynomial.map_mul]
    _ ≤ Nat.choose g.natDegree j * l2norm (g * h) := by
      gcongr
      exact mahlerMeasure_le_l2norm (f := g * h)

end

end HexPolyZMathlib
