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

private theorem range_foldl_add_eq_finset_sum_nat (g : Nat → Nat) (m : Nat) :
    (List.range m).foldl (fun acc i => acc + g i) 0 = ∑ i ∈ Finset.range m, g i := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, Finset.sum_range_succ]

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

/-- Landau's inequality specialized to `Polynomial ℤ` via the complex cast. -/
theorem mahlerMeasure_le_l2norm (f : Polynomial ℤ) :
    (f.map (Int.castRingHom ℂ)).mahlerMeasure ≤ l2norm f := by
  simpa [l2norm, support_map_intCast, sq_norm_coeff_map_intCast] using
    Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff (f.map (Int.castRingHom ℂ))

/--
The transported Mathlib coefficient-vector norm squared is bounded by the
executable squared coefficient norm.
-/
theorem l2norm_toPolynomial_sq_le_coeffNormSq (f : Hex.ZPoly) :
    (l2norm (toPolynomial f)) ^ 2 ≤ (Hex.ZPoly.coeffNormSq f : ℝ) := by
  let p := toPolynomial f
  have hsupport_subset : p.support ⊆ Finset.range f.size := by
    intro i hi
    by_contra hi_range
    have hsize : f.size ≤ i := Nat.le_of_not_gt (by
      simpa using hi_range)
    have hcoeff_zero : p.coeff i = 0 := by
      change (toPolynomial f).coeff i = 0
      rw [coeff_toPolynomial]
      exact Hex.DensePoly.coeff_eq_zero_of_size_le f hsize
    exact (Polynomial.mem_support_iff.mp hi) hcoeff_zero
  have hsqrt :
      (l2norm p) ^ 2 = ∑ i ∈ p.support, (p.coeff i : ℝ) ^ 2 := by
    unfold l2norm
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg fun i hi => sq_nonneg _
  have hsum_le :
      ∑ i ∈ p.support, (p.coeff i : ℝ) ^ 2 ≤
        ∑ i ∈ Finset.range f.size, (p.coeff i : ℝ) ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsupport_subset
      (fun i hi_range hi_support => sq_nonneg _)
  have hnorm_sum :
      (Hex.ZPoly.coeffNormSq f : ℝ) =
        ∑ i ∈ Finset.range f.size, (p.coeff i : ℝ) ^ 2 := by
    have hnat :
        Hex.ZPoly.coeffNormSq f =
          ∑ i ∈ Finset.range f.size, (f.coeff i).natAbs ^ 2 := by
      rw [Hex.ZPoly.coeffNormSq_eq_sum, range_foldl_add_eq_finset_sum_nat]
    rw [hnat]
    calc
      ((∑ i ∈ Finset.range f.size, (f.coeff i).natAbs ^ 2 : Nat) : ℝ) =
          ∑ i ∈ Finset.range f.size, ((f.coeff i).natAbs : ℝ) ^ 2 := by
        norm_cast
      _ = ∑ i ∈ Finset.range f.size, (p.coeff i : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [p, sq_abs, Nat.cast_natAbs]
  calc
    (l2norm (toPolynomial f)) ^ 2 = (l2norm p) ^ 2 := rfl
    _ = ∑ i ∈ p.support, (p.coeff i : ℝ) ^ 2 := hsqrt
    _ ≤ ∑ i ∈ Finset.range f.size, (p.coeff i : ℝ) ^ 2 := hsum_le
    _ = (Hex.ZPoly.coeffNormSq f : ℝ) := hnorm_sum.symm

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
