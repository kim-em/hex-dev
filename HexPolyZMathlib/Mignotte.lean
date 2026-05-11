import HexPolyZMathlib.Basic
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Data.Nat.Sqrt
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

private theorem range_foldl_add_eq_finset_sum_nat (g : Nat → Nat) (m : Nat) :
    (List.range m).foldl (fun acc i => acc + g i) 0 = ∑ i ∈ Finset.range m, g i := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, Finset.sum_range_succ]

private theorem sqrtStep_ge_natSqrt (n : Nat) {x : Nat} (hx : 1 ≤ x) :
    Nat.sqrt n ≤ (x + n / x) / 2 := by
  set s := Nat.sqrt n with hs_def
  rw [Nat.le_div_iff_mul_le (by decide : (0 : Nat) < 2)]
  by_cases hcase : 2 * s ≤ x
  · have hzero : 0 ≤ n / x := Nat.zero_le _
    omega
  · have hsx_lt : x < 2 * s := Nat.lt_of_not_le hcase
    have hsx_le : x ≤ 2 * s := Nat.le_of_lt hsx_lt
    have hsqle : s * s ≤ n := Nat.sqrt_le n
    have hkey : (2 * s - x) * x ≤ n := by
      have hsub_cast : ((2 * s - x : Nat) : Int) = 2 * (s : Int) - x := by
        rw [Int.ofNat_sub hsx_le]
        push_cast
        ring
      have hint : (((2 * s - x) * x : Nat) : Int) ≤ ((s * s : Nat) : Int) := by
        push_cast
        rw [hsub_cast]
        nlinarith [sq_nonneg ((s : Int) - x)]
      have hint' : (2 * s - x) * x ≤ s * s := by exact_mod_cast hint
      exact Nat.le_trans hint' hsqle
    have hdiv : 2 * s - x ≤ n / x := (Nat.le_div_iff_mul_le hx).mpr hkey
    omega

private theorem sqrtAux_ge_natSqrt (n : Nat) (hn : 1 ≤ n) :
    ∀ (fuel : Nat) {x : Nat}, 1 ≤ x → Nat.sqrt n ≤ x →
      Nat.sqrt n ≤ Hex.ZPoly.sqrtAux n fuel x := by
  intro fuel
  induction fuel with
  | zero =>
      intros x _hx hge
      exact hge
  | succ fuel ih =>
      intros x hx hge
      have hstep_ge : Nat.sqrt n ≤ Hex.ZPoly.sqrtStep n x :=
        sqrtStep_ge_natSqrt n hx
      have hstep_pos : 1 ≤ Hex.ZPoly.sqrtStep n x := by
        show 1 ≤ (x + n / x) / 2
        rw [Nat.le_div_iff_mul_le (by decide : (0 : Nat) < 2)]
        by_cases hx_eq : x = 1
        · subst hx_eq
          have hn_div : 1 ≤ n / 1 := by rw [Nat.div_one]; exact hn
          omega
        · have hx2 : 2 ≤ x := by omega
          have hzero : 0 ≤ n / x := Nat.zero_le _
          omega
      show Nat.sqrt n ≤
        (let next := Hex.ZPoly.sqrtStep n x
         if next ≥ x then x else Hex.ZPoly.sqrtAux n fuel next)
      by_cases h : Hex.ZPoly.sqrtStep n x ≥ x
      · simp only [h, if_true]
        exact hge
      · simp only [h, if_false]
        exact ih hstep_pos hstep_ge

theorem natSqrt_le_floorSqrt (n : Nat) : Nat.sqrt n ≤ Hex.ZPoly.floorSqrt n := by
  show Nat.sqrt n ≤
    if n = 0 then 0 else Hex.ZPoly.sqrtAux n (2 * n.log2 + 1) n
  by_cases hn : n = 0
  · subst hn; simp
  · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    simp [hn]
    exact sqrtAux_ge_natSqrt n hn' (2 * n.log2 + 1) hn' (Nat.sqrt_le_self n)

theorem lt_floorSqrt_succ_sq (n : Nat) :
    n < (Hex.ZPoly.floorSqrt n + 1) * (Hex.ZPoly.floorSqrt n + 1) := by
  have h1 : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  have h2 : Nat.sqrt n + 1 ≤ Hex.ZPoly.floorSqrt n + 1 :=
    Nat.add_le_add_right (natSqrt_le_floorSqrt n) 1
  exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul h2 h2)

/-- The executable `ceilSqrt n` squared dominates `n`. -/
theorem le_ceilSqrt_sq (n : Nat) : n ≤ Hex.ZPoly.ceilSqrt n * Hex.ZPoly.ceilSqrt n := by
  show n ≤ (if Hex.ZPoly.floorSqrt n * Hex.ZPoly.floorSqrt n = n then
    Hex.ZPoly.floorSqrt n else Hex.ZPoly.floorSqrt n + 1) *
    (if Hex.ZPoly.floorSqrt n * Hex.ZPoly.floorSqrt n = n then
      Hex.ZPoly.floorSqrt n else Hex.ZPoly.floorSqrt n + 1)
  by_cases h : Hex.ZPoly.floorSqrt n * Hex.ZPoly.floorSqrt n = n
  · simp [h]
  · simp [h]
    exact Nat.le_of_lt (lt_floorSqrt_succ_sq n)

/-- The executable squared-coefficient norm is bounded by the square of the
conservative `coeffL2NormBound`. -/
theorem coeffNormSq_le_coeffL2NormBound_sq (f : Hex.ZPoly) :
    Hex.ZPoly.coeffNormSq f ≤
      Hex.ZPoly.coeffL2NormBound f * Hex.ZPoly.coeffL2NormBound f := by
  show Hex.ZPoly.coeffNormSq f ≤
    Hex.ZPoly.ceilSqrt (Hex.ZPoly.coeffNormSq f) *
      Hex.ZPoly.ceilSqrt (Hex.ZPoly.coeffNormSq f)
  exact le_ceilSqrt_sq _

/-- The Mathlib coefficient-vector norm squared is bounded by the executable
squared coefficient norm. -/
theorem l2norm_toPolynomial_sq_le_coeffNormSq (f : Hex.ZPoly) :
    (l2norm (toPolynomial f)) ^ 2 ≤ (Hex.ZPoly.coeffNormSq f : ℝ) := by
  let p := toPolynomial f
  have hsupport_subset : p.support ⊆ Finset.range f.size := by
    intro i hi
    by_contra hi_range
    have hsize : f.size ≤ i := Nat.le_of_not_gt (by simpa using hi_range)
    have hcoeff_zero : p.coeff i = 0 := by
      change (toPolynomial f).coeff i = 0
      rw [coeff_toPolynomial]
      exact Hex.DensePoly.coeff_eq_zero_of_size_le f hsize
    exact (Polynomial.mem_support_iff.mp hi) hcoeff_zero
  have hsqrt :
      (l2norm p) ^ 2 = ∑ i ∈ p.support, (p.coeff i : ℝ) ^ 2 := by
    unfold l2norm
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum_le :
      ∑ i ∈ p.support, (p.coeff i : ℝ) ^ 2 ≤
        ∑ i ∈ Finset.range f.size, (p.coeff i : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsupport_subset
      (fun _ _ _ => sq_nonneg _)
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
        intro i _
        simp [p, sq_abs, Nat.cast_natAbs]
  calc
    (l2norm (toPolynomial f)) ^ 2 = (l2norm p) ^ 2 := rfl
    _ = ∑ i ∈ p.support, (p.coeff i : ℝ) ^ 2 := hsqrt
    _ ≤ ∑ i ∈ Finset.range f.size, (p.coeff i : ℝ) ^ 2 := hsum_le
    _ = (Hex.ZPoly.coeffNormSq f : ℝ) := hnorm_sum.symm

/-- The Mathlib coefficient-vector norm is dominated by the executable conservative
`coeffL2NormBound`. -/
theorem l2norm_toPolynomial_le_coeffL2NormBound (f : Hex.ZPoly) :
    l2norm (toPolynomial f) ≤ (Hex.ZPoly.coeffL2NormBound f : ℝ) := by
  have hl2_nonneg : 0 ≤ l2norm (toPolynomial f) := by
    unfold l2norm; exact Real.sqrt_nonneg _
  have hbound_nonneg : 0 ≤ (Hex.ZPoly.coeffL2NormBound f : ℝ) :=
    Nat.cast_nonneg _
  have hsq_le : (l2norm (toPolynomial f)) ^ 2 ≤
      (Hex.ZPoly.coeffL2NormBound f : ℝ) ^ 2 := by
    calc (l2norm (toPolynomial f)) ^ 2
        ≤ (Hex.ZPoly.coeffNormSq f : ℝ) :=
          l2norm_toPolynomial_sq_le_coeffNormSq f
      _ ≤ ((Hex.ZPoly.coeffL2NormBound f * Hex.ZPoly.coeffL2NormBound f : Nat) : ℝ) := by
          exact_mod_cast coeffNormSq_le_coeffL2NormBound_sq f
      _ = (Hex.ZPoly.coeffL2NormBound f : ℝ) ^ 2 := by push_cast; ring
  have hl2_eq :
      l2norm (toPolynomial f) = Real.sqrt ((l2norm (toPolynomial f)) ^ 2) :=
    (Real.sqrt_sq hl2_nonneg).symm
  have hb_eq :
      (Hex.ZPoly.coeffL2NormBound f : ℝ) =
        Real.sqrt ((Hex.ZPoly.coeffL2NormBound f : ℝ) ^ 2) :=
    (Real.sqrt_sq hbound_nonneg).symm
  rw [hl2_eq, hb_eq]
  exact Real.sqrt_le_sqrt hsq_le

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
