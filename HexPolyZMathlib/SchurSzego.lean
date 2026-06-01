import HexPolyZMathlib.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

/-!
Schur-Szego composition plumbing for Schmeisser's root-product theorem.

This file contains only the algebraic and multiset bookkeeping around the
binomial-normalized composition polynomial.  The analytic
de Bruijn-Springer/Schmeisser root theorem is proved separately.
-/

open scoped BigOperators

namespace Polynomial

noncomputable section

/--
Schmeisser's binomial-normalized composition polynomial at degree bound `n`.
Its `k`th coefficient is `f_k * g_k / choose n k` for `k ≤ n`, and zero
above `n`.
-/
def schmeisserComposition (n : ℕ) (f g : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    monomial k (f.coeff k * (g.coeff k / (Nat.choose n k : ℂ)))

@[simp]
theorem coeff_schmeisserComposition_of_le
    (n : ℕ) (f g : ℂ[X]) {k : ℕ} (hk : k ≤ n) :
    (schmeisserComposition n f g).coeff k =
      f.coeff k * (g.coeff k / (Nat.choose n k : ℂ)) := by
  rw [schmeisserComposition, finset_sum_coeff]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))]
  · simp
  · intro j hj hne
    simp [coeff_monomial, hne]

@[simp]
theorem coeff_schmeisserComposition_of_lt
    (n : ℕ) (f g : ℂ[X]) {k : ℕ} (hk : n < k) :
    (schmeisserComposition n f g).coeff k = 0 := by
  rw [schmeisserComposition, finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  have hj_le : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hne : j ≠ k := by omega
  simp [coeff_monomial, hne]

theorem support_schmeisserComposition_subset
    (n : ℕ) (f g : ℂ[X]) :
    (schmeisserComposition n f g).support ⊆ Finset.range (n + 1) := by
  intro k hk
  by_contra hmem
  have hk_gt : n < k := by
    have hle : n + 1 ≤ k := Nat.le_of_not_gt (by simpa using hmem)
    omega
  exact (Polynomial.mem_support_iff.mp hk) (coeff_schmeisserComposition_of_lt n f g hk_gt)

theorem natDegree_schmeisserComposition_le
    (n : ℕ) (f g : ℂ[X]) :
    (schmeisserComposition n f g).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  exact coeff_schmeisserComposition_of_lt n f g hk

theorem complex_nat_choose_ne_zero {n k : ℕ} (hk : k ≤ n) :
    (Nat.choose n k : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.choose_pos hk).ne'

theorem real_nat_choose_pos {n k : ℕ} (hk : k ≤ n) :
    0 < (Nat.choose n k : ℝ) := by
  exact_mod_cast Nat.choose_pos hk

theorem eq_schmeisserComposition_of_natDegree_le_of_coeff
    {n : ℕ} {f g h : ℂ[X]}
    (hdeg : h.natDegree ≤ n)
    (hcoeff : ∀ k ≤ n,
      h.coeff k = f.coeff k * (g.coeff k / (Nat.choose n k : ℂ))) :
    h = schmeisserComposition n f g := by
  ext k
  by_cases hk : k ≤ n
  · rw [hcoeff k hk, coeff_schmeisserComposition_of_le n f g hk]
  · have hk_gt : n < k := Nat.lt_of_not_ge hk
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hk_gt),
      coeff_schmeisserComposition_of_lt n f g hk_gt]

@[simp]
theorem schmeisserComposition_zero_left (n : ℕ) (g : ℂ[X]) :
    schmeisserComposition n 0 g = 0 := by
  ext k
  by_cases hk : k ≤ n
  · simp [coeff_schmeisserComposition_of_le n 0 g hk]
  · have hk' : n < k := by omega
    simp [coeff_schmeisserComposition_of_lt n 0 g hk']

@[simp]
theorem schmeisserComposition_zero_right (n : ℕ) (f : ℂ[X]) :
    schmeisserComposition n f 0 = 0 := by
  ext k
  by_cases hk : k ≤ n
  · simp [coeff_schmeisserComposition_of_le n f 0 hk]
  · have hk' : n < k := by omega
    simp [coeff_schmeisserComposition_of_lt n f 0 hk']

@[simp]
theorem schmeisserComposition_zero (f g : ℂ[X]) :
    schmeisserComposition 0 f g = C (f.coeff 0 * g.coeff 0) := by
  ext k
  rcases k with _ | k
  · simp [coeff_schmeisserComposition_of_le 0 f g (Nat.le_refl 0)]
  · simp [coeff_schmeisserComposition_of_lt 0 f g (Nat.succ_pos k)]

@[simp]
theorem schmeisserComposition_C_C (n : ℕ) (a b : ℂ) :
    schmeisserComposition n (C a) (C b) = C (a * b) := by
  ext k
  rcases k with _ | k
  · simp [coeff_schmeisserComposition_of_le n (C a) (C b) (Nat.zero_le n)]
  · by_cases hk : k.succ ≤ n
    · simp [coeff_schmeisserComposition_of_le n (C a) (C b) hk]
    · have hk' : n < k.succ := by omega
      simp [coeff_schmeisserComposition_of_lt n (C a) (C b) hk']

/--
Degree-two coefficient normal form, exposed next to the Schmeisser source
surface so degree-two arguments do not depend directly on Mathlib's theorem
name.
-/
theorem eq_quadratic_of_natDegree_le_two {p : ℂ[X]} (hp : p.natDegree ≤ 2) :
    p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
  eq_quadratic_of_degree_le_two (degree_le_of_natDegree_le hp)

/-- Coefficient normal form for the degree-two Schmeisser composition. -/
theorem schmeisserComposition_two_eq (f g : ℂ[X]) :
    schmeisserComposition 2 f g =
      C (f.coeff 2 * g.coeff 2) * X ^ 2 +
        C (f.coeff 1 * (g.coeff 1 / (2 : ℂ))) * X +
          C (f.coeff 0 * g.coeff 0) := by
  rw [eq_quadratic_of_natDegree_le_two (natDegree_schmeisserComposition_le 2 f g)]
  simp [coeff_schmeisserComposition_of_le]

/-- Quadratic roots are a two-element multiset exactly when Vieta's relations hold. -/
theorem roots_quadratic_eq_pair_iff_complex {a b c x₁ x₂ : ℂ} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).roots = ({x₁, x₂} : Multiset ℂ) ↔
      x₁ + x₂ = -b / a ∧ x₁ * x₂ = c / a :=
  roots_quadratic_eq_pair_iff_of_ne_zero' ha

/-- Build the quadratic root multiset from Vieta data. -/
theorem roots_quadratic_eq_pair_of_vieta_complex {a b c x₁ x₂ : ℂ}
    (ha : a ≠ 0)
    (hsum : x₁ + x₂ = -b / a)
    (hprod : x₁ * x₂ = c / a) :
    (C a * X ^ 2 + C b * X + C c).roots = ({x₁, x₂} : Multiset ℂ) :=
  (roots_quadratic_eq_pair_iff_complex ha).2 ⟨hsum, hprod⟩

/-- Sum relation extracted from a two-root quadratic multiset. -/
theorem quadratic_roots_sum_eq_of_roots_eq_pair {a b c x₁ x₂ : ℂ}
    (ha : a ≠ 0)
    (hroots : (C a * X ^ 2 + C b * X + C c).roots = ({x₁, x₂} : Multiset ℂ)) :
    x₁ + x₂ = -b / a :=
  ((roots_quadratic_eq_pair_iff_complex ha).1 hroots).1

/-- Product relation extracted from a two-root quadratic multiset. -/
theorem quadratic_roots_prod_eq_of_roots_eq_pair {a b c x₁ x₂ : ℂ}
    (ha : a ≠ 0)
    (hroots : (C a * X ^ 2 + C b * X + C c).roots = ({x₁, x₂} : Multiset ℂ)) :
    x₁ * x₂ = c / a :=
  ((roots_quadratic_eq_pair_iff_complex ha).1 hroots).2

theorem coeff_two_ne_zero_of_natDegree_eq_two {p : ℂ[X]} (hp : p.natDegree = 2) :
    p.coeff 2 ≠ 0 := by
  have hp_ne : p ≠ 0 := by
    intro hp_zero
    rw [hp_zero, natDegree_zero] at hp
    omega
  simpa [leadingCoeff, hp] using (leadingCoeff_ne_zero.mpr hp_ne)

/--
Exact complex quadratics have a two-root multiset, and the two roots satisfy
the coefficient-normalized Vieta relations used by the degree-two Schmeisser
source proof.
-/
theorem exists_roots_eq_pair_and_vieta_of_natDegree_eq_two {p : ℂ[X]}
    (hp : p.natDegree = 2) :
    ∃ x₁ x₂ : ℂ,
      p.roots = ({x₁, x₂} : Multiset ℂ) ∧
        x₁ + x₂ = -p.coeff 1 / p.coeff 2 ∧
          x₁ * x₂ = p.coeff 0 / p.coeff 2 := by
  have hcard : p.roots.card = 2 := by
    rw [IsAlgClosed.card_roots_eq_natDegree (p := p), hp]
  obtain ⟨x₁, x₂, hroots⟩ := Multiset.card_eq_two.mp hcard
  have hp_eq : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
    eq_quadratic_of_natDegree_le_two (by omega)
  have hquad_roots :
      (C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) : ℂ[X]).roots =
        ({x₁, x₂} : Multiset ℂ) := by
    rw [← hp_eq]
    exact hroots
  have hsum := quadratic_roots_sum_eq_of_roots_eq_pair
      (coeff_two_ne_zero_of_natDegree_eq_two hp) hquad_roots
  have hprod := quadratic_roots_prod_eq_of_roots_eq_pair
      (coeff_two_ne_zero_of_natDegree_eq_two hp) hquad_roots
  exact ⟨x₁, x₂, hroots, hsum, hprod⟩

/--
The binomial-normalized Schmeisser kernel for the derivative specialization:
`n * z * (z + 1)^(n - 1)`.
-/
def schmeisserDerivativeKernel (n : ℕ) : ℂ[X] :=
  C (n : ℂ) * X * (X + 1) ^ (n - 1)

@[simp]
theorem schmeisserDerivativeKernel_zero : schmeisserDerivativeKernel 0 = 0 := by
  simp [schmeisserDerivativeKernel]

@[simp]
theorem schmeisserDerivativeKernel_one : schmeisserDerivativeKernel 1 = X := by
  simp [schmeisserDerivativeKernel]

theorem coeff_X_mul_derivative_eq_schmeisser_coeff
    (p : ℂ[X]) {n k : ℕ} (hk : k ≤ n) :
    (X * p.derivative).coeff k =
      p.coeff k * (schmeisserDerivativeKernel n).coeff k / (Nat.choose n k : ℂ) := by
  rcases k with _ | k
  · simp [schmeisserDerivativeKernel]
  have hchoose_ne : (Nat.choose n (k + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hk_pos : 0 < n := lt_of_lt_of_le (Nat.succ_pos k) hk
  have hcoeff_kernel :
      (schmeisserDerivativeKernel n).coeff (k + 1) =
        (n : ℂ) * ((n - 1).choose k : ℂ) := by
    rw [schmeisserDerivativeKernel, mul_assoc, coeff_C_mul, coeff_X_mul,
      coeff_X_add_one_pow]
  have hchoose_cast :
      (n : ℂ) * ((n - 1).choose k : ℂ) =
        (Nat.choose n (k + 1) : ℂ) * (k + 1 : ℂ) := by
    have hnat :
        n * Nat.choose (n - 1) k = Nat.choose n (k + 1) * (k + 1) := by
      simpa [Nat.sub_add_cancel hk_pos] using Nat.add_one_mul_choose_eq (n - 1) k
    exact_mod_cast hnat
  calc
    (X * p.derivative).coeff (k + 1) = p.derivative.coeff k := by
      rw [coeff_X_mul]
    _ = p.coeff (k + 1) * (k + 1 : ℂ) := by
      rw [coeff_derivative]
    _ = p.coeff (k + 1) *
        ((schmeisserDerivativeKernel n).coeff (k + 1) /
          (Nat.choose n (k + 1) : ℂ)) := by
      rw [hcoeff_kernel, hchoose_cast]
      field_simp [hchoose_ne]
    _ = p.coeff (k + 1) * (schmeisserDerivativeKernel n).coeff (k + 1) /
        (Nat.choose n (k + 1) : ℂ) := by
      ring

theorem schmeisserComposition_derivativeKernel_eq_X_mul_derivative
    (p : ℂ[X]) :
    schmeisserComposition p.natDegree p (schmeisserDerivativeKernel p.natDegree) =
      X * p.derivative := by
  ext k
  by_cases hk : k ≤ p.natDegree
  · rw [coeff_schmeisserComposition_of_le _ _ _ hk,
      coeff_X_mul_derivative_eq_schmeisser_coeff p hk]
    ring
  · have hk_gt : p.natDegree < k := Nat.lt_of_not_ge hk
    rw [coeff_schmeisserComposition_of_lt _ _ _ hk_gt]
    rcases k with _ | k
    · omega
    · rw [coeff_X_mul, coeff_derivative,
        coeff_eq_zero_of_natDegree_lt hk_gt]
      simp

theorem roots_derivative_kernel_norm_le_one (n : ℕ) :
    ∀ z ∈ (schmeisserDerivativeKernel n).roots, ‖z‖ ≤ 1 := by
  intro z hz
  by_cases hn : n = 0
  · simp [schmeisserDerivativeKernel, hn] at hz
  by_cases hn_one : n = 1
  · subst n
    simp at hz
    simp [hz]
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have hkernel_assoc :
      schmeisserDerivativeKernel n = C (n : ℂ) * (X * (X + 1) ^ (n - 1)) := by
    rw [schmeisserDerivativeKernel, mul_assoc]
  rw [hkernel_assoc, roots_C_mul _ (by exact_mod_cast hn)] at hz
  have hprod_ne : (X * (X + 1) ^ (n - 1) : ℂ[X]) ≠ 0 := by
    exact mul_ne_zero X_ne_zero
      (pow_ne_zero _ (by simpa using X_add_C_ne_zero (1 : ℂ)))
  have hroots_X_add_one : (X + 1 : ℂ[X]).roots = ({-1} : Multiset ℂ) := by
    simpa using roots_X_add_C (1 : ℂ)
  rw [roots_mul hprod_ne, roots_X, roots_pow, hroots_X_add_one] at hz
  simp at hz
  rcases hz with hzero | ⟨_hnsub, hneg⟩
  · simp [hzero]
  · simp [hneg]

private theorem schur_boundary_core_normSq_sub_eq (A B : ℂ) :
    Complex.normSq (2 + A + B) - Complex.normSq (A + B + 2 * A * B) =
      4 * (1 - Complex.normSq (A * B) +
        (1 - Complex.normSq B) * A.re + (1 - Complex.normSq A) * B.re) := by
  simp [Complex.normSq_apply]
  ring

theorem schur_boundary_core_normSq_lt {A B : ℂ}
    (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) :
    Complex.normSq (A + B + 2 * A * B) < Complex.normSq (2 + A + B) := by
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg A
  have hB0 : 0 ≤ ‖B‖ := norm_nonneg B
  have hA_sq_lt : ‖A‖ ^ 2 < 1 := by
    have := (sq_lt_sq₀ hA0 (by norm_num : (0 : ℝ) ≤ 1)).mpr hA
    simpa using this
  have hB_sq_lt : ‖B‖ ^ 2 < 1 := by
    have := (sq_lt_sq₀ hB0 (by norm_num : (0 : ℝ) ≤ 1)).mpr hB
    simpa using this
  have hcoefA_nonneg : 0 ≤ 1 - Complex.normSq A := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  have hcoefB_nonneg : 0 ≤ 1 - Complex.normSq B := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  have hreA : -‖A‖ ≤ A.re := neg_le_of_abs_le (Complex.abs_re_le_norm A)
  have hreB : -‖B‖ ≤ B.re := neg_le_of_abs_le (Complex.abs_re_le_norm B)
  have htermA : (1 - Complex.normSq B) * (-‖A‖) ≤ (1 - Complex.normSq B) * A.re :=
    mul_le_mul_of_nonneg_left hreA hcoefB_nonneg
  have htermB : (1 - Complex.normSq A) * (-‖B‖) ≤ (1 - Complex.normSq A) * B.re :=
    mul_le_mul_of_nonneg_left hreB hcoefA_nonneg
  have hcore_lower :
      1 - Complex.normSq (A * B) + (1 - Complex.normSq B) * (-‖A‖) +
          (1 - Complex.normSq A) * (-‖B‖) ≤
        1 - Complex.normSq (A * B) + (1 - Complex.normSq B) * A.re +
          (1 - Complex.normSq A) * B.re := by
    nlinarith
  have hcore_pos_lower :
      0 < 1 - Complex.normSq (A * B) + (1 - Complex.normSq B) * (-‖A‖) +
          (1 - Complex.normSq A) * (-‖B‖) := by
    rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq A, Complex.normSq_eq_norm_sq B]
    have hAB : ‖A‖ * ‖B‖ < 1 := by
      nlinarith [mul_lt_mul_of_nonneg hA hB hA0 hB0]
    have hpos := mul_pos (sub_pos.mpr hA) (mul_pos (sub_pos.mpr hB) (sub_pos.mpr hAB))
    nlinarith
  have hcore_pos :
      0 < 1 - Complex.normSq (A * B) +
        (1 - Complex.normSq B) * A.re + (1 - Complex.normSq A) * B.re :=
    lt_of_lt_of_le hcore_pos_lower hcore_lower
  have hsub_pos : 0 < Complex.normSq (2 + A + B) -
      Complex.normSq (A + B + 2 * A * B) := by
    rw [schur_boundary_core_normSq_sub_eq]
    positivity
  linarith

theorem schur_boundary_normSq_lt {A B c : ℂ}
    (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) (hc : ‖c‖ = 1) :
    Complex.normSq (A + B + 2 * A * B * c) <
      Complex.normSq (2 + (A + B) * c) := by
  have hcnormSq : Complex.normSq c = 1 := by
    rw [Complex.normSq_eq_norm_sq, hc]
    norm_num
  have hAc : ‖A * c‖ < 1 := by
    rw [norm_mul, hc, mul_one]
    exact hA
  have hBc : ‖B * c‖ < 1 := by
    rw [norm_mul, hc, mul_one]
    exact hB
  have hcore := schur_boundary_core_normSq_lt (A := A * c) (B := B * c) hAc hBc
  have hnum_eq :
      A + B + 2 * A * B * c =
        (A * c + B * c + 2 * (A * c) * (B * c)) * (starRingEnd ℂ) c := by
    have hc_mul : c * (starRingEnd ℂ) c = 1 := by
      simpa [hcnormSq] using Complex.mul_conj c
    calc
      A + B + 2 * A * B * c = (A + B + 2 * A * B * c) * 1 := by ring
      _ = (A + B + 2 * A * B * c) * (c * (starRingEnd ℂ) c) := by rw [hc_mul]
      _ = (A * c + B * c + 2 * (A * c) * (B * c)) * (starRingEnd ℂ) c := by ring
  have hnum_norm :
      Complex.normSq (A + B + 2 * A * B * c) =
        Complex.normSq (A * c + B * c + 2 * (A * c) * (B * c)) := by
    rw [hnum_eq, Complex.normSq_mul, Complex.normSq_conj, hcnormSq, mul_one]
  have hden_norm :
      Complex.normSq (2 + (A + B) * c) =
        Complex.normSq (2 + A * c + B * c) := by
    congr 1
    ring
  rw [hnum_norm, hden_norm]
  exact hcore

theorem schur_boundary_denominator_ne_zero {A B c : ℂ}
    (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) (hc : ‖c‖ = 1) :
    2 + (A + B) * c ≠ 0 := by
  have hlt := schur_boundary_normSq_lt (A := A) (B := B) (c := c) hA hB hc
  intro hzero
  rw [hzero, Complex.normSq_zero] at hlt
  exact not_lt_of_ge (Complex.normSq_nonneg _) hlt

/-- Roots outside the radius, weighted by `‖z‖ / r` with multiplicity. -/
def rootsRadiusProduct (r : ℝ) (s : Multiset ℂ) : ℝ :=
  ((s.filter fun z => r ≤ ‖z‖).map fun z => ‖z‖ / r).prod

@[simp]
theorem rootsRadiusProduct_zero (r : ℝ) :
    rootsRadiusProduct r (0 : Multiset ℂ) = 1 := by
  simp [rootsRadiusProduct]

@[simp]
theorem rootsRadiusProduct_one (s : Multiset ℂ) :
    rootsRadiusProduct 1 s =
      ((s.filter fun z => 1 ≤ ‖z‖).map fun z => ‖z‖).prod := by
  simp [rootsRadiusProduct]

@[simp]
theorem filtered_norm_div_one (s : Multiset ℂ) :
    ((s.filter fun z => 1 ≤ ‖z‖).map fun z => ‖z‖ / (1 : ℝ)).prod =
      ((s.filter fun z => 1 ≤ ‖z‖).map fun z => ‖z‖).prod := by
  simp

theorem rootsRadiusProduct_eq_div_pow_card {r : ℝ} (s : Multiset ℂ) :
    rootsRadiusProduct r s =
      ((s.filter fun z => r ≤ ‖z‖).map fun z => ‖z‖).prod /
        r ^ (s.filter fun z => r ≤ ‖z‖).card := by
  rw [rootsRadiusProduct]
  simp_rw [div_eq_mul_inv]
  rw [Multiset.prod_map_mul]
  simp

theorem rootsRadiusProduct_mul_pow_card {r : ℝ} (hr : r ≠ 0) (s : Multiset ℂ) :
    rootsRadiusProduct r s * r ^ (s.filter fun z => r ≤ ‖z‖).card =
      ((s.filter fun z => r ≤ ‖z‖).map fun z => ‖z‖).prod := by
  rw [rootsRadiusProduct_eq_div_pow_card]
  field_simp [pow_ne_zero _ hr]

theorem rootsRadiusProduct_nonneg {r : ℝ} (hr : 0 ≤ r) (s : Multiset ℂ) :
    0 ≤ rootsRadiusProduct r s := by
  rw [rootsRadiusProduct]
  apply Multiset.prod_nonneg
  intro x hx
  rw [Multiset.mem_map] at hx
  rcases hx with ⟨z, _hz, rfl⟩
  exact div_nonneg (norm_nonneg z) hr

theorem rootsRadiusProduct_eq_one_of_forall_lt {r : ℝ} {s : Multiset ℂ}
    (h : ∀ z ∈ s, ‖z‖ < r) :
    rootsRadiusProduct r s = 1 := by
  rw [rootsRadiusProduct, Multiset.filter_eq_nil.2]
  · simp
  intro z hz hz_ge
  exact not_le_of_gt (h z hz) hz_ge

/--
The number of roots outside a closed radius threshold, counted with
multiplicity through the `Polynomial.roots` multiset.  This is the root-count
form of the zero-control predicate in `SPEC/Libraries/hex-poly-z-mathlib.md`.
-/
def rootsOutsideRadiusCount (r : ℝ) (s : Multiset ℂ) : ℕ :=
  (s.filter fun z => r ≤ ‖z‖).card

@[simp]
theorem rootsOutsideRadiusCount_zero (r : ℝ) :
    rootsOutsideRadiusCount r (0 : Multiset ℂ) = 0 := by
  simp [rootsOutsideRadiusCount]

theorem rootsOutsideRadiusCount_eq_filter_card (r : ℝ) (s : Multiset ℂ) :
    rootsOutsideRadiusCount r s = (s.filter fun z => r ≤ ‖z‖).card := rfl

/--
The number of roots strictly outside an open radius threshold, counted with
multiplicity through the `Polynomial.roots` multiset.
-/
def rootsStrictlyOutsideRadiusCount (r : ℝ) (s : Multiset ℂ) : ℕ :=
  (s.filter fun z => r < ‖z‖).card

@[simp]
theorem rootsStrictlyOutsideRadiusCount_zero (r : ℝ) :
    rootsStrictlyOutsideRadiusCount r (0 : Multiset ℂ) = 0 := by
  simp [rootsStrictlyOutsideRadiusCount]

theorem rootsStrictlyOutsideRadiusCount_eq_filter_card (r : ℝ) (s : Multiset ℂ) :
    rootsStrictlyOutsideRadiusCount r s = (s.filter fun z => r < ‖z‖).card := rfl

/-- All roots of a multiset lie in the closed disk centered at `c` of radius `R`. -/
def rootsInClosedDisk (c : ℂ) (R : ℝ) (s : Multiset ℂ) : Prop :=
  ∀ z ∈ s, ‖z - c‖ ≤ R

/-- All roots of `p` lie in the closed unit disk, with multiplicity carried by `roots`. -/
def rootsInClosedUnitDisk (p : ℂ[X]) : Prop :=
  rootsInClosedDisk 0 1 p.roots

theorem rootsInClosedUnitDisk_iff (p : ℂ[X]) :
    rootsInClosedUnitDisk p ↔ ∀ z ∈ p.roots, ‖z‖ ≤ 1 := by
  simp [rootsInClosedUnitDisk, rootsInClosedDisk]

/--
Radius-wise exterior-root-count domination from radius `r` onward.  This is
the finite multiset handoff used to turn Grace-Walsh-Szego/de Bruijn-Springer
zero control into exterior-product domination.
-/
def exteriorRootCountDominatedFrom (r : ℝ) (s t : Multiset ℂ) : Prop :=
  ∀ ρ : ℝ, r ≤ ρ → rootsOutsideRadiusCount ρ s ≤ rootsOutsideRadiusCount ρ t

/--
Open-threshold exterior-root-count domination from radius `r` onward. This is
the natural multiplicity-preserving surface for the open circular-domain
de Bruijn-Springer source before any closed-radius limiting wrapper is applied.
-/
def openExteriorRootCountDominatedFrom (r : ℝ) (s t : Multiset ℂ) : Prop :=
  ∀ ρ : ℝ, r ≤ ρ → rootsStrictlyOutsideRadiusCount ρ s ≤ rootsStrictlyOutsideRadiusCount ρ t

/--
Derivative-free zero-control statement for Schmeisser compositions: every
positive radius has no more exterior roots in the composition than in `f`,
counted with multiplicity through `Polynomial.roots`.
-/
def schmeisserCompositionZeroControl (n : ℕ) (f g : ℂ[X]) : Prop :=
  ∀ r : ℝ, 0 < r →
    rootsOutsideRadiusCount r (schmeisserComposition n f g).roots ≤
      rootsOutsideRadiusCount r f.roots

/--
Open-domain zero-control statement for Schmeisser compositions: every positive
open radius has no more strictly exterior roots in the composition than in `f`,
counted with multiplicity through `Polynomial.roots`.
-/
def schmeisserCompositionOpenZeroControl (n : ℕ) (f g : ℂ[X]) : Prop :=
  ∀ r : ℝ, 0 < r →
    rootsStrictlyOutsideRadiusCount r (schmeisserComposition n f g).roots ≤
      rootsStrictlyOutsideRadiusCount r f.roots

/--
Degree-`n` Grace-Walsh-Szego/de Bruijn-Springer zero-control predicate for the
Schmeisser composition.  The conclusion is radius-wise root-count domination
over `Polynomial.roots`, so multiplicities and roots at zero stay visible.
-/
def graceWalshSzegoZeroControlAtDegree (n : ℕ) : Prop :=
  ∀ f g : ℂ[X],
    f.natDegree ≤ n ∧ g.natDegree ≤ n →
      rootsInClosedUnitDisk g →
        schmeisserCompositionZeroControl n f g

/--
Open circular-domain Grace-Walsh-Szego/de Bruijn-Springer source predicate for
the Schmeisser composition. The conclusion-side radius threshold is open, while
the input roots still lie in the closed unit disk, as in Schmeisser's source
hypothesis. Root counts use `Polynomial.roots`, preserving multiplicities.
-/
def graceWalshSzegoOpenZeroControlAtDegree (n : ℕ) : Prop :=
  ∀ f g : ℂ[X],
    f.natDegree ≤ n ∧ g.natDegree ≤ n →
      rootsInClosedUnitDisk g →
        schmeisserCompositionOpenZeroControl n f g

/--
Exact-degree open circular-domain source predicate for the Schmeisser
composition.  This is the corrected degree-two source surface: the broader
`natDegree ≤ n` predicate is not valid at `n = 2`, because lower-degree inputs
are still composed with the binomial normalization for degree bound `2`.
-/
def graceWalshSzegoOpenZeroControlAtExactDegree (n : ℕ) : Prop :=
  ∀ f g : ℂ[X],
    f.natDegree = n ∧ g.natDegree = n →
      rootsInClosedUnitDisk g →
        schmeisserCompositionOpenZeroControl n f g

/--
Closed-radius counterpart of `graceWalshSzegoOpenZeroControlAtExactDegree`,
kept separate so exact-degree source proofs can use the same open-to-closed
finite-multiset bridge as the existing degree-bound source surface.
-/
def graceWalshSzegoZeroControlAtExactDegree (n : ℕ) : Prop :=
  ∀ f g : ℂ[X],
    f.natDegree = n ∧ g.natDegree = n →
      rootsInClosedUnitDisk g →
        schmeisserCompositionZeroControl n f g

theorem graceWalshSzegoZeroControlAtDegree_zero :
    graceWalshSzegoZeroControlAtDegree 0 := by
  intro f g _hfg_degree _hg_roots r _hr
  rw [schmeisserComposition_zero]
  have hroots : (C (f.coeff 0 * g.coeff 0) : ℂ[X]).roots = 0 :=
    roots_C (f.coeff 0 * g.coeff 0)
  rw [hroots]
  simp [rootsOutsideRadiusCount]

theorem graceWalshSzegoOpenZeroControlAtDegree_zero :
    graceWalshSzegoOpenZeroControlAtDegree 0 := by
  intro f g _hfg_degree _hg_roots r _hr
  rw [schmeisserComposition_zero]
  have hroots : (C (f.coeff 0 * g.coeff 0) : ℂ[X]).roots = 0 :=
    roots_C (f.coeff 0 * g.coeff 0)
  rw [hroots]
  simp [rootsStrictlyOutsideRadiusCount]

private theorem schmeisserComposition_one_eq
    (f g : ℂ[X]) :
    schmeisserComposition 1 f g =
      C (f.coeff 1 * g.coeff 1) * X + C (f.coeff 0 * g.coeff 0) := by
  rw [eq_X_add_C_of_natDegree_le_one (natDegree_schmeisserComposition_le 1 f g)]
  simp [coeff_schmeisserComposition_of_le]

theorem graceWalshSzegoOpenZeroControlAtDegree_one :
    graceWalshSzegoOpenZeroControlAtDegree 1 := by
  intro f g hfg_degree hg_roots r _hr
  rw [schmeisserComposition_one_eq]
  by_cases hf1 : f.coeff 1 = 0
  · have hcomp_const :
        C (f.coeff 1 * g.coeff 1) * X + C (f.coeff 0 * g.coeff 0) =
          C (f.coeff 0 * g.coeff 0) := by
      simp [hf1]
    rw [hcomp_const, roots_C]
    simp [rootsStrictlyOutsideRadiusCount]
  by_cases hg1 : g.coeff 1 = 0
  · have hcomp_const :
        C (f.coeff 1 * g.coeff 1) * X + C (f.coeff 0 * g.coeff 0) =
          C (f.coeff 0 * g.coeff 0) := by
      simp [hg1]
    rw [hcomp_const, roots_C]
    simp [rootsStrictlyOutsideRadiusCount]
  have hfg1 : f.coeff 1 * g.coeff 1 ≠ 0 := mul_ne_zero hf1 hg1
  have hf_roots :
      f.roots = ({-((f.coeff 1)⁻¹ * f.coeff 0)} : Multiset ℂ) := by
    have hf_linear : f = C (f.coeff 1) * X + C (f.coeff 0) :=
      eq_X_add_C_of_natDegree_le_one hfg_degree.1
    calc
      f.roots = (C (f.coeff 1) * X + C (f.coeff 0) : ℂ[X]).roots :=
        congrArg roots hf_linear
      _ = ({-((f.coeff 1)⁻¹ * f.coeff 0)} : Multiset ℂ) := by
        exact roots_C_mul_X_add_C (a := f.coeff 1) (b := f.coeff 0) hf1
  have hg_roots_eq :
      g.roots = ({-((g.coeff 1)⁻¹ * g.coeff 0)} : Multiset ℂ) := by
    have hg_linear : g = C (g.coeff 1) * X + C (g.coeff 0) :=
      eq_X_add_C_of_natDegree_le_one hfg_degree.2
    calc
      g.roots = (C (g.coeff 1) * X + C (g.coeff 0) : ℂ[X]).roots :=
        congrArg roots hg_linear
      _ = ({-((g.coeff 1)⁻¹ * g.coeff 0)} : Multiset ℂ) := by
        exact roots_C_mul_X_add_C (a := g.coeff 1) (b := g.coeff 0) hg1
  have hg_root_norm :
      ‖-((g.coeff 1)⁻¹ * g.coeff 0)‖ ≤ 1 := by
    rw [rootsInClosedUnitDisk_iff] at hg_roots
    exact hg_roots (-((g.coeff 1)⁻¹ * g.coeff 0)) (by simp [hg_roots_eq])
  have hcomp_roots :
      (C (f.coeff 1 * g.coeff 1) * X + C (f.coeff 0 * g.coeff 0) : ℂ[X]).roots =
        ({-((f.coeff 1 * g.coeff 1)⁻¹ * (f.coeff 0 * g.coeff 0))} : Multiset ℂ) := by
    rw [roots_C_mul_X_add_C (f.coeff 0 * g.coeff 0) hfg1]
  rw [hcomp_roots, hf_roots]
  have hnorm :
      ‖-((f.coeff 1 * g.coeff 1)⁻¹ * (f.coeff 0 * g.coeff 0))‖ ≤
        ‖-((f.coeff 1)⁻¹ * f.coeff 0)‖ := by
    have hfactor :
        (f.coeff 1 * g.coeff 1)⁻¹ * (f.coeff 0 * g.coeff 0) =
          ((f.coeff 1)⁻¹ * f.coeff 0) * ((g.coeff 1)⁻¹ * g.coeff 0) := by
      field_simp [hf1, hg1]
    calc
      ‖-((f.coeff 1 * g.coeff 1)⁻¹ * (f.coeff 0 * g.coeff 0))‖ =
          ‖-((f.coeff 1)⁻¹ * f.coeff 0)‖ *
            ‖-((g.coeff 1)⁻¹ * g.coeff 0)‖ := by
        rw [norm_neg, hfactor, norm_mul, norm_neg, norm_neg]
      _ ≤ ‖-((f.coeff 1)⁻¹ * f.coeff 0)‖ * 1 :=
        mul_le_mul_of_nonneg_left hg_root_norm (norm_nonneg _)
      _ = ‖-((f.coeff 1)⁻¹ * f.coeff 0)‖ := by simp
  simp only [rootsStrictlyOutsideRadiusCount, Multiset.filter_singleton]
  by_cases hlarge : r < ‖-((f.coeff 1 * g.coeff 1)⁻¹ * (f.coeff 0 * g.coeff 0))‖
  · have : r < ‖-((f.coeff 1)⁻¹ * f.coeff 0)‖ := lt_of_lt_of_le hlarge hnorm
    rw [if_pos hlarge, if_pos this]
    simp
  · rw [if_neg hlarge]
    exact Nat.zero_le _

theorem exteriorRootCountDominatedFrom_of_schmeisserCompositionZeroControl
    {n : ℕ} {f g : ℂ[X]} {r : ℝ}
    (hr : 0 < r)
    (hzero : schmeisserCompositionZeroControl n f g) :
    exteriorRootCountDominatedFrom r
      (schmeisserComposition n f g).roots f.roots := by
  intro ρ hρ
  exact hzero ρ (lt_of_lt_of_le hr hρ)

theorem openExteriorRootCountDominatedFrom_of_schmeisserCompositionOpenZeroControl
    {n : ℕ} {f g : ℂ[X]} {r : ℝ}
    (hr : 0 < r)
    (hzero : schmeisserCompositionOpenZeroControl n f g) :
    openExteriorRootCountDominatedFrom r
      (schmeisserComposition n f g).roots f.roots := by
  intro ρ hρ
  exact hzero ρ (lt_of_lt_of_le hr hρ)

theorem rootsOutsideRadiusCount_le_of_schmeisserCompositionZeroControl
    {n : ℕ} {f g : ℂ[X]} {r : ℝ}
    (hr : 0 < r)
    (hzero : schmeisserCompositionZeroControl n f g) :
    rootsOutsideRadiusCount r (schmeisserComposition n f g).roots ≤
      rootsOutsideRadiusCount r f.roots :=
  hzero r hr

theorem rootsStrictlyOutsideRadiusCount_le_of_schmeisserCompositionOpenZeroControl
    {n : ℕ} {f g : ℂ[X]} {r : ℝ}
    (hr : 0 < r)
    (hzero : schmeisserCompositionOpenZeroControl n f g) :
    rootsStrictlyOutsideRadiusCount r (schmeisserComposition n f g).roots ≤
      rootsStrictlyOutsideRadiusCount r f.roots :=
  hzero r hr

theorem rootsOutsideRadiusCount_le_of_graceWalshSzegoZeroControlAtDegree
    {n : ℕ} {f g : ℂ[X]} {r : ℝ}
    (hsource : graceWalshSzegoZeroControlAtDegree n)
    (hr : 0 < r)
    (hfg_degree : f.natDegree ≤ n ∧ g.natDegree ≤ n)
    (hg_roots : rootsInClosedUnitDisk g) :
    rootsOutsideRadiusCount r (schmeisserComposition n f g).roots ≤
      rootsOutsideRadiusCount r f.roots :=
  hsource f g hfg_degree hg_roots r hr

theorem rootsStrictlyOutsideRadiusCount_le_of_graceWalshSzegoOpenZeroControlAtDegree
    {n : ℕ} {f g : ℂ[X]} {r : ℝ}
    (hsource : graceWalshSzegoOpenZeroControlAtDegree n)
    (hr : 0 < r)
    (hfg_degree : f.natDegree ≤ n ∧ g.natDegree ≤ n)
    (hg_roots : rootsInClosedUnitDisk g) :
    rootsStrictlyOutsideRadiusCount r (schmeisserComposition n f g).roots ≤
      rootsStrictlyOutsideRadiusCount r f.roots :=
  hsource f g hfg_degree hg_roots r hr

theorem roots_count_radius_le_of_schmeisserComposition
    {n : ℕ} {f g : ℂ[X]} {r : ℝ}
    (hsource : graceWalshSzegoZeroControlAtDegree n)
    (hr : 0 < r)
    (hfg_degree : f.natDegree ≤ n ∧ g.natDegree ≤ n)
    (hg_roots : ∀ z ∈ g.roots, ‖z‖ ≤ 1) :
    ((schmeisserComposition n f g).roots.filter fun ζ => r ≤ ‖ζ‖).card ≤
      ((f.roots.filter fun z => r ≤ ‖z‖).card) := by
  simpa [rootsOutsideRadiusCount] using
    rootsOutsideRadiusCount_le_of_graceWalshSzegoZeroControlAtDegree
      hsource hr hfg_degree ((rootsInClosedUnitDisk_iff g).2 hg_roots)

theorem roots_strictly_count_radius_le_of_schmeisserComposition
    {n : ℕ} {f g : ℂ[X]} {r : ℝ}
    (hsource : graceWalshSzegoOpenZeroControlAtDegree n)
    (hr : 0 < r)
    (hfg_degree : f.natDegree ≤ n ∧ g.natDegree ≤ n)
    (hg_roots : ∀ z ∈ g.roots, ‖z‖ ≤ 1) :
    ((schmeisserComposition n f g).roots.filter fun ζ => r < ‖ζ‖).card ≤
      ((f.roots.filter fun z => r < ‖z‖).card) := by
  simpa [rootsStrictlyOutsideRadiusCount] using
    rootsStrictlyOutsideRadiusCount_le_of_graceWalshSzegoOpenZeroControlAtDegree
      hsource hr hfg_degree ((rootsInClosedUnitDisk_iff g).2 hg_roots)

theorem rootsStrictlyOutsideRadiusCount_le_of_graceWalshSzegoOpenZeroControlAtExactDegree
    {n : ℕ} {f g : ℂ[X]} {r : ℝ}
    (hsource : graceWalshSzegoOpenZeroControlAtExactDegree n)
    (hr : 0 < r)
    (hfg_degree : f.natDegree = n ∧ g.natDegree = n)
    (hg_roots : rootsInClosedUnitDisk g) :
    rootsStrictlyOutsideRadiusCount r (schmeisserComposition n f g).roots ≤
      rootsStrictlyOutsideRadiusCount r f.roots :=
  hsource f g hfg_degree hg_roots r hr

theorem roots_strictly_count_radius_le_of_schmeisserComposition_exact_source
    {n : ℕ} {f g : ℂ[X]} {r : ℝ}
    (hsource : graceWalshSzegoOpenZeroControlAtExactDegree n)
    (hr : 0 < r)
    (hfg_degree : f.natDegree = n ∧ g.natDegree = n)
    (hg_roots : ∀ z ∈ g.roots, ‖z‖ ≤ 1) :
    ((schmeisserComposition n f g).roots.filter fun ζ => r < ‖ζ‖).card ≤
      ((f.roots.filter fun z => r < ‖z‖).card) := by
  simpa [rootsStrictlyOutsideRadiusCount] using
    rootsStrictlyOutsideRadiusCount_le_of_graceWalshSzegoOpenZeroControlAtExactDegree
      hsource hr hfg_degree ((rootsInClosedUnitDisk_iff g).2 hg_roots)

theorem schmeisserCompositionZeroControl_of_graceWalshSzegoZeroControlAtDegree
    {n : ℕ} {f g : ℂ[X]}
    (hsource : graceWalshSzegoZeroControlAtDegree n)
    (hfg_degree : f.natDegree ≤ n ∧ g.natDegree ≤ n)
    (hg_roots : rootsInClosedUnitDisk g) :
    schmeisserCompositionZeroControl n f g :=
  hsource f g hfg_degree hg_roots

theorem schmeisserCompositionOpenZeroControl_of_graceWalshSzegoOpenZeroControlAtDegree
    {n : ℕ} {f g : ℂ[X]}
    (hsource : graceWalshSzegoOpenZeroControlAtDegree n)
    (hfg_degree : f.natDegree ≤ n ∧ g.natDegree ≤ n)
    (hg_roots : rootsInClosedUnitDisk g) :
    schmeisserCompositionOpenZeroControl n f g :=
  hsource f g hfg_degree hg_roots

theorem schmeisserCompositionOpenZeroControl_of_graceWalshSzegoOpenZeroControlAtExactDegree
    {n : ℕ} {f g : ℂ[X]}
    (hsource : graceWalshSzegoOpenZeroControlAtExactDegree n)
    (hfg_degree : f.natDegree = n ∧ g.natDegree = n)
    (hg_roots : rootsInClosedUnitDisk g) :
    schmeisserCompositionOpenZeroControl n f g :=
  hsource f g hfg_degree hg_roots

theorem schmeisserCompositionZeroControl_of_graceWalshSzegoZeroControlAtExactDegree
    {n : ℕ} {f g : ℂ[X]}
    (hsource : graceWalshSzegoZeroControlAtExactDegree n)
    (hfg_degree : f.natDegree = n ∧ g.natDegree = n)
    (hg_roots : rootsInClosedUnitDisk g) :
    schmeisserCompositionZeroControl n f g :=
  hsource f g hfg_degree hg_roots

/--
For any positive radius `r` and any two finite multisets `s`, `t` of complex
numbers, there is a strictly smaller positive threshold `ρ < r` at which the
open-radius filter equals the closed-radius filter simultaneously on both
multisets.  This is the finite-multiset open-to-closed witness used to derive
closed-radius count domination from an open-radius source hypothesis.
-/
private theorem exists_open_radius_witness_for_closed_count
    (s t : Multiset ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧
      (s.filter fun z => r ≤ ‖z‖) = (s.filter fun z => ρ < ‖z‖) ∧
      (t.filter fun z => r ≤ ‖z‖) = (t.filter fun z => ρ < ‖z‖) := by
  classical
  let belowList : List ℝ :=
    0 :: ((((s.map fun z => ‖z‖) + (t.map fun z => ‖z‖)).filter
            fun x => x < r).toList)
  have h_len : 0 < belowList.length := by simp [belowList]
  let M : ℝ := belowList.maximum_of_length_pos h_len
  have hM_mem : M ∈ belowList :=
    List.maximum_of_length_pos_mem (l := belowList) h_len
  have hzero_mem : (0 : ℝ) ∈ belowList := by simp [belowList]
  have hM_lt_r : M < r := by
    rcases List.mem_cons.1 hM_mem with hM0 | hM_tail
    · simpa [hM0] using hr
    · rw [Multiset.mem_toList] at hM_tail
      exact (Multiset.mem_filter.1 hM_tail).2
  have hM_nonneg : 0 ≤ M :=
    List.le_maximum_of_length_pos_of_mem (l := belowList) (a := 0)
      hzero_mem h_len
  refine ⟨(M + r) / 2, by linarith, by linarith, ?_, ?_⟩
  · refine Multiset.filter_congr ?_
    intro z hz
    refine ⟨fun hrz => by linarith, fun hρz => ?_⟩
    by_contra hnotr
    have hnotr : ‖z‖ < r := lt_of_not_ge hnotr
    have hmem : ‖z‖ ∈ belowList := by
      refine List.mem_cons.2 (Or.inr ?_)
      rw [Multiset.mem_toList, Multiset.mem_filter]
      refine ⟨?_, hnotr⟩
      rw [Multiset.mem_add]
      exact Or.inl (Multiset.mem_map.2 ⟨z, hz, rfl⟩)
    have : ‖z‖ ≤ M :=
      List.le_maximum_of_length_pos_of_mem (l := belowList) (a := ‖z‖) hmem h_len
    linarith
  · refine Multiset.filter_congr ?_
    intro z hz
    refine ⟨fun hrz => by linarith, fun hρz => ?_⟩
    by_contra hnotr
    have hnotr : ‖z‖ < r := lt_of_not_ge hnotr
    have hmem : ‖z‖ ∈ belowList := by
      refine List.mem_cons.2 (Or.inr ?_)
      rw [Multiset.mem_toList, Multiset.mem_filter]
      refine ⟨?_, hnotr⟩
      rw [Multiset.mem_add]
      exact Or.inr (Multiset.mem_map.2 ⟨z, hz, rfl⟩)
    have : ‖z‖ ≤ M :=
      List.le_maximum_of_length_pos_of_mem (l := belowList) (a := ‖z‖) hmem h_len
    linarith

/--
Closed-radius count-domination wrapper derived from the open-radius
de Bruijn-Springer / Grace-Walsh-Szego source theorem.  Given the open-form
source hypothesis at degree `n`, the closed-radius filter cardinality on the
Schmeisser composition is bounded by the closed-radius filter cardinality on
`f`, with multiplicities preserved by `Polynomial.roots`.
-/
theorem roots_count_radius_le_of_schmeisserComposition_source
    {n : ℕ} {f g : ℂ[X]} {r : ℝ}
    (hsource : graceWalshSzegoOpenZeroControlAtDegree n)
    (hr : 0 < r)
    (hfg_degree : f.natDegree ≤ n ∧ g.natDegree ≤ n)
    (hg_roots : ∀ z ∈ g.roots, ‖z‖ ≤ 1) :
    ((schmeisserComposition n f g).roots.filter fun ζ => r ≤ ‖ζ‖).card ≤
      ((f.roots.filter fun z => r ≤ ‖z‖).card) := by
  classical
  obtain ⟨ρ, hρ_pos, _hρ_lt_r, hs_eq, ht_eq⟩ :=
    exists_open_radius_witness_for_closed_count
      (schmeisserComposition n f g).roots f.roots hr
  rw [hs_eq, ht_eq]
  have hopen :=
    hsource f g hfg_degree ((rootsInClosedUnitDisk_iff g).2 hg_roots) ρ hρ_pos
  simpa [rootsStrictlyOutsideRadiusCount] using hopen

theorem roots_count_radius_le_of_schmeisserComposition_exact_source
    {n : ℕ} {f g : ℂ[X]} {r : ℝ}
    (hsource : graceWalshSzegoOpenZeroControlAtExactDegree n)
    (hr : 0 < r)
    (hfg_degree : f.natDegree = n ∧ g.natDegree = n)
    (hg_roots : ∀ z ∈ g.roots, ‖z‖ ≤ 1) :
    ((schmeisserComposition n f g).roots.filter fun ζ => r ≤ ‖ζ‖).card ≤
      ((f.roots.filter fun z => r ≤ ‖z‖).card) := by
  classical
  obtain ⟨ρ, hρ_pos, _hρ_lt_r, hs_eq, ht_eq⟩ :=
    exists_open_radius_witness_for_closed_count
      (schmeisserComposition n f g).roots f.roots hr
  rw [hs_eq, ht_eq]
  have hopen :=
    hsource f g hfg_degree ((rootsInClosedUnitDisk_iff g).2 hg_roots) ρ hρ_pos
  simpa [rootsStrictlyOutsideRadiusCount] using hopen

/--
Predicate-level lift from the open-form Grace-Walsh-Szego / de Bruijn-Springer
source theorem to the closed-form one.  Combined with
`graceWalshSzegoZeroControlAtDegree_zero`, this reduces the closed source proof
obligation at every degree to the open one.
-/
theorem graceWalshSzegoZeroControlAtDegree_of_open
    {n : ℕ}
    (hopen : graceWalshSzegoOpenZeroControlAtDegree n) :
    graceWalshSzegoZeroControlAtDegree n := by
  intro f g hfg_degree hg_roots r hr
  rw [rootsInClosedUnitDisk_iff] at hg_roots
  have := roots_count_radius_le_of_schmeisserComposition_source
    hopen hr hfg_degree hg_roots
  simpa [rootsOutsideRadiusCount] using this

theorem graceWalshSzegoZeroControlAtExactDegree_of_open
    {n : ℕ}
    (hopen : graceWalshSzegoOpenZeroControlAtExactDegree n) :
    graceWalshSzegoZeroControlAtExactDegree n := by
  intro f g hfg_degree hg_roots r hr
  rw [rootsInClosedUnitDisk_iff] at hg_roots
  have := roots_count_radius_le_of_schmeisserComposition_exact_source
    hopen hr hfg_degree hg_roots
  simpa [rootsOutsideRadiusCount] using this

private theorem multiset_prod_le_prod_of_forall_count_ge_le
    {s t : Multiset ℝ}
    (hs_one : ∀ x ∈ s, 1 ≤ x)
    (ht_one : ∀ x ∈ t, 1 ≤ x)
    (hcount : ∀ ρ : ℝ, 1 ≤ ρ →
      (s.filter fun x => ρ ≤ x).card ≤ (t.filter fun x => ρ ≤ x).card) :
    s.prod ≤ t.prod := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ s t : Multiset ℝ,
      (∀ x ∈ s, 1 ≤ x) →
      (∀ x ∈ t, 1 ≤ x) →
      (∀ ρ : ℝ, 1 ≤ ρ →
        (s.filter fun x => ρ ≤ x).card ≤ (t.filter fun x => ρ ≤ x).card) →
      s.card = n →
      s.prod ≤ t.prod
  refine (Nat.strongRecOn (motive := P) s.card ?_) s t hs_one ht_one hcount rfl
  intro n ih s t hs_one ht_one hcount hs_card
  by_cases hs_zero : s = 0
  · subst s
    simpa using Multiset.one_le_prod (s := t) ht_one
  have hs_card_pos : 0 < s.card := Multiset.card_pos.2 hs_zero
  let a : ℝ := s.toList.maximum_of_length_pos (by simpa using hs_card_pos)
  have ha_list : a ∈ s.toList :=
    List.maximum_of_length_pos_mem (l := s.toList) (by simpa using hs_card_pos)
  have ha_mem : a ∈ s := by simpa using ha_list
  have ha_one : 1 ≤ a := hs_one a ha_mem
  have ha_max : ∀ x ∈ s, x ≤ a := by
    intro x hx
    exact List.le_maximum_of_length_pos_of_mem (l := s.toList) (a := x)
      (by simpa using hx) (by simpa using hs_card_pos)
  have hs_filter_pos : 0 < (s.filter fun x => a ≤ x).card := by
    rw [Multiset.card_pos_iff_exists_mem]
    exact ⟨a, by simp [ha_mem]⟩
  have ht_filter_pos : 0 < (t.filter fun x => a ≤ x).card :=
    lt_of_lt_of_le hs_filter_pos (hcount a ha_one)
  obtain ⟨b, hb_filter⟩ := Multiset.card_pos_iff_exists_mem.1 ht_filter_pos
  have hb_mem : b ∈ t := (Multiset.mem_filter.1 hb_filter).1
  have hab : a ≤ b := (Multiset.mem_filter.1 hb_filter).2
  have hs_erase_one : ∀ x ∈ s.erase a, 1 ≤ x := by
    intro x hx
    exact hs_one x (Multiset.mem_of_mem_erase hx)
  have ht_erase_one : ∀ x ∈ t.erase b, 1 ≤ x := by
    intro x hx
    exact ht_one x (Multiset.mem_of_mem_erase hx)
  have hcount_erase : ∀ ρ : ℝ, 1 ≤ ρ →
      ((s.erase a).filter fun x => ρ ≤ x).card ≤
        ((t.erase b).filter fun x => ρ ≤ x).card := by
    intro ρ hρ_one
    by_cases hρa : ρ ≤ a
    · have ha_filter : a ∈ s.filter fun x => ρ ≤ x := by
        simp [ha_mem, hρa]
      have hb_filter' : b ∈ t.filter fun x => ρ ≤ x := by
        simp [hb_mem, hρa.trans hab]
      have hs_card_filter :
          ((s.erase a).filter fun x => ρ ≤ x).card =
            ((s.filter fun x => ρ ≤ x).card).pred := by
        rw [← Multiset.sub_singleton a s, Multiset.filter_sub, Multiset.filter_singleton,
          if_pos hρa, Multiset.sub_singleton, Multiset.card_erase_of_mem ha_filter]
      have ht_card_filter :
          ((t.erase b).filter fun x => ρ ≤ x).card =
            ((t.filter fun x => ρ ≤ x).card).pred := by
        rw [← Multiset.sub_singleton b t, Multiset.filter_sub, Multiset.filter_singleton,
          if_pos (hρa.trans hab), Multiset.sub_singleton, Multiset.card_erase_of_mem hb_filter']
      rw [hs_card_filter, ht_card_filter]
      exact Nat.pred_le_pred (hcount ρ hρ_one)
    · have hρa_lt : a < ρ := lt_of_not_ge hρa
      have hs_filter_empty : (s.erase a).filter (fun x => ρ ≤ x) = 0 := by
        rw [Multiset.filter_eq_nil]
        intro x hx hxρ
        exact not_le_of_gt hρa_lt (hxρ.trans (ha_max x (Multiset.mem_of_mem_erase hx)))
      rw [hs_filter_empty]
      exact Nat.zero_le _
  have hs_erase_card_lt : (s.erase a).card < n := by
    rw [Multiset.card_erase_of_mem ha_mem, hs_card]
    exact Nat.pred_lt (Nat.ne_of_gt (by rwa [← hs_card]))
  have hrec :
      (s.erase a).prod ≤ (t.erase b).prod :=
    ih (s.erase a).card hs_erase_card_lt (s.erase a) (t.erase b)
      hs_erase_one ht_erase_one hcount_erase rfl
  have hs_prod : s.prod = a * (s.erase a).prod := by
    rw [← Multiset.prod_cons, Multiset.cons_erase ha_mem]
  have ht_prod : t.prod = b * (t.erase b).prod := by
    rw [← Multiset.prod_cons, Multiset.cons_erase hb_mem]
  rw [hs_prod, ht_prod]
  exact mul_le_mul hab hrec (Multiset.prod_nonneg fun x hx =>
    le_trans zero_le_one (hs_erase_one x hx)) (le_trans zero_le_one (ha_one.trans hab))

theorem rootsRadiusProduct_le_of_forall_count_radius_le
    {r : ℝ} {s t : Multiset ℂ}
    (hr : 0 < r)
    (hcount : ∀ ρ : ℝ, r ≤ ρ →
      (s.filter fun z => ρ ≤ ‖z‖).card ≤
        (t.filter fun z => ρ ≤ ‖z‖).card) :
    rootsRadiusProduct r s ≤ rootsRadiusProduct r t := by
  rw [rootsRadiusProduct, rootsRadiusProduct]
  apply multiset_prod_le_prod_of_forall_count_ge_le
  · intro x hx
    rw [Multiset.mem_map] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact (one_le_div₀ hr).2 (Multiset.mem_filter.1 hz).2
  · intro x hx
    rw [Multiset.mem_map] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact (one_le_div₀ hr).2 (Multiset.mem_filter.1 hz).2
  · intro ρ hρ
    have hρ_nonneg : 0 ≤ ρ := le_trans zero_le_one hρ
    have hthreshold : r ≤ ρ * r := by
      rw [← one_mul r]
      simpa [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right hρ hr.le
    have hs_count :
        (((s.filter fun z => r ≤ ‖z‖).map fun z => ‖z‖ / r).filter fun x => ρ ≤ x).card =
          (s.filter fun z => ρ * r ≤ ‖z‖).card := by
      rw [Multiset.filter_map, Multiset.card_map, Multiset.filter_filter]
      apply congrArg Multiset.card
      apply Multiset.filter_congr
      intro z _hz
      constructor
      · intro hz
        exact (le_div_iff₀ hr).1 hz.1
      · intro hz
        exact ⟨(le_div_iff₀ hr).2 hz, hthreshold.trans hz⟩
    have ht_count :
        (((t.filter fun z => r ≤ ‖z‖).map fun z => ‖z‖ / r).filter fun x => ρ ≤ x).card =
          (t.filter fun z => ρ * r ≤ ‖z‖).card := by
      rw [Multiset.filter_map, Multiset.card_map, Multiset.filter_filter]
      apply congrArg Multiset.card
      apply Multiset.filter_congr
      intro z _hz
      constructor
      · intro hz
        exact (le_div_iff₀ hr).1 hz.1
      · intro hz
        exact ⟨(le_div_iff₀ hr).2 hz, hthreshold.trans hz⟩
    rw [hs_count, ht_count]
    exact hcount (ρ * r) hthreshold

theorem rootsRadiusProduct_le_of_exteriorRootCountDominatedFrom
    {r : ℝ} {s t : Multiset ℂ}
    (hr : 0 < r)
    (hcount : exteriorRootCountDominatedFrom r s t) :
    rootsRadiusProduct r s ≤ rootsRadiusProduct r t :=
  rootsRadiusProduct_le_of_forall_count_radius_le hr (by
    intro ρ hρ
    simpa [rootsOutsideRadiusCount] using hcount ρ hρ)

theorem rootsRadiusProduct_le_of_schmeisserCompositionZeroControl
    {n : ℕ} {f g : ℂ[X]} {r : ℝ}
    (hr : 0 < r)
    (hzero : schmeisserCompositionZeroControl n f g) :
    rootsRadiusProduct r (schmeisserComposition n f g).roots ≤
      rootsRadiusProduct r f.roots :=
  rootsRadiusProduct_le_of_exteriorRootCountDominatedFrom hr
    (exteriorRootCountDominatedFrom_of_schmeisserCompositionZeroControl hr hzero)

theorem rootsRadiusProduct_le_of_graceWalshSzegoZeroControlAtDegree
    {n : ℕ} {f g : ℂ[X]} {r : ℝ}
    (hsource : graceWalshSzegoZeroControlAtDegree n)
    (hr : 0 < r)
    (hfg_degree : f.natDegree ≤ n ∧ g.natDegree ≤ n)
    (hg_roots : rootsInClosedUnitDisk g) :
    rootsRadiusProduct r (schmeisserComposition n f g).roots ≤
      rootsRadiusProduct r f.roots :=
  rootsRadiusProduct_le_of_schmeisserCompositionZeroControl hr
    (schmeisserCompositionZeroControl_of_graceWalshSzegoZeroControlAtDegree
      hsource hfg_degree hg_roots)

/--
Coefficient-form packaging for Schmeisser's Lemma 9 / de Bruijn-Springer
composition-polynomial theorem.

The hard analytic source theorem supplies `hsource` from the degree and
closed-unit-disk hypotheses. This lemma keeps the coefficient-form API used by
downstream derivative adapters separate from that analytic proof.
-/
theorem rootsRadiusProduct_le_of_schmeisserComposition_of_source
    {n : ℕ} {f g h : ℂ[X]} {r : ℝ}
    (_hr : 0 < r)
    (_hfg_degree : f.natDegree ≤ n ∧ g.natDegree ≤ n)
    (hh_degree : h.natDegree ≤ n)
    (hh_coeff : ∀ k ≤ n,
      h.coeff k = f.coeff k * (g.coeff k / (Nat.choose n k : ℂ)))
    (_hg_roots : ∀ z ∈ g.roots, ‖z‖ ≤ 1)
    (hsource :
      rootsRadiusProduct r (schmeisserComposition n f g).roots ≤
        rootsRadiusProduct r f.roots) :
    rootsRadiusProduct r h.roots ≤ rootsRadiusProduct r f.roots := by
  rw [eq_schmeisserComposition_of_natDegree_le_of_coeff hh_degree hh_coeff]
  exact hsource

theorem rootsRadiusProduct_le_of_schmeisserCompositionZeroControl_of_coeff
    {n : ℕ} {f g h : ℂ[X]} {r : ℝ}
    (hr : 0 < r)
    (_hfg_degree : f.natDegree ≤ n ∧ g.natDegree ≤ n)
    (hh_degree : h.natDegree ≤ n)
    (hh_coeff : ∀ k ≤ n,
      h.coeff k = f.coeff k * (g.coeff k / (Nat.choose n k : ℂ)))
    (_hg_roots : rootsInClosedUnitDisk g)
    (hzero : schmeisserCompositionZeroControl n f g) :
    rootsRadiusProduct r h.roots ≤ rootsRadiusProduct r f.roots := by
  rw [eq_schmeisserComposition_of_natDegree_le_of_coeff hh_degree hh_coeff]
  exact rootsRadiusProduct_le_of_schmeisserCompositionZeroControl hr hzero

theorem rootsRadiusProduct_le_of_graceWalshSzegoZeroControlAtDegree_of_coeff
    {n : ℕ} {f g h : ℂ[X]} {r : ℝ}
    (hsource : graceWalshSzegoZeroControlAtDegree n)
    (hr : 0 < r)
    (hfg_degree : f.natDegree ≤ n ∧ g.natDegree ≤ n)
    (hh_degree : h.natDegree ≤ n)
    (hh_coeff : ∀ k ≤ n,
      h.coeff k = f.coeff k * (g.coeff k / (Nat.choose n k : ℂ)))
    (hg_roots : rootsInClosedUnitDisk g) :
    rootsRadiusProduct r h.roots ≤ rootsRadiusProduct r f.roots := by
  rw [eq_schmeisserComposition_of_natDegree_le_of_coeff hh_degree hh_coeff]
  exact rootsRadiusProduct_le_of_graceWalshSzegoZeroControlAtDegree
    hsource hr hfg_degree hg_roots

/--
Radius-one compatibility wrapper for Schmeisser's Lemma 9 / de Bruijn-Springer
composition-polynomial theorem.
-/
theorem roots_filter_norm_product_le_of_schmeisserComposition_radius_one_of_source
    {n : ℕ} {f g h : ℂ[X]}
    (hfg_degree : f.natDegree ≤ n ∧ g.natDegree ≤ n)
    (hh_degree : h.natDegree ≤ n)
    (hh_coeff : ∀ k ≤ n,
      h.coeff k = f.coeff k * (g.coeff k / (Nat.choose n k : ℂ)))
    (hg_roots : ∀ z ∈ g.roots, ‖z‖ ≤ 1)
    (hsource :
      (((schmeisserComposition n f g).roots.filter fun ζ => 1 ≤ ‖ζ‖).map fun ζ => ‖ζ‖).prod ≤
        ((f.roots.filter fun z => 1 ≤ ‖z‖).map fun z => ‖z‖).prod) :
    ((h.roots.filter fun ζ => 1 ≤ ‖ζ‖).map fun ζ => ‖ζ‖).prod ≤
      ((f.roots.filter fun z => 1 ≤ ‖z‖).map fun z => ‖z‖).prod := by
  simpa [rootsRadiusProduct] using
    rootsRadiusProduct_le_of_schmeisserComposition_of_source
      (r := 1) (by norm_num) hfg_degree hh_degree hh_coeff hg_roots (by
        simpa [rootsRadiusProduct] using hsource)

end

end Polynomial
