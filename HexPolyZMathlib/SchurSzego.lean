import HexPolyZMathlib.Basic
import Mathlib.Analysis.Polynomial.MahlerMeasure

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

/-- Roots outside the radius, weighted by `‖z‖ / r` with multiplicity. -/
def rootsRadiusProduct (r : ℝ) (s : Multiset ℂ) : ℝ :=
  ((s.filter fun z => r ≤ ‖z‖).map fun z => ‖z‖ / r).prod

@[simp]
theorem rootsRadiusProduct_one (s : Multiset ℂ) :
    rootsRadiusProduct 1 s =
      ((s.filter fun z => 1 ≤ ‖z‖).map fun z => ‖z‖).prod := by
  simp [rootsRadiusProduct]

theorem rootsRadiusProduct_eq_div_pow_card {r : ℝ} (s : Multiset ℂ) :
    rootsRadiusProduct r s =
      ((s.filter fun z => r ≤ ‖z‖).map fun z => ‖z‖).prod /
        r ^ (s.filter fun z => r ≤ ‖z‖).card := by
  rw [rootsRadiusProduct]
  simp_rw [div_eq_mul_inv]
  rw [Multiset.prod_map_mul]
  simp

/--
Arbitrary-radius packaging for Schmeisser's Lemma 9 / de Bruijn-Springer
composition-polynomial theorem.

The hard analytic source theorem supplies `hsource` from the degree,
closed-unit-disk, and positive-radius hypotheses. This lemma keeps the
coefficient-form API separate from that analytic proof.
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

/--
Radius-one packaging for Schmeisser's Lemma 9 / de Bruijn-Springer
composition-polynomial theorem.

The hard analytic source theorem supplies `hsource` from the degree and
closed-unit-disk hypotheses. This lemma keeps the coefficient-form API used by
downstream derivative adapters separate from that analytic proof.
-/
theorem roots_filter_norm_product_le_of_schmeisserComposition_radius_one_of_source
    {n : ℕ} {f g h : ℂ[X]}
    (_hfg_degree : f.natDegree ≤ n ∧ g.natDegree ≤ n)
    (hh_degree : h.natDegree ≤ n)
    (hh_coeff : ∀ k ≤ n,
      h.coeff k = f.coeff k * (g.coeff k / (Nat.choose n k : ℂ)))
    (_hg_roots : ∀ z ∈ g.roots, ‖z‖ ≤ 1)
    (hsource :
      (((schmeisserComposition n f g).roots.filter fun ζ => 1 ≤ ‖ζ‖).map fun ζ => ‖ζ‖).prod ≤
        ((f.roots.filter fun z => 1 ≤ ‖z‖).map fun z => ‖z‖).prod) :
    ((h.roots.filter fun ζ => 1 ≤ ‖ζ‖).map fun ζ => ‖ζ‖).prod ≤
      ((f.roots.filter fun z => 1 ≤ ‖z‖).map fun z => ‖z‖).prod := by
  rw [eq_schmeisserComposition_of_natDegree_le_of_coeff hh_degree hh_coeff]
  exact hsource

end

end Polynomial
