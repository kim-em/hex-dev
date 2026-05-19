import HexPolyZMathlib.Basic
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Normed.Module.Convex

/-!
Schur-reflected Robinson forms for complex polynomials.

The Robinson form keeps roots in the closed unit disk as the usual factors
`X - C α` and reflects exterior roots to `1 - C (conj α) * X`.  This form is
the local polynomial transform used by the later Mahler/Boyd derivative-bound
arguments.
-/

open scoped BigOperators
open scoped ComplexConjugate

namespace Polynomial

noncomputable section

/-- The linear factor contributed by a root in the Robinson form. -/
def robinsonFactor (α : ℂ) : ℂ[X] :=
  if ‖α‖ ≤ 1 then X - C α else 1 - C (conj α) * X

/--
The Robinson form of a complex polynomial, obtained by Schur-reflecting roots
outside the closed unit disk.
-/
def robinsonForm (p : ℂ[X]) : ℂ[X] :=
  C p.leadingCoeff * (p.roots.map robinsonFactor).prod

/-- The root obtained by Schur-reflecting `α` across the unit circle. -/
def schurReflectedRoot (α : ℂ) : ℂ :=
  (conj α)⁻¹

/--
The straight-line root path from `α` to its Schur reflection.  The Boyd/Mahler
single-factor argument needs a monotonicity theorem for the Mahler measure of
the derivative along this family.
-/
def schurRootPath (α : ℂ) (t : ℝ) : ℂ :=
  ((1 - t : ℝ) : ℂ) * α + (t : ℂ) * schurReflectedRoot α

/-- Mahler measure of the derivative after adjoining one moving linear factor. -/
def derivativeMahlerAlongLinearFactor (f : ℂ[X]) (β : ℂ) : ℝ :=
  ((f * (X - C β)).derivative).mahlerMeasure

/-- The summand obtained by differentiating the linear factor for one root. -/
def rootDeletionDerivativeSummand (p : ℂ[X]) (α : ℂ) : ℂ[X] :=
  C p.leadingCoeff * ((p.roots.erase α).map fun β => X - C β).prod

theorem derivative_eq_sum_rootDeletionDerivativeSummand (p : ℂ[X]) :
    p.derivative =
      (p.roots.map fun α => rootDeletionDerivativeSummand p α).sum := by
  classical
  calc
    p.derivative =
        (C p.leadingCoeff * (p.roots.map fun α => X - C α).prod).derivative := by
      exact congrArg derivative (IsAlgClosed.splits p).eq_prod_roots
    _ = C p.leadingCoeff *
        ((p.roots.map fun α => ((p.roots.erase α).map fun β => X - C β).prod).sum) := by
      rw [derivative_C_mul, derivative_prod]
      simp
    _ = (p.roots.map fun α => rootDeletionDerivativeSummand p α).sum := by
      rw [← AddMonoidHom.coe_mulLeft,
        (AddMonoidHom.mulLeft (C p.leadingCoeff)).map_multiset_sum,
        AddMonoidHom.coe_mulLeft]
      simp [rootDeletionDerivativeSummand]

theorem mahlerMeasure_rootDeletionDerivativeSummand_le (p : ℂ[X]) (α : ℂ) :
    (rootDeletionDerivativeSummand p α).mahlerMeasure ≤ p.mahlerMeasure := by
  classical
  rw [rootDeletionDerivativeSummand, mahlerMeasure_mul, mahlerMeasure_const,
    prod_mahlerMeasure_eq_mahlerMeasure_prod, mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  simp only [Multiset.map_map, Function.comp_apply, mahlerMeasure_X_sub_C]
  apply mul_le_mul_of_nonneg_left
  · by_cases hα : α ∈ p.roots
    · have herase_nonneg :
          0 ≤ (Multiset.map (fun β : ℂ => max (1 : ℝ) ‖β‖) (p.roots.erase α)).prod := by
        induction p.roots.erase α using Multiset.induction_on with
        | empty => simp
        | cons β s ih =>
            simpa using mul_nonneg (le_trans zero_le_one (le_max_left (1 : ℝ) ‖β‖)) ih
      calc
        (Multiset.map (fun β : ℂ => max (1 : ℝ) ‖β‖) (p.roots.erase α)).prod ≤
            max (1 : ℝ) ‖α‖ *
              (Multiset.map (fun β : ℂ => max (1 : ℝ) ‖β‖) (p.roots.erase α)).prod :=
          le_mul_of_one_le_left herase_nonneg (le_max_left (1 : ℝ) ‖α‖)
        _ = (Multiset.map (fun β : ℂ => max (1 : ℝ) ‖β‖) p.roots).prod := by
          rw [← Multiset.cons_erase hα]
          simp
    · rw [Multiset.erase_of_notMem hα]
  · exact norm_nonneg _

@[simp]
theorem schurRootPath_zero (α : ℂ) : schurRootPath α 0 = α := by
  simp [schurRootPath]

@[simp]
theorem schurRootPath_one (α : ℂ) : schurRootPath α 1 = schurReflectedRoot α := by
  simp [schurRootPath]

theorem reflectedLinearFactor_eq_C_mul_X_sub_C_schurReflectedRoot {α : ℂ} (hα : α ≠ 0) :
    (1 - C (conj α) * X : ℂ[X]) =
      C (-(conj α)) * (X - C (schurReflectedRoot α)) := by
  have hconj : conj α ≠ 0 := by
    change star α ≠ 0
    rw [star_ne_zero]
    exact hα
  rw [schurReflectedRoot, mul_sub, ← C_mul]
  have hmul : -(conj α) * (conj α)⁻¹ = -1 := by
    rw [neg_mul, mul_inv_cancel₀ hconj]
  rw [hmul]
  rw [mul_comm]
  have hxneg : X * C (-(conj α)) = -(X * C (conj α)) := by
    rw [← mul_neg, ← C_neg]
  rw [mul_comm (C (-(conj α))) X]
  rw [hxneg]
  norm_num
  ring

theorem derivativeMahler_reflectedLinearFactor_eq
    (f : ℂ[X]) {α : ℂ} (hα : α ≠ 0) :
    ((f * (1 - C (conj α) * X)).derivative).mahlerMeasure =
      ‖α‖ * derivativeMahlerAlongLinearFactor f (schurReflectedRoot α) := by
  have hpoly :
      f * (1 - C (conj α) * X : ℂ[X]) =
        C (-(conj α)) * (f * (X - C (schurReflectedRoot α))) := by
    rw [reflectedLinearFactor_eq_C_mul_X_sub_C_schurReflectedRoot hα]
    ring
  rw [hpoly, derivative_C_mul, mahlerMeasure_mul, mahlerMeasure_const,
    derivativeMahlerAlongLinearFactor, norm_neg, Complex.norm_conj]

theorem derivativeMahlerAlongLinearFactor_le_schurReflectedRoot_of_monotoneOn
    (f : ℂ[X]) (α : ℂ)
    (hmono : MonotoneOn
      (fun t : ℝ => derivativeMahlerAlongLinearFactor f (schurRootPath α t))
      (Set.Icc 0 1)) :
    derivativeMahlerAlongLinearFactor f α ≤
      derivativeMahlerAlongLinearFactor f (schurReflectedRoot α) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h := hmono h0 h1 (by norm_num : (0 : ℝ) ≤ 1)
  change derivativeMahlerAlongLinearFactor f (schurRootPath α 0) ≤
    derivativeMahlerAlongLinearFactor f (schurRootPath α 1) at h
  rw [schurRootPath_zero, schurRootPath_one] at h
  exact h

theorem mahlerMeasure_derivative_le_of_schurRootPath_monotone
    (f : ℂ[X]) {α : ℂ} (hα : 1 < ‖α‖)
    (hmono : derivativeMahlerAlongLinearFactor f α ≤
      derivativeMahlerAlongLinearFactor f (schurReflectedRoot α)) :
    (f * (X - C α)).derivative.mahlerMeasure ≤
      (f * (1 - C (conj α) * X)).derivative.mahlerMeasure := by
  have hα_ne : α ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hα))
  rw [derivativeMahler_reflectedLinearFactor_eq f hα_ne]
  calc
    (f * (X - C α)).derivative.mahlerMeasure =
        derivativeMahlerAlongLinearFactor f α := by
      rfl
    _ ≤ derivativeMahlerAlongLinearFactor f (schurReflectedRoot α) := hmono
    _ ≤ ‖α‖ * derivativeMahlerAlongLinearFactor f (schurReflectedRoot α) := by
      exact le_mul_of_one_le_left (mahlerMeasure_nonneg _) hα.le

theorem mahlerMeasure_derivative_le_of_schurRootPath_monotoneOn
    (f : ℂ[X]) {α : ℂ} (hα : 1 < ‖α‖)
    (hmono : MonotoneOn
      (fun t : ℝ => derivativeMahlerAlongLinearFactor f (schurRootPath α t))
      (Set.Icc 0 1)) :
    (f * (X - C α)).derivative.mahlerMeasure ≤
      (f * (1 - C (conj α) * X)).derivative.mahlerMeasure :=
  mahlerMeasure_derivative_le_of_schurRootPath_monotone f hα
    (derivativeMahlerAlongLinearFactor_le_schurReflectedRoot_of_monotoneOn f α hmono)

@[simp]
theorem robinsonFactor_of_norm_le {α : ℂ} (hα : ‖α‖ ≤ 1) :
    robinsonFactor α = X - C α := by
  simp [robinsonFactor, hα]

@[simp]
theorem robinsonFactor_of_one_lt_norm {α : ℂ} (hα : 1 < ‖α‖) :
    robinsonFactor α = 1 - C (conj α) * X := by
  simp [robinsonFactor, not_le.mpr hα]

@[simp]
theorem robinsonForm_zero : robinsonForm (0 : ℂ[X]) = 0 := by
  simp [robinsonForm]

theorem norm_eval_robinsonFactor_eq_norm_eval_X_sub_C
    {α z : ℂ} (hz : ‖z‖ = 1) :
    ‖(robinsonFactor α).eval z‖ = ‖(X - C α : ℂ[X]).eval z‖ := by
  by_cases hα : ‖α‖ ≤ 1
  · simp [robinsonFactor, hα]
  · have hα' : 1 < ‖α‖ := lt_of_not_ge hα
    have hz_mul_conj : z * conj z = 1 := by
      have hnormSq : Complex.normSq z = 1 := by
        rw [Complex.normSq_eq_norm_sq, hz]
        norm_num
      simpa [hnormSq] using Complex.mul_conj z
    have hfactor :
        1 - conj α * z = z * (conj z - conj α) := by
      calc
        1 - conj α * z = z * conj z - conj α * z := by rw [hz_mul_conj]
        _ = z * (conj z - conj α) := by ring
    have hnorm_sub : ‖conj z - conj α‖ = ‖z - α‖ := by
      have hsub : conj z - conj α = conj (z - α) := by
        simp [map_sub]
      rw [hsub, Complex.norm_conj]
    calc
      ‖(robinsonFactor α).eval z‖ = ‖1 - conj α * z‖ := by
        simp [robinsonFactor, not_le.mpr hα']
      _ = ‖z * (conj z - conj α)‖ := by rw [hfactor]
      _ = ‖z‖ * ‖conj z - conj α‖ := by
        rw [Complex.norm_mul]
      _ = ‖z‖ * ‖z - α‖ := by rw [hnorm_sub]
      _ = ‖z - α‖ := by simp [hz]
      _ = ‖(X - C α : ℂ[X]).eval z‖ := by simp

theorem norm_eval_robinsonForm_eq_norm_eval
    {p : ℂ[X]} {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(p.robinsonForm).eval z‖ = ‖p.eval z‖ := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [robinsonForm]
    have hprod :
        ‖(p.roots.map fun α => (robinsonFactor α).eval z).prod‖ =
          ‖(p.roots.map fun α => (X - C α : ℂ[X]).eval z).prod‖ := by
      induction p.roots using Multiset.induction_on with
      | empty => simp
      | cons α s ih =>
          simp [norm_eval_robinsonFactor_eq_norm_eval_X_sub_C (α := α) (z := z) hz, ih]
    calc
      ‖(C p.leadingCoeff * (p.roots.map robinsonFactor).prod).eval z‖ =
          ‖p.leadingCoeff‖ * ‖(p.roots.map fun α => (robinsonFactor α).eval z).prod‖ := by
        simp [eval_multiset_prod, Multiset.map_map]
      _ = ‖p.leadingCoeff‖ * ‖(p.roots.map fun α => (X - C α : ℂ[X]).eval z).prod‖ := by
        rw [hprod]
      _ = ‖p.eval z‖ := by
        rw [(IsAlgClosed.splits p).eval_eq_prod_roots z]
        simp

theorem logMahlerMeasure_eq_of_boundary_norm_eq {p q : ℂ[X]}
    (hboundary : ∀ {z : ℂ}, ‖z‖ = 1 → ‖q.eval z‖ = ‖p.eval z‖) :
    q.logMahlerMeasure = p.logMahlerMeasure := by
  rw [logMahlerMeasure_def, logMahlerMeasure_def]
  apply Real.circleAverage_congr_sphere
  intro z hz
  have hz_norm : ‖z‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hz
  simpa using congrArg Real.log (hboundary hz_norm)

theorem mahlerMeasure_eq_of_boundary_norm_eq_of_ne_zero {p q : ℂ[X]}
    (hboundary : ∀ {z : ℂ}, ‖z‖ = 1 → ‖q.eval z‖ = ‖p.eval z‖)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    q.mahlerMeasure = p.mahlerMeasure := by
  have hlog := logMahlerMeasure_eq_of_boundary_norm_eq hboundary
  rw [logMahlerMeasure_def, logMahlerMeasure_def] at hlog
  rw [mahlerMeasure_def_of_ne_zero hq, mahlerMeasure_def_of_ne_zero hp]
  exact congrArg Real.exp hlog

theorem mahlerMeasure_robinsonFactor (α : ℂ) :
    (robinsonFactor α).mahlerMeasure = max 1 ‖α‖ := by
  by_cases hα : ‖α‖ ≤ 1
  · rw [robinsonFactor_of_norm_le hα, mahlerMeasure_X_sub_C]
  · have hα' : 1 < ‖α‖ := lt_of_not_ge hα
    have hconj_ne : conj α ≠ 0 := by
      change star α ≠ 0
      rw [star_ne_zero]
      exact norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hα'))
    rw [robinsonFactor_of_one_lt_norm hα']
    calc
      (1 - C (conj α) * X : ℂ[X]).mahlerMeasure =
          ((C (-(conj α)) * X + C 1 : ℂ[X])).mahlerMeasure := by
        congr 1
        rw [map_neg]
        simp only [map_one]
        rw [sub_eq_add_neg, add_comm]
        rw [neg_mul]
      _ = max ‖-(conj α)‖ ‖(1 : ℂ)‖ := by
        simpa using mahlerMeasure_C_mul_X_add_C (a := -(conj α)) (b := 1) (by simpa using hconj_ne)
      _ = max 1 ‖α‖ := by
        rw [norm_neg, Complex.norm_conj, norm_one]
        exact max_comm _ _

theorem mahlerMeasure_robinsonForm (p : ℂ[X]) :
    p.robinsonForm.mahlerMeasure = p.mahlerMeasure := by
  rw [robinsonForm, mahlerMeasure_mul, mahlerMeasure_const,
    prod_mahlerMeasure_eq_mahlerMeasure_prod, mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  congr 1
  induction p.roots using Multiset.induction_on with
  | empty => simp
  | cons α s ih =>
      simp [mahlerMeasure_robinsonFactor]

theorem robinsonFactor_ne_zero (α : ℂ) : robinsonFactor α ≠ 0 := by
  by_cases hα : ‖α‖ ≤ 1
  · rw [robinsonFactor_of_norm_le hα]
    exact X_sub_C_ne_zero α
  · have hα' : 1 < ‖α‖ := lt_of_not_ge hα
    have hα_ne : α ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hα'))
    have hconj_ne : conj α ≠ 0 := by
      change star α ≠ 0
      rw [star_ne_zero]
      exact hα_ne
    rw [robinsonFactor_of_one_lt_norm hα']
    have hdeg : (1 - C (conj α) * X : ℂ[X]).degree = 1 := by
      rw [show (1 - C (conj α) * X : ℂ[X]) = C (-(conj α)) * X + C 1 by
        simp [sub_eq_add_neg, add_comm, neg_mul, map_neg, map_one]]
      exact degree_linear (neg_ne_zero.mpr hconj_ne)
    intro h
    rw [h, degree_zero] at hdeg
    exact (by decide : (⊥ : WithBot ℕ) ≠ 1) hdeg

theorem norm_root_robinsonFactor_le (α : ℂ) {β : ℂ}
    (hβ : β ∈ (robinsonFactor α).roots) : ‖β‖ ≤ 1 := by
  by_cases hα : ‖α‖ ≤ 1
  · rw [robinsonFactor_of_norm_le hα, roots_X_sub_C, Multiset.mem_singleton] at hβ
    exact hβ ▸ hα
  · have hα' : 1 < ‖α‖ := lt_of_not_ge hα
    have hα_pos : (0 : ℝ) < ‖α‖ := lt_trans zero_lt_one hα'
    have hα_ne : α ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hα_pos)
    have hconj_ne : conj α ≠ 0 := by
      change star α ≠ 0
      rw [star_ne_zero]
      exact hα_ne
    rw [robinsonFactor_of_one_lt_norm hα'] at hβ
    have hrewrite : (1 - C (conj α) * X : ℂ[X]) = C (-(conj α)) * X + C 1 := by
      simp [sub_eq_add_neg, add_comm, neg_mul, map_neg, map_one]
    rw [hrewrite, roots_C_mul_X_add_C 1 (neg_ne_zero.mpr hconj_ne),
      Multiset.mem_singleton] at hβ
    rw [hβ]
    have : ‖-((-(conj α))⁻¹ * 1)‖ = ‖α‖⁻¹ := by
      rw [mul_one, norm_neg, norm_inv, norm_neg, Complex.norm_conj]
    rw [this]
    rw [inv_le_one_iff₀]
    right
    exact hα'.le

theorem norm_root_robinsonForm_le {p : ℂ[X]} {β : ℂ}
    (hβ : β ∈ p.robinsonForm.roots) : ‖β‖ ≤ 1 := by
  by_cases hp : p = 0
  · rw [hp, robinsonForm_zero, roots_zero] at hβ
    exact absurd hβ (Multiset.notMem_zero β)
  have hlead : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  rw [robinsonForm, roots_C_mul _ hlead] at hβ
  have hne : (0 : ℂ[X]) ∉ p.roots.map robinsonFactor := by
    intro h
    rw [Multiset.mem_map] at h
    obtain ⟨α, _, hα⟩ := h
    exact robinsonFactor_ne_zero α hα
  rw [roots_multiset_prod _ hne, Multiset.mem_bind] at hβ
  obtain ⟨q, hq_mem, hβq⟩ := hβ
  rw [Multiset.mem_map] at hq_mem
  obtain ⟨α, _, rfl⟩ := hq_mem
  exact norm_root_robinsonFactor_le α hβq

theorem natDegree_robinsonFactor (α : ℂ) : (robinsonFactor α).natDegree = 1 := by
  by_cases hα : ‖α‖ ≤ 1
  · rw [robinsonFactor_of_norm_le hα]
    exact natDegree_X_sub_C α
  · have hα' : 1 < ‖α‖ := lt_of_not_ge hα
    have hα_ne : α ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hα'))
    have hconj_ne : conj α ≠ 0 := by
      change star α ≠ 0
      rw [star_ne_zero]
      exact hα_ne
    rw [robinsonFactor_of_one_lt_norm hα',
      show (1 - C (conj α) * X : ℂ[X]) = C (-(conj α)) * X + C 1 by
        simp [sub_eq_add_neg, add_comm, neg_mul, map_neg, map_one]]
    exact natDegree_linear (neg_ne_zero.mpr hconj_ne)

theorem natDegree_robinsonForm (p : ℂ[X]) : p.robinsonForm.natDegree = p.natDegree := by
  by_cases hp : p = 0
  · simp [hp]
  have hlead : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hne : (0 : ℂ[X]) ∉ p.roots.map robinsonFactor := by
    intro h
    rw [Multiset.mem_map] at h
    obtain ⟨α, _, hα⟩ := h
    exact robinsonFactor_ne_zero α hα
  rw [robinsonForm, natDegree_C_mul hlead, natDegree_multiset_prod _ hne, Multiset.map_map]
  have hcong : p.roots.map (natDegree ∘ robinsonFactor) = p.roots.map (fun _ => (1 : ℕ)) := by
    apply Multiset.map_congr rfl
    intro α _
    exact natDegree_robinsonFactor α
  rw [hcong]
  simp [Multiset.sum_replicate, IsAlgClosed.card_roots_eq_natDegree]

theorem norm_root_robinsonForm_derivative_le {p : ℂ[X]} {β : ℂ}
    (hβ : β ∈ p.robinsonForm.derivative.roots) : ‖β‖ ≤ 1 := by
  have hd_ne : p.robinsonForm.derivative ≠ 0 := by
    intro h
    rw [h, roots_zero] at hβ
    exact absurd hβ (Multiset.notMem_zero β)
  have hrf_ne : p.robinsonForm ≠ 0 := by
    intro h
    apply hd_ne
    rw [h, derivative_zero]
  have hrf_deg : 0 < p.robinsonForm.degree := by
    by_contra h
    rw [not_lt] at h
    have hnatDeg : p.robinsonForm.natDegree = 0 := by
      have hle : p.robinsonForm.natDegree ≤ 0 := natDegree_le_of_degree_le h
      omega
    exact hd_ne (derivative_of_natDegree_zero hnatDeg)
  have hβ_eval : eval β p.robinsonForm.derivative = 0 := (mem_roots hd_ne).mp hβ
  have hβ_rootSet : β ∈ p.robinsonForm.derivative.rootSet ℂ := by
    rw [mem_rootSet_of_ne hd_ne]
    simpa using hβ_eval
  have hβ_convex : β ∈ convexHull ℝ (p.robinsonForm.rootSet ℂ) :=
    rootSet_derivative_subset_convexHull_rootSet hrf_deg hβ_rootSet
  have hsub : p.robinsonForm.rootSet ℂ ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro γ hγ
    rw [mem_rootSet_of_ne hrf_ne] at hγ
    rw [Metric.mem_closedBall, dist_zero_right]
    apply norm_root_robinsonForm_le
    rw [mem_roots hrf_ne]
    simpa using hγ
  have hconv : Convex ℝ (Metric.closedBall (0 : ℂ) 1) := convex_closedBall 0 1
  have hchm := convexHull_min hsub hconv hβ_convex
  rwa [Metric.mem_closedBall, dist_zero_right] at hchm

private theorem mahlerMeasure_eq_norm_leadingCoeff_of_roots_le_one {p : ℂ[X]}
    (h : ∀ α ∈ p.roots, ‖α‖ ≤ 1) : p.mahlerMeasure = ‖p.leadingCoeff‖ := by
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  have hprod : (p.roots.map (fun a => max 1 ‖a‖)).prod = 1 := by
    apply Multiset.prod_eq_one
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨α, hα, rfl⟩ := hx
    exact max_eq_left (h α hα)
  rw [hprod, mul_one]

theorem norm_root_derivative_le_of_roots_le_one {p : ℂ[X]}
    (hroots : ∀ α ∈ p.roots, ‖α‖ ≤ 1) {β : ℂ}
    (hβ : β ∈ p.derivative.roots) : ‖β‖ ≤ 1 := by
  have hd_ne : p.derivative ≠ 0 := by
    intro h
    rw [h, roots_zero] at hβ
    exact absurd hβ (Multiset.notMem_zero β)
  have hp_ne : p ≠ 0 := by
    intro h
    apply hd_ne
    rw [h, derivative_zero]
  have hp_deg : 0 < p.degree := by
    by_contra h
    rw [not_lt] at h
    have hnatDeg : p.natDegree = 0 := by
      have hle : p.natDegree ≤ 0 := natDegree_le_of_degree_le h
      omega
    exact hd_ne (derivative_of_natDegree_zero hnatDeg)
  have hβ_eval : eval β p.derivative = 0 := (mem_roots hd_ne).mp hβ
  have hβ_rootSet : β ∈ p.derivative.rootSet ℂ := by
    rw [mem_rootSet_of_ne hd_ne]
    simpa using hβ_eval
  have hβ_convex : β ∈ convexHull ℝ (p.rootSet ℂ) :=
    rootSet_derivative_subset_convexHull_rootSet hp_deg hβ_rootSet
  have hsub : p.rootSet ℂ ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro γ hγ
    rw [mem_rootSet_of_ne hp_ne] at hγ
    rw [Metric.mem_closedBall, dist_zero_right]
    apply hroots
    rw [mem_roots hp_ne]
    simpa using hγ
  have hconv : Convex ℝ (Metric.closedBall (0 : ℂ) 1) := convex_closedBall 0 1
  have hchm := convexHull_min hsub hconv hβ_convex
  rwa [Metric.mem_closedBall, dist_zero_right] at hchm

theorem mahlerMeasure_derivative_eq_natDegree_mul_of_roots_le_one
    (p : ℂ[X]) (hroots : ∀ α ∈ p.roots, ‖α‖ ≤ 1) :
    p.derivative.mahlerMeasure = p.natDegree * p.mahlerMeasure := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hnatDeg : p.natDegree = 0
  · have hderiv : p.derivative = 0 := derivative_of_natDegree_zero hnatDeg
    rw [hderiv, mahlerMeasure_zero, hnatDeg]
    simp
  have hnatpos : 0 < p.natDegree := Nat.pos_of_ne_zero hnatDeg
  have hMM_deriv : p.derivative.mahlerMeasure =
      ‖p.derivative.leadingCoeff‖ := by
    apply mahlerMeasure_eq_norm_leadingCoeff_of_roots_le_one
    intro α; exact norm_root_derivative_le_of_roots_le_one hroots
  have hsub : p.natDegree - 1 + 1 = p.natDegree :=
    Nat.sub_add_cancel hnatpos
  have hdeg_deriv : p.derivative.natDegree = p.natDegree - 1 :=
    natDegree_eq_of_degree_eq_some (degree_derivative_eq p hnatpos)
  have hcast : ((p.natDegree - 1 : ℕ) : ℂ) + 1 = (p.natDegree : ℂ) := by
    rw [Nat.cast_sub hnatpos, Nat.cast_one]; ring
  have hlead_deriv : p.derivative.leadingCoeff =
      p.leadingCoeff * (p.natDegree : ℂ) := by
    unfold leadingCoeff
    rw [hdeg_deriv, coeff_derivative, hsub, hcast]
  have hMM_p : p.mahlerMeasure = ‖p.leadingCoeff‖ := by
    exact mahlerMeasure_eq_norm_leadingCoeff_of_roots_le_one hroots
  rw [hMM_deriv, hlead_deriv, norm_mul, Complex.norm_natCast, ← hMM_p, mul_comm]

theorem mahlerMeasure_robinsonForm_derivative (p : ℂ[X]) :
    p.robinsonForm.derivative.mahlerMeasure = p.natDegree * p.mahlerMeasure := by
  rw [mahlerMeasure_derivative_eq_natDegree_mul_of_roots_le_one p.robinsonForm
    (by intro α; exact norm_root_robinsonForm_le), natDegree_robinsonForm,
    mahlerMeasure_robinsonForm]

end

end Polynomial
