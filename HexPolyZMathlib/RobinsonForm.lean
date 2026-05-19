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

/--
The polynomial obtained from `p` by Schur-reflecting one selected exterior root
while leaving all other roots in their original linear factors.
-/
def schurReflectedAtRootForm (p : ℂ[X]) (α : ℂ) : ℂ[X] :=
  C p.leadingCoeff * ((p.roots.erase α).map fun β => X - C β).prod *
    (1 - C (conj α) * X)

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

/--
One root-reflection step in the de Bruijn-Springer/Boyd route toward
`p.derivative.mahlerMeasure ≤ p.natDegree * p.mahlerMeasure`: if the Mahler
measure of the derivative is monotone along the Schur path for the selected
linear factor, then reflecting that exterior root cannot decrease the Mahler
measure of the derivative.
-/
theorem mahlerMeasure_derivative_le_schurReflectedAtRootForm_derivative_of_monotoneOn
    (p : ℂ[X]) {α : ℂ} (hαmem : α ∈ p.roots) (hα : 1 < ‖α‖)
    (hmono : MonotoneOn
      (fun t : ℝ =>
        derivativeMahlerAlongLinearFactor
          (C p.leadingCoeff * ((p.roots.erase α).map fun β => X - C β).prod)
          (schurRootPath α t))
      (Set.Icc 0 1)) :
    p.derivative.mahlerMeasure ≤ (schurReflectedAtRootForm p α).derivative.mahlerMeasure := by
  let f : ℂ[X] := C p.leadingCoeff * ((p.roots.erase α).map fun β => X - C β).prod
  have hp_factor : p = f * (X - C α) := by
    calc
      p = C p.leadingCoeff * (p.roots.map fun β => X - C β).prod := by
        exact (IsAlgClosed.splits p).eq_prod_roots
      _ = C p.leadingCoeff *
          (((p.roots.erase α).map fun β => X - C β).prod * (X - C α)) := by
        rw [← Multiset.cons_erase hαmem]
        simp [mul_comm]
      _ = f * (X - C α) := by
        simp [f, mul_assoc]
  have hreflect :
      schurReflectedAtRootForm p α = f * (1 - C (conj α) * X) := by
    simp [schurReflectedAtRootForm, f, mul_assoc]
  calc
    p.derivative.mahlerMeasure = (f * (X - C α)).derivative.mahlerMeasure := by
      rw [hp_factor]
    _ ≤ (f * (1 - C (conj α) * X)).derivative.mahlerMeasure :=
      mahlerMeasure_derivative_le_of_schurRootPath_monotoneOn f hα hmono
    _ = (schurReflectedAtRootForm p α).derivative.mahlerMeasure := by
      rw [hreflect]

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

open Filter MeasureTheory Set in
/--
Jensen/circle-average upper bound used in the Mahler--Boyd analytic route:
the exponential Mahler measure is bounded by the unit-circle mean of the
absolute value.  This is the first Jensen step in the standard Landau/Mahler
integral proof, exposed here so derivative-bound arguments can cite the
analytic ingredient directly rather than hiding it inside a coefficient norm
estimate.
-/
theorem mahlerMeasure_le_circleAverage_norm (p : ℂ[X]) :
    p.mahlerMeasure ≤ Real.circleAverage (fun z => ‖p.eval z‖) 0 1 := by
  have : IsFiniteMeasure (volume.restrict (uIoc 0 (2 * Real.pi))) := by
    rw [uIoc_of_le (by positivity)]
    infer_instance
  have : NeZero (volume (uIoc 0 (2 * Real.pi))) := ⟨by simp⟩
  by_cases hp : p = 0
  · rw [hp, mahlerMeasure_zero]
    exact Real.circleAverage_nonneg_of_nonneg (fun z _ => norm_nonneg (eval z (0 : ℂ[X])))
  have hpos_ae : ∀ᵐ (θ : ℝ) ∂volume.restrict (uIoc 0 (2 * Real.pi)),
      0 < ‖p.eval (circleMap 0 1 θ)‖ := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    refine Set.Finite.measure_zero ?_ _
    simp only [norm_pos_iff, ne_eq, compl_setOf, Classical.not_imp, Decidable.not_not]
    refine Finite.of_finite_image (f := circleMap 0 1) (p.roots.finite_toSet.subset ?_) ?_
    · rintro z ⟨θ, ⟨_, heval⟩, rfl⟩
      exact (mem_roots hp).mpr heval
    · apply InjOn.mono fun _ h => h.1
      exact injOn_circleMap_of_abs_sub_le one_ne_zero (by simp [abs_of_pos Real.pi_pos])
  have hlog_ae : ∀ᵐ (θ : ℝ) ∂volume.restrict (uIoc 0 (2 * Real.pi)),
      Real.exp (Real.log ‖p.eval (circleMap 0 1 θ)‖) =
        ‖p.eval (circleMap 0 1 θ)‖ := by
    filter_upwards [hpos_ae] with θ hθ
    exact Real.exp_log hθ
  have hcont : Continuous (fun θ : ℝ => ‖p.eval (circleMap 0 1 θ)‖) := by fun_prop
  rw [mahlerMeasure_def_of_ne_zero hp]
  change Real.exp (Real.circleAverage (fun z => Real.log ‖p.eval z‖) 0 1) ≤
    Real.circleAverage (fun z => ‖p.eval z‖) 0 1
  calc
    Real.exp (Real.circleAverage (fun z => Real.log ‖p.eval z‖) 0 1)
        ≤ Real.circleAverage
            (fun z => Real.exp (Real.log ‖p.eval z‖)) 0 1 := by
      rw [Real.circleAverage_eq_intervalAverage, Real.circleAverage_eq_intervalAverage]
      refine convexOn_exp.map_average_le Real.continuousOn_exp isClosed_univ (by simp) ?_ ?_
      · rw [Set.uIoc_of_le (by positivity : 0 ≤ 2 * Real.pi)]
        exact ((analyticOnNhd_id.aeval_polynomial p).meromorphicOn.circleIntegrable_log_norm).1
      · exact (integrable_congr hlog_ae).mpr hcont.integrableOn_uIoc
    _ = Real.circleAverage (fun z => ‖p.eval z‖) 0 1 := by
      rw [Real.circleAverage_eq_intervalAverage, Real.circleAverage_eq_intervalAverage]
      exact average_congr hlog_ae

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

theorem Multiset.prod_le_of_sum_log_le {s t : Multiset ℝ}
    (hs : ∀ x ∈ s, 0 < x) (ht : ∀ x ∈ t, 0 < x)
    (hlog : (s.map fun x => Real.log x).sum ≤ (t.map fun x => Real.log x).sum) :
    s.prod ≤ t.prod := by
  have hsprod : 0 < s.prod := Multiset.prod_pos hs
  have htprod : 0 < t.prod := Multiset.prod_pos ht
  rw [← Real.log_le_log_iff hsprod htprod]
  rw [Real.log_multiset_prod (fun x hx => (hs x hx).ne'),
    Real.log_multiset_prod (fun x hx => (ht x hx).ne')]
  exact hlog

theorem prod_max_one_norm_roots_derivative_le_of_sum_log_le
    (p : ℂ[X])
    (hlog :
      (p.derivative.roots.map fun β => Real.log (max (1 : ℝ) ‖β‖)).sum ≤
        (p.roots.map fun α => Real.log (max (1 : ℝ) ‖α‖)).sum) :
    (p.derivative.roots.map fun β => max (1 : ℝ) ‖β‖).prod ≤
      (p.roots.map fun α => max (1 : ℝ) ‖α‖).prod := by
  apply Multiset.prod_le_of_sum_log_le
  · intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨β, _hβ, rfl⟩ := hx
    exact lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) ‖β‖)
  · intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨α, _hα, rfl⟩ := hx
    exact lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) ‖α‖)
  · simpa [Multiset.map_map, Function.comp_def] using hlog

private theorem Multiset.prod_max_one_norm_eq_prod_filter_norm (s : Multiset ℂ) :
    (s.map fun z => max (1 : ℝ) ‖z‖).prod =
      ((s.filter fun z => 1 ≤ ‖z‖).map fun z => ‖z‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
      by_cases hz : 1 ≤ ‖z‖
      · simp [hz, ih]
      · have hz_le : ‖z‖ ≤ 1 := le_of_not_ge hz
        simp [hz, max_eq_left hz_le, ih]

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

/--
The desired derivative root-product comparison follows from the `r = 1`
instance of Schmeisser's de Bruijn-Springer product inequality.
-/
theorem prod_max_one_norm_roots_derivative_le_of_schmeisser_radius_one
    (p : ℂ[X])
    (hSchmeisser :
      ((p.derivative.roots.filter fun β => 1 ≤ ‖β‖).map fun β => ‖β‖).prod ≤
        ((p.roots.filter fun α => 1 ≤ ‖α‖).map fun α => ‖α‖).prod) :
    (p.derivative.roots.map fun β => max (1 : ℝ) ‖β‖).prod ≤
      (p.roots.map fun α => max (1 : ℝ) ‖α‖).prod := by
  rw [Multiset.prod_max_one_norm_eq_prod_filter_norm,
    Multiset.prod_max_one_norm_eq_prod_filter_norm]
  exact hSchmeisser

/--
The Schmeisser specialization is naturally applied to `X * p.derivative`.
The extra root contributed by `X` is `0`, hence it is removed by the
`1 ≤ ‖β‖` filter.
-/
theorem roots_filter_norm_product_derivative_le_of_X_mul_derivative
    (p : ℂ[X])
    (h :
      ((((X : ℂ[X]) * p.derivative).roots.filter fun β => 1 ≤ ‖β‖).map fun β => ‖β‖).prod ≤
        ((p.roots.filter fun α => 1 ≤ ‖α‖).map fun α => ‖α‖).prod) :
    ((p.derivative.roots.filter fun β => 1 ≤ ‖β‖).map fun β => ‖β‖).prod ≤
      ((p.roots.filter fun α => 1 ≤ ‖α‖).map fun α => ‖α‖).prod := by
  by_cases hpderiv : p.derivative = 0
  · simpa [hpderiv, roots_zero] using h
  · have hroots :
        (((X : ℂ[X]) * p.derivative).roots.filter fun β => 1 ≤ ‖β‖) =
          (p.derivative.roots.filter fun β => 1 ≤ ‖β‖) := by
      rw [roots_mul (mul_ne_zero X_ne_zero hpderiv), roots_X, Multiset.filter_add]
      simp
    rwa [hroots] at h

theorem prod_max_one_norm_roots_derivative_le_of_mahlerMeasure_derivative_le
    (p : ℂ[X])
    (hderiv : p.derivative.mahlerMeasure ≤ p.natDegree * p.mahlerMeasure) :
    (p.derivative.roots.map fun β => max (1 : ℝ) ‖β‖).prod ≤
      (p.roots.map fun α => max (1 : ℝ) ‖α‖).prod := by
  by_cases hnatDeg : p.natDegree = 0
  · rw [derivative_of_natDegree_zero hnatDeg, roots_zero]
    exact one_le_prod_max_one_norm_roots p
  have hnatpos : 0 < p.natDegree := Nat.pos_of_ne_zero hnatDeg
  have hp_ne : p ≠ 0 := by
    intro hp
    exact hnatDeg (by simp [hp])
  have hsub : p.natDegree - 1 + 1 = p.natDegree :=
    Nat.sub_add_cancel hnatpos
  have hdeg_deriv : p.derivative.natDegree = p.natDegree - 1 :=
    natDegree_eq_of_degree_eq_some (degree_derivative_eq p hnatpos)
  have hcast : ((p.natDegree - 1 : ℕ) : ℂ) + 1 = (p.natDegree : ℂ) := by
    rw [Nat.cast_sub hnatpos, Nat.cast_one]
    ring
  have hlead_deriv : p.derivative.leadingCoeff =
      p.leadingCoeff * (p.natDegree : ℂ) := by
    unfold leadingCoeff
    rw [hdeg_deriv, coeff_derivative, hsub, hcast]
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
    mahlerMeasure_eq_leadingCoeff_mul_prod_roots] at hderiv
  rw [hlead_deriv, norm_mul, Complex.norm_natCast] at hderiv
  have hscale_pos : 0 < (p.natDegree : ℝ) * ‖p.leadingCoeff‖ := by
    exact mul_pos (Nat.cast_pos.mpr hnatpos)
      (norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hp_ne))
  have hscaled :
      ((p.natDegree : ℝ) * ‖p.leadingCoeff‖) *
          (p.derivative.roots.map fun β => max (1 : ℝ) ‖β‖).prod ≤
        ((p.natDegree : ℝ) * ‖p.leadingCoeff‖) *
          (p.roots.map fun α => max (1 : ℝ) ‖α‖).prod := by
    convert hderiv using 1 <;> ring
  rwa [mul_le_mul_iff_right₀ hscale_pos] at hscaled

/--
Closed-unit-disk derivative root-product comparison.  The analytic input is
Gauss-Lucas: derivative roots stay in the convex hull of the original roots,
which is still contained in the closed unit disk.
-/
theorem prod_max_one_norm_roots_derivative_le_of_roots_le_one
    (p : ℂ[X]) (hroots : ∀ α ∈ p.roots, ‖α‖ ≤ 1) :
    (p.derivative.roots.map fun β => max (1 : ℝ) ‖β‖).prod ≤
      (p.roots.map fun α => max (1 : ℝ) ‖α‖).prod := by
  have hderiv_prod :
      (p.derivative.roots.map fun β => max (1 : ℝ) ‖β‖).prod = 1 := by
    apply Multiset.prod_eq_one
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨β, hβ, rfl⟩ := hx
    exact max_eq_left (norm_root_derivative_le_of_roots_le_one hroots hβ)
  rw [hderiv_prod]
  exact one_le_prod_max_one_norm_roots p

/--
Robinson endpoint root-product comparison for the derivative.  This is the
closed-disk endpoint of the de Bruijn-Springer/Boyd reflection route: all roots
of `p.robinsonForm` lie in the closed unit disk, so Gauss-Lucas puts all roots
of its derivative there as well.
-/
theorem prod_max_one_norm_roots_robinsonForm_derivative_le
    (p : ℂ[X]) :
    (p.robinsonForm.derivative.roots.map fun β => max (1 : ℝ) ‖β‖).prod ≤
      (p.roots.map fun α => max (1 : ℝ) ‖α‖).prod := by
  have hderiv_prod :
      (p.robinsonForm.derivative.roots.map fun β => max (1 : ℝ) ‖β‖).prod = 1 := by
    apply Multiset.prod_eq_one
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨β, hβ, rfl⟩ := hx
    exact max_eq_left (norm_root_robinsonForm_derivative_le hβ)
  rw [hderiv_prod]
  exact one_le_prod_max_one_norm_roots p

theorem mahlerMeasure_derivative_le_derivative_of_boundary_norm_eq_of_roots_le_one_of_derivative_le
    {p q : ℂ[X]}
    (hpderiv : p.derivative.mahlerMeasure ≤ p.natDegree * p.mahlerMeasure)
    (hboundary : ∀ {z : ℂ}, ‖z‖ = 1 → ‖q.eval z‖ = ‖p.eval z‖)
    (hqroots : ∀ {β : ℂ}, β ∈ q.roots → ‖β‖ ≤ 1)
    (hdeg : q.natDegree = p.natDegree) :
    p.derivative.mahlerMeasure ≤ q.derivative.mahlerMeasure := by
  by_cases hq : q = 0
  · have hp_natDegree : p.natDegree = 0 := by
      simpa [hq] using hdeg.symm
    rw [hq, derivative_zero, derivative_of_natDegree_zero hp_natDegree]
  by_cases hp : p = 0
  · rw [hp, derivative_zero]
    exact mahlerMeasure_nonneg _
  have hmeasure : q.mahlerMeasure = p.mahlerMeasure :=
    mahlerMeasure_eq_of_boundary_norm_eq_of_ne_zero hboundary hp hq
  have hqderiv :
      q.derivative.mahlerMeasure = q.natDegree * q.mahlerMeasure :=
    mahlerMeasure_derivative_eq_natDegree_mul_of_roots_le_one q (by
      intro β hβ
      exact hqroots hβ)
  calc
    p.derivative.mahlerMeasure ≤ p.natDegree * p.mahlerMeasure := hpderiv
    _ = q.natDegree * q.mahlerMeasure := by rw [← hdeg, hmeasure]
    _ = q.derivative.mahlerMeasure := hqderiv.symm

theorem mahlerMeasure_robinsonForm_derivative (p : ℂ[X]) :
    p.robinsonForm.derivative.mahlerMeasure = p.natDegree * p.mahlerMeasure := by
  rw [mahlerMeasure_derivative_eq_natDegree_mul_of_roots_le_one p.robinsonForm
    (by intro α; exact norm_root_robinsonForm_le), natDegree_robinsonForm,
    mahlerMeasure_robinsonForm]

/--
The finite root-deletion derivative sum for the Robinson form has the same
Mahler bound as the derivative itself.
-/
theorem mahlerMeasure_robinsonRootDeletionDerivativeSum_le (p : ℂ[X]) :
    (C p.leadingCoeff *
        (p.roots.map fun α =>
          ((p.roots.erase α).map robinsonFactor).prod * (robinsonFactor α).derivative).sum
      ).mahlerMeasure ≤ p.natDegree * p.mahlerMeasure := by
  have hderiv :
      C p.leadingCoeff *
          (p.roots.map fun α =>
            ((p.roots.erase α).map robinsonFactor).prod * (robinsonFactor α).derivative).sum =
        p.robinsonForm.derivative := by
    rw [robinsonForm, derivative_C_mul, derivative_prod]
  rw [hderiv, mahlerMeasure_robinsonForm_derivative]

end

end Polynomial
