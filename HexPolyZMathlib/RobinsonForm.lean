import HexPolyZMathlib.Basic
import Mathlib.Analysis.Polynomial.MahlerMeasure

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

end

end Polynomial
