/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Kantorovich
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Matrix.Normed

public section

/-!
# Newton--Kantorovich for complex polynomials in the sup norm

We model `ℂ` as `Fin 2 → ℝ`, with Mathlib's product sup norm. Multiplication by
`z` is the real matrix `[[z.re, -z.im], [z.im, z.re]]`; its operator norm is
the common absolute row sum `|z.re| + |z.im|`.
-/

open Polynomial

namespace NewtonKantorovich

/-- Complex numbers represented as two real coordinates with the sup norm. -/
abbrev ComplexSup := Fin 2 → ℝ

namespace ComplexSup

/-- The natural continuous real-linear equivalence between `ℂ` and its
two-coordinate sup-norm model. -/
@[expose] noncomputable def equiv : ℂ ≃L[ℝ] ComplexSup :=
  Complex.equivRealProdCLM.trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm

@[simp] theorem equiv_apply_zero (z : ℂ) : equiv z 0 = z.re := by
  rfl

@[simp] theorem equiv_apply_one (z : ℂ) : equiv z 1 = z.im := by
  rfl

@[simp] theorem equiv_symm_re (x : ComplexSup) : (equiv.symm x).re = x 0 := by
  rfl

@[simp] theorem equiv_symm_im (x : ComplexSup) : (equiv.symm x).im = x 1 := by
  rfl

/-- The transported norm is the maximum absolute coordinate. -/
theorem norm_equiv (z : ℂ) : ‖equiv z‖ = max |z.re| |z.im| := by
  rw [Pi.norm_def]
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  simp

/-- The real matrix of multiplication by a complex scalar. -/
@[expose] def mulMatrix (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![z.re, -z.im; z.im, z.re]

/-- Multiplication by a complex scalar as a continuous real-linear operator on
the sup-norm model. -/
@[expose] noncomputable def mul (z : ℂ) : ComplexSup →L[ℝ] ComplexSup :=
  ContinuousLinearMap.mk (Matrix.mulVecLin (mulMatrix z))

@[simp] theorem mul_apply_zero (z : ℂ) (x : ComplexSup) :
    mul z x 0 = z.re * x 0 - z.im * x 1 := by
  simp [mul, mulMatrix, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, sub_eq_add_neg]

@[simp] theorem mul_apply_one (z : ℂ) (x : ComplexSup) :
    mul z x 1 = z.im * x 0 + z.re * x 1 := by
  simp [mul, mulMatrix, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]

/-- Transporting the sup-norm multiplication operator back to `ℂ` gives
ordinary complex multiplication. -/
theorem equiv_symm_mul (z : ℂ) (x : ComplexSup) :
    equiv.symm (mul z x) = z * equiv.symm x := by
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp [Complex.mul_im, add_comm]

/-- Complex multiplication is conjugation of scalar multiplication by the
coordinate equivalence. -/
theorem mul_eq_transport (z : ℂ) :
    mul z = equiv.toContinuousLinearMap.comp
      (((ContinuousLinearMap.toSpanSingleton ℂ z).restrictScalars ℝ).comp
        equiv.symm.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro x
  apply equiv.symm.injective
  rw [equiv_symm_mul]
  simp [mul_comm]

/-- Exact sup-operator norm of complex multiplication. -/
theorem norm_mul (z : ℂ) : ‖mul z‖ = |z.re| + |z.im| := by
  change ‖ContinuousLinearMap.mk (Matrix.mulVecLin (mulMatrix z))‖ = _
  rw [← Matrix.linfty_opNorm_eq_opNorm (mulMatrix z)]
  rw [Matrix.linfty_opNorm_def]
  have hrow : ∀ i : Fin 2, (∑ j : Fin 2, ‖mulMatrix z i j‖₊) =
      ‖z.re‖₊ + ‖z.im‖₊ := by
    intro i
    fin_cases i <;> simp [mulMatrix, Fin.sum_univ_two, add_comm]
  simp_rw [hrow]
  rw [Finset.sup_const Finset.univ_nonempty]
  rfl

/-- Complex multiplication varies continuously in the operator norm. -/
theorem continuous_mul : Continuous mul := by
  have hscalar : Continuous fun z : ℂ =>
      (ContinuousLinearMap.toSpanSingleton ℂ z).restrictScalars ℝ :=
    (ContinuousLinearMap.continuous_restrictScalars ℝ).comp
      ContinuousLinearMap.toSpanSingletonCLE.continuous
  have hpre : Continuous fun z : ℂ =>
      ((ContinuousLinearMap.toSpanSingleton ℂ z).restrictScalars ℝ).comp
        equiv.symm.toContinuousLinearMap :=
    (equiv.symm.toContinuousLinearMap.precomp ℂ).continuous.comp hscalar
  have hpost : Continuous fun z : ℂ => equiv.toContinuousLinearMap.comp
      (((ContinuousLinearMap.toSpanSingleton ℂ z).restrictScalars ℝ).comp
        equiv.symm.toContinuousLinearMap) :=
    (equiv.toContinuousLinearMap.postcomp ComplexSup).continuous.comp hpre
  convert hpost using 1
  funext z
  exact mul_eq_transport z

@[simp] theorem mul_one : mul 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply equiv.symm.injective
  simp [equiv_symm_mul]

theorem mul_sub (z w : ℂ) : mul (z - w) = mul z - mul w := by
  apply ContinuousLinearMap.ext
  intro x
  apply equiv.symm.injective
  simp [equiv_symm_mul, sub_mul]

theorem mul_add (z w : ℂ) : mul (z + w) = mul z + mul w := by
  apply ContinuousLinearMap.ext
  intro x
  apply equiv.symm.injective
  simp [equiv_symm_mul, add_mul]

@[simp] theorem mul_zero : mul 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply equiv.symm.injective
  simp [equiv_symm_mul]

theorem mul_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    mul (∑ i ∈ S, f i) = ∑ i ∈ S, mul (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => simp [hi, mul_add, ih]

theorem mul_comp (z w : ℂ) : (mul z).comp (mul w) = mul (z * w) := by
  apply ContinuousLinearMap.ext
  intro x
  apply equiv.symm.injective
  simp [equiv_symm_mul, mul_assoc]

/-- Exact first-order defect: there is no Euclidean-to-sup norm loss. -/
theorem norm_one_sub_mul (z : ℂ) :
    ‖1 - mul z‖ = |1 - z.re| + |z.im| := by
  rw [← mul_one, ← mul_sub, norm_mul]
  simp

/-- Comparison of the sup operator norm with the Euclidean complex norm. -/
theorem norm_mul_le_sqrt_two (z : ℂ) : ‖mul z‖ ≤ √2 * ‖z‖ := by
  rw [norm_mul]
  refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by norm_num), Complex.sq_norm, Complex.normSq_apply]
  have hre : |z.re| ^ 2 = z.re ^ 2 := sq_abs _
  have him : |z.im| ^ 2 = z.im ^ 2 := sq_abs _
  nlinarith [sq_nonneg (|z.re| - |z.im|)]

/-- Evaluation of a complex polynomial, transported to the sup-norm model. -/
@[expose] noncomputable def eval (p : ℂ[X]) (x : ComplexSup) : ComplexSup :=
  equiv (p.eval (equiv.symm x))

/-- The real Fréchet derivative of transported polynomial evaluation. -/
@[expose] noncomputable def evalDeriv (p : ℂ[X]) (x : ComplexSup) :
    ComplexSup →L[ℝ] ComplexSup :=
  mul (p.derivative.eval (equiv.symm x))

/-- Transported polynomial evaluation has the expected real Fréchet
derivative. The norm-inherited parent structures are explicit because `Pi`
also has definitionally distinct direct parent instances; the generic
Newton--Kantorovich theorem consumes the norm-inherited ones. -/
theorem hasFDerivAt_eval (p : ℂ[X]) (x : ComplexSup) :
    @HasFDerivAt ℝ _ ComplexSup Pi.normedAddCommGroup.toAddCommGroup
      Pi.normedSpace.toModule PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      ComplexSup Pi.normedAddCommGroup.toAddCommGroup Pi.normedSpace.toModule
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (eval p) (evalDeriv p x) x := by
  have hp := ((p.hasDerivAt (equiv.symm x)).hasFDerivAt.restrictScalars ℝ)
  have hin := hp.comp x equiv.symm.hasFDerivAt
  have hout := equiv.hasFDerivAt.comp x hin
  rw [evalDeriv, mul_eq_transport]
  convert hout using 1
  rfl

/-- The derivative of transported polynomial evaluation varies
continuously. -/
theorem continuous_evalDeriv (p : ℂ[X]) : Continuous (evalDeriv p) := by
  have hp : Continuous fun z : ℂ => p.derivative.eval z :=
    continuous_iff_continuousAt.2 fun z => (p.derivative.hasDerivAt z).continuousAt
  exact continuous_mul.comp (hp.comp equiv.symm.continuous)

/-- Newton--Kantorovich specialized to a complex polynomial in sup-norm
coordinates. The witness-specific estimates enter only through the three
exact bounds `hy`, `hz₁`, and `hz₂`. -/
theorem existsUnique_root {p : ℂ[X]} {A : ComplexSup →L[ℝ] ComplexSup}
    {R : ENNReal} {x₀ : ComplexSup} {y z₁ z₂ r : NNReal}
    (hy : ‖A (eval p x₀)‖₊ ≤ y)
    (hz₁ : ‖1 - A.comp (evalDeriv p x₀)‖₊ ≤ z₁)
    (hz₂ : ∀ x ∈ Metric.closedEBall x₀ R,
      ‖A.comp (evalDeriv p x - evalDeriv p x₀)‖₊ ≤ z₂ * ‖x - x₀‖₊)
    (hrR : r ≤ R)
    (hyr : y + z₁ * r + z₂ * r ^ 2 / 2 ≤ r)
    (hzr : z₁ + z₂ * r < 1) :
    ∃! x, p.eval (equiv.symm x) = 0 ∧ ‖x - x₀‖₊ ≤ r := by
  have h := newton_kantorovich_fd (X := ComplexSup) (Y := ComplexSup) rfl
    (hasFDerivAt_eval p) (continuous_evalDeriv p) hy hz₁ hz₂ hrR hyr hzr
  simpa only [eval, equiv.map_eq_zero_iff] using h

end ComplexSup

end NewtonKantorovich
