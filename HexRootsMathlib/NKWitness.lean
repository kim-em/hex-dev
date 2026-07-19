/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Geometry
public import HexRootsMathlib.KantorovichPoly
public import HexRootsMathlib.Taylor

public section

/-!
# Semantics of executable Newton--Kantorovich witnesses

This module decodes `Hex.nkWitness` into named exact data and connects those
data to the complex-polynomial Newton--Kantorovich theorem.
-/

namespace HexRootsMathlib

noncomputable section

open Finset

namespace NKData

/-- Exact Taylor coefficients used by the executable witness. -/
@[expose] def coeffs (p : Hex.ZPoly) (s : Hex.DyadicSquare) :
    Array Hex.GaussDyadic :=
  Hex.taylor p s.center

/-- The exact first Taylor coefficient. -/
@[expose] def c1 (p : Hex.ZPoly) (s : Hex.DyadicSquare) : Hex.GaussDyadic :=
  (coeffs p s).getD 1 (0, 0)

/-- Squared modulus of the first Taylor coefficient. -/
@[expose] def normSq (p : Hex.ZPoly) (s : Hex.DyadicSquare) : Dyadic :=
  Hex.GaussDyadic.normSq (c1 p s)

/-- Precision used for the executable reciprocal floor. -/
@[expose] def invPrec (p : Hex.ZPoly) (s : Hex.DyadicSquare) : Int :=
  8 + max 0 (Hex.Dyadic.ceilLog2 (normSq p s))

/-- Executable approximate inverse of the first Taylor coefficient. -/
@[expose] def inverse (p : Hex.ZPoly) (s : Hex.DyadicSquare) : Hex.GaussDyadic :=
  let u := Hex.Dyadic.invFloor (normSq p s) (invPrec p s)
  ((c1 p s).1 * u, -(c1 p s).2 * u)

/-- Taylor coefficient after multiplication by the approximate inverse. -/
@[expose] def residual (p : Hex.ZPoly) (s : Hex.DyadicSquare) (k : Nat) :
    Hex.GaussDyadic :=
  Hex.GaussDyadic.mul (inverse p s) ((coeffs p s).getD k (0, 0))

/-- Exact sup norm of the constant Newton residual. -/
@[expose] def y (p : Hex.ZPoly) (s : Hex.DyadicSquare) : Dyadic :=
  Hex.GaussDyadic.lo (residual p s 0)

/-- Exact sup-operator norm of the first-order defect. -/
@[expose] def z1 (p : Hex.ZPoly) (s : Hex.DyadicSquare) : Dyadic :=
  Hex.Dyadic.abs (1 - (residual p s 1).1) +
    Hex.Dyadic.abs (residual p s 1).2

/-- One step of the running-power fold used by the executable radial bound. -/
@[expose] def z2Step (p : Hex.ZPoly) (s : Hex.DyadicSquare)
    (acc : Dyadic × Dyadic) (i : Nat) : Dyadic × Dyadic :=
  if 2 ≤ i then
    (acc.1 + Dyadic.ofInt i * Hex.GaussDyadic.hi (residual p s i) * acc.2,
      acc.2 * s.radiusHi)
  else acc

/-- Running-power fold used by the executable radial derivative bound. -/
@[expose] def z2Sum (p : Hex.ZPoly) (s : Hex.DyadicSquare) : Dyadic :=
  ((List.range (coeffs p s).size).foldl (z2Step p s) (0, 1)).1

/-- Executable radial derivative-Lipschitz bound. -/
@[expose] def z2 (p : Hex.ZPoly) (s : Hex.DyadicSquare) : Dyadic :=
  2 * z2Sum p s

/-- Sup radius of the certified square. -/
@[expose] def radius (s : Hex.DyadicSquare) : Dyadic :=
  Dyadic.ofIntWithPrec 1 s.prec

/-- Exact representation of half the squared sup radius. -/
@[expose] def halfRadiusSq (s : Hex.DyadicSquare) : Dyadic :=
  Dyadic.ofIntWithPrec 1 (2 * s.prec + 1)

/-- Decode the Boolean witness into its three strict exact inequalities. -/
theorem witness_iff (p : Hex.ZPoly) (s : Hex.DyadicSquare) :
    Hex.nkWitness p s ↔
      2 ≤ (coeffs p s).size ∧
      0 < normSq p s ∧
      y p s + z1 p s * radius s + z2 p s * halfRadiusSq s < radius s ∧
      z1 p s + z2 p s * radius s < 1 := by
  simp only [Hex.nkWitness, Hex.nkWitnessCheck, coeffs, c1, normSq, invPrec,
    inverse, residual, y, z1, z2Sum, z2, radius, halfRadiusSq]
  split <;> rename_i hsize
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨hsize, h0, h1, h2⟩
    · rintro ⟨_, h0, h1, h2⟩
      exact ⟨⟨h0, h1⟩, h2⟩
  · simp [hsize]

/-- Casting the fold accumulator gives its mathematical partial sum and the
next real power of the radial bound. -/
theorem toReal_fold_z2 (p : Hex.ZPoly) (s : Hex.DyadicSquare) (n : Nat) :
    (Dyadic.toReal ((List.range n).foldl (z2Step p s) (0, 1)).1 =
        ∑ i ∈ Finset.range n, if 2 ≤ i then
          (i : ℝ) * Dyadic.toReal (Hex.GaussDyadic.hi (residual p s i)) *
            Dyadic.toReal s.radiusHi ^ (i - 2)
        else 0) ∧
      Dyadic.toReal ((List.range n).foldl (z2Step p s) (0, 1)).2 =
        Dyadic.toReal s.radiusHi ^ (n - 2) := by
  induction n with
  | zero => simp [Dyadic.toReal_zero]
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, Finset.sum_range_succ]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hn : 2 ≤ n
      · have hpow : n + 1 - 2 = (n - 2) + 1 := by omega
        simp [z2Step, hn, ih.1, ih.2, hpow, pow_succ]
      · have hn' : ¬2 ≤ n := hn
        have hpow : n + 1 - 2 = 0 := by omega
        have hprev : n - 2 = 0 := by omega
        simp [z2Step, hn', ih.1, ih.2, hpow, hprev]

/-- Real closed form of the executable running-power sum. -/
theorem toReal_z2Sum (p : Hex.ZPoly) (s : Hex.DyadicSquare) :
    Dyadic.toReal (z2Sum p s) =
      ∑ i ∈ Finset.range (coeffs p s).size, if 2 ≤ i then
        (i : ℝ) * Dyadic.toReal (Hex.GaussDyadic.hi (residual p s i)) *
          Dyadic.toReal s.radiusHi ^ (i - 2)
      else 0 := by
  exact (toReal_fold_z2 p s (coeffs p s).size).1

@[simp] theorem coeffs_size (p : Hex.ZPoly) (s : Hex.DyadicSquare) :
    (coeffs p s).size = p.size := by
  simp [coeffs, Hex.taylor_size]

/-- The zeroth executable Taylor coefficient is evaluation at the centre. -/
theorem coeff_zero (p : Hex.ZPoly) (s : Hex.DyadicSquare) :
    GaussDyadic.toComplex ((coeffs p s).getD 0 (0, 0)) =
      (toPolyℂ p).eval (DyadicSquare.center s) := by
  rw [coeffs, taylor_coeff, ← Polynomial.taylor_apply,
    Polynomial.taylor_coeff_zero]
  rfl

/-- The first executable Taylor coefficient is derivative evaluation at the
centre. -/
theorem coeff_one (p : Hex.ZPoly) (s : Hex.DyadicSquare) :
    GaussDyadic.toComplex (c1 p s) =
      (toPolyℂ p).derivative.eval (DyadicSquare.center s) := by
  rw [c1, coeffs, taylor_coeff, ← Polynomial.taylor_apply,
    Polynomial.taylor_coeff_one]
  rfl

/-- Casting a residual gives multiplication of the approximate inverse by
the corresponding exact Taylor coefficient. -/
theorem toComplex_residual (p : Hex.ZPoly) (s : Hex.DyadicSquare) (k : Nat) :
    GaussDyadic.toComplex (residual p s k) =
      GaussDyadic.toComplex (inverse p s) *
        ((toPolyℂ p).comp (Polynomial.X +
          Polynomial.C (DyadicSquare.center s))).coeff k := by
  rw [residual, GaussDyadic.toComplex_mul, coeffs, taylor_coeff,
    DyadicSquare.center_eq]

@[simp] theorem toReal_radius (s : Hex.DyadicSquare) :
    Dyadic.toReal (radius s) = DyadicSquare.halfWidth s := by
  simp [radius, DyadicSquare.halfWidth_eq]

/-- The sup-norm centre corresponding to the executable square centre. -/
@[expose] def centerSup (s : Hex.DyadicSquare) :
    NewtonKantorovich.ComplexSup :=
  NewtonKantorovich.ComplexSup.equiv (DyadicSquare.center s)

/-- Complex scalar used as the executable approximate inverse. -/
@[expose] def inverseComplex (p : Hex.ZPoly) (s : Hex.DyadicSquare) : ℂ :=
  GaussDyadic.toComplex (inverse p s)

/-- Approximate inverse as a real-linear operator in sup coordinates. -/
@[expose] def approxInverse (p : Hex.ZPoly) (s : Hex.DyadicSquare) :
    NewtonKantorovich.ComplexSup →L[ℝ] NewtonKantorovich.ComplexSup :=
  NewtonKantorovich.ComplexSup.mul (inverseComplex p s)

theorem eval_center (p : Hex.ZPoly) (s : Hex.DyadicSquare) :
    NewtonKantorovich.ComplexSup.eval (toPolyℂ p) (centerSup s) =
      NewtonKantorovich.ComplexSup.equiv
        (GaussDyadic.toComplex ((coeffs p s).getD 0 (0, 0))) := by
  rw [NewtonKantorovich.ComplexSup.eval, centerSup,
    ContinuousLinearEquiv.symm_apply_apply, coeff_zero]

theorem apply_residual (p : Hex.ZPoly) (s : Hex.DyadicSquare) (k : Nat) :
    NewtonKantorovich.ComplexSup.mul (inverseComplex p s)
        (NewtonKantorovich.ComplexSup.equiv
          (GaussDyadic.toComplex ((coeffs p s).getD k (0, 0)))) =
      NewtonKantorovich.ComplexSup.equiv
        (GaussDyadic.toComplex (residual p s k)) := by
  apply NewtonKantorovich.ComplexSup.equiv.symm.injective
  rw [NewtonKantorovich.ComplexSup.equiv_symm_mul]
  simp [inverseComplex, residual]

/-- The first Newton quantity is exact: no Euclidean norm conversion enters. -/
theorem norm_residual (p : Hex.ZPoly) (s : Hex.DyadicSquare) :
    ‖approxInverse p s
        (NewtonKantorovich.ComplexSup.eval (toPolyℂ p) (centerSup s))‖ =
      Dyadic.toReal (y p s) := by
  rw [eval_center]
  change ‖NewtonKantorovich.ComplexSup.mul (inverseComplex p s)
      (NewtonKantorovich.ComplexSup.equiv
        (GaussDyadic.toComplex ((coeffs p s).getD 0 (0, 0))))‖ = _
  rw [apply_residual, NewtonKantorovich.ComplexSup.norm_equiv,
    ← GaussDyadic.toReal_lo]
  rfl

theorem comp_deriv_center (p : Hex.ZPoly) (s : Hex.DyadicSquare) :
    (approxInverse p s).comp
        (NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p) (centerSup s)) =
      NewtonKantorovich.ComplexSup.mul
        (GaussDyadic.toComplex (residual p s 1)) := by
  rw [approxInverse, NewtonKantorovich.ComplexSup.evalDeriv,
    centerSup, ContinuousLinearEquiv.symm_apply_apply,
    NewtonKantorovich.ComplexSup.mul_comp, ← coeff_one]
  rw [inverseComplex, residual, c1, GaussDyadic.toComplex_mul]

/-- The first-order defect bound is the exact sup operator norm. -/
theorem norm_defect (p : Hex.ZPoly) (s : Hex.DyadicSquare) :
    ‖1 - (approxInverse p s).comp
        (NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p) (centerSup s))‖ =
      Dyadic.toReal (z1 p s) := by
  rw [comp_deriv_center, NewtonKantorovich.ComplexSup.norm_one_sub_mul]
  simp [z1]

/-- A nonempty executable polynomial has complex degree below its stored
coefficient count. -/
theorem natDegree_lt_size (p : Hex.ZPoly) (hp : 0 < p.size) :
    (toPolyℂ p).natDegree < p.size := by
  rw [natDegree_toPolyℂ]
  have hdegree : p.degree? = some (p.size - 1) := by
    simp [Hex.DensePoly.degree?, Nat.ne_of_gt hp]
  rw [hdegree, Option.getD_some]
  omega

/-- The exact Taylor shift at the square centre. -/
@[expose] def shifted (p : Hex.ZPoly) (s : Hex.DyadicSquare) : Polynomial ℂ :=
  Polynomial.taylor (DyadicSquare.center s) (toPolyℂ p)

theorem shifted_coeff (p : Hex.ZPoly) (s : Hex.DyadicSquare) (k : Nat) :
    (shifted p s).coeff k =
      GaussDyadic.toComplex ((coeffs p s).getD k (0, 0)) := by
  rw [shifted, Polynomial.taylor_apply, DyadicSquare.center_eq, coeffs]
  exact (taylor_coeff p s.center k).symm

theorem shifted_deriv (p : Hex.ZPoly) (s : Hex.DyadicSquare) (δ : ℂ) :
    (shifted p s).derivative.eval δ =
      (toPolyℂ p).derivative.eval (DyadicSquare.center s + δ) := by
  simp [shifted, Polynomial.taylor_apply, Polynomial.derivative_comp, add_comm]

/-- Radial Taylor identity for the derivative difference. The index is `k`,
not the mean-value overestimate `k * (k - 1)`. -/
theorem deriv_sub_center (p : Hex.ZPoly) (s : Hex.DyadicSquare)
    (hsize : 2 ≤ (coeffs p s).size) (δ : ℂ) :
    (toPolyℂ p).derivative.eval (DyadicSquare.center s + δ) -
        (toPolyℂ p).derivative.eval (DyadicSquare.center s) =
      ∑ k ∈ Finset.range (coeffs p s).size, if 2 ≤ k then
        (k : ℂ) * GaussDyadic.toComplex ((coeffs p s).getD k (0, 0)) *
          δ ^ (k - 1)
      else 0 := by
  have hzero : (shifted p s).derivative.eval 0 =
      (toPolyℂ p).derivative.eval (DyadicSquare.center s) := by
    simpa using shifted_deriv p s 0
  have hp : 0 < p.size := by
    rw [← coeffs_size p s]
    omega
  rw [← shifted_deriv p s δ, ← hzero,
    Polynomial.derivative_eval, Polynomial.derivative_eval]
  have hdegree : (shifted p s).natDegree < (coeffs p s).size := by
    rw [shifted, Polynomial.natDegree_taylor, coeffs_size]
    exact natDegree_lt_size p hp
  rw [(shifted p s).sum_over_range' (fun _ => by simp)
      (coeffs p s).size hdegree,
    (shifted p s).sum_over_range' (fun _ => by simp)
      (coeffs p s).size hdegree, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [shifted_coeff]
  by_cases hk2 : 2 ≤ k
  · have hk1 : 0 < k - 1 := by omega
    rw [if_pos hk2, zero_pow (Nat.ne_of_gt hk1)]
    simp only [mul_zero, sub_zero]
    ring
  · have hk0 : k = 0 ∨ k = 1 := by omega
    rcases hk0 with rfl | rfl <;> simp

/-- The derivative difference after applying the executable approximate
inverse, still as an exact finite Taylor sum. -/
theorem inverse_deriv_sub (p : Hex.ZPoly) (s : Hex.DyadicSquare)
    (hsize : 2 ≤ (coeffs p s).size) (δ : ℂ) :
    inverseComplex p s *
        ((toPolyℂ p).derivative.eval (DyadicSquare.center s + δ) -
          (toPolyℂ p).derivative.eval (DyadicSquare.center s)) =
      ∑ k ∈ Finset.range (coeffs p s).size, if 2 ≤ k then
        (k : ℂ) * GaussDyadic.toComplex (residual p s k) * δ ^ (k - 1)
      else 0 := by
  rw [deriv_sub_center p s hsize, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk2 : 2 ≤ k
  · simp only [hk2, ↓reduceIte]
    rw [residual, GaussDyadic.toComplex_mul, inverseComplex]
    ring
  · simp [hk2]

/-- One radial Taylor term has the executable bound. There is one `√2` from
the scalar operator norm and one from complex modulus versus sup norm; they
combine to the factor `2`. -/
theorem norm_term_le (d : Hex.GaussDyadic) (δ : ℂ) (k : Nat)
    (hk : 2 ≤ k) {ρ t : ℝ} (hρ : ‖δ‖ ≤ ρ) (ht : ‖δ‖ ≤ √2 * t) :
    ‖NewtonKantorovich.ComplexSup.mul
        ((k : ℂ) * GaussDyadic.toComplex d * δ ^ (k - 1))‖ ≤
      2 * ((k : ℝ) * Dyadic.toReal (Hex.GaussDyadic.hi d) * ρ ^ (k - 2)) * t := by
  have hpow : k - 1 = (k - 2) + 1 := by omega
  have hρ0 : 0 ≤ ρ := (norm_nonneg δ).trans hρ
  have hhi0 : 0 ≤ Dyadic.toReal (Hex.GaussDyadic.hi d) := by
    rw [GaussDyadic.toReal_hi]
    positivity
  have ht0 : 0 ≤ t := by
    have hsqrt : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
    nlinarith [norm_nonneg δ]
  have hsqrt : √2 * √2 = (2 : ℝ) := by
    simpa only [pow_two] using Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  calc
    _ ≤ √2 * ‖(k : ℂ) * GaussDyadic.toComplex d * δ ^ (k - 1)‖ :=
      NewtonKantorovich.ComplexSup.norm_mul_le_sqrt_two _
    _ = √2 * (k : ℝ) * ‖GaussDyadic.toComplex d‖ * ‖δ‖ ^ (k - 2) * ‖δ‖ := by
      rw [norm_mul, norm_mul, norm_natCast, norm_pow, hpow, pow_succ]
      ring
    _ ≤ √2 * (k : ℝ) * Dyadic.toReal (Hex.GaussDyadic.hi d) *
        ‖δ‖ ^ (k - 2) * ‖δ‖ := by
      gcongr
      exact GaussDyadic.norm_le_hi d
    _ ≤ √2 * (k : ℝ) * Dyadic.toReal (Hex.GaussDyadic.hi d) *
        ρ ^ (k - 2) * ‖δ‖ := by
      gcongr
    _ ≤ √2 * (k : ℝ) * Dyadic.toReal (Hex.GaussDyadic.hi d) *
        ρ ^ (k - 2) * (√2 * t) := by
      gcongr
    _ = 2 * ((k : ℝ) * Dyadic.toReal (Hex.GaussDyadic.hi d) *
        ρ ^ (k - 2)) * t := by
      calc
        _ = (√2 * √2) * ((k : ℝ) *
            Dyadic.toReal (Hex.GaussDyadic.hi d) * ρ ^ (k - 2)) * t := by ring
        _ = _ := by rw [hsqrt]

/-- Complex displacement from the executable square centre. -/
@[expose] def delta (s : Hex.DyadicSquare)
    (x : NewtonKantorovich.ComplexSup) : ℂ :=
  NewtonKantorovich.ComplexSup.equiv.symm x - DyadicSquare.center s

@[simp] theorem equiv_delta (s : Hex.DyadicSquare)
    (x : NewtonKantorovich.ComplexSup) :
    NewtonKantorovich.ComplexSup.equiv (delta s x) = x - centerSup s := by
  simp [delta, centerSup, map_sub]

theorem norm_delta_le (s : Hex.DyadicSquare)
    (x : NewtonKantorovich.ComplexSup) :
    ‖delta s x‖ ≤ √2 * ‖x - centerSup s‖ := by
  calc
    ‖delta s x‖ ≤ √2 * max |(delta s x).re| |(delta s x).im| :=
      Complex.norm_le_sqrt_two_mul_max _
    _ = √2 * ‖NewtonKantorovich.ComplexSup.equiv (delta s x)‖ := by
      rw [NewtonKantorovich.ComplexSup.norm_equiv]
    _ = _ := by rw [equiv_delta]

theorem norm_delta_le_radiusHi (s : Hex.DyadicSquare)
    (x : NewtonKantorovich.ComplexSup)
    (hx : ‖x - centerSup s‖ ≤ DyadicSquare.halfWidth s) :
    ‖delta s x‖ ≤ Dyadic.toReal s.radiusHi := by
  apply le_of_lt
  calc
    ‖delta s x‖ ≤ √2 * ‖x - centerSup s‖ := norm_delta_le s x
    _ ≤ √2 * DyadicSquare.halfWidth s := by gcongr
    _ = DyadicSquare.radius s := by rw [DyadicSquare.radius, mul_comm]
    _ < Dyadic.toReal s.radiusHi := DyadicSquare.radius_lt_radiusHi s

/-- Applying the approximate inverse to the derivative difference gives the
finite sum whose terms are bounded by `z2`. -/
theorem comp_deriv_sub_eq_sum (p : Hex.ZPoly) (s : Hex.DyadicSquare)
    (hsize : 2 ≤ (coeffs p s).size) (x : NewtonKantorovich.ComplexSup) :
    (approxInverse p s).comp
        (NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p) x -
          NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p) (centerSup s)) =
      ∑ k ∈ Finset.range (coeffs p s).size, if 2 ≤ k then
        NewtonKantorovich.ComplexSup.mul
          ((k : ℂ) * GaussDyadic.toComplex (residual p s k) *
            delta s x ^ (k - 1))
      else 0 := by
  simp only [approxInverse, NewtonKantorovich.ComplexSup.evalDeriv, centerSup,
    ContinuousLinearEquiv.symm_apply_apply]
  rw [
    ← NewtonKantorovich.ComplexSup.mul_sub,
    NewtonKantorovich.ComplexSup.mul_comp]
  have hsum := inverse_deriv_sub p s hsize (delta s x)
  have hcentre : DyadicSquare.center s + delta s x =
      NewtonKantorovich.ComplexSup.equiv.symm x := by
    simp [delta]
  rw [hcentre] at hsum
  rw [hsum, NewtonKantorovich.ComplexSup.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk2 : 2 ≤ k <;> simp [hk2]

/-- The executable `z2` is a radial Lipschitz bound for the transported
polynomial derivative on the certified sup ball. -/
theorem deriv_lipschitz (p : Hex.ZPoly) (s : Hex.DyadicSquare)
    (hsize : 2 ≤ (coeffs p s).size) (x : NewtonKantorovich.ComplexSup)
    (hx : ‖x - centerSup s‖ ≤ DyadicSquare.halfWidth s) :
    ‖(approxInverse p s).comp
        (NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p) x -
          NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p) (centerSup s))‖ ≤
      Dyadic.toReal (z2 p s) * ‖x - centerSup s‖ := by
  rw [comp_deriv_sub_eq_sum p s hsize]
  calc
    _ ≤ ∑ k ∈ Finset.range (coeffs p s).size, ‖if 2 ≤ k then
        NewtonKantorovich.ComplexSup.mul
          ((k : ℂ) * GaussDyadic.toComplex (residual p s k) *
            delta s x ^ (k - 1))
      else 0‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (coeffs p s).size, if 2 ≤ k then
        2 * ((k : ℝ) * Dyadic.toReal (Hex.GaussDyadic.hi (residual p s k)) *
          Dyadic.toReal s.radiusHi ^ (k - 2)) * ‖x - centerSup s‖
      else 0 := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hk2 : 2 ≤ k
        · simp only [hk2, ↓reduceIte]
          exact norm_term_le _ _ k hk2 (norm_delta_le_radiusHi s x hx)
            (norm_delta_le s x)
        · simp [hk2]
    _ = _ := by
      rw [z2, Dyadic.toReal_mul, Dyadic.toReal_two, toReal_z2Sum,
        Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hk2 : 2 ≤ k <;> simp [hk2]

@[simp] theorem toReal_halfRadiusSq (s : Hex.DyadicSquare) :
    Dyadic.toReal (halfRadiusSq s) = DyadicSquare.halfWidth s ^ 2 / 2 := by
  simp only [halfRadiusSq, Dyadic.toReal_ofIntWithPrec, Int.cast_one, one_mul,
    DyadicSquare.halfWidth_eq]
  rw [show -(2 * s.prec + 1) = -s.prec + -s.prec + (-1 : Int) by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num [pow_two]
  ring

theorem toReal_z2_nonneg (p : Hex.ZPoly) (s : Hex.DyadicSquare) :
    0 ≤ Dyadic.toReal (z2 p s) := by
  rw [z2, Dyadic.toReal_mul, Dyadic.toReal_two, toReal_z2Sum]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun k hk => ?_)
  split_ifs
  · have hhi : 0 ≤ Dyadic.toReal (Hex.GaussDyadic.hi (residual p s k)) := by
      rw [GaussDyadic.toReal_hi]
      positivity
    have hradius : 0 ≤ DyadicSquare.radius s := by
      exact mul_nonneg (le_of_lt (by
        rw [DyadicSquare.halfWidth_eq]
        positivity)) (Real.sqrt_nonneg 2)
    have hρ : 0 ≤ Dyadic.toReal s.radiusHi := by
      exact hradius.trans (le_of_lt (DyadicSquare.radius_lt_radiusHi s))
    positivity
  · exact le_rfl

/-- Nonnegative Newton quantities in the format consumed by the generic
theorem. -/
@[expose] def yNN (p : Hex.ZPoly) (s : Hex.DyadicSquare) : NNReal :=
  ⟨Dyadic.toReal (y p s), by
    rw [← norm_residual]
    positivity⟩

@[expose] def z1NN (p : Hex.ZPoly) (s : Hex.DyadicSquare) : NNReal :=
  ⟨Dyadic.toReal (z1 p s), by
    rw [← norm_defect]
    positivity⟩

@[expose] def z2NN (p : Hex.ZPoly) (s : Hex.DyadicSquare) : NNReal :=
  ⟨Dyadic.toReal (z2 p s), toReal_z2_nonneg p s⟩

@[expose] def radiusNN (s : Hex.DyadicSquare) : NNReal :=
  ⟨DyadicSquare.halfWidth s, by
    rw [DyadicSquare.halfWidth_eq]
    positivity⟩

/-- The strict radius and contraction inequalities encoded by the executable
witness. -/
theorem witness_inequalities {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.nkWitness p s) :
    yNN p s + z1NN p s * radiusNN s +
          z2NN p s * radiusNN s ^ 2 / 2 < radiusNN s ∧
      z1NN p s + z2NN p s * radiusNN s < 1 := by
  obtain ⟨_, _, hyr, hzr⟩ := (witness_iff p s).mp h
  have hyr' := Dyadic.toReal_lt_toReal_iff.mpr hyr
  have hzr' := Dyadic.toReal_lt_toReal_iff.mpr hzr
  simp only [Dyadic.toReal_add, Dyadic.toReal_mul, toReal_radius,
    toReal_halfRadiusSq, Dyadic.toReal_one] at hyr' hzr'
  constructor
  · apply NNReal.coe_lt_coe.mp
    change Dyadic.toReal (y p s) + Dyadic.toReal (z1 p s) *
        DyadicSquare.halfWidth s + Dyadic.toReal (z2 p s) *
          DyadicSquare.halfWidth s ^ 2 / 2 < DyadicSquare.halfWidth s
    nlinarith [hyr']
  · apply NNReal.coe_lt_coe.mp
    change Dyadic.toReal (z1 p s) + Dyadic.toReal (z2 p s) *
        DyadicSquare.halfWidth s < 1
    exact hzr'

/-- The generic Newton--Kantorovich theorem applied to the exact executable
quantities, before transporting the result back from sup coordinates. -/
theorem existsUnique_root_sup {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.nkWitness p s) :
    ∃! x, (toPolyℂ p).eval
          (NewtonKantorovich.ComplexSup.equiv.symm x) = 0 ∧
        ‖x - centerSup s‖₊ ≤ radiusNN s := by
  have hsize := (witness_iff p s).mp h |>.1
  obtain ⟨hyr, hzr⟩ := witness_inequalities h
  apply NewtonKantorovich.ComplexSup.existsUnique_root
      (A := approxInverse p s) (R := (radiusNN s : ENNReal))
      (x₀ := centerSup s) (y := yNN p s) (z₁ := z1NN p s)
      (z₂ := z2NN p s) (r := radiusNN s)
  · apply NNReal.coe_le_coe.mp
    change ‖approxInverse p s
      (NewtonKantorovich.ComplexSup.eval (toPolyℂ p) (centerSup s))‖ ≤
        Dyadic.toReal (y p s)
    rw [norm_residual]
  · apply NNReal.coe_le_coe.mp
    change ‖1 - (approxInverse p s).comp
        (NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p) (centerSup s))‖ ≤
      Dyadic.toReal (z1 p s)
    rw [norm_defect]
  · intro x hx
    rw [Metric.closedEBall_coe,
      NewtonKantorovich.mem_closedBall_iff_nnnorm] at hx
    have hx' : ‖x - centerSup s‖ ≤ DyadicSquare.halfWidth s := by
      exact_mod_cast hx
    apply NNReal.coe_le_coe.mp
    change ‖(approxInverse p s).comp
        (NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p) x -
          NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p) (centerSup s))‖ ≤
      Dyadic.toReal (z2 p s) * ‖x - centerSup s‖
    exact deriv_lipschitz p s hsize x hx'
  · simp
  · exact hyr.le
  · exact hzr

theorem mem_closedSquare_iff (s : Hex.DyadicSquare) (z : ℂ) :
    z ∈ DyadicSquare.closedSquare s ↔
      ‖NewtonKantorovich.ComplexSup.equiv z - centerSup s‖ ≤
        DyadicSquare.halfWidth s := by
  change max |(z - DyadicSquare.center s).re|
      |(z - DyadicSquare.center s).im| ≤ DyadicSquare.halfWidth s ↔ _
  rw [← NewtonKantorovich.ComplexSup.norm_equiv, map_sub]
  rfl

theorem mem_openSquare_iff (s : Hex.DyadicSquare) (z : ℂ) :
    z ∈ DyadicSquare.openSquare s ↔
      ‖NewtonKantorovich.ComplexSup.equiv z - centerSup s‖ <
        DyadicSquare.halfWidth s := by
  change max |(z - DyadicSquare.center s).re|
      |(z - DyadicSquare.center s).im| < DyadicSquare.halfWidth s ↔ _
  rw [← NewtonKantorovich.ComplexSup.norm_equiv, map_sub]
  rfl

/-- An executable Newton witness certifies exactly one root in the closed
dyadic square. -/
theorem existsUnique_root {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.nkWitness p s) :
    ∃! z, (toPolyℂ p).eval z = 0 ∧ z ∈ DyadicSquare.closedSquare s := by
  obtain ⟨x, hx, hunique⟩ := existsUnique_root_sup h
  refine ⟨NewtonKantorovich.ComplexSup.equiv.symm x, ?_, ?_⟩
  · constructor
    · exact hx.1
    · rw [mem_closedSquare_iff]
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        (show ‖x - centerSup s‖ ≤ DyadicSquare.halfWidth s by
          exact_mod_cast hx.2)
  · rintro z ⟨hzroot, hzmem⟩
    apply NewtonKantorovich.ComplexSup.equiv.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    apply hunique
    constructor
    · simpa using hzroot
    · apply NNReal.coe_le_coe.mp
      change ‖NewtonKantorovich.ComplexSup.equiv z - centerSup s‖ ≤
        DyadicSquare.halfWidth s
      exact (mem_closedSquare_iff s z).mp hzmem

/-- Throughout the certified square, the approximate-inverse derivative
defect has norm strictly below one. -/
theorem defect_lt_one {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.nkWitness p s) (z : ℂ) (hz : z ∈ DyadicSquare.closedSquare s) :
    ‖1 - (approxInverse p s).comp
        (NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p)
          (NewtonKantorovich.ComplexSup.equiv z))‖ < 1 := by
  have hsize := (witness_iff p s).mp h |>.1
  have hz' := (mem_closedSquare_iff s z).mp hz
  have hlip := deriv_lipschitz p s hsize
    (NewtonKantorovich.ComplexSup.equiv z) hz'
  have hzr := (witness_inequalities h).2
  have hzr' : Dyadic.toReal (z1 p s) + Dyadic.toReal (z2 p s) *
      DyadicSquare.halfWidth s < 1 := by
    exact_mod_cast hzr
  calc
    _ = ‖(1 - (approxInverse p s).comp
          (NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p) (centerSup s))) -
        (approxInverse p s).comp
          (NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p)
              (NewtonKantorovich.ComplexSup.equiv z) -
            NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p)
              (centerSup s))‖ := by
      congr 1
      apply ContinuousLinearMap.ext
      intro x
      simp
    _ ≤ ‖1 - (approxInverse p s).comp
          (NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p) (centerSup s))‖ +
        ‖(approxInverse p s).comp
          (NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p)
              (NewtonKantorovich.ComplexSup.equiv z) -
            NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p)
              (centerSup s))‖ := norm_sub_le _ _
    _ ≤ Dyadic.toReal (z1 p s) + Dyadic.toReal (z2 p s) *
        ‖NewtonKantorovich.ComplexSup.equiv z - centerSup s‖ := by
      rw [norm_defect]
      gcongr
    _ ≤ Dyadic.toReal (z1 p s) + Dyadic.toReal (z2 p s) *
        DyadicSquare.halfWidth s := by
      gcongr
      exact toReal_z2_nonneg p s
    _ < 1 := hzr'

/-- Every root in a Newton-certified square is simple. -/
theorem derivative_ne_zero {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.nkWitness p s) {z : ℂ} (hz : z ∈ DyadicSquare.closedSquare s) :
    (toPolyℂ p).derivative.eval z ≠ 0 := by
  intro hzero
  have hdef := defect_lt_one h z hz
  have hevalDeriv : NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p)
      (NewtonKantorovich.ComplexSup.equiv z) = 0 := by
    rw [NewtonKantorovich.ComplexSup.evalDeriv,
      ContinuousLinearEquiv.symm_apply_apply, hzero,
      NewtonKantorovich.ComplexSup.mul_zero]
  rw [hevalDeriv] at hdef
  simp at hdef

/-- The strict radius check places every root in the certified closed square
strictly inside that square. -/
theorem root_mem_openSquare {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.nkWitness p s) {z : ℂ} (hzroot : (toPolyℂ p).eval z = 0)
    (hz : z ∈ DyadicSquare.closedSquare s) :
    z ∈ DyadicSquare.openSquare s := by
  let x₀ := centerSup s
  let x := NewtonKantorovich.ComplexSup.equiv z
  let A := approxInverse p s
  let F := NewtonKantorovich.ComplexSup.eval (toPolyℂ p)
  let DF := NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p)
  let T (u : NewtonKantorovich.ComplexSup) := u - A (F u)
  let DT (u : NewtonKantorovich.ComplexSup) := 1 - A.comp (DF u)
  have hsize := (witness_iff p s).mp h |>.1
  have hxnorm := (mem_closedSquare_iff s z).mp hz
  have hx : x ∈ Metric.closedBall x₀ (radiusNN s) := by
    rw [NewtonKantorovich.mem_closedBall_iff_nnnorm]
    apply NNReal.coe_le_coe.mp
    exact hxnorm
  have hT (u) : HasFDerivAt T (DT u) u :=
    (hasFDerivAt_id u).sub
      (A.hasFDerivAt.comp u (NewtonKantorovich.ComplexSup.hasFDerivAt_eval _ _))
  have hDT : Continuous DT := by
    have hcomp : Continuous fun u => A.comp (DF u) :=
      (A.postcomp NewtonKantorovich.ComplexSup).continuous.comp
        (NewtonKantorovich.ComplexSup.continuous_evalDeriv _)
    exact continuous_const.sub hcomp
  have hy : ‖T x₀ - x₀‖₊ ≤ yNN p s := by
    have hy0 : ‖approxInverse p s
        (NewtonKantorovich.ComplexSup.eval (toPolyℂ p) (centerSup s))‖₊ =
        yNN p s := by
      apply NNReal.eq
      exact norm_residual p s
    simpa [T, F, A, x₀] using hy0.le
  have hz1 : ‖DT x₀‖₊ ≤ z1NN p s := by
    apply NNReal.coe_le_coe.mp
    change ‖1 - (approxInverse p s).comp
        (NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p) (centerSup s))‖ ≤
      Dyadic.toReal (z1 p s)
    exact (norm_defect p s).le
  have hz2 : ∀ u ∈ Metric.closedBall x₀ (radiusNN s),
      ‖DT u - DT x₀‖₊ ≤ z2NN p s * ‖u - x₀‖₊ := by
    intro u hu
    have hu' : ‖u - centerSup s‖ ≤ DyadicSquare.halfWidth s := by
      rw [NewtonKantorovich.mem_closedBall_iff_nnnorm] at hu
      exact_mod_cast hu
    have hlip := deriv_lipschitz p s hsize u hu'
    have hlipNN : ‖(approxInverse p s).comp
          (NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p) u -
            NewtonKantorovich.ComplexSup.evalDeriv (toPolyℂ p) (centerSup s))‖₊ ≤
        z2NN p s * ‖u - centerSup s‖₊ := by
      rw [show z2NN p s = ⟨Dyadic.toReal (z2 p s),
        toReal_z2_nonneg p s⟩ from rfl]
      apply NNReal.coe_le_coe.mp
      exact hlip
    rw [← nnnorm_neg]
    simpa [DT, DF, A, x₀] using hlipNN
  have hbound := NewtonKantorovich.image_bound hT hDT hy hz1 hz2
    (le_refl (radiusNN s)) hx
  have hFx : F x = 0 := by
    change NewtonKantorovich.ComplexSup.equiv
      ((toPolyℂ p).eval (NewtonKantorovich.ComplexSup.equiv.symm
        (NewtonKantorovich.ComplexSup.equiv z))) = 0
    rw [ContinuousLinearEquiv.symm_apply_apply, hzroot, map_zero]
  have hfixed : T x = x := by simp [T, hFx]
  have hstrict := (witness_inequalities h).1
  rw [mem_openSquare_iff]
  have hnn : ‖NewtonKantorovich.ComplexSup.equiv z - centerSup s‖₊ <
      radiusNN s := by
    calc
      _ = ‖T x - x₀‖₊ := by
        rw [hfixed]
      _ ≤ yNN p s + z1NN p s * radiusNN s +
          z2NN p s * radiusNN s ^ 2 / 2 := hbound
      _ < radiusNN s := hstrict
  exact_mod_cast hnn

/-- Combined semantic contract of an executable Newton witness. -/
theorem sound {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.nkWitness p s) :
    ∃ z, (toPolyℂ p).eval z = 0 ∧
      z ∈ DyadicSquare.openSquare s ∧
      (toPolyℂ p).derivative.eval z ≠ 0 ∧
      ∀ w, (toPolyℂ p).eval w = 0 →
        w ∈ DyadicSquare.closedSquare s → w = z := by
  obtain ⟨z, hz, hunique⟩ := existsUnique_root h
  exact ⟨z, hz.1, root_mem_openSquare h hz.1 hz.2,
    derivative_ne_zero h hz.2, fun w hwroot hwmem =>
      hunique w ⟨hwroot, hwmem⟩⟩

end NKData

end

end HexRootsMathlib
