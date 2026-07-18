/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib
public import HexPolyZ
public import HexPolyMathlib.Basic
public import HexRealRoots.Mobius
public import HexRealRootsMathlib.Separation
public import HexRealRootsMathlib.ChainCorrespond
-- `import all` so the non-`@[expose]` bodies of `signVar`, `mobiusTransform`
-- (and the private endpoint helpers it captures), and `Dyadic.toReal` unfold
-- here, matching the discipline in `ChainCorrespond`.
import all HexRealRoots.Var
import all HexRealRoots.Mobius
import all HexRealRootsMathlib.Separation

public section

/-!
# The Möbius transform correspondence for the Descartes engine

This module connects the executable integer Möbius transform
`Hex.mobiusTransform` and the Descartes variation count `Hex.descartesVar`
(both in `HexRealRoots.Mobius`) to an abstract `Polynomial` Möbius transform
`HexRealRootsMathlib.mobiusPoly` built entirely from Mathlib primitives
(`Polynomial.comp`, `Polynomial.reflect`).

The abstract transform is
`mobiusPoly n a b P = (reflect n ((P.comp (X + C b)).comp (C (a-b) * X))).comp (X + C 1)`;
its defining evaluation identity is
`(mobiusPoly n a b P).eval z = (1+z)^n * P.eval ((a+b*z)/(1+z))` (`1+z ≠ 0`),
so the positive real roots of `mobiusPoly n a b P` are the images of the real
roots of `P` in the open interval `(a, b)` under `w ↦ (w-a)/(b-w)`.
-/

namespace HexRealRootsMathlib

open Polynomial

noncomputable section

/-- The abstract Möbius transform over a commutative ring: clears to the
`(a, b)` window, homogenizes at degree `n`, and shifts back to the positive
axis. Built from Mathlib primitives so `reflect_mul` and the composition
lemmas apply directly. -/
@[expose] def mobiusPoly {R : Type*} [CommRing R] (n : ℕ) (a b : R) (P : Polynomial R) :
    Polynomial R :=
  (Polynomial.reflect n ((P.comp (Polynomial.X + Polynomial.C b)).comp
    (Polynomial.C (a - b) * Polynomial.X))).comp (Polynomial.X + Polynomial.C 1)

/-- The inner (pre-reflection) polynomial of the Möbius transform. -/
@[expose] def mobiusInner {R : Type*} [CommRing R] (a b : R) (P : Polynomial R) :
    Polynomial R :=
  (P.comp (Polynomial.X + Polynomial.C b)).comp (Polynomial.C (a - b) * Polynomial.X)

theorem mobiusPoly_eq_reflect_comp {R : Type*} [CommRing R] (n : ℕ) (a b : R)
    (P : Polynomial R) :
    mobiusPoly n a b P
      = (Polynomial.reflect n (mobiusInner a b P)).comp (Polynomial.X + Polynomial.C 1) :=
  rfl

/-- **Ring-hom commutation.** The Möbius transform commutes with mapping along a
ring homomorphism `φ`: every stage (`X + C` shift, `C (a-b) * X` dilation,
`reflect`, the final `X + C 1` shift) is built from `comp`, `reflect`, `C`, `X`,
`+`, `*`, `-`, which all commute with `Polynomial.map φ`. This is the bridge from
the real transform to its complex-root picture (`φ = algebraMap ℝ ℂ`). -/
theorem mobiusPoly_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (n : ℕ) (a b : R) (P : Polynomial R) :
    (mobiusPoly n a b P).map φ = mobiusPoly n (φ a) (φ b) (P.map φ) := by
  simp only [mobiusPoly_eq_reflect_comp, mobiusInner, Polynomial.map_comp,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.map_C, map_sub, Polynomial.C_1, Polynomial.map_one,
    ← Polynomial.reflect_map]

/-- The inner Möbius polynomial has degree at most that of `P`: composing with
the degree-one shift `X + C b` preserves degree, and composing with the (at
most) degree-one dilation `C (a-b) * X` cannot raise it. Proved without
`Nontrivial R` (both linear factors are bounded by degree `1`). -/
theorem natDegree_mobiusInner_le {R : Type*} [CommRing R] (a b : R) (P : Polynomial R) :
    (mobiusInner a b P).natDegree ≤ P.natDegree := by
  have h1 : (Polynomial.X + Polynomial.C b : Polynomial R).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    rw [Polynomial.natDegree_C]
    exact max_le Polynomial.natDegree_X_le (Nat.zero_le _)
  have h2 : (Polynomial.C (a - b) * Polynomial.X : Polynomial R).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    rw [Polynomial.natDegree_C, zero_add]
    exact Polynomial.natDegree_X_le
  have hcomp : (P.comp (Polynomial.X + Polynomial.C b)).natDegree ≤ P.natDegree :=
    le_trans Polynomial.natDegree_comp_le
      (le_trans (Nat.mul_le_mul_left _ h1) (le_of_eq (Nat.mul_one _)))
  refine le_trans Polynomial.natDegree_comp_le ?_
  exact le_trans (Nat.mul_le_mul hcomp h2) (le_of_eq (Nat.mul_one _))

/-- `natDegree (reflect N f) ≤ N` when `f.natDegree ≤ N`: reflection sends the
support into `[0, N]`. -/
theorem natDegree_reflect_le {R : Type*} [CommRing R] {N : ℕ} {f : Polynomial R}
    (hf : f.natDegree ≤ N) : (Polynomial.reflect N f).natDegree ≤ N := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [Polynomial.coeff_reflect, Polynomial.revAt_eq_self_of_lt hm]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hf hm)

/-! ### The reflect evaluation identity over a field -/

/-- **Reflect evaluation.** Over a field, for `f.natDegree ≤ N` and `z ≠ 0`,
`(reflect N f).eval z = z^N * f.eval z⁻¹`: reflection is the `x ↦ 1/x`
homogenization at degree `N`. -/
theorem eval_reflect {K : Type*} [Field K] {N : ℕ} {f : Polynomial K}
    (hf : f.natDegree ≤ N) {z : K} (hz : z ≠ 0) :
    (Polynomial.reflect N f).eval z = z ^ N * f.eval z⁻¹ := by
  have hrd : (Polynomial.reflect N f).natDegree < N + 1 :=
    Nat.lt_succ_of_le (natDegree_reflect_le hf)
  have hfd : f.natDegree < N + 1 := Nat.lt_succ_of_le hf
  rw [Polynomial.eval_eq_sum_range' hrd,
    ← Finset.sum_range_reflect (fun i => (Polynomial.reflect N f).coeff i * z ^ i) (N + 1),
    Polynomial.eval_eq_sum_range' hfd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ N := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
  rw [show N + 1 - 1 - j = N - j from by omega, Polynomial.coeff_reflect,
    Polynomial.revAt_le (Nat.sub_le N j), Nat.sub_sub_self hjle, inv_pow, pow_sub₀ z hz hjle]
  ring

/-! ### Multiplicativity -/

/-- **Multiplicativity of the Möbius transform.** With degrees split across the
two factors, `mobiusPoly` of a product is the product of the transforms. The
degree hypotheses feed `reflect_mul`. -/
theorem mobiusPoly_mul {R : Type*} [CommRing R] {n₁ n₂ : ℕ} (a b : R)
    {P Q : Polynomial R} (hP : P.natDegree ≤ n₁) (hQ : Q.natDegree ≤ n₂) :
    mobiusPoly (n₁ + n₂) a b (P * Q)
      = mobiusPoly n₁ a b P * mobiusPoly n₂ a b Q := by
  rw [mobiusPoly_eq_reflect_comp, mobiusPoly_eq_reflect_comp, mobiusPoly_eq_reflect_comp]
  have hinner : mobiusInner a b (P * Q) = mobiusInner a b P * mobiusInner a b Q := by
    unfold mobiusInner
    rw [Polynomial.mul_comp, Polynomial.mul_comp]
  rw [hinner, Polynomial.reflect_mul _ _
      (le_trans (natDegree_mobiusInner_le a b P) hP)
      (le_trans (natDegree_mobiusInner_le a b Q) hQ),
    Polynomial.mul_comp]

/-! ### The evaluation identity over a field -/

/-- **Evaluation identity.** Over a field, for `P.natDegree ≤ n` and `1 + z ≠ 0`,
`(mobiusPoly n a b P).eval z = (1+z)^n * P.eval ((a+b*z)/(1+z))`. This is the
Möbius map `t ↦ (a + b t)/(1 + t)` cleared to a polynomial: positive real roots
`t` of `mobiusPoly` correspond to real roots of `P` at `(a + b t)/(1 + t)`. -/
theorem mobiusPoly_eval {K : Type*} [Field K] {n : ℕ} (a b : K) {P : Polynomial K}
    (hP : P.natDegree ≤ n) {z : K} (hz : (1 : K) + z ≠ 0) :
    (mobiusPoly n a b P).eval z = (1 + z) ^ n * P.eval ((a + b * z) / (1 + z)) := by
  have hz1 : z + 1 ≠ 0 := by rwa [add_comm] at hz
  rw [mobiusPoly_eq_reflect_comp, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C,
    eval_reflect (le_trans (natDegree_mobiusInner_le a b P) hP) hz1, add_comm z 1]
  congr 1
  unfold mobiusInner
  rw [Polynomial.eval_comp, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  congr 1
  field_simp
  ring

/-! ### The value at `-1`: leading-coefficient extraction and nonvanishing -/

/-- **Value at `-1`.** `(mobiusPoly n a b P).eval (-1) = (P.comp (X + C b)).coeff n · (a-b)^n`.
The homogenization sends the top coefficient to the constant term, read off at
`-1` (which the final `X + 1` shift sends to `0`). -/
theorem mobiusPoly_eval_neg_one {R : Type*} [CommRing R] (n : ℕ) (a b : R)
    (P : Polynomial R) :
    (mobiusPoly n a b P).eval (-1)
      = (P.comp (X + C b)).coeff n * (a - b) ^ n := by
  rw [mobiusPoly_eq_reflect_comp, eval_comp, eval_add, eval_X, eval_C, neg_add_cancel,
    ← coeff_zero_eq_eval_zero, coeff_reflect, revAt_zero]
  unfold mobiusInner
  rw [comp_C_mul_X_coeff]

/-- Shifting by `X + C b` preserves the top coefficient: at the natural degree,
`(P.comp (X + C b)).coeff = P.leadingCoeff`. -/
theorem coeff_comp_X_add_C_natDegree {K : Type*} [Field K] (P : Polynomial K) (b : K) :
    (P.comp (X + C b)).coeff P.natDegree = P.leadingCoeff := by
  by_cases hP : P = 0
  · simp [hP]
  have hnd : (P.comp (X + C b)).natDegree = P.natDegree := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  have hlc : (P.comp (X + C b)).leadingCoeff = P.leadingCoeff := by
    rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero),
      leadingCoeff_X_add_C, one_pow, mul_one]
  conv_lhs => rw [show P.natDegree = (P.comp (X + C b)).natDegree from hnd.symm]
  exact hlc

/-- **Value at `-1`, leading form.** When `n = natDegree P`, the value at `-1`
is `P.leadingCoeff · (a-b)^n`. -/
theorem mobiusPoly_eval_neg_one_leading {K : Type*} [Field K] {n : ℕ} (a b : K)
    {P : Polynomial K} (hn : P.natDegree = n) :
    (mobiusPoly n a b P).eval (-1) = P.leadingCoeff * (a - b) ^ n := by
  subst hn
  rw [mobiusPoly_eval_neg_one, coeff_comp_X_add_C_natDegree]

/-- **Nonvanishing.** For `a ≠ b` and `P ≠ 0` at its own degree, the transform is
nonzero: its value at `-1` is `P.leadingCoeff · (a-b)^n ≠ 0`. -/
theorem mobiusPoly_ne_zero {K : Type*} [Field K] {n : ℕ} (a b : K)
    {P : Polynomial K} (hab : a ≠ b) (hP : P ≠ 0) (hn : P.natDegree = n) :
    mobiusPoly n a b P ≠ 0 := by
  intro h
  have hval := mobiusPoly_eval_neg_one_leading a b hn
  rw [h, eval_zero] at hval
  exact (mul_ne_zero (leadingCoeff_ne_zero.mpr hP)
    (pow_ne_zero _ (sub_ne_zero.mpr hab))) hval.symm

/-! ### Linear values -/

/-- **Linear value (interior).** For `w ≠ b`, the degree-one transform maps the
factor `X - C w` to `C (b-w) · (X - C ((w-a)/(b-w)))`: the root `w` of `X - C w`
goes to `(w-a)/(b-w)`. -/
theorem mobiusPoly_X_sub_C {K : Type*} [Field K] (a b w : K) (hwb : w ≠ b) :
    mobiusPoly 1 a b (X - C w) = C (b - w) * (X - C ((w - a) / (b - w))) := by
  have hbw : b - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hwb)
  have hval : mobiusPoly 1 a b (X - C w) = C (b - w) * X + C (a - w) := by
    rw [mobiusPoly_eq_reflect_comp]
    have hinner : mobiusInner a b (X - C w) = C (a - b) * X + C (b - w) := by
      unfold mobiusInner
      simp only [sub_comp, add_comp, X_comp, C_comp]
      rw [add_sub_assoc, ← C_sub]
    rw [hinner,
      show (C (a - b) * X + C (b - w) : Polynomial K) = C (a - b) * X ^ 1 + C (b - w) from by
        rw [pow_one],
      reflect_add, reflect_C_mul_X_pow, reflect_C, revAt_le (le_refl 1)]
    simp only [Nat.sub_self, pow_zero, mul_one, pow_one]
    rw [add_comp, mul_comp, C_comp, X_comp, C_comp, mul_add,
      mul_comm (C (b - w)) (C 1), ← C_mul, one_mul,
      add_comm (C (b - w) * X) (C (b - w)), ← add_assoc, ← C_add,
      show (a - b) + (b - w) = a - w from by ring]
    ring
  rw [hval, mul_sub, ← C_mul,
    show (b - w) * ((w - a) / (b - w)) = w - a from by field_simp,
    show (a - w : K) = -(w - a) from by ring, map_neg]
  ring

/-- **Linear value (right endpoint).** The factor `X - C b` (a root at the
excluded upper endpoint) collapses to the constant `C (a - b)`: it has no
positive-root image. -/
theorem mobiusPoly_X_sub_C_upper {R : Type*} [CommRing R] (a b : R) :
    mobiusPoly 1 a b (X - C b) = C (a - b) := by
  rw [mobiusPoly_eq_reflect_comp]
  have hinner : mobiusInner a b (X - C b) = C (a - b) * X := by
    unfold mobiusInner
    simp only [sub_comp, add_comp, X_comp, C_comp]
    ring
  rw [hinner,
    show (C (a - b) * X : Polynomial R) = C (a - b) * X ^ 1 from by rw [pow_one],
    reflect_C_mul_X_pow, revAt_le (le_refl 1)]
  simp only [Nat.sub_self, pow_zero, mul_one]
  rw [C_comp]

/-! ### Powers, nonvanishing, and root correspondences -/

/-- `mobiusPoly 0` fixes constants. -/
theorem mobiusPoly_C {R : Type*} [CommRing R] (a b c : R) :
    mobiusPoly 0 a b (C c) = C c := by
  rw [mobiusPoly_eq_reflect_comp]
  have hinner : mobiusInner a b (C c) = C c := by
    unfold mobiusInner
    rw [C_comp, C_comp]
  rw [hinner, reflect_C, pow_zero, mul_one, C_comp]

/-- `mobiusPoly 0` fixes `1`. -/
theorem mobiusPoly_one {R : Type*} [CommRing R] (a b : R) :
    mobiusPoly 0 a b 1 = 1 := by
  rw [← C_1, mobiusPoly_C]

/-- Power form of multiplicativity: with a degree bound per factor,
`mobiusPoly` of a power is the power of the transform. -/
theorem mobiusPoly_pow {R : Type*} [CommRing R] {k : ℕ} (a b : R) {Q : Polynomial R}
    (hQ : Q.natDegree ≤ k) (m : ℕ) :
    mobiusPoly (m * k) a b (Q ^ m) = (mobiusPoly k a b Q) ^ m := by
  induction m with
  | zero => rw [Nat.zero_mul, pow_zero, pow_zero, mobiusPoly_one]
  | succ m ih =>
      rw [pow_succ, pow_succ, Nat.succ_mul,
        mobiusPoly_mul a b (le_trans natDegree_pow_le (Nat.mul_le_mul_left m hQ)) hQ, ih]

/-- **Nonvanishing, degree-free form.** Over a field, for `a ≠ b`, the Möbius
transform of a nonzero polynomial is nonzero at every window degree `k`: each
pipeline stage (`X + C` shifts, the `C (a-b) * X` dilation, `reflect`) reflects
zeroness. -/
theorem mobiusPoly_ne_zero_of_ne {K : Type*} [Field K] {k : ℕ} {a b : K}
    (hab : a ≠ b) {P : Polynomial K} (hP : P ≠ 0) :
    mobiusPoly k a b P ≠ 0 := by
  have h1 : P.comp (X + C b) ≠ 0 := comp_X_add_C_eq_zero_iff.not.mpr hP
  have h2 : (P.comp (X + C b)).comp (C (a - b) * X) ≠ 0 :=
    (comp_C_mul_X_eq_zero_iff
      (mem_nonZeroDivisors_of_ne_zero (sub_ne_zero.mpr hab))).not.mpr h1
  have h3 : Polynomial.reflect k ((P.comp (X + C b)).comp (C (a - b) * X)) ≠ 0 :=
    reflect_eq_zero_iff.not.mpr h2
  show (Polynomial.reflect k ((P.comp (X + C b)).comp (C (a - b) * X))).comp (X + C 1) ≠ 0
  exact comp_X_add_C_eq_zero_iff.not.mpr h3

/-- The image `(w-a)/(b-w)` of `w ∈ (a, b)` pulls back to `w` under the inverse
Möbius map `t ↦ (a+b*t)/(1+t)`. -/
private theorem mobius_inverse {K : Type*} [Field K] {a b w : K} (hab : a ≠ b)
    (hwb : w ≠ b) :
    (1 : K) + (w - a) / (b - w) ≠ 0 ∧
      (a + b * ((w - a) / (b - w))) / (1 + (w - a) / (b - w)) = w := by
  have hbw : b - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hwb)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hq : (b - a) / (b - w) ≠ 0 := div_ne_zero hba hbw
  have h1t : (1 : K) + (w - a) / (b - w) = (b - a) / (b - w) := by
    rw [eq_div_iff hbw, add_mul, one_mul, div_mul_cancel₀ _ hbw]
    ring
  refine ⟨by rw [h1t]; exact hq, ?_⟩
  have hnum : a + b * ((w - a) / (b - w)) = w * ((b - a) / (b - w)) := by
    rw [← mul_div_assoc, ← mul_div_assoc, eq_div_iff hbw, add_mul,
      div_mul_cancel₀ _ hbw]
    ring
  rw [h1t, hnum, mul_div_cancel_right₀ w hq]

/-- **Root-multiplicity correspondence.** Over a field, for `a ≠ b` and a target
`w ≠ b`, the multiplicity of `(w-a)/(b-w)` in the transform equals the
multiplicity of `w` in `P`. -/
theorem rootMultiplicity_mobiusPoly {K : Type*} [Field K] {n : ℕ} {a b w : K}
    (hab : a ≠ b) (hwb : w ≠ b) {P : Polynomial K} (hP : P ≠ 0)
    (hdeg : P.natDegree ≤ n) :
    (mobiusPoly n a b P).rootMultiplicity ((w - a) / (b - w))
      = P.rootMultiplicity w := by
  set m := P.rootMultiplicity w with hm
  set t := (w - a) / (b - w) with ht
  obtain ⟨Q, hPQ, hndvd⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP w
  have hQw : Q.eval w ≠ 0 := fun h => hndvd (dvd_iff_isRoot.mpr h)
  have hQ0 : Q ≠ 0 := fun h => hP (by rw [hPQ, h, mul_zero])
  have hdegX : ((X - C w : Polynomial K) ^ m).natDegree = m := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  have hmn : m ≤ n := by
    have h := natDegree_le_of_dvd (P.pow_rootMultiplicity_dvd w) hP
    rw [hdegX] at h
    omega
  have hdegQ : Q.natDegree ≤ n - m := by
    have := congrArg natDegree hPQ
    rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero w)) hQ0, hdegX] at this
    omega
  -- The transform of the pure `(X - C w)^m` factor.
  have hpow : mobiusPoly m a b ((X - C w) ^ m)
      = (C (b - w)) ^ m * (X - C t) ^ m := by
    have h := mobiusPoly_pow a b (Q := X - C w) (k := 1)
      (le_of_eq (natDegree_X_sub_C w)) m
    rw [Nat.mul_one] at h
    rw [h, mobiusPoly_X_sub_C a b w hwb, mul_pow]
  -- Split the transform along the factorization.
  have hsplit : mobiusPoly n a b P
      = (C (b - w)) ^ m * (X - C t) ^ m * mobiusPoly (n - m) a b Q := by
    have hn : n = m + (n - m) := by omega
    conv_lhs => rw [hn, hPQ]
    rw [mobiusPoly_mul a b (le_of_eq hdegX) hdegQ, hpow]
  -- The residual factor does not vanish at `t`.
  obtain ⟨h1t, hinv⟩ := mobius_inverse hab hwb
  have hQt : ¬ (mobiusPoly (n - m) a b Q).IsRoot t := by
    rw [IsRoot, mobiusPoly_eval a b hdegQ h1t, hinv]
    exact mul_ne_zero (pow_ne_zero _ h1t) hQw
  have hQm0 : mobiusPoly (n - m) a b Q ≠ 0 := mobiusPoly_ne_zero_of_ne hab hQ0
  have hbw : (b - w : K) ≠ 0 := sub_ne_zero.mpr (Ne.symm hwb)
  have hCm0 : ((C (b - w) : Polynomial K)) ^ m ≠ 0 := pow_ne_zero _ (C_ne_zero.mpr hbw)
  have hXm0 : ((X - C t : Polynomial K)) ^ m ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero t)
  rw [hsplit, rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hCm0 hXm0) hQm0),
    rootMultiplicity_mul (mul_ne_zero hCm0 hXm0), rootMultiplicity_eq_zero hQt,
    ← C_pow, rootMultiplicity_C, rootMultiplicity_X_sub_C_pow]
  omega

/-- **Positive-root correspondence over `ℝ`.** For `a < b` and `natDegree P ≤ n`,
the positive roots of the transform are exactly the images of the roots of `P`
in the open interval `(a, b)` under `w ↦ (w-a)/(b-w)`. -/
theorem pos_root_mobiusPoly_iff {n : ℕ} {a b : ℝ} (hab : a < b) {P : Polynomial ℝ}
    (hdeg : P.natDegree ≤ n) {t : ℝ} :
    (0 < t ∧ (mobiusPoly n a b P).IsRoot t)
      ↔ ∃ w ∈ Set.Ioo a b, P.IsRoot w ∧ t = (w - a) / (b - w) := by
  constructor
  · rintro ⟨ht, hroot⟩
    have h1t : (1 : ℝ) + t ≠ 0 := by linarith
    set w := (a + b * t) / (1 + t) with hw
    have hwa : a < w := by
      rw [hw, lt_div_iff₀ (by linarith)]
      nlinarith
    have hwb : w < b := by
      rw [hw, div_lt_iff₀ (by linarith)]
      nlinarith
    refine ⟨w, ⟨hwa, hwb⟩, ?_, ?_⟩
    · have := hroot
      rw [IsRoot, mobiusPoly_eval a b hdeg h1t] at this
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ h1t)
    · rw [hw]
      have hq : (b - a) / (1 + t) ≠ 0 :=
        div_ne_zero (ne_of_gt (by linarith : (0:ℝ) < b - a)) h1t
      have hbw : b - (a + b * t) / (1 + t) = (b - a) / (1 + t) := by
        rw [eq_div_iff h1t, sub_mul, div_mul_cancel₀ _ h1t]
        ring
      have haw : (a + b * t) / (1 + t) - a = t * ((b - a) / (1 + t)) := by
        rw [← mul_div_assoc, eq_div_iff h1t, sub_mul, div_mul_cancel₀ _ h1t]
        ring
      rw [haw, hbw, mul_div_cancel_right₀ t hq]
  · rintro ⟨w, ⟨hwa, hwb⟩, hroot, rfl⟩
    have hbw : (0 : ℝ) < b - w := by linarith
    have ht : 0 < (w - a) / (b - w) := div_pos (by linarith) hbw
    obtain ⟨h1t, hinv⟩ := mobius_inverse (ne_of_lt hab) (ne_of_lt hwb)
    refine ⟨ht, ?_⟩
    rw [IsRoot, mobiusPoly_eval a b hdeg h1t, hinv, hroot, mul_zero]

/-- Root-count reduction: `countP` of a root multiset as a `Finset` sum of
multiplicities. -/
private theorem countP_roots_eq_sum (f : Polynomial ℝ) (p : ℝ → Prop)
    [DecidablePred p] :
    f.roots.countP (fun x => p x) = ∑ x ∈ f.roots.toFinset.filter p, f.roots.count x := by
  classical
  rw [Multiset.countP_eq_card_filter,
    ← Multiset.toFinset_sum_count_eq (f.roots.filter p)]
  refine Finset.sum_congr ?_ (fun x hx => ?_)
  · ext x
    simp [Multiset.mem_toFinset, and_comm]
  · rw [Finset.mem_filter, Multiset.mem_toFinset] at hx
    rw [Multiset.count_filter, if_pos hx.2]

/-- **Windowed root-count correspondence over `ℝ`.** For `a < b`, `P ≠ 0`, and
`natDegree P ≤ n`, the number of positive roots of the transform (with
multiplicity) equals the number of roots of `P` in the open interval `(a, b)`. -/
theorem countP_roots_mobiusPoly {n : ℕ} {a b : ℝ} (hab : a < b) {P : Polynomial ℝ}
    (hP : P ≠ 0) (hdeg : P.natDegree ≤ n) :
    (mobiusPoly n a b P).roots.countP (fun t => 0 < t)
      = P.roots.countP (fun w => a < w ∧ w < b) := by
  classical
  have hF0 : mobiusPoly n a b P ≠ 0 := mobiusPoly_ne_zero_of_ne (ne_of_lt hab) hP
  rw [countP_roots_eq_sum, countP_roots_eq_sum]
  refine Finset.sum_nbij' (i := fun t => (a + b * t) / (1 + t))
    (j := fun w => (w - a) / (b - w)) ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro t ht
    rw [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hF0] at ht
    obtain ⟨w, hwIoo, hwroot, hteq⟩ := (pos_root_mobiusPoly_iff hab hdeg).mp ⟨ht.2, ht.1⟩
    have hw : (a + b * t) / (1 + t) = w := by
      rw [hteq]
      exact (mobius_inverse (ne_of_lt hab) (ne_of_lt hwIoo.2)).2
    rw [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hP, hw]
    exact ⟨hwroot, hwIoo.1, hwIoo.2⟩
  · -- backward membership
    intro w hw
    rw [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hP] at hw
    have := (pos_root_mobiusPoly_iff hab hdeg).mpr
      ⟨w, ⟨hw.2.1, hw.2.2⟩, hw.1, rfl⟩
    rw [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hF0]
    exact ⟨this.2, this.1⟩
  · -- left inverse
    intro t ht
    rw [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hF0] at ht
    obtain ⟨w, hwIoo, _, hteq⟩ := (pos_root_mobiusPoly_iff hab hdeg).mp ⟨ht.2, ht.1⟩
    have hw : (a + b * t) / (1 + t) = w := by
      rw [hteq]
      exact (mobius_inverse (ne_of_lt hab) (ne_of_lt hwIoo.2)).2
    rw [hw, ← hteq]
  · -- right inverse
    intro w hw
    rw [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hP] at hw
    exact (mobius_inverse (ne_of_lt hab) (ne_of_lt hw.2.2)).2
  · -- multiplicities agree
    intro t ht
    rw [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hF0] at ht
    obtain ⟨w, hwIoo, _, hteq⟩ := (pos_root_mobiusPoly_iff hab hdeg).mp ⟨ht.2, ht.1⟩
    have hw : (a + b * t) / (1 + t) = w := by
      rw [hteq]
      exact (mobius_inverse (ne_of_lt hab) (ne_of_lt hwIoo.2)).2
    rw [count_roots, count_roots, hw, hteq]
    exact rootMultiplicity_mobiusPoly (ne_of_lt hab) (ne_of_lt hwIoo.2) hP hdeg

/-- **Complex root image, no `b`-root case.** Over `ℂ`, for `a ≠ b` and
`Q.eval b ≠ 0`, the roots of the transform at the exact degree are precisely the
images of the roots of `Q` under `w ↦ (w-a)/(b-w)`. Induction peeling one linear
factor at a time (every complex polynomial of positive degree has a root). -/
private theorem roots_mobiusPoly_of_eval_ne {a b : ℂ} (hab : a ≠ b) :
    ∀ (d : ℕ) (Q : Polynomial ℂ), Q.natDegree = d → Q ≠ 0 → Q.eval b ≠ 0 →
      (mobiusPoly d a b Q).roots = Q.roots.map (fun w => (w - a) / (b - w))
  | 0, Q, hd, hQ0, _ => by
      obtain ⟨c, rfl⟩ := (natDegree_eq_zero).mp hd
      rw [mobiusPoly_C, roots_C, Multiset.map_zero]
  | d + 1, Q, hd, hQ0, hQb => by
      obtain ⟨w, hw⟩ := Complex.exists_root (f := Q)
        (by rw [degree_eq_natDegree hQ0, hd]; exact_mod_cast Nat.succ_pos d)
      obtain ⟨Q', rfl⟩ := (dvd_iff_isRoot.mpr hw)
      have hQ'0 : Q' ≠ 0 := fun h => hQ0 (by rw [h, mul_zero])
      have hwb : w ≠ b := by
        rintro rfl
        rw [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] at hQb
        exact hQb rfl
      have hQ'b : Q'.eval b ≠ 0 := by
        rw [eval_mul] at hQb
        exact right_ne_zero_of_mul hQb
      have hd' : Q'.natDegree = d := by
        rw [natDegree_mul (X_sub_C_ne_zero w) hQ'0, natDegree_X_sub_C] at hd
        omega
      have hstep : mobiusPoly (d + 1) a b ((X - C w) * Q')
          = mobiusPoly 1 a b (X - C w) * mobiusPoly d a b Q' := by
        rw [show d + 1 = 1 + d from Nat.add_comm d 1]
        exact mobiusPoly_mul a b (le_of_eq (natDegree_X_sub_C w)) (le_of_eq hd')
      have hbw : (b - w : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hwb)
      rw [hstep, mobiusPoly_X_sub_C a b w hwb,
        roots_mul (mul_ne_zero
          (mul_ne_zero (C_ne_zero.mpr hbw) (X_sub_C_ne_zero _))
          (mobiusPoly_ne_zero_of_ne hab hQ'0)),
        roots_C_mul _ hbw, roots_X_sub_C,
        roots_mul (mul_ne_zero (X_sub_C_ne_zero w) hQ'0), roots_X_sub_C,
        Multiset.map_add, Multiset.map_singleton,
        roots_mobiusPoly_of_eval_ne hab d Q' hd' hQ'0 hQ'b]

/-- **Complex root image.** Over `ℂ`, for `a ≠ b` and `P ≠ 0`, the roots of the
Möbius transform at the exact degree `n = natDegree P` are the images of the
roots of `P` *other than `b`* under `w ↦ (w-a)/(b-w)`: the `b`-roots escape to
infinity via the degree drop in the homogenization. -/
theorem roots_mobiusPoly {a b : ℂ} (hab : a ≠ b) {P : Polynomial ℂ} (hP : P ≠ 0) :
    (mobiusPoly P.natDegree a b P).roots
      = (P.roots.filter (· ≠ b)).map (fun w => (w - a) / (b - w)) := by
  classical
  set m := P.rootMultiplicity b with hm
  obtain ⟨Q, hPQ, hndvd⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP b
  have hQb : Q.eval b ≠ 0 := fun h => hndvd (dvd_iff_isRoot.mpr h)
  have hQ0 : Q ≠ 0 := fun h => hP (by rw [hPQ, h, mul_zero])
  have hdegX : ((X - C b : Polynomial ℂ) ^ m).natDegree = m := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  have hdegP : P.natDegree = m + Q.natDegree := by
    rw [hPQ, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero b)) hQ0, hdegX]
  have hpow : mobiusPoly m a b ((X - C b) ^ m) = (C (a - b)) ^ m := by
    have h := mobiusPoly_pow a b (Q := X - C b) (k := 1)
      (le_of_eq (natDegree_X_sub_C b)) m
    rw [Nat.mul_one] at h
    rw [h, mobiusPoly_X_sub_C_upper]
  have hsplit : mobiusPoly P.natDegree a b P
      = (C (a - b)) ^ m * mobiusPoly Q.natDegree a b Q := by
    conv_lhs => rw [hdegP, hPQ]
    rw [mobiusPoly_mul a b (le_of_eq hdegX) (le_refl _), hpow]
  have hCab : ((a - b : ℂ)) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hab)
  have hfilter : P.roots.filter (· ≠ b) = Q.roots := by
    rw [hPQ, roots_mul (by rw [← hPQ]; exact hP), roots_pow, roots_X_sub_C,
      Multiset.filter_add]
    have h1 : (m • ({b} : Multiset ℂ)).filter (· ≠ b) = 0 := by
      rw [Multiset.nsmul_singleton, Multiset.filter_eq_nil]
      intro x hx
      rw [Multiset.eq_of_mem_replicate hx]
      simp
    have h2 : Q.roots.filter (· ≠ b) = Q.roots := by
      rw [Multiset.filter_eq_self]
      intro x hx
      rintro rfl
      exact hQb ((mem_roots hQ0).mp hx)
    rw [h1, h2, Multiset.zero_add]
  rw [hsplit, ← C_pow, roots_C_mul _ hCab, hfilter,
    roots_mobiusPoly_of_eval_ne hab Q.natDegree Q rfl hQ0 hQb]

/-! ### The Descartes variation-count bridge

`Hex.descartesVar` counts sign variations of the *ascending* coefficient list via
`Hex.signVar` (adjacent opposite-sign pairs), while `Polynomial.signVariations`
counts them on the *descending* `coeffList` via a `destutter`. We bridge the two
by (i) reversal invariance of the adjacent count and (ii) an
adjacent-count↔`destutter`-length identity on a zero-free list. -/

/-- Appending a single entry adds one variation exactly when it is opposite in
sign to the previous entry. -/
private theorem countSignChanges_concat : ∀ (l : List ℝ) (x : ℝ),
    Sturm.countSignChanges (l ++ [x]) =
      Sturm.countSignChanges l + (l.getLast?).elim 0 (fun y => if y * x < 0 then 1 else 0)
  | [], x => by simp [Sturm.countSignChanges]
  | [a], x => by simp [Sturm.countSignChanges]
  | a :: b :: t, x => by
      rw [List.cons_append, List.cons_append, Sturm.countSignChanges_cons_cons,
        ← List.cons_append, countSignChanges_concat (b :: t) x,
        Sturm.countSignChanges_cons_cons, List.getLast?_cons_cons]
      ring

/-- The adjacent-opposite-sign count is invariant under reversal. -/
private theorem countSignChanges_reverse : ∀ l : List ℝ,
    Sturm.countSignChanges l.reverse = Sturm.countSignChanges l
  | [] => rfl
  | a :: t => by
      rw [List.reverse_cons, countSignChanges_concat, countSignChanges_reverse t]
      cases t with
      | nil => simp [Sturm.countSignChanges]
      | cons b t' =>
          rw [Sturm.countSignChanges_cons_cons, List.getLast?_reverse, List.head?_cons,
            Option.elim_some, mul_comm b a]
          ring

/-- `Sturm.signVariations` is invariant under reversal (reading the coefficient
list forwards or backwards gives the same count). -/
theorem signVariations_reverse (l : List ℝ) :
    Sturm.signVariations l.reverse = Sturm.signVariations l := by
  unfold Sturm.signVariations
  rw [List.filter_reverse, countSignChanges_reverse]

/-- For nonzero reals, `a * b < 0` iff the two entries have different signs. -/
private theorem mul_neg_iff_sign_ne {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b < 0) ↔ (SignType.sign a ≠ SignType.sign b) := by
  have hsa : SignType.sign a ≠ 0 := fun h => ha (sign_eq_zero_iff.mp h)
  have hsb : SignType.sign b ≠ 0 := fun h => hb (sign_eq_zero_iff.mp h)
  rw [← sign_eq_neg_one_iff, sign_mul]
  cases ha' : SignType.sign a <;> cases hb' : SignType.sign b <;> simp_all

/-- **Adjacent-count ↔ `destutter'` length.** On a zero-free real tail `m` with
a nonzero lead `a`, the adjacent-opposite-sign count of `a :: m` equals the
length of the accumulator-form `destutter'` (seeded with `sign a`) minus one. -/
private theorem countSignChanges_destutter' : ∀ (m : List ℝ) (a : ℝ), a ≠ 0 →
    (∀ x ∈ m, x ≠ 0) →
    Sturm.countSignChanges (a :: m)
      = ((m.map SignType.sign).destutter' (· ≠ ·) (SignType.sign a)).length - 1
  | [], a, _, _ => by simp [Sturm.countSignChanges, List.destutter'_nil]
  | b :: t, a, ha, hm => by
      have hb : b ≠ 0 := hm b (by simp)
      have ht : ∀ x ∈ t, x ≠ 0 := fun x hx => hm x (List.mem_cons_of_mem _ hx)
      have hIH := countSignChanges_destutter' t b hb ht
      rw [Sturm.countSignChanges_cons_cons, List.map_cons]
      by_cases hsab : SignType.sign a ≠ SignType.sign b
      · rw [List.destutter'_cons_pos _ hsab, List.length_cons,
          if_pos ((mul_neg_iff_sign_ne ha hb).mpr hsab), hIH, Nat.add_sub_cancel]
        exact Nat.add_sub_cancel'
          (List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _))
      · rw [List.destutter'_cons_neg _ hsab,
          if_neg (fun h => hsab ((mul_neg_iff_sign_ne ha hb).mp h)), Nat.zero_add,
          not_not.mp hsab]
        exact hIH

/-- **Adjacent-count ↔ destutter length.** On a zero-free real list, the number
of adjacent opposite-sign pairs equals the length of the sign-`destutter` minus
one: `Sturm.countSignChanges` matches Mathlib's `destutter`-based count. -/
private theorem countSignChanges_eq_destutter (m : List ℝ) (hm : ∀ x ∈ m, x ≠ 0) :
    Sturm.countSignChanges m = ((m.map SignType.sign).destutter (· ≠ ·)).length - 1 := by
  cases m with
  | nil => simp [Sturm.countSignChanges]
  | cons a t =>
      have ha : a ≠ 0 := hm a (by simp)
      have ht : ∀ x ∈ t, x ≠ 0 := fun x hx => hm x (List.mem_cons_of_mem _ hx)
      rw [List.map_cons, List.destutter_cons', countSignChanges_destutter' t a ha ht]

/-- **Descending-list variation bridge.** For any real polynomial, the abstract
`Sturm.signVariations` of the ascending coefficient list equals Mathlib's
`Polynomial.signVariations` (which reads the descending `coeffList`). -/
theorem sturm_signVariations_range_eq (P : Polynomial ℝ) :
    Sturm.signVariations ((List.range (P.natDegree + 1)).map P.coeff)
      = Polynomial.signVariations P := by
  by_cases hP : P = 0
  · subst hP
    simp [Sturm.signVariations]
  have hasc_rev : ((List.range (P.natDegree + 1)).map P.coeff).reverse = P.coeffList := by
    rw [Polynomial.coeffList, Polynomial.withBotSucc_degree_eq_natDegree_add_one hP,
      List.map_reverse]
  rw [← signVariations_reverse ((List.range (P.natDegree + 1)).map P.coeff), hasc_rev]
  -- Now: Sturm.signVariations (coeffList P) = Polynomial.signVariations P.
  have hp : ((fun s : SignType => decide (s ≠ 0)) ∘ SignType.sign)
      = (fun v : ℝ => decide (v ≠ 0)) := by
    funext v
    by_cases h : v = 0 <;> simp [Function.comp_apply, h, sign_eq_zero_iff]
  have hfilters : (P.coeffList.filter (fun v : ℝ => decide (v ≠ 0))).map SignType.sign
      = (P.coeffList.map SignType.sign).filter (fun s : SignType => decide (s ≠ 0)) := by
    rw [List.filter_map, hp]
  simp only [Sturm.signVariations, Polynomial.signVariations]
  rw [countSignChanges_eq_destutter _ (fun x hx => by simpa using (List.mem_filter.mp hx).2),
    hfilters]

/-- Casting an integer's sign to `ℝ` preserves `SignType.sign`. -/
private theorem sign_intCast_sign' (n : Int) :
    SignType.sign ((n.sign : ℝ)) = SignType.sign ((n : ℝ)) := by
  rcases lt_trichotomy n 0 with h | h | h
  · rw [Int.sign_eq_neg_one_of_neg h]
    have h2 : (n : ℝ) < 0 := by exact_mod_cast h
    rw [show ((-1 : Int) : ℝ) = -1 by norm_num, sign_neg (by norm_num), sign_neg h2]
  · subst h; simp
  · rw [Int.sign_eq_one_of_pos h]
    have h2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
    rw [show ((1 : Int) : ℝ) = 1 by norm_num, sign_pos (by norm_num), sign_pos h2]

/-- The stored coefficient list is the range map of the coefficient function. -/
private theorem toArray_toList_eq_range_map (q : Hex.ZPoly) :
    q.toArray.toList = (List.range q.size).map q.coeff := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, Array.length_toList, Hex.DensePoly.toArray_size]
  · intro i h1 _
    have hi : i < q.toArray.size := by
      rw [Array.length_toList] at h1; exact h1
    rw [Array.getElem_toList, List.getElem_map, List.getElem_range,
      ← Hex.DensePoly.toArray_getD q i, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hi, Option.getD_some]

/-- **Descartes variation bridge.** The executable `Hex.descartesVar q` equals
Mathlib's `Polynomial.signVariations (toPolyℝ q)`. The executable count is on the
ascending sign list; the abstract count on the descending `coeffList`; the two
agree by reversal invariance and the `destutter` identity above. -/
theorem descartesVar_eq_signVariations (q : Hex.ZPoly) :
    Hex.descartesVar q = Polynomial.signVariations (toPolyℝ q) := by
  by_cases hq : q = 0
  · subst hq
    rw [toPolyℝ_zero, Polynomial.signVariations_zero]
    rfl
  have hpos : 0 < q.size := by
    rcases Nat.eq_zero_or_pos q.size with h | h
    · refine absurd (Hex.DensePoly.ext_coeff (fun n => ?_)) hq
      rw [Hex.DensePoly.coeff_zero]
      exact Hex.DensePoly.coeff_eq_zero_of_size_le q (by omega)
    · exact h
  have hlist : q.toArray.toList.map (Int.cast : ℤ → ℝ)
      = (List.range ((toPolyℝ q).natDegree + 1)).map (toPolyℝ q).coeff := by
    have hsize : q.size = (toPolyℝ q).natDegree + 1 := by
      rw [natDegree_toPolyℝ, Hex.DensePoly.degree?_eq_some_of_pos_size q hpos, Option.getD_some]
      omega
    rw [toArray_toList_eq_range_map q, List.map_map, hsize]
    apply List.map_congr_left
    intro i _
    simp
  show Hex.signVar (q.toArray.toList.map Int.sign) = _
  rw [signVar_eq,
    show Sturm.signVariations ((q.toArray.toList.map Int.sign).map (Int.cast : ℤ → ℝ))
        = Sturm.signVariations (q.toArray.toList.map (Int.cast : ℤ → ℝ)) from ?_,
    hlist]
  · exact sturm_signVariations_range_eq (toPolyℝ q)
  · apply Sturm.signVariations_congr
    rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff,
      List.forall₂_same]
    intro x _
    exact sign_intCast_sign' x

/-! ### The executable bridge: `Hex.mobiusTransform` is `mobiusPoly` up to `2^{s·n}`

The executable pipeline works over `ℤ` after clearing the dyadic endpoint
denominators by `2^s`. The private `Hex.mobiusEndpoints`/`Hex.dyadicNumExp`
cannot be named cross-module, so `numExp`/`endpoints`/`mobiusSteps` below are
public verbatim mirrors, identified with the executable transform by `rfl`
after case-splitting the endpoint constructors. -/

/-- Public mirror of the private `Hex.dyadicNumExp`: the
`(numerator, denominator-exponent)` pair of a dyadic value. -/
def numExp : Dyadic → Int × Int
  | .zero => (0, 0)
  | .ofOdd n k _ => (n, k)

/-- Public mirror of the private `Hex.mobiusEndpoints`: the integer endpoint
numerators over the common power-of-two denominator `2^s`. -/
def endpoints (I : Hex.DyadicInterval) : Int × Int × Nat :=
  let na := (numExp I.lower).1
  let ka := (numExp I.lower).2
  let nb := (numExp I.upper).1
  let kb := (numExp I.upper).2
  let sInt := max 0 (max ka kb)
  (na * (2 : Int) ^ (sInt - ka).toNat, nb * (2 : Int) ^ (sInt - kb).toNat, sInt.toNat)

/-- Public mirror of the `Hex.mobiusTransform` pipeline past the endpoint
computation, parameterized by the integer data `(α, β, s)`. -/
noncomputable def mobiusSteps (p : Hex.ZPoly) (α β : Int) (s : Nat) : Hex.ZPoly :=
  if p.size ≤ 1 then p else
  let n := p.size - 1
  let cleared := Hex.DensePoly.ofCoeffs
    ((List.range p.size).map (fun i => p.coeff i * (2 : Int) ^ (s * (n - i)))).toArray
  let shifted := Hex.DensePoly.compose cleared (Hex.DensePoly.ofCoeffs #[β, (1 : Int)])
  let scaled := Hex.ZPoly.dilate (α - β) shifted
  let reversed := Hex.DensePoly.ofCoeffs
    ((List.range (n + 1)).map (fun i => scaled.coeff (n - i))).toArray
  Hex.DensePoly.compose reversed (Hex.DensePoly.ofCoeffs #[(1 : Int), 1])

/-- The executable transform is the mirrored pipeline at the mirrored endpoint
data: both sides reduce to the same term once the endpoint constructors are
split. -/
theorem mobiusTransform_eq_steps (p : Hex.ZPoly) (I : Hex.DyadicInterval) :
    Hex.mobiusTransform p I
      = mobiusSteps p (endpoints I).1 (endpoints I).2.1 (endpoints I).2.2 := by
  obtain ⟨lo, hi, hlt⟩ := I
  cases lo <;> cases hi <;> rfl

/-- The real value of a dyadic in terms of its `numExp` data, at any common
exponent `s` dominating its own: `toReal d = (numerator · 2^{s-k}) · 2^{-s}`. -/
private theorem toReal_numExp (d : Dyadic) {s : Int} (hks : (numExp d).2 ≤ s) :
    Dyadic.toReal d
      = ((numExp d).1 * (2 : Int) ^ ((s - (numExp d).2).toNat) : ℤ) * (2 : ℝ) ^ (-s) := by
  cases d with
  | zero =>
      show Dyadic.toReal .zero = (((0 : ℤ) * _ : ℤ) : ℝ) * _
      rw [show Dyadic.zero = (0 : Dyadic) from rfl, toReal_zero]
      push_cast
      ring
  | ofOdd n k hn =>
      show Dyadic.toReal (.ofOdd n k hn) = ((n * (2 : Int) ^ ((s - k).toNat) : ℤ) : ℝ) * _
      have hks' : k ≤ s := hks
      have htr : Dyadic.toReal (Dyadic.ofOdd n k hn) = (n : ℝ) * 2 ^ (-k) := by
        unfold Dyadic.toReal
        rw [Dyadic.toRat_ofOdd_eq_mul_two_pow]
        push_cast
        ring
      rw [htr]
      push_cast
      rw [← zpow_natCast (2:ℝ) ((s - k).toNat), Int.toNat_of_nonneg (by omega), mul_assoc,
        ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
      congr 2
      omega

/-- The `endpoints` data recovers the real endpoint values:
`toReal I.lower = α·2^{-s}` and `toReal I.upper = β·2^{-s}`. -/
private theorem endpoints_spec (I : Hex.DyadicInterval) :
    Dyadic.toReal I.lower
        = ((endpoints I).1 : ℝ) * (2 : ℝ) ^ (-((endpoints I).2.2 : ℤ))
      ∧ Dyadic.toReal I.upper
        = ((endpoints I).2.1 : ℝ) * (2 : ℝ) ^ (-((endpoints I).2.2 : ℤ)) := by
  set ka := (numExp I.lower).2 with hka
  set kb := (numExp I.upper).2 with hkb
  set sInt := max 0 (max ka kb) with hs
  have hs0 : 0 ≤ sInt := le_max_left _ _
  have hsa : ka ≤ sInt := le_trans (le_max_left _ _) (le_max_right _ _)
  have hsb : kb ≤ sInt := le_trans (le_max_right _ _) (le_max_right _ _)
  have h1 : (endpoints I).1 = (numExp I.lower).1 * (2 : Int) ^ ((sInt - ka).toNat) := rfl
  have h2 : (endpoints I).2.1 = (numExp I.upper).1 * (2 : Int) ^ ((sInt - kb).toNat) := rfl
  have h3 : ((endpoints I).2.2 : ℤ) = sInt := by
    show ((sInt.toNat : ℕ) : ℤ) = sInt
    exact Int.toNat_of_nonneg hs0
  constructor
  · rw [h1, h3]
    exact_mod_cast toReal_numExp I.lower hsa
  · rw [h2, h3]
    exact_mod_cast toReal_numExp I.upper hsb

/-- The real cast intertwines the executable Horner composition with
`Polynomial.comp`. -/
theorem toPolyℝ_compose (p q : Hex.ZPoly) :
    toPolyℝ (Hex.DensePoly.compose p q) = (toPolyℝ p).comp (toPolyℝ q) := by
  show (HexPolyMathlib.toPolynomial (Hex.DensePoly.compose p q)).map (Int.castRingHom ℝ) = _
  rw [HexPolyMathlib.toPolynomial_compose, Polynomial.map_comp]

/-- The real cast turns the executable dilation into composition with
`C c * X`. -/
theorem toPolyℝ_dilate (c : Int) (q : Hex.ZPoly) :
    toPolyℝ (Hex.ZPoly.dilate c q) = (toPolyℝ q).comp (C (c : ℝ) * X) := by
  ext j
  rw [coeff_toPolyℝ, Hex.ZPoly.coeff_dilate, comp_C_mul_X_coeff, coeff_toPolyℝ]
  push_cast
  ring

/-- The real cast of the executable monic linear polynomial `#[u, 1]`. -/
private theorem toPolyℝ_linear (u : Int) :
    toPolyℝ (Hex.DensePoly.ofCoeffs #[u, (1 : Int)]) = X + C (u : ℝ) := by
  ext j
  rw [coeff_toPolyℝ, Hex.DensePoly.coeff_ofCoeffs, coeff_add, coeff_X, coeff_C]
  match j with
  | 0 => simp [Array.getD]
  | 1 => simp [Array.getD]
  | (k + 2) =>
      rw [if_neg (by omega), if_neg (by omega), add_zero,
        Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp), Option.getD_none]
      exact Int.cast_zero

/-- The clearing step: coefficient scaling `aᵢ ↦ aᵢ·2^{s·(n-i)}` is
`2^{s·n} · p(x·2^{-s})` over `ℝ`. -/
private theorem toPolyℝ_cleared (p : Hex.ZPoly) (s : Nat) :
    toPolyℝ (Hex.DensePoly.ofCoeffs
        ((List.range p.size).map
          (fun i => p.coeff i * (2 : Int) ^ (s * (p.size - 1 - i)))).toArray)
      = C ((2 : ℝ) ^ (s * (p.size - 1)))
        * (toPolyℝ p).comp (C ((2 : ℝ) ^ (-(s : ℤ))) * X) := by
  ext j
  rw [coeff_toPolyℝ, Hex.DensePoly.coeff_ofCoeffs_list,
    HexPolyMathlib.list_getD_map_range_zero, coeff_C_mul, comp_C_mul_X_coeff, coeff_toPolyℝ]
  by_cases hj : j < p.size
  · rw [if_pos hj]
    have hkey : ((2:ℝ) ^ (-(s:ℤ))) ^ j = ((2:ℝ) ^ (s * j))⁻¹ := by
      rw [zpow_neg, zpow_natCast, inv_pow, ← pow_mul]
    have hsplit : s * (p.size - 1) = s * (p.size - 1 - j) + s * j := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
    rw [hkey, hsplit, pow_add]
    push_cast
    have h2 : ((2:ℝ) ^ (s * j)) ≠ 0 := by positivity
    field_simp
  · rw [if_neg hj, Hex.DensePoly.coeff_eq_zero_of_size_le p (by omega),
      show (Zero.zero : ℤ) = 0 from rfl, Int.cast_zero]
    ring

/-- The reversal step: rebuilding the coefficient array reversed at index `n`
is `Polynomial.reflect n` over `ℝ`, provided the degree stayed within the
window. -/
private theorem toPolyℝ_reversed (q : Hex.ZPoly) (n : Nat)
    (hq : (toPolyℝ q).natDegree ≤ n) :
    toPolyℝ (Hex.DensePoly.ofCoeffs
        ((List.range (n + 1)).map (fun i => q.coeff (n - i))).toArray)
      = Polynomial.reflect n (toPolyℝ q) := by
  ext j
  rw [coeff_toPolyℝ, Hex.DensePoly.coeff_ofCoeffs_list,
    HexPolyMathlib.list_getD_map_range_zero, coeff_reflect]
  by_cases hj : j < n + 1
  · rw [if_pos hj, revAt_le (by omega), coeff_toPolyℝ]
  · rw [if_neg hj, revAt_eq_self_of_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact Int.cast_zero

/-- The composed inner form of `mobiusInner`: substitution of the affine map
`(a-b)·x + b` in one step. -/
private theorem mobiusInner_eq_comp {K : Type*} [CommRing K] (a b : K)
    (P : Polynomial K) :
    mobiusInner a b P = P.comp (C (a - b) * X + C b) := by
  unfold mobiusInner
  rw [comp_assoc, add_comp, X_comp, C_comp]

/-- Stage algebra: composing the cleared form `C k * P(c·x)` with the shift
`x + β'` and then the dilation `(α'-β')·x` is `C k` times the inner Möbius
polynomial at `(α'·c, β'·c)`. -/
private theorem inner_stages {K : Type*} [CommRing K] (P : Polynomial K)
    (k c β' α' : K) :
    ((C k * P.comp (C c * X)).comp (X + C β')).comp (C (α' - β') * X)
      = C k * mobiusInner (α' * c) (β' * c) P := by
  rw [mobiusInner_eq_comp]
  simp only [mul_comp, add_comp, C_comp, X_comp, comp_assoc]
  congr 2
  rw [mul_add, ← mul_assoc, ← C_mul, ← C_mul, mul_comm c (α' - β'), sub_mul, mul_comm c β']

/-- The scaled stage of the pipeline in abstract form. -/
private theorem toPolyℝ_scaled_stage (p : Hex.ZPoly) (α β : Int) (s : Nat) :
    toPolyℝ (Hex.ZPoly.dilate (α - β)
        (Hex.DensePoly.compose
          (Hex.DensePoly.ofCoeffs
            ((List.range p.size).map
              (fun i => p.coeff i * (2 : Int) ^ (s * (p.size - 1 - i)))).toArray)
          (Hex.DensePoly.ofCoeffs #[β, (1 : Int)])))
      = C ((2 : ℝ) ^ (s * (p.size - 1)))
        * mobiusInner ((α : ℝ) * (2 : ℝ) ^ (-(s : ℤ))) ((β : ℝ) * (2 : ℝ) ^ (-(s : ℤ)))
            (toPolyℝ p) := by
  rw [toPolyℝ_dilate, toPolyℝ_compose, toPolyℝ_linear, toPolyℝ_cleared,
    show (((α - β : ℤ) : ℝ)) = (α : ℝ) - (β : ℝ) from by push_cast; ring]
  exact inner_stages (toPolyℝ p) _ _ _ _

/-- **The pipeline correspondence.** For `2 ≤ p.size`, the mirrored pipeline is
`C (2^{s·n}) · mobiusPoly n (α·2^{-s}) (β·2^{-s})` of the real cast, with
`n = p.size - 1`. -/
private theorem toPolyℝ_mobiusSteps (p : Hex.ZPoly) (α β : Int) (s : Nat)
    (hp : 2 ≤ p.size) :
    toPolyℝ (mobiusSteps p α β s)
      = C ((2 : ℝ) ^ (s * (p.size - 1)))
        * mobiusPoly (p.size - 1)
            ((α : ℝ) * (2 : ℝ) ^ (-(s : ℤ))) ((β : ℝ) * (2 : ℝ) ^ (-(s : ℤ)))
            (toPolyℝ p) := by
  have hunf : mobiusSteps p α β s
      = Hex.DensePoly.compose
          (Hex.DensePoly.ofCoeffs
            ((List.range (p.size - 1 + 1)).map (fun i =>
              (Hex.ZPoly.dilate (α - β)
                (Hex.DensePoly.compose
                  (Hex.DensePoly.ofCoeffs
                    ((List.range p.size).map
                      (fun i => p.coeff i * (2 : Int) ^ (s * (p.size - 1 - i)))).toArray)
                  (Hex.DensePoly.ofCoeffs #[β, (1 : Int)]))).coeff
                (p.size - 1 - i))).toArray)
          (Hex.DensePoly.ofCoeffs #[(1 : Int), 1]) := by
    unfold mobiusSteps
    rw [if_neg (by omega)]
  have hdeg' : (toPolyℝ (Hex.ZPoly.dilate (α - β)
      (Hex.DensePoly.compose
        (Hex.DensePoly.ofCoeffs
          ((List.range p.size).map
            (fun i => p.coeff i * (2 : Int) ^ (s * (p.size - 1 - i)))).toArray)
        (Hex.DensePoly.ofCoeffs #[β, (1 : Int)])))).natDegree ≤ p.size - 1 := by
    rw [toPolyℝ_scaled_stage]
    refine le_trans (natDegree_C_mul_le _ _)
      (le_trans (natDegree_mobiusInner_le _ _ _) ?_)
    rw [natDegree_toPolyℝ, Hex.DensePoly.degree?_eq_some_of_pos_size p (by omega),
      Option.getD_some]
  rw [hunf, toPolyℝ_compose, toPolyℝ_linear, Int.cast_one,
    toPolyℝ_reversed _ (p.size - 1) hdeg', toPolyℝ_scaled_stage, reflect_C_mul,
    mul_comp, C_comp, ← mobiusPoly_eq_reflect_comp]

/-- **The executable Möbius bridge.** For positive-degree `p`, the real cast of
`Hex.mobiusTransform p I` is `2^{s·n}` times the abstract `mobiusPoly` at the
real endpoint values, with `n` the degree of `p` and `s` the common
denominator exponent of `I`'s endpoints. -/
theorem toPolyℝ_mobiusTransform (p : Hex.ZPoly) (I : Hex.DyadicInterval)
    (hdeg : 1 ≤ (p.degree?).getD 0) :
    toPolyℝ (Hex.mobiusTransform p I)
      = C ((2 : ℝ) ^ ((endpoints I).2.2 * ((p.degree?).getD 0)))
        * mobiusPoly ((p.degree?).getD 0)
            (Dyadic.toReal I.lower) (Dyadic.toReal I.upper) (toPolyℝ p) := by
  have hsize : 2 ≤ p.size := by
    by_contra h
    have h1 : p.size ≤ 1 := by omega
    rcases Nat.eq_zero_or_pos p.size with h0 | hpos
    · rw [(Hex.DensePoly.degree?_eq_none_iff p).mpr h0] at hdeg
      simp at hdeg
    · rw [Hex.DensePoly.degree?_eq_some_of_pos_size p hpos, Option.getD_some] at hdeg
      omega
  have hn : (p.degree?).getD 0 = p.size - 1 := by
    rw [Hex.DensePoly.degree?_eq_some_of_pos_size p (by omega), Option.getD_some]
  obtain ⟨hlo, hhi⟩ := endpoints_spec I
  rw [mobiusTransform_eq_steps, toPolyℝ_mobiusSteps p _ _ _ hsize, hn, hlo, hhi]

/-- **Positivity of the clearing factor**: existential form of the bridge for
consumers that only need `toPolyℝ (mobiusTransform p I)` to be a positive
constant multiple of the abstract transform. -/
theorem toPolyℝ_mobiusTransform' (p : Hex.ZPoly) (I : Hex.DyadicInterval)
    (hdeg : 1 ≤ (p.degree?).getD 0) :
    ∃ c : ℝ, 0 < c ∧
      toPolyℝ (Hex.mobiusTransform p I)
        = C c * mobiusPoly ((p.degree?).getD 0)
            (Dyadic.toReal I.lower) (Dyadic.toReal I.upper) (toPolyℝ p) :=
  ⟨_, by positivity, toPolyℝ_mobiusTransform p I hdeg⟩

/-! ### The composed Descartes corollary -/

/-- **The Descartes count of the transform is the abstract sign-variation
count.** The `2^{s·n}` clearing factor is absorbed by
`Polynomial.signVariations_C_mul`; this is the form the engine proof cites. -/
theorem descartesVar_mobiusTransform (p : Hex.ZPoly) (I : Hex.DyadicInterval)
    (hdeg : 1 ≤ (p.degree?).getD 0) :
    Hex.descartesVar (Hex.mobiusTransform p I)
      = Polynomial.signVariations
          (mobiusPoly ((p.degree?).getD 0)
            (Dyadic.toReal I.lower) (Dyadic.toReal I.upper) (toPolyℝ p)) := by
  rw [descartesVar_eq_signVariations, toPolyℝ_mobiusTransform p I hdeg,
    Polynomial.signVariations_C_mul _ (by positivity)]

/-! Sanity checks against the executable fixtures from `HexRealRoots.Mobius`:
`mobiusTransform (x − 1)` on `(0, 2]` is `x − 1` (fixture `#[-1, 1]`), matched
here abstractly and through the bridge. -/

example : mobiusPoly 1 (0 : ℝ) 2 (X - C 1) = X - C 1 := by
  rw [mobiusPoly_X_sub_C (0 : ℝ) 2 1 (by norm_num)]
  norm_num

example :
    toPolyℝ (Hex.mobiusTransform (Hex.DensePoly.ofCoeffs #[(-1 : Int), 1])
        (Hex.DyadicInterval.mk (Dyadic.ofInt 0) (Dyadic.ofInt 2) (by decide)))
      = X - C 1 := by
  have h1 : toPolyℝ (Hex.DensePoly.ofCoeffs #[(-1 : Int), 1]) = X - C 1 := by
    rw [toPolyℝ_linear]
    norm_num [sub_eq_add_neg]
  rw [toPolyℝ_mobiusTransform _ _ (by decide),
    show ((Hex.DensePoly.ofCoeffs #[(-1 : Int), 1]).degree?).getD 0 = 1 from rfl,
    show (endpoints (Hex.DyadicInterval.mk (Dyadic.ofInt 0) (Dyadic.ofInt 2)
      (by decide))).2.2 = 0 from rfl,
    h1, toReal_ofInt, toReal_ofInt,
    show ((0 : Int) : ℝ) = 0 from by norm_num,
    show ((2 : Int) : ℝ) = 2 from by norm_num,
    mobiusPoly_X_sub_C (0 : ℝ) 2 1 (by norm_num)]
  norm_num

end

end HexRealRootsMathlib
