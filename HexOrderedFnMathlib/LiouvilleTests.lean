/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFnMathlib.Extension
public import HexOrderedFnMathlib.Infinitesimal
public import HexOrderedFn.ExtensionTests
public meta import HexOrderedFn.ExtensionTests
public meta import HexOrderedFn.Real
public meta import HexOrderedFn.Extension
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
public import Mathlib.RingTheory.Localization.Integral

@[expose] public section

namespace Hex.OrderedFn.LiouvilleTests

open Oracle Hex.OrderedFn.Real Filter Topology

local instance (priority := 2000) : Lean.Grind.Field Rat := Field.toGrindField

/-- Test-only rational partial sums for the specified Liouville constant. -/
def partialSum (n : Nat) : Rat :=
  ∑ i ∈ Finset.range (n + 1), 1 / (2 : Rat) ^ i.factorial

def bounds (n : Nat) : Bounds :=
  ⟨partialSum n, partialSum n + 2 / (2 : Rat) ^ (n + 1).factorial, by
    have : (0 : Rat) ≤ 2 / (2 : Rat) ^ (n + 1).factorial := by positivity
    linarith⟩

theorem partialSum_cast (n : Nat) :
    (partialSum n : ℝ) = LiouvilleNumber.partialSum 2 n := by
  simp [partialSum, LiouvilleNumber.partialSum]

theorem bounds_contains (n : Nat) : Contains (bounds n) (liouvilleNumber 2) := by
  have hp := LiouvilleNumber.remainder_pos (by norm_num : (1 : ℝ) < 2) n
  have hs := LiouvilleNumber.partialSum_add_remainder (by norm_num : (1 : ℝ) < 2) n
  have hu := LiouvilleNumber.remainder_lt' n (by norm_num : (1 : ℝ) < 2)
  norm_num at hu
  rw [← div_eq_mul_inv] at hu
  simp only [Contains, bounds, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_pow, partialSum_cast]
  constructor <;> linarith

theorem bounds_width (n : Nat) : (bounds n).width ≤ precision n := by
  simp only [bounds, Bounds.width, add_sub_cancel_left, precision]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h := pow_le_pow_right₀ (by norm_num : (1 : Rat) ≤ 2) (Nat.self_le_factorial (n + 1))
  simpa [pow_succ, mul_comm] using h

/-- A denominator-based dyadic precision gives a computable width adapter. -/
def provider (δ : Rat) : Bounds := bounds (δ.den.log2 + 1)

theorem provider_contains (δ : Rat) : Contains (provider δ) (liouvilleNumber 2) :=
  bounds_contains _

theorem provider_width (δ : Rat) (hδ : 0 < δ) : (provider δ).width ≤ δ := by
  apply (bounds_width _).trans
  have hd : (0 : Rat) < δ.den := by exact_mod_cast δ.den_pos
  have hn : (1 : Rat) ≤ δ.num := by
    exact_mod_cast (show (1 : Int) ≤ δ.num by have := Rat.num_pos.mpr hδ; omega)
  calc
    precision (δ.den.log2 + 1) = 1 / (2 : Rat) ^ (δ.den.log2 + 1) := rfl
    _ ≤ 1 / (δ.den : Rat) := one_div_le_one_div_of_le hd
      (by exact_mod_cast (Nat.lt_log2_self (n := δ.den)).le)
    _ ≤ (δ.num : Rat) / δ.den := div_le_div_of_nonneg_right hn hd.le
    _ = δ := Rat.num_div_den δ

theorem transcendence : RelativeTranscendence (Rat.castHom ℝ) (liouvilleNumber 2) := by
  have ht : Transcendental ℚ (liouvilleNumber 2) := by
    intro h
    exact transcendental_liouvilleNumber (by decide : 2 ≤ 2)
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr h)
  intro p hp he
  exact ht ⟨p, hp, by
    have hm : algebraMap Rat ℝ = Rat.castHom ℝ := by ext; simp
    simpa [Polynomial.aeval_def, hm] using he⟩

def source : Approximation Rat := .ofConstant provider

theorem source_correct : ApproximationCorrect (Rat.castHom ℝ) (liouvilleNumber 2) source :=
  .ofConstant provider _ (fun δ _ => provider_contains δ)

theorem source_width : ApproximationWidth source := .ofConstant provider provider_width

def registered : Registration Rat := registration source_correct source_width transcendence

abbrev E := Extension registered

def positive : E := ExtensionTests.positive registered
def negative : E := ExtensionTests.negative registered
def quotient : E := ExtensionTests.quotient registered


def p : DensePoly Rat := .ofList [-5/4, 1]
def q : DensePoly Rat := .ofList [-2, 1]

def preparedPositive : E := ⟨RationalFn.ofPoly p⟩
def preparedNegative : E := ⟨RationalFn.ofPoly q⟩

theorem positive_eq : positive = preparedPositive := by
  apply (Extension.evalHom transcendence).injective
  change Extension.evalHom transcendence (Extension.X - Extension.C (5 / 4 : Rat) : E) = _
  rw [map_sub, Extension.evalHom_X, Extension.evalHom_C]
  rw [Extension.evalHom_apply]
  norm_num [preparedPositive, Real.eval, RationalFn.ofPoly,
    HexPolyMathlib.eval₂_horner, p, DensePoly.ofList, Array.foldr,
    Finset.sum_range_succ, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow]
  ring

theorem negative_eq : negative = preparedNegative := by
  apply (Extension.evalHom transcendence).injective
  change Extension.evalHom transcendence (Extension.X - Extension.C (2 : Rat) : E) = _
  rw [map_sub, Extension.evalHom_X, Extension.evalHom_C, Extension.evalHom_apply]
  norm_num [preparedNegative, Real.eval, RationalFn.ofPoly,
    HexPolyMathlib.eval₂_horner, q, DensePoly.ofList, Array.foldr,
    Finset.sum_range_succ, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow]
  ring

def preparedQuotient : E := ⟨RationalFn.ofCoprime p q
  (by change q.leadingCoeff = 1; decide +kernel)
  ⟨DensePoly.C (4/3), DensePoly.C (-4/3), by decide +kernel⟩⟩

theorem quotient_eq : quotient = preparedQuotient := by
  apply (Extension.evalHom transcendence).injective
  change Extension.evalHom transcendence (positive / negative) = _
  rw [map_div₀, positive_eq, negative_eq]
  simp only [Extension.evalHom_apply]
  norm_num [preparedPositive, preparedNegative, preparedQuotient, Real.eval,
    RationalFn.ofPoly, RationalFn.ofCoprime]

theorem positive_sign : Extension.sign positive = 1 :=
  Extension.sign_of_attempt source_correct positive (n := 2) (by
    change attempt source _ _ = _
    rw [positive_eq]
    decide +kernel)

theorem negative_sign : Extension.sign negative = -1 :=
  Extension.sign_of_attempt source_correct negative (n := 0) (by
    change attempt source _ _ = _
    rw [negative_eq]
    decide +kernel)

theorem quotient_sign : Extension.sign quotient = -1 :=
  Extension.sign_of_attempt source_correct quotient (n := 2) (by
    change attempt source _ _ = _
    rw [quotient_eq]
    decide +kernel)

local instance : LinearOrder E := Extension.linearOrder source_correct transcendence
local instance : IsStrictOrderedRing E := Extension.strictOrderedRing source_correct transcendence
local instance : Lean.Grind.OrderedRing E := Extension.orderedRing source_correct transcendence

example : Std.IsLinearOrder E := inferInstance
example : Std.LawfulOrderLT E := inferInstance
example : (0 : E) < positive := (Extension.sign_pos_iff source_correct transcendence _).mp positive_sign
example : negative < (0 : E) := (Extension.sign_neg_iff source_correct transcendence _).mp negative_sign
example : quotient < (0 : E) := (Extension.sign_neg_iff source_correct transcendence _).mp quotient_sign

example : (positive / negative) * negative = positive := by
  apply div_mul_cancel₀
  exact ne_of_lt ((Extension.sign_neg_iff source_correct transcendence _).mp negative_sign)

example : Contains (Extension.approx positive (1 / 8))
    (Extension.evalHom transcendence positive) :=
  Extension.approx_contains source_correct transcendence _ _

example : (Extension.approx positive (1 / 8)).width ≤ 1 / 8 :=
  Extension.approx_width _ _ (by norm_num)


-- The next real level uses this level's derived coefficient approximations.
example (σ : ℝ) (constant : Rat → Bounds)
    (hc : ∀ δ, 0 < δ → Contains (constant δ) σ)
    (hw : ∀ δ, 0 < δ → (constant δ).width ≤ δ)
    (ht : RelativeTranscendence (Extension.evalHom (r := registered) transcendence) σ)
    (f : RationalFn E) :
    ∃ N, ∀ n ≥ N, (attempt (Extension.approximation (r := registered) constant) f n).isSome = true := by
  revert f
  rw [← Extension.coreField_eq]
  intro f
  exact attempt_progress (Extension.approximation_correct source_correct transcendence constant σ hc)
    (Extension.approximation_width constant hw) ht f

-- Reusing a constant from the predecessor is not relative transcendence.
example : ¬RelativeTranscendence (Extension.evalHom (r := registered) transcendence)
    (liouvilleNumber 2 + 1) := by
  intro h
  exact h.ne_image (Extension.X + 1 : E) (by simp)

-- Narrow bounds for this provider do not authenticate another subject.
example : ¬ApproximationCorrect (Rat.castHom ℝ) 2 source := by
  intro h
  have hc := h.constant 1 (by norm_num)
  norm_num [source, Approximation.ofConstant, provider, bounds, partialSum,
    Contains, Finset.sum_range_succ, Nat.log2_def] at hc

def refinedSource : Approximation Rat := .ofConstant (fun δ => provider (δ / 2))

theorem refined_correct : ApproximationCorrect (Rat.castHom ℝ)
    (liouvilleNumber 2) refinedSource :=
  .ofConstant _ _ (fun δ _ => provider_contains (δ / 2))

theorem refined_width : ApproximationWidth refinedSource := .ofConstant _ (by
  intro δ hδ
  exact (provider_width _ (by positivity)).trans (by linarith))

def refined : Registration Rat := registration refined_correct refined_width transcendence

#guard_msgs (drop info) in
#check_failure (show Extension refined from positive)

example : Extension.sign (Extension.transport refined positive) = Extension.sign positive :=
  Extension.sign_transport refined source_correct refined_correct transcendence positive

open scoped Hex.OrderedFn.Infinitesimal

-- Opening the infinitesimal scope preserves the predecessor's real order.
example : negative < (0 : E) := (Extension.sign_neg_iff source_correct transcendence _).mp negative_sign


example : (0 : ExtensionTests.Mixed registered) < ExtensionTests.epsilon registered := by
  unfold ExtensionTests.epsilon ExtensionTests.Mixed
  rw [← Extension.coreField_eq]
  exact Infinitesimal.X_pos

/-- info: 'Hex.OrderedFn.Real.sign_acc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.OrderedFn.Real.sign_acc
/-- info: 'Hex.OrderedFn.Real.approx_acc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.OrderedFn.Real.approx_acc
/-- info: 'Hex.OrderedFn.LiouvilleTests.positive_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms positive_sign

end Hex.OrderedFn.LiouvilleTests
