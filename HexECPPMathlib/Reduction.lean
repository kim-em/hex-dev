/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexECPP.Cert
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic

/-!
# Interpreting certificate arithmetic over finite fields

The integer `n` in a primality certificate need not yet be known prime.
For each prime divisor `p` of `n`, verified modular inverses remain inverses
in `ZMod p`, and the curve remains nonsingular. We interpret the supplied
coordinates as Mathlib elliptic curve points and prove that every accepted
addition agrees with the group law. A finite starting point stays different
from the identity after reduction. These facts justify the point-order
argument used to prove `n` prime.
-/

@[expose] public section

namespace Hex.ECPP

open WeierstrassCurve

/-- The short Weierstrass curve supplied by an ECPP step, reduced modulo `p`. -/
def shortCurve (p a b : ℕ) : WeierstrassCurve (ZMod p) :=
  ⟨0, 0, 0, a, b⟩

/-- The checker's short curve has zero coefficients `a₁`, `a₂` and `a₃`. -/
instance shortCurveIsShortNF (p a b : ℕ) : (shortCurve p a b).IsShortNF :=
  ⟨rfl, rfl, rfl⟩

/-- The checker coprimality guard excludes characteristics two and three. -/
theorem prime_divisor_gt_three {p n : ℕ} (prime : p.Prime) (hp : p ∣ n)
    (hmod : n % 6 = 1 ∨ n % 6 = 5) : 3 < p := by
  have hp2 := prime.two_le
  by_contra h
  have hsmall : p = 2 ∨ p = 3 := by omega
  rcases hsmall with rfl | rfl
  · obtain ⟨k, rfl⟩ := hp
    rcases hmod with hmod | hmod <;> omega
  · obtain ⟨k, rfl⟩ := hp
    rcases hmod with hmod | hmod <;> omega

/-- Reduction modulo a multiple of `p` preserves the residue in `ZMod p`. -/
theorem cast_mod {p n : ℕ} (hp : p ∣ n) (t : ℕ) :
    ((t % n : ℕ) : ZMod p) = t := by
  exact (ZMod.natCast_eq_natCast_iff _ _ p).mpr
    ((Nat.mod_modEq t n).of_dvd hp)

/-- The checker's natural modular subtraction is field subtraction after
reduction at any prime divisor. -/
theorem cast_modSub {p n : ℕ} (hp : p ∣ n) (hn : 0 < n) (a b : ℕ) :
    ((modSub n a b : ℕ) : ZMod p) = (a : ZMod p) - b := by
  have hle : b % n ≤ a % n + n := by
    have hb := Nat.mod_lt b hn
    omega
  simp only [modSub, cast_mod hp, Nat.cast_sub hle, Nat.cast_add]
  rw [(ZMod.natCast_eq_zero_iff n p).mpr hp]
  ring

/-- A consumed inverse witness is an actual inverse in every prime residue field. -/
theorem inverse_witness {p n d u : ℕ} [Fact p.Prime] (hp : p ∣ n)
    (h : d * u % n = 1) : (u : ZMod p) = (d : ZMod p)⁻¹ := by
  have hdu := congrArg (fun t : ℕ => (t : ZMod p)) h
  simp only [cast_mod hp, Nat.cast_mul, Nat.cast_one] at hdu
  exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hdu)

/-- The coordinates produced by a checked division branch are the field
secant or tangent formulas over every prime divisor. -/
theorem addWithInverse_reduced {p n x₁ y₁ x₂ d v : ℕ} [Fact p.Prime]
    {ws rest : List ℕ} {R : Point} (hp : p ∣ n) (hn : 0 < n)
    (h : addWithInverse n x₁ y₁ x₂ d v ws = some (R, rest)) :
    ∃ X Y : ℕ, R = .affine X Y ∧
      (X : ZMod p) = ((v : ZMod p) / d) ^ 2 - x₁ - x₂ ∧
      (Y : ZMod p) = ((v : ZMod p) / d) * ((x₁ : ZMod p) - X) - y₁ := by
  obtain ⟨u, _, _, hdu, rfl⟩ := addWithInverse_spec h
  let s := v * u % n
  let X := modSub n (modSub n (s * s % n) x₁) x₂
  let Y := modSub n (s * (modSub n x₁ X) % n) y₁
  have hs : (s : ZMod p) = (v : ZMod p) / d := by
    dsimp [s]
    rw [cast_mod hp, Nat.cast_mul, inverse_witness hp hdu, div_eq_mul_inv]
  refine ⟨X, Y, rfl, ?_, ?_⟩
  · dsimp [X]
    rw [cast_modSub hp hn, cast_modSub hp hn, cast_mod hp, Nat.cast_mul, hs]
    ring
  · dsimp [Y]
    rw [cast_modSub hp hn, cast_mod hp, Nat.cast_mul, cast_modSub hp hn, hs]

/-- A checked raw point lies on the reduced short curve. -/
theorem onCurve_reduced {p n a b x y : ℕ} (hp : p ∣ n)
    (h : onCurve n a b x y = true) :
    (shortCurve p a b).toAffine.Equation (x : ZMod p) (y : ZMod p) := by
  have heq : (y * y) % n = (x * x * x + a * x + b) % n := by
    simpa only [onCurve, beq_iff_eq] using h
  have heq' := congrArg (fun t : ℕ => (t : ZMod p)) heq
  simp only [cast_mod hp, Nat.cast_mul, Nat.cast_add] at heq'
  rw [WeierstrassCurve.Affine.equation_iff]
  dsimp [shortCurve]
  simp only [zero_mul, add_zero]
  calc
    (y : ZMod p) ^ 2 = y * y := by ring
    _ = x * x * x + (a : ZMod p) * x + b := heq'
    _ = x ^ 3 + (a : ZMod p) * x + b := by ring

set_option linter.style.haveILetI false in
/-- The checked discriminant inverse makes the reduced short curve nonsingular. -/
theorem shortCurve_elliptic {p n a b inv : ℕ} (prime : p.Prime)
    (hp3 : 3 < p) (hp : p ∣ n)
    (h : ((4 * a * a * a + 27 * b * b) * inv) % n = 1) :
    (shortCurve p a b).toAffine.IsElliptic := by
  letI : Fact p.Prime := ⟨prime⟩
  have hcast := congrArg (fun t : ℕ => (t : ZMod p)) h
  simp only [cast_mod hp, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcast
  have hfactor : (4 * (a : ZMod p) ^ 3 + 27 * (b : ZMod p) ^ 2) * inv = 1 := by
    calc
      _ = (4 * (a : ZMod p) * a * a + 27 * (b : ZMod p) * b) * inv := by ring
      _ = 1 := hcast
  have hD : (4 * (a : ZMod p) ^ 3 + 27 * (b : ZMod p) ^ 2) ≠ 0 := by
    intro hz
    have hzero : (0 : ZMod p) = 1 := by simpa only [hz, zero_mul] using hfactor
    exact zero_ne_one hzero
  have h16 : (16 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 16 := (ZMod.natCast_eq_zero_iff 16 p).mp hz
    have hpow : p ∣ 2 ^ 4 := by simpa using hdiv
    have h2 : p ∣ 2 := prime.dvd_of_dvd_pow hpow
    have : p ≤ 2 := Nat.le_of_dvd (by omega) h2
    omega
  apply (WeierstrassCurve.isElliptic_iff (shortCurve p a b)).2
  rw [WeierstrassCurve.Δ_of_isShortNF]
  dsimp [shortCurve]
  have hne : (-16 * (4 * (a : ZMod p) ^ 3 + 27 * (b : ZMod p) ^ 2)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr h16) hD
  exact isUnit_iff_ne_zero.mpr hne

/-- A raw point represents an actual nonsingular affine point after reducing
its coordinates into a prime field. -/
def Point.Rep (p a b : ℕ) (raw : Point)
    (P : (shortCurve p a b).toAffine.Point) : Prop :=
  match raw with
  | .infinity => P = 0
  | .affine x y =>
      ∃ h : (shortCurve p a b).toAffine.Nonsingular (x : ZMod p) (y : ZMod p),
        P = .some _ _ h

set_option linter.style.haveILetI false in
/-- The checked starting point represents a nonidentity group element over
every prime divisor of the candidate. -/
theorem startingPoint_rep {p n a b x y inv : ℕ} (prime : p.Prime)
    (hp3 : 3 < p) (hp : p ∣ n)
    (hdisc : ((4 * a * a * a + 27 * b * b) * inv) % n = 1)
    (hcurve : onCurve n a b x y = true) :
    ∃ P : (shortCurve p a b).toAffine.Point,
      (Point.affine x y).Rep p a b P ∧ P ≠ 0 := by
  letI : Fact p.Prime := ⟨prime⟩
  letI : (shortCurve p a b).toAffine.IsElliptic :=
    shortCurve_elliptic prime hp3 hp hdisc
  have heq := onCurve_reduced hp hcurve
  have hnon : (shortCurve p a b).toAffine.Nonsingular (x : ZMod p) (y : ZMod p) :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular).mp heq
  refine ⟨.some _ _ hnon, ⟨hnon, rfl⟩, ?_⟩
  exact WeierstrassCurve.Affine.Point.some_ne_zero hnon

/-- The witness quotient in the distinct-abscissa branch is Mathlib's
secant slope. -/
theorem secant_slope {p n a b x₁ y₁ x₂ y₂ : ℕ} [Fact p.Prime]
    (hp : p ∣ n) (hn : 0 < n) (hne : (x₁ : ZMod p) ≠ x₂) :
    (shortCurve p a b).toAffine.slope x₁ x₂ y₁ y₂ =
      ((modSub n y₂ y₁ : ℕ) : ZMod p) /
        ((modSub n x₂ x₁ : ℕ) : ZMod p) := by
  rw [WeierstrassCurve.Affine.slope, ite_eq_right hne,
    cast_modSub hp hn, cast_modSub hp hn]
  have hy : (y₁ : ZMod p) - y₂ = -((y₂ : ZMod p) - y₁) := by ring
  have hx : (x₁ : ZMod p) - x₂ = -((x₂ : ZMod p) - x₁) := by ring
  rw [hy, hx]
  simp only [div_neg, neg_div, neg_neg]

/-- The witness quotient in the equal-point branch is Mathlib's tangent
slope. The inverse witness excludes a vertical tangent in every field. -/
theorem tangent_slope {p n a b x y u : ℕ} [Fact p.Prime]
    (hp : p ∣ n)
    (hu : (2 * y % n) * u % n = 1) :
    (shortCurve p a b).toAffine.slope x x y y =
      (((3 * x * x + a) % n : ℕ) : ZMod p) /
        (((2 * y) % n : ℕ) : ZMod p) := by
  have hdu := congrArg (fun t : ℕ => (t : ZMod p)) hu
  simp only [cast_mod hp, Nat.cast_mul, Nat.cast_one] at hdu
  have h2y : (2 : ZMod p) * y ≠ 0 := by
    intro hz
    simp [hz] at hdu
  have hne : (y : ZMod p) ≠ (shortCurve p a b).toAffine.negY x y := by
    intro hy
    simp only [WeierstrassCurve.Affine.negY, shortCurve, zero_mul,
      sub_zero] at hy
    apply h2y
    have hsum : (y : ZMod p) + y = 0 := by
      nth_rw 1 [hy]
      exact neg_add_cancel _
    simpa only [two_mul] using hsum
  rw [WeierstrassCurve.Affine.slope, ite_eq_left rfl, ite_eq_right hne,
    cast_mod hp, cast_mod hp]
  simp only [WeierstrassCurve.Affine.negY, shortCurve, zero_mul,
    sub_zero, Nat.cast_add, Nat.cast_mul]
  congr 1 <;> ring

/-- If raw coordinates equal Mathlib's affine addition formulas, they
represent the actual group sum. -/
theorem formula_rep {p a b x₁ y₁ x₂ y₂ X Y : ℕ} [Fact p.Prime]
    (h₁ : (shortCurve p a b).toAffine.Nonsingular (x₁ : ZMod p) (y₁ : ZMod p))
    (h₂ : (shortCurve p a b).toAffine.Nonsingular (x₂ : ZMod p) (y₂ : ZMod p))
    (hxy : ¬((x₁ : ZMod p) = x₂ ∧
      (y₁ : ZMod p) = (shortCurve p a b).toAffine.negY x₂ y₂))
    (hx : (X : ZMod p) = (shortCurve p a b).toAffine.addX x₁ x₂
      ((shortCurve p a b).toAffine.slope x₁ x₂ y₁ y₂))
    (hy : (Y : ZMod p) = (shortCurve p a b).toAffine.addY x₁ x₂ y₁
      ((shortCurve p a b).toAffine.slope x₁ x₂ y₁ y₂)) :
    (Point.affine X Y).Rep p a b
      (.some _ _ h₁ + .some _ _ h₂) := by
  have hsum := (shortCurve p a b).toAffine.nonsingular_add h₁ h₂ hxy
  have hXY : (shortCurve p a b).toAffine.Nonsingular (X : ZMod p) (Y : ZMod p) := by
    rw [hx, hy]
    exact hsum
  refine ⟨hXY, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_some hxy]
  simp only [← hx, ← hy]

/-- A checked secant branch is the actual affine group sum in every prime
residue field. -/
theorem secant_rep {p n a b x₁ y₁ x₂ y₂ : ℕ} [Fact p.Prime]
    {ws rest : List ℕ} {R : Point} (hp : p ∣ n) (hn : 0 < n)
    (h₁ : (shortCurve p a b).toAffine.Nonsingular (x₁ : ZMod p) (y₁ : ZMod p))
    (h₂ : (shortCurve p a b).toAffine.Nonsingular (x₂ : ZMod p) (y₂ : ZMod p))
    (h : addWithInverse n x₁ y₁ x₂ (modSub n x₂ x₁)
      (modSub n y₂ y₁) ws = some (R, rest)) :
    R.Rep p a b (.some _ _ h₁ + .some _ _ h₂) := by
  obtain ⟨u, _, _, hdu, _⟩ := addWithInverse_spec h
  have hduF := congrArg (fun t : ℕ => (t : ZMod p)) hdu
  simp only [cast_mod hp, Nat.cast_mul, Nat.cast_one,
    cast_modSub hp hn] at hduF
  have hneq : (x₁ : ZMod p) ≠ x₂ := by
    intro heq
    have hz : (x₂ : ZMod p) - x₁ = 0 := sub_eq_zero.mpr heq.symm
    rw [hz] at hduF
    simp at hduF
  obtain ⟨X, Y, rfl, hx, hy⟩ := addWithInverse_reduced hp hn h
  have hslope := secant_slope (a := a) (b := b)
    (x₁ := x₁) (y₁ := y₁) (x₂ := x₂) (y₂ := y₂) hp hn hneq
  have hxF : (X : ZMod p) = (shortCurve p a b).toAffine.addX x₁ x₂
      ((shortCurve p a b).toAffine.slope x₁ x₂ y₁ y₂) := by
    rw [hslope]
    simpa only [WeierstrassCurve.Affine.addX, shortCurve,
      zero_mul, add_zero, zero_sub, sub_zero] using hx
  have hyF : (Y : ZMod p) = (shortCurve p a b).toAffine.addY x₁ x₂ y₁
      ((shortCurve p a b).toAffine.slope x₁ x₂ y₁ y₂) := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    have hxF' := hxF
    rw [hslope] at hxF'
    rw [← hxF']
    dsimp [shortCurve]
    simp only [zero_mul, sub_zero]
    ring_nf at hy ⊢
    exact hy
  exact formula_rep h₁ h₂ (fun hxy => hneq hxy.1) hxF hyF

/-- A checked tangent branch is the actual affine group sum in every prime
residue field. -/
theorem tangent_rep {p n a b x y : ℕ} [Fact p.Prime]
    {ws rest : List ℕ} {R : Point} (hp : p ∣ n) (hn : 0 < n)
    (hpoint : (shortCurve p a b).toAffine.Nonsingular (x : ZMod p) (y : ZMod p))
    (h : addWithInverse n x y x (2 * y % n)
      ((3 * x * x + a) % n) ws = some (R, rest)) :
    R.Rep p a b (.some _ _ hpoint + .some _ _ hpoint) := by
  obtain ⟨u, _, _, hdu, _⟩ := addWithInverse_spec h
  have hduF := congrArg (fun t : ℕ => (t : ZMod p)) hdu
  simp only [cast_mod hp, Nat.cast_mul, Nat.cast_one] at hduF
  have hne : (y : ZMod p) ≠ (shortCurve p a b).toAffine.negY x y := by
    intro heq
    simp only [WeierstrassCurve.Affine.negY, shortCurve, zero_mul,
      sub_zero] at heq
    have hz : (2 : ZMod p) * y = 0 := by
      have hsum : (y : ZMod p) + y = 0 := by
        nth_rw 1 [heq]
        exact neg_add_cancel _
      simpa only [two_mul] using hsum
    norm_num only [Nat.cast_ofNat] at hduF
    rw [hz] at hduF
    simp at hduF
  obtain ⟨X, Y, rfl, hx, hy⟩ := addWithInverse_reduced hp hn h
  have hslope := tangent_slope (a := a) (b := b) (x := x) (y := y) hp hdu
  have hxF : (X : ZMod p) = (shortCurve p a b).toAffine.addX x x
      ((shortCurve p a b).toAffine.slope x x y y) := by
    rw [hslope]
    simpa only [WeierstrassCurve.Affine.addX, shortCurve,
      zero_mul, add_zero, zero_sub, sub_zero] using hx
  have hyF : (Y : ZMod p) = (shortCurve p a b).toAffine.addY x x y
      ((shortCurve p a b).toAffine.slope x x y y) := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    have hxF' := hxF
    rw [hslope] at hxF'
    rw [← hxF']
    dsimp [shortCurve]
    simp only [zero_mul, sub_zero]
    ring_nf at hy ⊢
    exact hy
  exact formula_rep hpoint hpoint (fun hxy => hne hxy.2) hxF hyF

/-- Every accepted raw addition agrees with Mathlib's group law after
reduction to a prime divisor. -/
theorem add_rep {p n a b : ℕ} [Fact p.Prime] (hp : p ∣ n) (hn : 0 < n)
    {P Q R : Point} {U V : (shortCurve p a b).toAffine.Point}
    {ws rest : List ℕ} (hP : P.Rep p a b U) (hQ : Q.Rep p a b V)
    (h : add? n a P Q ws = some (R, rest)) :
    R.Rep p a b (U + V) := by
  cases P with
  | infinity =>
    simp only [Point.Rep] at hP
    simp only [add?] at h
    cases h
    simpa [hP] using hQ
  | affine x₁ y₁ =>
    cases Q with
    | infinity =>
      simp only [Point.Rep] at hQ
      simp only [add?] at h
      cases h
      simpa [hQ] using hP
    | affine x₂ y₂ =>
      obtain ⟨h₁, rfl⟩ := hP
      obtain ⟨h₂, rfl⟩ := hQ
      by_cases hx : x₁ = x₂
      · subst x₂
        by_cases hzero : (y₁ + y₂) % n = 0
        · have hfield := congrArg (fun t : ℕ => (t : ZMod p)) hzero
          simp only [cast_mod hp, Nat.cast_add, Nat.cast_zero] at hfield
          have hy : (y₁ : ZMod p) =
              (shortCurve p a b).toAffine.negY x₁ y₂ := by
            simp only [WeierstrassCurve.Affine.negY, shortCurve,
              zero_mul, sub_zero]
            exact eq_neg_of_add_eq_zero_left hfield
          have hgroup := WeierstrassCurve.Affine.Point.add_of_Y_eq
            (h₁ := h₁) (h₂ := h₂) rfl hy
          simp [add?, hzero] at h
          rcases h with ⟨rfl, rfl⟩
          simp [Point.Rep, hgroup]
        · by_cases hy : y₁ = y₂
          · subst y₂
            have h' : addWithInverse n x₁ y₁ x₁ (2 * y₁ % n)
                ((3 * x₁ * x₁ + a) % n) ws = some (R, rest) := by
              simpa [add?, hzero] using h
            exact tangent_rep hp hn h₁ h'
          · simp [add?, hzero, hy] at h
      · have h' : addWithInverse n x₁ y₁ x₂ (modSub n x₂ x₁)
            (modSub n y₂ y₁) ws = some (R, rest) := by
          simpa [add?, hx] using h
        exact secant_rep hp hn h₁ h₂ h'

end Hex.ECPP
