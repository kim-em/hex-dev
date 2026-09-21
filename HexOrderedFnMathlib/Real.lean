/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFn.Real
public import HexOrderedFnMathlib.Oracle
public import HexPolyMathlib.PolynomialEquivalence

@[expose] public section

namespace Hex.OrderedFn.Real

open Oracle HexPolyMathlib
universe u
variable {K : Type u} [Field K] [DecidableEq K]
variable {ι : K →+* ℝ} {τ : ℝ} {a : Approximation K}

/-- Evaluate the stored canonical fraction. At a pole this is total real division;
it is not a field embedding without relative transcendence. -/
noncomputable def eval (ι : K →+* ℝ) (τ : ℝ) (f : RationalFn K) : ℝ :=
  (toPolynomial f.num).eval₂ ι τ / (toPolynomial f.den).eval₂ ι τ

theorem precision_pos (n : Nat) : 0 < precision n := by
  unfold precision
  positivity

/-- Containment composes through the actual array Horner loop. -/
theorem enclose_sound (ha : ApproximationCorrect ι τ a) (p : DensePoly K)
    (δ : Rat) (hδ : 0 < δ) : Contains (enclose a p δ) ((toPolynomial p).eval₂ ι τ) := by
  rw [eval₂_horner]
  unfold enclose
  rw [← Array.foldr_toList]
  have h : ∀ l : List K,
      Contains (l.foldr (fun c acc => (a.coeff c δ).add ((a.constant δ).mul acc))
        (.singleton 0)) (l.foldr (fun c acc => ι c + τ * acc) 0) := by
    intro l
    induction l with
    | nil => simpa using Contains.singleton 0
    | cons c cs ih => exact (ha.coeff c δ hδ).add ((ha.constant δ hδ).mul ih)
  exact h p.coeffs.toList

/-- Every successful total-sign trial is sound from containment alone.
Convergence and transcendence belong to the separate progress obligation. -/
theorem attempt_sound (ha : ApproximationCorrect ι τ a) (f : RationalFn K)
    (n : Nat) {s : Int} (hs : attempt a f n = some s) : s = sgn (eval ι τ f) := by
  unfold attempt at hs
  split at hs
  next hz =>
    cases hs
    simp [eval, hz, sgn]
  next hz =>
    cases hn : (enclose a f.num (precision n)).sign? with
    | none => simp [hn] at hs
    | some sn =>
      cases hd : (enclose a f.den (precision n)).sign? with
      | none => simp [hn, hd] at hs
      | some sd =>
        have hn' := ((enclose_sound ha f.num _ (precision_pos n)).sign hn).1
        have hd' := ((enclose_sound ha f.den _ (precision_pos n)).sign hd).1
        simp [hn, hd] at hs
        rw [← hs, hn', hd', eval, sgn_div]

/-- Successful trials agree, independently of the supplied termination proof. -/
theorem attempt_unique (ha : ApproximationCorrect ι τ a) (f : RationalFn K)
    (i j : Nat) (s t : Int) (hs : attempt a f i = some s) (ht : attempt a f j = some t) :
    s = t := (attempt_sound ha f i hs).trans (attempt_sound ha f j ht).symm

/-- A total per-query sign agrees with evaluation of its canonical fraction. -/
theorem sign_sound (ha : ApproximationCorrect ι τ a) (f : RationalFn K)
    (h : Acc (Next (attempt a f)) 0) : sign a f h = sgn (eval ι τ f) := by
  obtain ⟨n, _, hn⟩ := firstSome_spec (attempt a f) 0 h
  exact attempt_sound ha f n hn

/-- Finite supplied evidence identifies the total result without reducing its
accessibility proof. Containment binds the evidence to these providers and subject. -/
theorem sign_of_attempt (ha : ApproximationCorrect ι τ a) (f : RationalFn K)
    (h : Acc (Next (attempt a f)) 0) {n : Nat} {s : Int}
    (hs : attempt a f n = some s) : sign a f h = s :=
  firstSome_eq _ _ h hs (attempt_unique ha f)

theorem approxAttempt_contains (ha : ApproximationCorrect ι τ a) (f : RationalFn K)
    (δ : Rat) (n : Nat) {b : Bounds} (hb : approxAttempt a f δ n = some b) :
    Contains b (eval ι τ f) := by
  unfold approxAttempt at hb
  split at hb
  next hz =>
    split at hb
    · cases hb
      simp [eval, hz, Contains, Bounds.singleton]
    · contradiction
  next hz =>
    cases hd : (enclose a f.num (precision n)).div? (enclose a f.den (precision n)) with
    | none => simp [hd] at hb
    | some c =>
      simp [hd] at hb
      rcases hb with ⟨_, rfl⟩
      exact ((enclose_sound ha f.num _ (precision_pos n)).div
        (enclose_sound ha f.den _ (precision_pos n)) hd).1

/-- Containment is separate from the computational rational width theorem. -/
theorem approx_contains (ha : ApproximationCorrect ι τ a) (f : RationalFn K)
    (δ : Rat) (h : 0 < δ → Acc (Next (approxAttempt a f δ)) 0) (hδ : 0 < δ) :
    Contains (approx a f δ h) (eval ι τ f) := by
  simp only [approx, dite_eq_left hδ]
  obtain ⟨n, _, hn⟩ := firstSome_spec (approxAttempt a f δ) 0 (h hδ)
  exact approxAttempt_contains ha f δ n hn

/-- Finite success proves both the sign and regularity of the stored denominator.
Source-expression divisor guards remain the responsibility of expression consumers. -/
theorem finiteAttempt_sound (ha : ApproximationCorrect ι τ a) (f : RationalFn K)
    (n : Nat) {s : Int} (hs : finiteAttempt a f n = some s) :
    s = sgn (eval ι τ f) ∧ (toPolynomial f.den).eval₂ ι τ ≠ 0 := by
  unfold finiteAttempt at hs
  cases hd : (enclose a f.den (precision n)).sign? with
  | none => simp [hd] at hs
  | some sd =>
    cases hn : (enclose a f.num (precision n)).exactSign? with
    | none => simp [hd, hn] at hs
    | some sn =>
      have hn' := (enclose_sound ha f.num _ (precision_pos n)).exactSign hn
      have hd' := (enclose_sound ha f.den _ (precision_pos n)).sign hd
      simp [hn, hd] at hs
      exact ⟨by rw [← hs, hn', hd'.1, eval, sgn_div], hd'.2⟩

theorem sign?_sound (ha : ApproximationCorrect ι τ a) (f : RationalFn K)
    (fuel : Nat) {s : Int} (hs : sign? a f fuel = some s) :
    s = sgn (eval ι τ f) ∧ (toPolynomial f.den).eval₂ ι τ ≠ 0 := by
  have h : ∀ fuel n, sign?.go a f fuel n = some s →
      s = sgn (eval ι τ f) ∧ (toPolynomial f.den).eval₂ ι τ ≠ 0 := by
    intro fuel
    induction fuel with
    | zero => simp [sign?.go]
    | succ fuel ih =>
      intro n hn
      cases he : finiteAttempt a f n with
      | none => exact ih (n + 1) (by simpa [sign?.go, he] using hn)
      | some t =>
        have : t = s := by simpa [sign?.go, he] using hn
        exact this ▸ finiteAttempt_sound ha f n he
  exact h fuel 0 hs

end Hex.OrderedFn.Real
