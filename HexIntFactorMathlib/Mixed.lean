/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Mixed.Replay
public import HexECPPMathlib.Soundness
public import HexPrimalityMathlib.Prime
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

/-! Unconditional mathematical soundness of mixed complete and partial data.
The partial correspondence includes the uncertified residual's multiplicity. -/

namespace Hex.Nat.Mixed

/-- Discharge the computational ECPP obligation using the existing soundness proof. -/
theorem ecppSoundness : Soundness := by
  intro n c h
  exact Hex.Nat.prime_iff.mpr (Hex.ECPP.natPrime_of_checkAt h)

private theorem product_ne_zero {fs : List PrimePower}
    (hp : ∀ e ∈ fs, _root_.Nat.Prime e.prime) :
    (fs.map fun e => e.prime ^ e.exponent).prod ≠ 0 := by
  induction fs with
  | nil => simp
  | cons e fs ih =>
      simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_ne_zero ((Nat.pow_pos (hp e (by simp)).pos).ne')
        (ih (fun x hx => hp x (by simp [hx])))

private theorem powers_lookup (fs : List PrimePower)
    (hs : fs.Pairwise (fun a b => a.prime < b.prime))
    (hp : ∀ e ∈ fs, _root_.Nat.Prime e.prime) (p : Nat) :
    ((fs.map fun (e : PrimePower) => e.prime ^ e.exponent).prod).factorization p =
      (fs.find? fun e => e.prime == p).elim 0 (·.exponent) := by
  induction fs with
  | nil => simp
  | cons e fs ih =>
      obtain ⟨hlt, htail⟩ := List.pairwise_cons.mp hs
      have he := hp e (by simp)
      have hpr : ∀ x ∈ fs, _root_.Nat.Prime x.prime := fun x hx => hp x (by simp [hx])
      rw [List.map_cons, List.prod_cons,
        Nat.factorization_mul ((Nat.pow_pos he.pos).ne') (product_ne_zero hpr),
        Finsupp.add_apply, he.factorization_pow, ih htail hpr]
      by_cases hep : e.prime = p
      · have hfind : fs.find? (fun x => x.prime == p) = none := by
          apply List.find?_eq_none.mpr
          intro x hx
          have hne : x.prime ≠ p := by
            intro heq
            have h := hlt x hx
            rw [hep, heq] at h
            exact Nat.lt_irrefl _ h
          simp [hne]
        simp [hep, hfind]
      · simp [hep, Ne.symm hep]

/-- Every accepted complete entry has unconditional Mathlib primality. -/
theorem CheckedFactorization.prime {n : Nat} (F : CheckedFactorization n)
    (e : PrimePower) (he : e ∈ F.raw.factors) : _root_.Nat.Prime e.prime :=
  Hex.Nat.prime_iff.mp (checkFactorization_prime ecppSoundness F.valid e he)

/-- The mixed canonical list gives exactly Mathlib's complete multiplicities. -/
theorem factorization_eq (F : Factorization) (h : checkFactorization F = true) (p : Nat) :
    F.subject.factorization p =
      (F.factors.find? fun e => e.prime == p).elim 0 (·.exponent) := by
  rw [← checkFactorization_prod h]
  exact powers_lookup F.factors (checkFactorization_sorted h)
    (fun e he => Hex.Nat.prime_iff.mp (checkFactorization_prime ecppSoundness h e he)) p

/-- Headline subject-bound correspondence for complete mixed data. -/
theorem CheckedFactorization.factorization_eq {n : Nat} (F : CheckedFactorization n) (p : Nat) :
    n.factorization p =
      (F.raw.factors.find? fun e => e.prime == p).elim 0 (·.exponent) := by
  simpa only [F.subject_eq] using Hex.Nat.Mixed.factorization_eq F.raw F.valid p

/-- Complete listed support contains every prime divisor, and only those divisors. -/
theorem CheckedFactorization.primeSupport {n q : Nat} (F : CheckedFactorization n)
    (hq : _root_.Nat.Prime q) : q ∣ n ↔ ∃ e ∈ F.raw.factors, e.prime = q := by
  simpa only [F.subject_eq] using
    checkFactorization_primeSupport ecppSoundness F.valid (Hex.Nat.prime_iff.mpr hq)

/-- A complete entry's exponent is its exact power-divisibility multiplicity. -/
theorem CheckedFactorization.multiplicity {n : Nat} (F : CheckedFactorization n)
    {e : PrimePower} (he : e ∈ F.raw.factors) {k : Nat} :
    e.prime ^ k ∣ n ↔ k ≤ e.exponent := by
  rw [← F.subject_eq]
  exact checkFactorization_multiplicity ecppSoundness F.valid he

/-- Every accepted partial entry has unconditional Mathlib primality. -/
theorem CheckedPartialFactorization.prime {n : Nat} (F : CheckedPartialFactorization n)
    (e : PrimePower) (he : e ∈ F.raw.factors) : _root_.Nat.Prime e.prime :=
  Hex.Nat.prime_iff.mp (checkPartial_prime ecppSoundness F.valid e he)

/-- Partial multiplicities include any further prime powers in the residual. -/
theorem partial_factorization_eq (F : PartialFactorization) (h : checkPartial F = true) (p : Nat) :
    F.subject.factorization p =
      (F.factors.find? fun e => e.prime == p).elim 0 (·.exponent) +
      F.residual.factorization p := by
  have hpos : 0 < (F.factors.map fun e => e.prime ^ e.exponent).prod * F.residual := by
    rw [checkPartial_prod h]
    exact checkPartial_pos h
  have hprod : (F.factors.map fun e => e.prime ^ e.exponent).prod ≠ 0 := by
    intro hz
    simp [hz] at hpos
  have hres : F.residual ≠ 0 := by
    intro hz
    simp [hz] at hpos
  rw [← checkPartial_prod h, Nat.factorization_mul hprod hres, Finsupp.add_apply]
  rw [powers_lookup F.factors (checkPartial_sorted h)
    (fun e he => Hex.Nat.prime_iff.mp (checkPartial_prime ecppSoundness h e he)) p]

/-- Headline subject-bound correspondence for partial mixed data. -/
theorem CheckedPartialFactorization.factorization_eq {n : Nat}
    (F : CheckedPartialFactorization n) (p : Nat) :
    n.factorization p =
      (F.raw.factors.find? fun e => e.prime == p).elim 0 (·.exponent) +
      F.raw.residual.factorization p := by
  simpa only [F.subject_eq] using partial_factorization_eq F.raw F.valid p

/-- A partial certified exponent is a lower bound, without certifying the residual. -/
theorem CheckedPartialFactorization.exponent_le {n : Nat} (F : CheckedPartialFactorization n)
    {e : PrimePower} (he : e ∈ F.raw.factors) : e.exponent ≤ n.factorization e.prime := by
  apply ((F.prime e he).pow_dvd_iff_le_factorization F.pos.ne').mp
  rw [← F.subject_eq]
  exact checkPartial_dvd F.valid he

/-- Prime support splits between the listed bases and the unclaimed residual. -/
theorem CheckedPartialFactorization.primeSupport {n q : Nat} (F : CheckedPartialFactorization n)
    (hq : _root_.Nat.Prime q) :
    q ∣ n ↔ (∃ e ∈ F.raw.factors, e.prime = q) ∨ q ∣ F.raw.residual := by
  simpa only [F.subject_eq] using
    checkPartial_primeSupport ecppSoundness F.valid (Hex.Nat.prime_iff.mpr hq)

/-- Partial exponents are exact when the corresponding base does not divide the residual. -/
theorem CheckedPartialFactorization.multiplicity {n : Nat} (F : CheckedPartialFactorization n)
    {e : PrimePower} (he : e ∈ F.raw.factors) (hr : ¬e.prime ∣ F.raw.residual) {k : Nat} :
    e.prime ^ k ∣ n ↔ k ≤ e.exponent := by
  rw [← F.subject_eq]
  exact checkPartial_multiplicity ecppSoundness F.valid he hr

end Hex.Nat.Mixed
