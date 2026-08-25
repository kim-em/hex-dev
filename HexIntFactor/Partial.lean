/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Cert

public section

/-! Checked partial factorizations.  Unlike a complete certificate, the
residual carries no primality or completeness claim. -/

namespace Hex

namespace Nat

/-- A raw partial factorization. -/
structure PartialFactorization where
  /-- The original input. -/
  subject : Nat
  /-- Certified prime powers already removed. -/
  factors : List PrimePower
  /-- The cofactor not yet certified prime. -/
  residual : Nat
deriving Repr

/-- Accept or reject partial factorization data. -/
@[expose]
def checkPartial (F : PartialFactorization) : Bool :=
  decide (0 < F.subject) && checkEntries F.factors &&
    match factorProduct F.subject F.factors 1 with
    | none => false
    | some acc =>
        decide (boundedPowMul F.subject F.residual acc 1 = some F.subject)

/-- Accepted partial factorization data tied to its requested subject. -/
structure CheckedPartialFactorization (n : Nat) where
  /-- The untrusted representation. -/
  raw : PartialFactorization
  /-- The representation is about `n`. -/
  subject_eq : raw.subject = n
  /-- Full partial-checker replay succeeds. -/
  valid : checkPartial raw = true

private theorem checkedPartial_parts {F : PartialFactorization}
    (h : checkPartial F = true) :
    0 < F.subject ∧ checkEntries F.factors = true ∧
      ∃ acc, factorProduct F.subject F.factors 1 = some acc ∧
        boundedPowMul F.subject F.residual acc 1 = some F.subject := by
  unfold checkPartial at h
  split at h
  · simp at h
  next acc hprod =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, acc, hprod, h.2⟩

private theorem boundedPowMul_eq {bound q : Nat} :
    ∀ (e acc r : Nat), boundedPowMul bound q acc e = some r →
      r = acc * q ^ e := by
  intro e
  induction e with
  | zero =>
      intro acc r h
      unfold boundedPowMul at h
      injection h with h
      subst h
      simp
  | succ e ih =>
      intro acc r h
      unfold boundedPowMul at h
      by_cases hb : bound < acc * q
      · rw [if_pos hb] at h
        cases h
      · rw [if_neg hb] at h
        rw [ih (acc * q) r h, Nat.pow_succ, Nat.mul_assoc,
          Nat.mul_comm q (q ^ e)]

private theorem factorProduct_eq {bound : Nat} :
    ∀ (l : List PrimePower) (acc r : Nat),
      factorProduct bound l acc = some r →
        r = acc * (l.map fun e => e.prime ^ e.exponent).prod := by
  intro l
  induction l with
  | nil =>
      intro acc r h
      unfold factorProduct at h
      injection h with h
      subst h
      simp
  | cons e rest ih =>
      intro acc r h
      unfold factorProduct at h
      split at h
      · cases h
      next acc' hp =>
        rw [ih acc' r h, boundedPowMul_eq e.exponent acc acc' hp]
        simp [Nat.mul_assoc]

/-- Accepted partial data reconstructs its subject exactly. -/
theorem checkPartial_prod {F : PartialFactorization}
    (h : checkPartial F = true) :
    (F.factors.map (fun e => e.prime ^ e.exponent)).prod * F.residual =
      F.subject := by
  obtain ⟨acc, hacc, hfinal⟩ := (checkedPartial_parts h).2.2
  have hprod := factorProduct_eq F.factors 1 acc hacc
  have hmul := boundedPowMul_eq 1 acc F.subject hfinal
  simpa [hprod] using hmul.symm

/-- Every prime power exposed by accepted partial data is genuinely prime. -/
theorem checkPartial_prime {F : PartialFactorization}
    (h : checkPartial F = true) :
    ∀ e ∈ F.factors, Prime e.prime :=
  checkEntries_prime (checkedPartial_parts h).2.1

end Nat

end Hex
