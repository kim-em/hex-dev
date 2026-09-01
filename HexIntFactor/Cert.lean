/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Cert

public section

/-!
Kernel-replayable certificates for complete natural-number factorizations.

The checker treats every field as untrusted.  In particular the prime stored
by an entry is definitionally the subject of its primality certificate, and
the product accumulator stops before constructing a value above the claimed
subject.
-/

namespace Hex

namespace Nat

/-- One prime power in a factorization. -/
structure PrimePower where
  /-- The positive multiplicity of the prime. -/
  exponent : Nat
  /-- A certificate for the base. -/
  cert : PrimeCert
deriving Repr

/-- The base of a prime-power entry. -/
@[expose]
def PrimePower.prime (e : PrimePower) : Nat := e.cert.subject

/-- A raw, untrusted complete factorization. -/
structure Factorization where
  /-- The number claimed to be factored. -/
  subject : Nat
  /-- Distinct prime powers, claimed in ascending order. -/
  factors : List PrimePower
deriving Repr

/-- Bounded product of a factor list. -/
@[expose]
def factorProduct (bound : Nat) : List PrimePower → Nat → Option Nat
  | [], acc => some acc
  | e :: rest, acc =>
      match boundedPowMul bound e.prime acc e.exponent with
      | none => none
      | some acc' => factorProduct bound rest acc'

/-- Structural and primality checks for the canonical factor list. -/
@[expose]
def checkEntries : List PrimePower → Bool
  | [] => true
  | [e] => decide (0 < e.exponent) && checkPrime e.cert
  | e :: next :: rest =>
      decide (0 < e.exponent) && checkPrime e.cert &&
        decide (e.prime < next.prime) && checkEntries (next :: rest)

/-- Accept or reject a complete factorization certificate. -/
@[expose]
def checkFactorization (F : Factorization) : Bool :=
  decide (0 < F.subject) && checkEntries F.factors &&
    decide (factorProduct F.subject F.factors 1 = some F.subject)

/-- Accepted factorization data tied to the subject requested by its caller. -/
structure CheckedFactorization (n : Nat) where
  /-- The raw certificate. -/
  raw : Factorization
  /-- The certificate is about `n`. -/
  subject_eq : raw.subject = n
  /-- Full checker replay succeeds. -/
  valid : checkFactorization raw = true

/-- On success, the factor accumulator computes the ordinary product. -/
theorem factorProduct_eq {bound : Nat} :
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

namespace Internal

/-- Characterize a successful factor-list fold followed by one bounded
residual multiplication. This is the shared proof boundary for complete and
partial factorization checkers. -/
theorem factorProduct_parts {bound : Nat} {entries : List PrimePower}
    {initial folded residual result : Nat}
    (hfold : factorProduct bound entries initial = some folded)
    (hresidual : boundedPowMul bound residual folded 1 = some result) :
    folded = initial *
        (entries.map fun e => e.prime ^ e.exponent).prod ∧
      result = folded * residual := by
  exact ⟨factorProduct_eq entries initial folded hfold,
    by simpa using boundedPowMul_eq 1 folded result hresidual⟩

end Internal

theorem checkEntries_positive : ∀ {l : List PrimePower},
    checkEntries l = true → ∀ e ∈ l, 0 < e.exponent := by
  intro l
  induction l with
  | nil => simp
  | cons e rest ih =>
      cases rest with
      | nil =>
          intro h x hx
          simp only [checkEntries, Bool.and_eq_true, decide_eq_true_eq] at h
          simpa using List.mem_singleton.mp hx ▸ h.1
      | cons next rest =>
          intro h x hx
          simp only [checkEntries, Bool.and_eq_true, decide_eq_true_eq] at h
          rcases List.mem_cons.mp hx with rfl | hx
          · exact h.1.1.1
          · exact ih h.2 x hx

theorem checkEntries_prime : ∀ {l : List PrimePower},
    checkEntries l = true → ∀ e ∈ l, Prime e.prime := by
  intro l
  induction l with
  | nil => simp
  | cons e rest ih =>
      cases rest with
      | nil =>
          intro h x hx
          simp only [checkEntries, Bool.and_eq_true, decide_eq_true_eq] at h
          have hx' := List.mem_singleton.mp hx
          subst x
          exact prime_of_checkPrime h.2
      | cons next rest =>
          intro h x hx
          simp only [checkEntries, Bool.and_eq_true, decide_eq_true_eq] at h
          rcases List.mem_cons.mp hx with rfl | hx
          · exact prime_of_checkPrime h.1.1.2
          · exact ih h.2 x hx

theorem checkEntries_pairwise : ∀ {l : List PrimePower},
    checkEntries l = true → l.Pairwise (fun a b => a.prime < b.prime) := by
  intro l
  induction l with
  | nil => simp
  | cons e rest ih =>
      cases rest with
      | nil => simp
      | cons next rest =>
          intro h
          simp only [checkEntries, Bool.and_eq_true, decide_eq_true_eq] at h
          have htail := ih h.2
          rw [List.pairwise_cons]
          refine ⟨?_, htail⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact h.1.2
          · exact Nat.lt_trans h.1.2 ((List.pairwise_cons.mp htail).1 x hx)

private theorem checked_parts {F : Factorization}
    (h : checkFactorization F = true) :
    0 < F.subject ∧ checkEntries F.factors = true ∧
      factorProduct F.subject F.factors 1 = some F.subject := by
  simpa [checkFactorization, Bool.and_eq_true, and_assoc] using h

/-- A complete factorization accepted by the checker has positive subject. -/
theorem checkFactorization_pos {F : Factorization}
    (h : checkFactorization F = true) : 0 < F.subject :=
  (checked_parts h).1

/-- The subject indexed by checked complete factorization data is positive. -/
theorem CheckedFactorization.pos {n : Nat} (F : CheckedFactorization n) :
    0 < n := by
  rw [← F.subject_eq]
  exact checkFactorization_pos F.valid

/-- The checked prime powers multiply to the claimed subject. -/
theorem checkFactorization_prod {F : Factorization}
    (h : checkFactorization F = true) :
    (F.factors.map (fun e => e.prime ^ e.exponent)).prod = F.subject := by
  have hp := factorProduct_eq F.factors 1 F.subject (checked_parts h).2.2
  simpa using hp.symm

/-- Every listed base is prime. -/
theorem checkFactorization_prime {F : Factorization}
    (h : checkFactorization F = true) :
    ∀ e ∈ F.factors, Prime e.prime :=
  checkEntries_prime (checked_parts h).2.1

/-- Every listed exponent is positive. -/
theorem checkFactorization_exponent {F : Factorization}
    (h : checkFactorization F = true) :
    ∀ e ∈ F.factors, 0 < e.exponent :=
  checkEntries_positive (checked_parts h).2.1

/-- Listed bases are strictly ascending. -/
theorem checkFactorization_sorted {F : Factorization}
    (h : checkFactorization F = true) :
    F.factors.Pairwise (fun a b => a.prime < b.prime) :=
  checkEntries_pairwise (checked_parts h).2.1

namespace Internal

/-- A prime dividing a product of certified prime powers is the base of one
of the entries. Exponents need not be positive for this direction. -/
theorem prime_mem_of_dvd_prod {q : Nat} (hq : Prime q) :
    ∀ {entries : List PrimePower},
      (∀ e ∈ entries, Prime e.prime) →
      q ∣ (entries.map fun e => e.prime ^ e.exponent).prod →
      ∃ e ∈ entries, e.prime = q := by
  intro entries hprime hdvd
  induction entries with
  | nil =>
      exact absurd (Nat.dvd_one.mp hdvd) hq.ne_one
  | cons e rest ih =>
      simp only [List.map_cons, List.prod_cons] at hdvd
      rcases hq.dvd_mul.mp hdvd with he | hrest
      · have hbase := hq.dvd_of_dvd_pow he
        rcases (hprime e (by simp)).2 q hbase with hq1 | heq
        · exact absurd hq1 hq.ne_one
        · exact ⟨e, by simp, heq.symm⟩
      · obtain ⟨e, he, heq⟩ := ih
          (fun e he => hprime e (by simp [he])) hrest
        exact ⟨e, by simp [he], heq⟩

/-- The first prime in a strictly ordered list of prime powers does not divide
the product represented by its tail. -/
theorem not_dvd_tail_prod {entry : PrimePower} {rest : List PrimePower}
    (hp : Prime entry.prime) (htail : ∀ e ∈ rest, Prime e.prime)
    (hsorted : (entry :: rest).Pairwise fun a b => a.prime < b.prime) :
    ¬entry.prime ∣ (rest.map fun e => e.prime ^ e.exponent).prod := by
  intro hdvd
  obtain ⟨e, he, heq⟩ := prime_mem_of_dvd_prod hp htail hdvd
  have hlt := (List.pairwise_cons.mp hsorted).1 e he
  rw [heq] at hlt
  exact Nat.lt_irrefl _ hlt

end Internal

private theorem prime_eq_of_dvd {p q : Nat} (hp : Prime p) (hq : Prime q)
    (h : p ∣ q) : p = q := by
  rcases hq.2 p h with h | h
  · exact absurd h hp.ne_one
  · exact h

private theorem prime_dvd_product_iff {q : Nat} (hq : Prime q) :
    ∀ {l : List PrimePower}, (∀ e ∈ l, Prime e.prime) →
      (∀ e ∈ l, 0 < e.exponent) →
      (q ∣ (l.map fun e => e.prime ^ e.exponent).prod ↔
        ∃ e ∈ l, e.prime = q) := by
  intro l hprime hpos
  induction l with
  | nil =>
      simp [hq.ne_one]
  | cons e rest ih =>
      rw [List.map_cons, List.prod_cons, hq.dvd_mul]
      have he := hprime e (List.mem_cons_self)
      have hrest : ∀ x ∈ rest, Prime x.prime := by
        intro x hx
        exact hprime x (List.mem_cons_of_mem e hx)
      have hrestPos : ∀ x ∈ rest, 0 < x.exponent := by
        intro x hx
        exact hpos x (List.mem_cons_of_mem e hx)
      rw [ih hrest hrestPos]
      constructor
      · intro h
        rcases h with h | h
        · have hd := hq.dvd_of_dvd_pow h
          exact ⟨e, List.mem_cons_self, (prime_eq_of_dvd hq he hd).symm⟩
        · obtain ⟨x, hx, heq⟩ := h
          exact ⟨x, List.mem_cons_of_mem e hx, heq⟩
      · rintro ⟨x, hx, heq⟩
        rcases List.mem_cons.mp hx with hx | hx
        · subst x
          left
          rw [heq]
          obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero
            (Nat.ne_of_gt (hpos e List.mem_cons_self))
          rw [hj]
          exact ⟨q ^ j, by simp [Nat.pow_succ, Nat.mul_comm]⟩
        · exact Or.inr ⟨x, hx, heq⟩

/-- The listed bases are exactly the prime support of the subject. -/
theorem checkFactorization_primeSupport {F : Factorization}
    (h : checkFactorization F = true) {q : Nat} (hq : Prime q) :
    q ∣ F.subject ↔ ∃ e ∈ F.factors, e.prime = q := by
  rw [← checkFactorization_prod h]
  exact prime_dvd_product_iff hq (checkFactorization_prime h)
    (checkFactorization_exponent h)

private theorem multiplicity_list :
    ∀ {l : List PrimePower} {target : PrimePower},
      l.Pairwise (fun a b => a.prime < b.prime) →
      (∀ e ∈ l, Prime e.prime) →
      (∀ e ∈ l, 0 < e.exponent) → target ∈ l → ∀ {k : Nat},
        target.prime ^ k ∣
            (l.map fun e => e.prime ^ e.exponent).prod ↔
          k ≤ target.exponent := by
  intro l
  induction l with
  | nil =>
      intro target _ _ _ hmem
      cases hmem
  | cons head tail ih =>
      intro target hsorted hprime hpos hmem k
      rw [List.pairwise_cons] at hsorted
      have hheadPrime := hprime head List.mem_cons_self
      have htailPrime : ∀ e ∈ tail, Prime e.prime := by
        intro e he
        exact hprime e (List.mem_cons_of_mem head he)
      have htailPos : ∀ e ∈ tail, 0 < e.exponent := by
        intro e he
        exact hpos e (List.mem_cons_of_mem head he)
      rcases List.mem_cons.mp hmem with rfl | hmem
      · simp only [List.map_cons, List.prod_cons]
        let rest := (tail.map fun e => e.prime ^ e.exponent).prod
        have hnot : ¬target.prime ∣ rest := by
          intro hdvd
          obtain ⟨e, he, heq⟩ :=
            (prime_dvd_product_iff hheadPrime htailPrime htailPos).mp hdvd
          have hlt := hsorted.1 e he
          rw [heq] at hlt
          exact (Nat.lt_irrefl _ hlt)
        constructor
        · intro hdvd
          by_cases hle : k ≤ target.exponent
          · exact hle
          · exfalso
            have hlt : target.exponent < k := Nat.lt_of_not_ge hle
            have hexp_le : target.exponent ≤ k := Nat.le_of_lt hlt
            have hk : target.exponent + (k - target.exponent) = k :=
            Nat.add_sub_of_le hexp_le
            have hpow : target.prime ^ target.exponent *
                  target.prime ^ (k - target.exponent) ∣
                target.prime ^ target.exponent * rest := by
              rw [← Nat.pow_add, hk]
              exact hdvd
            have hremain : target.prime ^ (k - target.exponent) ∣ rest :=
              (Nat.mul_dvd_mul_iff_left
                (Nat.pow_pos hheadPrime.pos)).mp hpow
            apply hnot
            exact Nat.dvd_of_pow_dvd (by omega) hremain
        · intro hle
          exact Nat.dvd_trans (Nat.pow_dvd_pow _ hle)
            (Nat.dvd_mul_right _ rest)
      · simp only [List.map_cons, List.prod_cons]
        have htargetPrime := htailPrime target hmem
        have hne : target.prime ≠ head.prime := by
          intro heq
          have hlt := hsorted.1 target hmem
          rw [heq] at hlt
          exact Nat.lt_irrefl _ hlt
        have hnotDvd : ¬target.prime ∣ head.prime := by
          intro hdvd
          exact hne (prime_eq_of_dvd htargetPrime hheadPrime hdvd)
        have hcop : Nat.Coprime (target.prime ^ k)
            (head.prime ^ head.exponent) :=
          Nat.Coprime.pow k head.exponent
            (htargetPrime.coprime_of_not_dvd hnotDvd)
        rw [← ih hsorted.2 htailPrime htailPos hmem]
        constructor
        · exact hcop.dvd_of_dvd_mul_left
        · intro hdvd
          exact Nat.dvd_trans hdvd (Nat.dvd_mul_left _ _)

/-- A listed prime power occurs with exactly its claimed multiplicity. -/
theorem checkFactorization_multiplicity {F : Factorization}
    (h : checkFactorization F = true) {e : PrimePower} (he : e ∈ F.factors)
    {k : Nat} : e.prime ^ k ∣ F.subject ↔ k ≤ e.exponent := by
  rw [← checkFactorization_prod h]
  exact multiplicity_list (checkFactorization_sorted h)
    (checkFactorization_prime h) (checkFactorization_exponent h) he

end Nat

end Hex
