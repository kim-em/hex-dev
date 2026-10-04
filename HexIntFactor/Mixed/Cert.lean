/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Partial
public import HexECPP.Cert

public section

/-! Optional mixed primality certificates. Arithmetic replay is unconditional;
number-theoretic facts explicitly require ECPP checker soundness. -/

namespace Hex.Nat.Mixed

/-- Subject-bound primality evidence, without a backward Primality dependency. -/
inductive Evidence where
  | legacy (cert : Hex.Nat.PrimeCert)
  | ecpp (cert : Hex.ECPP.Cert)
deriving Repr

/-- Check evidence at the explicitly proposed base. -/
@[expose] def checkEvidence (p : Nat) : Evidence → Bool
  | .legacy c => decide (c.subject = p) && Hex.Nat.checkPrime c
  | .ecpp c => Hex.ECPP.checkAt p c

/-- The ECPP soundness obligation discharged by the mathematical companion. -/
@[expose] def Soundness : Prop :=
  ∀ (n : Nat) (c : Hex.ECPP.Cert), Hex.ECPP.checkAt n c = true → Hex.Nat.Prime n

/-- Accepted evidence proves primality under the explicit ECPP obligation. -/
theorem prime_of_checkEvidence (soundness : Soundness) {p : Nat} {c : Evidence}
    (h : checkEvidence p c = true) : Hex.Nat.Prime p := by
  cases c with
  | legacy c =>
      simp only [checkEvidence, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [← h.1]
      exact Hex.Nat.prime_of_checkPrime h.2
  | ecpp c => exact soundness p c h

/-- A proposed base, positive multiplicity and bound primality evidence. -/
structure PrimePower where
  /-- The base against which evidence is checked. -/
  prime : Nat
  /-- Positive multiplicity. -/
  exponent : Nat
  /-- Legacy or ECPP evidence for this exact base. -/
  cert : Evidence
deriving Repr

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
  | [e] => decide (0 < e.exponent) && checkEvidence e.prime e.cert
  | e :: next :: rest =>
      decide (0 < e.exponent) && checkEvidence e.prime e.cert &&
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

/-- Accepted entries have strictly positive multiplicities. -/
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

/-- Accepted bases are prime under ECPP soundness. -/
theorem checkEntries_prime (soundness : Soundness) : ∀ {l : List PrimePower},
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
          exact prime_of_checkEvidence soundness h.2
      | cons next rest =>
          intro h x hx
          simp only [checkEntries, Bool.and_eq_true, decide_eq_true_eq] at h
          rcases List.mem_cons.mp hx with rfl | hx
          · exact prime_of_checkEvidence soundness h.1.1.2
          · exact ih h.2 x hx

/-- Accepted bases are strictly ascending and therefore distinct. -/
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
theorem checkFactorization_prime (soundness : Soundness) {F : Factorization}
    (h : checkFactorization F = true) :
    ∀ e ∈ F.factors, Prime e.prime :=
  checkEntries_prime soundness (checked_parts h).2.1

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
theorem checkFactorization_primeSupport (soundness : Soundness) {F : Factorization}
    (h : checkFactorization F = true) {q : Nat} (hq : Prime q) :
    q ∣ F.subject ↔ ∃ e ∈ F.factors, e.prime = q := by
  rw [← checkFactorization_prod h]
  exact prime_dvd_product_iff hq (checkFactorization_prime soundness h)
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
theorem checkFactorization_multiplicity (soundness : Soundness) {F : Factorization}
    (h : checkFactorization F = true) {e : PrimePower} (he : e ∈ F.factors)
    {k : Nat} : e.prime ^ k ∣ F.subject ↔ k ≤ e.exponent := by
  rw [← checkFactorization_prod h]
  exact multiplicity_list (checkFactorization_sorted h)
    (checkFactorization_prime soundness h) (checkFactorization_exponent h) he

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

/-- A partial factorization accepted by the checker has positive subject. -/
theorem checkPartial_pos {F : PartialFactorization}
    (h : checkPartial F = true) : 0 < F.subject :=
  (checkedPartial_parts h).1

/-- The subject indexed by checked partial factorization data is positive. -/
theorem CheckedPartialFactorization.pos {n : Nat}
    (F : CheckedPartialFactorization n) : 0 < n := by
  rw [← F.subject_eq]
  exact checkPartial_pos F.valid

/-- Accepted partial data reconstructs its subject exactly. -/
theorem checkPartial_prod {F : PartialFactorization}
    (h : checkPartial F = true) :
    (F.factors.map (fun e => e.prime ^ e.exponent)).prod * F.residual =
      F.subject := by
  obtain ⟨acc, hacc, hfinal⟩ := (checkedPartial_parts h).2.2
  obtain ⟨hprod, hmul⟩ := Internal.factorProduct_parts hacc hfinal
  simpa [hprod] using hmul.symm

/-- Every prime power exposed by accepted partial data is genuinely prime. -/
theorem checkPartial_prime (soundness : Soundness) {F : PartialFactorization}
    (h : checkPartial F = true) :
    ∀ e ∈ F.factors, Prime e.prime :=
  checkEntries_prime soundness (checkedPartial_parts h).2.1

/-- Every listed exponent in accepted partial data is positive. -/
theorem checkPartial_exponent {F : PartialFactorization}
    (h : checkPartial F = true) :
    ∀ e ∈ F.factors, 0 < e.exponent :=
  checkEntries_positive (checkedPartial_parts h).2.1

/-- Listed bases in accepted partial data are strictly ascending. -/
theorem checkPartial_sorted {F : PartialFactorization}
    (h : checkPartial F = true) :
    F.factors.Pairwise (fun a b => a.prime < b.prime) :=
  checkEntries_pairwise (checkedPartial_parts h).2.1

/-- A checked partial factorization with residual one is already a complete
factorization certificate; no second checker replay is needed. -/
theorem checkFactorization_of_checkPartial {F : PartialFactorization}
    (h : checkPartial F = true) (hr : F.residual = 1) :
    checkFactorization ⟨F.subject, F.factors⟩ = true := by
  obtain ⟨hsubject, hentries, acc, hproduct, hresidual⟩ :=
    checkedPartial_parts h
  have hacc : acc = F.subject := by
    obtain ⟨_, heq⟩ := Internal.factorProduct_parts hproduct hresidual
    simpa [hr] using heq.symm
  simp only [checkFactorization, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hsubject, hentries⟩, hacc ▸ hproduct⟩

/-- Replay complete data at a caller's requested subject. -/
@[expose] def checkAt (n : Nat) (F : Factorization) : Bool :=
  decide (F.subject = n) && checkFactorization F

/-- Replay partial data at a caller's requested subject. -/
@[expose] def checkPartialAt (n : Nat) (F : PartialFactorization) : Bool :=
  decide (F.subject = n) && checkPartial F

/-- Partial prime support also includes prime divisors of the residual. -/
theorem checkPartial_primeSupport (soundness : Soundness) {F : PartialFactorization}
    (h : checkPartial F = true) {q : Nat} (hq : Hex.Nat.Prime q) :
    q ∣ F.subject ↔ (∃ e ∈ F.factors, e.prime = q) ∨ q ∣ F.residual := by
  rw [← checkPartial_prod h, hq.dvd_mul]
  rw [prime_dvd_product_iff hq (checkPartial_prime soundness h)
    (checkPartial_exponent h)]

/-- A partial listed exponent is exact if the residual has no further copy. -/
theorem checkPartial_multiplicity (soundness : Soundness) {F : PartialFactorization}
    (h : checkPartial F = true) {e : PrimePower} (he : e ∈ F.factors)
    (hr : ¬e.prime ∣ F.residual) {k : Nat} :
    e.prime ^ k ∣ F.subject ↔ k ≤ e.exponent := by
  rw [← checkPartial_prod h]
  have hp := checkPartial_prime soundness h e he
  have hcop : Nat.Coprime (e.prime ^ k) F.residual := by
    simpa using Nat.Coprime.pow k 1 (hp.coprime_of_not_dvd hr)
  have hm := multiplicity_list (checkPartial_sorted h)
    (checkPartial_prime soundness h) (checkPartial_exponent h) he (k := k)
  constructor
  · intro hd
    apply hm.mp
    rw [Nat.mul_comm] at hd
    exact hcop.dvd_of_dvd_mul_left hd
  · intro hk
    exact Nat.dvd_trans (hm.mpr hk) (Nat.dvd_mul_right _ _)

/-- A listed prime power divides the partial subject even without primality. -/
theorem checkPartial_dvd {F : PartialFactorization}
    (h : checkPartial F = true) {e : PrimePower} (he : e ∈ F.factors) :
    e.prime ^ e.exponent ∣ F.subject := by
  have aux : ∀ (fs : List PrimePower), e ∈ fs →
      e.prime ^ e.exponent ∣ (fs.map fun x => x.prime ^ x.exponent).prod := by
    intro fs
    induction fs with
    | nil => simp
    | cons f fs ih =>
        intro hm
        simp only [List.map_cons, List.prod_cons]
        rcases List.mem_cons.mp hm with rfl | hm
        · exact Nat.dvd_mul_right _ _
        · exact Nat.dvd_trans (ih hm) (Nat.dvd_mul_left _ _)
  rw [← checkPartial_prod h]
  exact Nat.dvd_trans (aux F.factors he) (Nat.dvd_mul_right _ _)

/-- Embed a legacy entry without changing its base or multiplicity. -/
@[expose] def PrimePower.ofLegacy (e : Hex.Nat.PrimePower) : PrimePower :=
  ⟨e.prime, e.exponent, .legacy e.cert⟩

/-- Embed raw legacy complete data in the mixed representation. -/
@[expose] def Factorization.ofLegacy (F : Hex.Nat.Factorization) : Factorization :=
  ⟨F.subject, F.factors.map PrimePower.ofLegacy⟩

/-- Embed raw legacy partial data in the mixed representation. -/
@[expose] def PartialFactorization.ofLegacy (F : Hex.Nat.PartialFactorization) : PartialFactorization :=
  ⟨F.subject, F.factors.map PrimePower.ofLegacy, F.residual⟩

private theorem entries_legacy (fs : List Hex.Nat.PrimePower) :
    checkEntries (fs.map PrimePower.ofLegacy) = Hex.Nat.checkEntries fs := by
  induction fs with
  | nil => rfl
  | cons e fs ih =>
      cases fs with
      | nil => simp [checkEntries, Hex.Nat.checkEntries, PrimePower.ofLegacy,
          checkEvidence, Hex.Nat.PrimePower.prime]
      | cons f fs =>
          simp only [List.map_cons, checkEntries, Hex.Nat.checkEntries,
            PrimePower.ofLegacy, checkEvidence, Hex.Nat.PrimePower.prime,
            decide_true, Bool.true_and] at ih ⊢
          rw [ih]
          congr 1

private theorem product_legacy (bound : Nat) (fs : List Hex.Nat.PrimePower) (acc : Nat) :
    factorProduct bound (fs.map PrimePower.ofLegacy) acc = Hex.Nat.factorProduct bound fs acc := by
  induction fs generalizing acc with
  | nil => rfl
  | cons e fs ih =>
      simp only [List.map_cons, factorProduct, Hex.Nat.factorProduct, PrimePower.ofLegacy]
      split <;> simp_all

/-- Complete legacy checker acceptance is preserved exactly. -/
theorem checkFactorization_ofLegacy (F : Hex.Nat.Factorization) :
    checkFactorization (Factorization.ofLegacy F) = Hex.Nat.checkFactorization F := by
  simp [checkFactorization, Hex.Nat.checkFactorization, Factorization.ofLegacy,
    entries_legacy, product_legacy]
  congr 1

/-- Partial legacy checker acceptance is preserved exactly. -/
theorem checkPartial_ofLegacy (F : Hex.Nat.PartialFactorization) :
    checkPartial (PartialFactorization.ofLegacy F) = Hex.Nat.checkPartial F := by
  simp [checkPartial, Hex.Nat.checkPartial, PartialFactorization.ofLegacy,
    entries_legacy, product_legacy]
  congr 1

/-- Embed checked legacy complete data, preserving the requested subject. -/
def CheckedFactorization.ofLegacy {n : Nat} (F : Hex.Nat.CheckedFactorization n) :
    CheckedFactorization n :=
  ⟨Factorization.ofLegacy F.raw, F.subject_eq, by rw [checkFactorization_ofLegacy]; exact F.valid⟩

/-- Embed checked legacy partial data, preserving the requested subject. -/
def CheckedPartialFactorization.ofLegacy {n : Nat} (F : Hex.Nat.CheckedPartialFactorization n) :
    CheckedPartialFactorization n :=
  ⟨PartialFactorization.ofLegacy F.raw, F.subject_eq, by rw [checkPartial_ofLegacy]; exact F.valid⟩

/-- Extract an entry only if it carries correctly bound legacy evidence. -/
def PrimePower.toLegacy (e : PrimePower) : Option Hex.Nat.PrimePower :=
  match e.cert with
  | .ecpp _ => none
  | .legacy c => if c.subject = e.prime then some ⟨e.exponent, c⟩ else none

/-- Explicit legacy conversion rejects ECPP and replays the legacy checker. -/
def CheckedFactorization.toLegacy {n : Nat} (F : CheckedFactorization n) :
    Option (Hex.Nat.CheckedFactorization n) := do
  let fs ← F.raw.factors.mapM PrimePower.toLegacy
  let raw : Hex.Nat.Factorization := ⟨F.raw.subject, fs⟩
  if hs : raw.subject = n then
    if hv : Hex.Nat.checkFactorization raw = true then some ⟨raw, hs, hv⟩ else none
  else none

/-- Explicit partial conversion rejects ECPP and replays the legacy checker. -/
def CheckedPartialFactorization.toLegacy {n : Nat} (F : CheckedPartialFactorization n) :
    Option (Hex.Nat.CheckedPartialFactorization n) := do
  let fs ← F.raw.factors.mapM PrimePower.toLegacy
  let raw : Hex.Nat.PartialFactorization := ⟨F.raw.subject, fs, F.raw.residual⟩
  if hs : raw.subject = n then
    if hv : Hex.Nat.checkPartial raw = true then some ⟨raw, hs, hv⟩ else none
  else none

end Hex.Nat.Mixed
