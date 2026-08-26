/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor.Divisors
import HexPrimalityMathlib.Prime
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Divisors

/-! Correspondence between checked factor lists and `Nat.factorization`. -/

namespace Hex

namespace Nat

/-- Exponent stored for `p`, or zero when `p` is absent. -/
def factorExponent (F : Factorization) (p : Nat) : Nat :=
  (F.factors.find? fun e => e.prime == p).elim 0 (·.exponent)

/-- The listed primes, repeated according to their checked exponents. -/
def expandedFactors (F : Factorization) : List Nat :=
  F.factors.flatMap fun e => List.replicate e.exponent e.prime

private theorem expandedFactors_prod (F : Factorization) :
    (expandedFactors F).prod =
      (F.factors.map fun e => e.prime ^ e.exponent).prod := by
  unfold expandedFactors
  induction F.factors with
  | nil => simp
  | cons e entries ih => simp [ih]

private theorem prime_of_mem_expandedFactors (F : Factorization)
    (h : checkFactorization F = true) :
    ∀ p ∈ expandedFactors F, _root_.Nat.Prime p := by
  intro p hp
  simp only [expandedFactors, List.mem_flatMap, List.mem_replicate] at hp
  obtain ⟨e, he, _, rfl⟩ := hp
  exact prime_iff.mp (checkFactorization_prime h e he)

private theorem subject_ne_zero {F : Factorization}
    (h : checkFactorization F = true) : F.subject ≠ 0 := by
  have hp := h
  simp only [checkFactorization, Bool.and_eq_true, decide_eq_true_eq] at hp
  omega

private theorem factorization_entry_eq (F : Factorization)
    (h : checkFactorization F = true) (e : PrimePower) (he : e ∈ F.factors) :
    F.subject.factorization e.prime = e.exponent := by
  have hp : _root_.Nat.Prime e.prime :=
    prime_iff.mp (checkFactorization_prime h e he)
  have hn := subject_ne_zero h
  apply Nat.le_antisymm
  · have hdvd : e.prime ^ (F.subject.factorization e.prime) ∣ F.subject :=
      (hp.pow_dvd_iff_le_factorization hn).2 (Nat.le_refl _)
    exact (checkFactorization_multiplicity h he).1 hdvd
  · apply (hp.pow_dvd_iff_le_factorization hn).1
    exact (checkFactorization_multiplicity h he).2 (Nat.le_refl _)

/-- The checked list and Mathlib's finitely-supported factorization agree
pointwise. -/
theorem factorization_eq (F : Factorization)
    (h : checkFactorization F = true) (p : Nat) :
    F.subject.factorization p = factorExponent F p := by
  unfold factorExponent
  cases hfind : F.factors.find? (fun e => e.prime == p) with
  | some e =>
    simp only [hfind, Option.elim_some]
    have he := List.mem_of_find?_eq_some hfind
    have hep : e.prime = p := by
      simpa using List.find?_some hfind
    subst p
    exact factorization_entry_eq F h e he
  | none =>
    simp only [hfind, Option.elim_none]
    by_cases hp : _root_.Nat.Prime p
    · apply Nat.factorization_eq_zero_of_not_dvd
      intro hdiv
      obtain ⟨e, he, hep⟩ :=
        (checkFactorization_primeSupport h (prime_iff.mpr hp)).mp hdiv
      have hreject := List.find?_eq_none.mp hfind e he
      simp [hep] at hreject
    · exact Nat.factorization_eq_zero_of_not_prime F.subject hp

/-- Mathlib's factor list is the multiset obtained by repeating each checked
prime according to its exponent. -/
theorem factors_eq (F : Factorization) (h : checkFactorization F = true) :
    (F.subject.primeFactorsList : Multiset Nat) = expandedFactors F := by
  apply Multiset.coe_eq_coe.mpr
  exact (Nat.primeFactorsList_unique
    (expandedFactors_prod F |>.trans (checkFactorization_prod h))
    (prime_of_mem_expandedFactors F h)).symm

/-- A listed exponent is exactly Mathlib's multiplicity. -/
theorem factorization_entry (F : Factorization)
    (h : checkFactorization F = true) (e : PrimePower) (he : e ∈ F.factors) :
    F.subject.factorization e.prime = e.exponent :=
  factorization_entry_eq F h e he

/-- An absent prime has zero Mathlib multiplicity. -/
theorem factorization_absent (F : Factorization)
    (h : checkFactorization F = true) {p : Nat} (_hp : _root_.Nat.Prime p)
    (hmem : ∀ e ∈ F.factors, e.prime ≠ p) :
    F.subject.factorization p = 0 := by
  rw [factorization_eq F h]
  unfold factorExponent
  rw [List.find?_eq_none.mpr]
  · rfl
  · intro e he
    simpa using hmem e he

/-- The checked divisor enumeration is Mathlib's divisor finset. -/
theorem divisors_eq {n : Nat} (F : CheckedFactorization n) :
    (divisors F).toList.toFinset = n.divisors := by
  have hn : n ≠ 0 := by
    have hv := F.valid
    simp only [checkFactorization, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact (F.subject_eq ▸ hv.1.1).ne'
  ext d
  simp only [List.mem_toFinset, Hex.Nat.mem_divisors F,
    _root_.Nat.mem_divisors]
  exact ⟨fun hd => ⟨hd, hn⟩, And.left⟩

/-- The checked totient agrees with Mathlib's Euler totient. -/
theorem totient_eq {n : Nat} (F : CheckedFactorization n) :
    totient F = _root_.Nat.totient n := by
  rw [Hex.Nat.totient, _root_.Nat.totient]
  rw [← List.toFinset_card_of_nodup
    (List.nodup_range.filter (fun a => decide (Nat.Coprime a n)))]
  rw [List.toFinset_filter, List.toFinset_range]
  simp [_root_.Nat.coprime_comm]

/-- The checked generalized divisor sum is the corresponding sum over
Mathlib's divisor finset. -/
theorem sigma_eq {n k : Nat} (F : CheckedFactorization n) :
    sigma F k = ∑ d ∈ n.divisors, d ^ k := by
  rw [sigma_eq_sum, ← List.sum_toFinset _ (divisors_nodup F), divisors_eq F]

/-- The checked radical is Mathlib's product of the distinct prime factors. -/
theorem radical_eq {n : Nat} (F : CheckedFactorization n) :
    radical F = ∏ p ∈ n.primeFactors, p := by
  have hn : n ≠ 0 := by
    have hv := F.valid
    simp only [checkFactorization, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact (F.subject_eq ▸ hv.1.1).ne'
  have hset : (F.raw.factors.map fun e => e.prime).toFinset = n.primeFactors := by
    ext p
    simp only [List.mem_toFinset, List.mem_map, Nat.mem_primeFactors_of_ne_zero hn]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨prime_iff.mp (checkFactorization_prime F.valid e he),
        by simpa [F.subject_eq] using
          (checkFactorization_primeSupport F.valid
            (checkFactorization_prime F.valid e he)).mpr ⟨e, he, rfl⟩⟩
    · rintro ⟨hp, hpn⟩
      obtain ⟨e, he, hep⟩ :=
        (checkFactorization_primeSupport F.valid (prime_iff.mpr hp)).mp
          (by simpa [F.subject_eq] using hpn)
      exact ⟨e, he, hep⟩
  have hnodup : (F.raw.factors.map fun e => e.prime).Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    simpa only [List.pairwise_map] using
      (checkFactorization_sorted F.valid).imp
        (fun hlt => Nat.ne_of_lt hlt)
  rw [radical]
  calc
    (F.raw.factors.map fun e => e.prime).prod =
        (F.raw.factors.map fun e => e.prime).toFinset.prod id := by
      symm
      simpa [Function.comp_def] using
        List.prod_toFinset (fun p : Nat => p) hnodup
    _ = ∏ p ∈ n.primeFactors, p := by simp [hset]

/-- Mathlib recognizes the computed squarefree part as squarefree. -/
theorem squarefreePart_mathlib {n : Nat} (F : CheckedFactorization n) :
    Squarefree (squarefreePart F) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro q hq hq2
  have hn : 0 < n := by
    have hv := F.valid
    simp only [checkFactorization, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact F.subject_eq ▸ hv.1.1
  have hd : 0 < squareDivisor F := by
    apply Nat.pos_of_ne_zero
    intro hd0
    have hzero : 0 ∣ n := by
      simpa [hd0] using (squareDivisor_spec F).1
    exact hn.ne' (Nat.eq_zero_of_zero_dvd hzero)
  have hbig : (q * squareDivisor F) ^ 2 ∣ n := by
    have hmul : (q * squareDivisor F) ^ 2 ∣
        squarefreePart F * squareDivisor F ^ 2 := by
      obtain ⟨t, ht⟩ := hq2
      refine ⟨t, ?_⟩
      rw [ht]
      simp [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    rw [squarefreePart_mul_square F] at hmul
    exact hmul
  have hqd := (squareDivisor_spec F).2 (q * squareDivisor F) hbig
  have hle := Nat.le_of_dvd hd hqd
  have htwo := Nat.mul_le_mul_right (squareDivisor F) hq.two_le
  omega

/-- The computed root is the greatest root of a square divisor, in Mathlib's
order-theoretic vocabulary. -/
theorem squareDivisor_mathlib {n : Nat} (F : CheckedFactorization n) :
    IsGreatest {d : Nat | d ^ 2 ∣ n} (squareDivisor F) := by
  have hn : 0 < n := by
    have hv := F.valid
    simp only [checkFactorization, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact F.subject_eq ▸ hv.1.1
  have hd : 0 < squareDivisor F := by
    apply Nat.pos_of_ne_zero
    intro hd0
    have hzero : 0 ∣ n := by
      simpa [hd0] using (squareDivisor_spec F).1
    exact hn.ne' (Nat.eq_zero_of_zero_dvd hzero)
  refine ⟨(squareDivisor_spec F).1, ?_⟩
  intro d hdvd
  exact Nat.le_of_dvd hd ((squareDivisor_spec F).2 d hdvd)

end Nat

end Hex
