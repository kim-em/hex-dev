/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor.Divisors
import HexPrimalityMathlib.Prime
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Divisors

/-! Correspondence between checked factor lists and `Nat.factorization`. -/

namespace Hex

namespace Nat

/-- The listed primes, repeated according to their checked exponents. -/
private def expandedFactors (F : Factorization) : List Nat :=
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

private theorem expandedFactors_sorted (F : Factorization)
    (h : checkFactorization F = true) :
    (expandedFactors F).SortedLE := by
  apply List.Pairwise.sortedLE
  rw [expandedFactors, List.pairwise_flatMap]
  constructor
  · intro e he
    exact List.pairwise_replicate_of_refl
  · apply (checkFactorization_sorted h).imp
    intro e f hef x hx y hy
    simp only [List.mem_replicate] at hx hy
    rcases hx with ⟨_, rfl⟩
    rcases hy with ⟨_, rfl⟩
    exact Nat.le_of_lt hef

/-- A listed exponent is exactly Mathlib's multiplicity. -/
theorem factorization_entry (F : Factorization)
    (h : checkFactorization F = true) (e : PrimePower) (he : e ∈ F.factors) :
    F.subject.factorization e.prime = e.exponent := by
  have hp : _root_.Nat.Prime e.prime :=
    prime_iff.mp (checkFactorization_prime h e he)
  have hn := (checkFactorization_pos h).ne'
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
    F.subject.factorization p =
      (F.factors.find? fun e => e.prime == p).elim 0 (·.exponent) := by
  cases hfind : F.factors.find? (fun e => e.prime == p) with
  | some e =>
    simp only [Option.elim_some]
    have he := List.mem_of_find?_eq_some hfind
    have hep : e.prime = p := by
      simpa using List.find?_some hfind
    subst p
    exact factorization_entry F h e he
  | none =>
    simp only [Option.elim_none]
    by_cases hp : _root_.Nat.Prime p
    · apply Nat.factorization_eq_zero_of_not_dvd
      intro hdiv
      obtain ⟨e, he, hep⟩ :=
        (checkFactorization_primeSupport h (prime_iff.mpr hp)).mp hdiv
      have hreject := List.find?_eq_none.mp hfind e he
      simp [hep] at hreject
    · exact Nat.factorization_eq_zero_of_not_prime F.subject hp

/-- Pointwise factorization correspondence for checked data. -/
theorem CheckedFactorization.factorization_eq {n : Nat}
    (F : CheckedFactorization n) (p : Nat) :
    n.factorization p =
      (F.raw.factors.find? fun e => e.prime == p).elim 0 (·.exponent) := by
  calc
    n.factorization p = F.raw.subject.factorization p :=
      (congrArg (fun m => m.factorization p) F.subject_eq).symm
    _ = _ := Hex.Nat.factorization_eq F.raw F.valid p

/-- Mathlib's canonical sorted factor list is obtained by repeating each
checked prime according to its exponent. -/
theorem factors_eq (F : Factorization) (h : checkFactorization F = true) :
    F.subject.primeFactorsList =
      F.factors.flatMap fun e => List.replicate e.exponent e.prime := by
  change F.subject.primeFactorsList = expandedFactors F
  apply List.Perm.eq_of_sortedLE
  · exact Nat.primeFactorsList_sorted _
  · exact expandedFactors_sorted F h
  · exact (Nat.primeFactorsList_unique
      (expandedFactors_prod F |>.trans (checkFactorization_prod h))
      (prime_of_mem_expandedFactors F h)).symm

/-- Canonical factor-list correspondence for checked data. -/
theorem CheckedFactorization.primeFactorsList_eq {n : Nat}
    (F : CheckedFactorization n) :
    n.primeFactorsList =
      F.raw.factors.flatMap fun e => List.replicate e.exponent e.prime := by
  calc
    n.primeFactorsList = F.raw.subject.primeFactorsList :=
      (congrArg Nat.primeFactorsList F.subject_eq).symm
    _ = _ := factors_eq F.raw F.valid

/-- A base absent from the checked list has zero Mathlib multiplicity. -/
theorem factorization_absent (F : Factorization)
    (h : checkFactorization F = true) {p : Nat}
    (hmem : ∀ e ∈ F.factors, e.prime ≠ p) :
    F.subject.factorization p = 0 := by
  rw [factorization_eq F h]
  rw [List.find?_eq_none.mpr]
  · rfl
  · intro e he
    simpa using hmem e he

/-- The checked divisor enumeration is Mathlib's divisor finset. -/
theorem divisors_eq {n : Nat} (F : CheckedFactorization n) :
    (divisors F).toList.toFinset = n.divisors := by
  have hn : n ≠ 0 := F.pos.ne'
  ext d
  simp only [List.mem_toFinset, Hex.Nat.mem_divisors F,
    _root_.Nat.mem_divisors]
  exact ⟨fun hd => ⟨hd, hn⟩, And.left⟩

/-- The checked divisor enumeration is Mathlib's divisor finset in ascending
order. -/
theorem divisors_list_eq {n : Nat} (F : CheckedFactorization n) :
    (divisors F).toList = n.divisors.sort (· ≤ ·) := by
  symm
  rw [← divisors_eq F]
  exact (List.toFinset_sort (r := (· ≤ ·)) (divisors_nodup F)).2
    (divisors_sorted F)

/-- The checked divisor count is the cardinality of Mathlib's divisor
finset. -/
theorem numDivisors_eq_card {n : Nat} (F : CheckedFactorization n) :
    numDivisors F = n.divisors.card := by
  rw [numDivisors_eq_size, ← Array.length_toList,
    ← List.toFinset_card_of_nodup (divisors_nodup F), divisors_eq F]

/-- The checked totient agrees with Mathlib's Euler totient. -/
theorem totient_eq {n : Nat} (F : CheckedFactorization n) :
    totient F = _root_.Nat.totient n := by
  rw [Hex.Nat.totient_eq_count F, _root_.Nat.totient]
  rw [← List.toFinset_card_of_nodup
    (List.nodup_range.filter (fun a => decide (Nat.Coprime a n)))]
  rw [List.toFinset_filter, List.toFinset_range]
  simp [_root_.Nat.coprime_comm]

/-- The checked generalized divisor sum is the corresponding sum over
Mathlib's divisor finset. -/
theorem sigma_eq {n k : Nat} (F : CheckedFactorization n) :
    sigma F k = ∑ d ∈ n.divisors, d ^ k := by
  rw [sigma_eq_sum, ← List.sum_toFinset _ (divisors_nodup F), divisors_eq F]

/-- The checked prime bases are Mathlib's distinct prime factors. -/
theorem primeFactors_eq {n : Nat} (F : CheckedFactorization n) :
    (F.raw.factors.map fun e => e.prime).toFinset = n.primeFactors := by
  have hn : n ≠ 0 := F.pos.ne'
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

/-- The checked radical is Mathlib's product of the distinct prime factors. -/
theorem radical_eq {n : Nat} (F : CheckedFactorization n) :
    radical F = ∏ p ∈ n.primeFactors, p := by
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
    _ = ∏ p ∈ n.primeFactors, p := by simp [primeFactors_eq F]

/-- The checked squarefree decision agrees with Mathlib's squarefree
predicate. -/
theorem isSquarefree_iff_squarefree {n : Nat} (F : CheckedFactorization n) :
    isSquarefree F = true ↔ Squarefree n := by
  rw [Hex.Nat.isSquarefree_iff, Nat.squarefree_iff_prime_squarefree]
  constructor
  · intro h q hq hq2
    exact h q (prime_iff.mpr hq) (by simpa [Nat.pow_two] using hq2)
  · intro h q hq hq2
    exact h q (prime_iff.mp hq) (by simpa [Nat.pow_two] using hq2)

/-- Mathlib recognizes the computed squarefree part as squarefree. -/
theorem squarefreePart_mathlib {n : Nat} (F : CheckedFactorization n) :
    Squarefree (squarefreePart F) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro q hq hq2
  have hn : 0 < n := F.pos
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
  have hn : 0 < n := F.pos
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
