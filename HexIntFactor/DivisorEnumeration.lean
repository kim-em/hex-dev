/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Cert

public section

/-! Canonical divisor enumeration from a checked prime-power list. -/

namespace Hex

namespace Nat

namespace DivisorEnumeration

/-- The powers `acc, acc * p, ..., acc * p ^ e`. -/
@[expose]
def powers (p : Nat) : Nat → Nat → List Nat
  | 0, acc => [acc]
  | e + 1, acc => acc :: powers p e (acc * p)

/-- Extend divisor products with every allowed power of one prime. -/
@[expose]
def extend (values : List Nat) (entry : PrimePower) : List Nat :=
  values.flatMap fun d =>
    (powers entry.prime entry.exponent 1).map fun q => d * q

/-- Unsorted positive divisors generated from a canonical prime-power list. -/
@[expose]
def values : List PrimePower → List Nat
  | [] => [1]
  | entry :: rest => extend (values rest) entry

private theorem mem_powers {p e acc x : Nat} :
    x ∈ powers p e acc ↔ ∃ j, j ≤ e ∧ x = acc * p ^ j := by
  induction e generalizing acc with
  | zero => simp [powers]
  | succ e ih =>
      simp only [powers, List.mem_cons, ih]
      constructor
      · intro h
        rcases h with rfl | ⟨j, hj, rfl⟩
        · exact ⟨0, by omega, by simp⟩
        · refine ⟨j + 1, by omega, ?_⟩
          rw [Nat.pow_succ]
          ac_rfl
      · rintro ⟨j, hj, rfl⟩
        cases j with
        | zero => simp
        | succ j =>
            right
            refine ⟨j, by omega, ?_⟩
            rw [Nat.pow_succ]
            ac_rfl

@[simp] private theorem length_powers (p e acc : Nat) :
    (powers p e acc).length = e + 1 := by
  induction e generalizing acc with
  | zero => simp [powers]
  | succ e ih => simp [powers, ih, Nat.add_assoc]

private theorem prime_dvd_pow {p a : Nat} (hp : Prime p) :
    ∀ {k : Nat}, p ∣ a ^ k → p ∣ a := by
  intro k
  induction k with
  | zero =>
      intro h
      exact absurd (Nat.dvd_one.mp h) hp.ne_one
  | succ k ih =>
      intro h
      rw [Nat.pow_succ] at h
      exact (hp.dvd_mul.mp h).elim ih id

private theorem divisor_prime_power {p e d : Nat} (hp : Prime p)
    (hd : d ∣ p ^ e) : ∃ j, j ≤ e ∧ d = p ^ j := by
  induction e generalizing d with
  | zero =>
      refine ⟨0, by omega, ?_⟩
      rw [Nat.pow_zero]
      exact Nat.dvd_one.mp hd
  | succ e ih =>
      by_cases hd1 : d = 1
      · refine ⟨0, by omega, ?_⟩
        rw [hd1, Nat.pow_zero]
      · have hd2 : 2 ≤ d := by
          have hdpos := Nat.pos_of_dvd_of_pos hd (Nat.pow_pos hp.pos)
          omega
        obtain ⟨q, hq, hqd⟩ := exists_prime_dvd hd2
        have hqp : q ∣ p := prime_dvd_pow hq (Nat.dvd_trans hqd hd)
        have hqpEq : q = p := by
          rcases hp.2 q hqp with hq1 | hqpEq
          · exact absurd hq1 hq.ne_one
          · exact hqpEq
        have hpd : p ∣ d := hqpEq ▸ hqd
        obtain ⟨d', rfl⟩ := hpd
        have hd' : d' ∣ p ^ e := by
          apply (Nat.mul_dvd_mul_iff_left hp.pos).mp
          simpa [Nat.pow_succ, Nat.mul_comm] using hd
        obtain ⟨j, hj, rfl⟩ := ih hd'
        refine ⟨j + 1, by omega, ?_⟩
        simp [Nat.pow_succ, Nat.mul_comm]

private theorem mem_powers_one_iff {p e d : Nat} (hp : Prime p) :
    d ∈ powers p e 1 ↔ d ∣ p ^ e := by
  rw [mem_powers]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa using Nat.pow_dvd_pow p hj
  · intro hd
    obtain ⟨j, hj, rfl⟩ := divisor_prime_power hp hd
    exact ⟨j, hj, by simp⟩

private theorem prime_dvd_product {q : Nat} (hq : Prime q) :
    ∀ (entries : List PrimePower),
      (∀ e ∈ entries, Prime e.prime) →
      q ∣ (entries.map fun e => e.prime ^ e.exponent).prod →
      ∃ e ∈ entries, e.prime = q := by
  intro entries hprime hdvd
  induction entries with
  | nil =>
      exact absurd (Nat.dvd_one.mp hdvd) hq.ne_one
  | cons e rest ih =>
      simp only [List.map_cons, List.prod_cons] at hdvd
      rcases hq.dvd_mul.mp hdvd with he | hr
      · have he' := prime_dvd_pow hq he
        rcases (hprime e (by simp)).2 q he' with heq | heq
        · exact absurd heq hq.ne_one
        · exact ⟨e, by simp, heq.symm⟩
      · obtain ⟨x, hx, heq⟩ := ih
          (fun x hx => hprime x (by simp [hx])) hr
        exact ⟨x, by simp [hx], heq⟩

private theorem head_coprime {entry : PrimePower} {rest : List PrimePower}
    (hprime : ∀ e ∈ entry :: rest, Prime e.prime)
    (hsorted : (entry :: rest).Pairwise fun a b => a.prime < b.prime) :
    Nat.Coprime (entry.prime ^ entry.exponent)
      (rest.map fun e => e.prime ^ e.exponent).prod := by
  have hp := hprime entry (by simp)
  have htail : ∀ e ∈ rest, Prime e.prime := by
    intro e he
    exact hprime e (by simp [he])
  have hnot : ¬entry.prime ∣
      (rest.map fun e => e.prime ^ e.exponent).prod := by
    intro hd
    obtain ⟨e, he, heq⟩ := prime_dvd_product hp rest htail hd
    have hlt := (List.pairwise_cons.mp hsorted).1 e he
    rw [heq] at hlt
    exact Nat.lt_irrefl _ hlt
  exact (hp.coprime_of_not_dvd hnot).pow_left _

/-- Generated values are exactly the divisors of the represented product. -/
theorem mem_values_iff {entries : List PrimePower} {d : Nat}
    (hprime : ∀ e ∈ entries, Prime e.prime)
    (hsorted : entries.Pairwise fun a b => a.prime < b.prime) :
    d ∈ values entries ↔
      d ∣ (entries.map fun e => e.prime ^ e.exponent).prod := by
  induction entries generalizing d with
  | nil => simp [values]
  | cons entry rest ih =>
      have hp := hprime entry (by simp)
      have htail : ∀ e ∈ rest, Prime e.prime := by
        intro e he
        exact hprime e (by simp [he])
      have hsortedTail := (List.pairwise_cons.mp hsorted).2
      have hcop := head_coprime hprime hsorted
      simp only [values, extend, List.mem_flatMap, List.mem_map,
        List.map_cons, List.prod_cons]
      constructor
      · rintro ⟨b, hb, a, ha, rfl⟩
        have hb' := (ih htail hsortedTail).mp hb
        have ha' := (mem_powers_one_iff hp).mp ha
        simpa [Nat.mul_comm] using Nat.mul_dvd_mul ha' hb'
      · intro hd
        let A := entry.prime ^ entry.exponent
        let B := (rest.map fun e => e.prime ^ e.exponent).prod
        let a := Nat.gcd d A
        let b := Nat.gcd d B
        have ha : a ∣ A := Nat.gcd_dvd_right d A
        have hb : b ∣ B := Nat.gcd_dvd_right d B
        have hab : a * b = d := by
          calc
            a * b = Nat.gcd d (A * B) := by
              symm
              exact hcop.gcd_mul d
            _ = d := Nat.gcd_eq_left_iff_dvd.mpr hd
        refine ⟨b, (ih htail hsortedTail).mpr hb, a,
          (mem_powers_one_iff hp).mpr ha, ?_⟩
        simpa [Nat.mul_comm] using hab

private theorem product_pos (entries : List PrimePower)
    (hprime : ∀ e ∈ entries, Prime e.prime) :
    0 < (entries.map fun e => e.prime ^ e.exponent).prod := by
  induction entries with
  | nil => simp
  | cons e rest ih =>
      simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_pos (Nat.pow_pos (hprime e (by simp)).pos)
        (ih fun x hx => hprime x (by simp [hx]))

private theorem nodup_powers (p e acc : Nat) (hp : Prime p) (hacc : 0 < acc) :
    (powers p e acc).Nodup := by
  induction e generalizing acc with
  | zero => simp [powers]
  | succ e ih =>
      simp only [powers, List.nodup_cons]
      refine ⟨?_, ih (acc * p) (Nat.mul_pos hacc hp.pos)⟩
      intro hmem
      obtain ⟨j, _, heq⟩ := mem_powers.mp hmem
      have hlt : acc < (acc * p) * p ^ j := by
        exact Nat.lt_of_lt_of_le
          (by simpa using (Nat.mul_lt_mul_left hacc).mpr hp.one_lt)
          (Nat.le_mul_of_pos_right (acc * p) (Nat.pow_pos hp.pos))
      exact Nat.ne_of_lt hlt heq

private theorem unique_split {A B a₁ a₂ b₁ b₂ : Nat}
    (hcop : Nat.Coprime A B) (hA : 0 < A)
    (ha₁ : a₁ ∣ A) (ha₂ : a₂ ∣ A) (hb₁ : b₁ ∣ B) (hb₂ : b₂ ∣ B)
    (h : b₁ * a₁ = b₂ * a₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have ha₁b₂ : Nat.Coprime a₁ b₂ :=
    (hcop.coprime_dvd_left ha₁).coprime_dvd_right hb₂
  have ha₂b₁ : Nat.Coprime a₂ b₁ :=
    (hcop.coprime_dvd_left ha₂).coprime_dvd_right hb₁
  have ha₁a₂ : a₁ ∣ a₂ := by
    apply ha₁b₂.dvd_of_dvd_mul_right
    exact ⟨b₁, by simpa [Nat.mul_comm] using h.symm⟩
  have ha₂a₁ : a₂ ∣ a₁ := by
    apply ha₂b₁.dvd_of_dvd_mul_right
    exact ⟨b₂, by simpa [Nat.mul_comm] using h⟩
  have ha : a₁ = a₂ := Nat.dvd_antisymm ha₁a₂ ha₂a₁
  subst a₂
  have haPos := Nat.pos_of_dvd_of_pos ha₁ hA
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left haPos (by simpa [Nat.mul_comm] using h)⟩

/-- Canonical prime powers generate every divisor exactly once. -/
theorem nodup_values {entries : List PrimePower}
    (hprime : ∀ e ∈ entries, Prime e.prime)
    (hsorted : entries.Pairwise fun a b => a.prime < b.prime) :
    (values entries).Nodup := by
  induction entries with
  | nil => simp [values]
  | cons entry rest ih =>
      have hp := hprime entry (by simp)
      have htail : ∀ e ∈ rest, Prime e.prime := by
        intro e he
        exact hprime e (by simp [he])
      have hsortedTail := (List.pairwise_cons.mp hsorted).2
      have hcop := head_coprime hprime hsorted
      have htailNodup := ih htail hsortedTail
      have htailPos := product_pos rest htail
      rw [values, extend, List.nodup_iff_pairwise_ne,
        List.pairwise_flatMap]
      refine ⟨?_, ?_⟩
      · intro b hb
        rw [List.pairwise_map]
        exact (nodup_powers entry.prime entry.exponent 1 hp (by decide)).imp
          (fun hne heq => hne (Nat.eq_of_mul_eq_mul_left
            (Nat.pos_of_dvd_of_pos
              ((mem_values_iff htail hsortedTail).mp hb) htailPos) heq))
      · rw [List.nodup_iff_pairwise_ne] at htailNodup
        apply htailNodup.imp_of_mem
        intro b₁ b₂ hb₁ hb₂ hbne
        intro x hx y hy heq
        obtain ⟨a₁, ha₁, rfl⟩ := List.mem_map.mp hx
        obtain ⟨a₂, ha₂, rfl⟩ := List.mem_map.mp hy
        apply hbne
        exact (unique_split hcop (Nat.pow_pos hp.pos)
          ((mem_powers_one_iff hp).mp ha₁)
          ((mem_powers_one_iff hp).mp ha₂)
          ((mem_values_iff htail hsortedTail).mp hb₁)
          ((mem_values_iff htail hsortedTail).mp hb₂)
          heq).2

private theorem length_extend (values : List Nat) (entry : PrimePower) :
    (extend values entry).length = values.length * (entry.exponent + 1) := by
  unfold extend
  simp only [List.length_flatMap, List.length_map, length_powers]
  induction values with
  | nil => simp
  | cons d rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih, Nat.succ_mul]
      exact Nat.add_comm _ _

/-- The generated list has the textbook product-of-successors size. -/
theorem length_values (entries : List PrimePower) :
    (values entries).length =
      (entries.map fun e => e.exponent + 1).prod := by
  induction entries with
  | nil => simp [values]
  | cons entry rest ih =>
      simp [values, length_extend, ih, Nat.mul_comm]

end DivisorEnumeration

end Nat

end Hex
