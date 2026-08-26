/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.DivisorEnumeration

public section

/-! Arithmetic functions computed from already-checked factorization data. -/

namespace Hex

namespace Nat

/-- Positive divisors, in ascending order. -/
@[expose]
def divisors {n : Nat} (F : CheckedFactorization n) : Array Nat :=
  (DivisorEnumeration.values F.raw.factors).mergeSort
    (fun a b => decide (a ≤ b)) |>.toArray

/-- Number of positive divisors, `τ(n) = ∏ (eᵢ + 1)`. -/
@[expose]
def numDivisors {n : Nat} (F : CheckedFactorization n) : Nat :=
  (F.raw.factors.map fun e => e.exponent + 1).prod

/-- The geometric sum for one prime-power entry. The `0` and `1` bases use
their total finite-sum values; certified factorizations only contain primes. -/
@[expose]
def sigmaEntry (entry : PrimePower) (k : Nat) : Nat :=
  if k = 0 then
    entry.exponent + 1
  else
    let q := entry.prime ^ k
    if q = 0 then 1
    else if q = 1 then entry.exponent + 1
    else (q ^ (entry.exponent + 1) - 1) / (q - 1)

/-- Generalized divisor sum `σ_k`. -/
@[expose]
def sigma {n : Nat} (F : CheckedFactorization n) (k : Nat) : Nat :=
  if k = 0 then
    numDivisors F
  else
    (F.raw.factors.map fun entry => sigmaEntry entry k).prod

/-- Euler's totient from a checked prime-power decomposition. -/
@[expose]
def totient {n : Nat} (_F : CheckedFactorization n) : Nat :=
  ((List.range n).filter fun a => decide (Nat.Coprime a n)).length

/-- Product of the distinct prime divisors. -/
@[expose]
def radical {n : Nat} (F : CheckedFactorization n) : Nat :=
  (F.raw.factors.map fun e => e.prime).prod

/-- Largest square-divisor root, computed from certified multiplicities. -/
@[expose]
def squareDivisor {n : Nat} (F : CheckedFactorization n) : Nat :=
  (F.raw.factors.map fun e => e.prime ^ (e.exponent / 2)).prod

/-- Squarefree part, computed from the odd certified multiplicities. -/
@[expose]
def squarefreePart {n : Nat} (F : CheckedFactorization n) : Nat :=
  (F.raw.factors.map fun e => e.prime ^ (e.exponent % 2)).prod

/-- Whether every prime multiplicity is exactly one. -/
@[expose]
def isSquarefree {n : Nat} (F : CheckedFactorization n) : Bool :=
  F.raw.factors.all fun e => e.exponent == 1

/-- The largest square-divisor root uses half of each certified exponent. -/
theorem squareDivisor_eq_prod {n : Nat} (F : CheckedFactorization n) :
    squareDivisor F =
      (F.raw.factors.map fun e => e.prime ^ (e.exponent / 2)).prod :=
  rfl

/-- The squarefree part retains exactly the parity of each certified exponent. -/
theorem squarefreePart_eq_prod {n : Nat} (F : CheckedFactorization n) :
    squarefreePart F =
      (F.raw.factors.map fun e => e.prime ^ (e.exponent % 2)).prod :=
  rfl

/-- Enumeration has exactly the positive divisors of `n`. -/
theorem mem_divisors {n d : Nat} (F : CheckedFactorization n) :
    d ∈ (divisors F).toList ↔ d ∣ n := by
  rw [divisors, List.toList_toArray, List.mem_mergeSort,
    DivisorEnumeration.mem_values_iff
      (checkFactorization_prime F.valid)
      (checkFactorization_sorted F.valid),
    checkFactorization_prod F.valid, F.subject_eq]

/-- The ascending divisor enumeration contains no duplicates. -/
theorem divisors_nodup {n : Nat} (F : CheckedFactorization n) :
    (divisors F).toList.Nodup := by
  apply (List.mergeSort_perm _ _).symm.nodup
  exact DivisorEnumeration.nodup_values
    (checkFactorization_prime F.valid)
    (checkFactorization_sorted F.valid)

/-- The divisor enumeration is in ascending order. -/
theorem divisors_sorted {n : Nat} (F : CheckedFactorization n) :
    (divisors F).toList.Pairwise (fun a b => a ≤ b) := by
  rw [divisors, List.toList_toArray]
  simpa only [decide_eq_true_eq] using
    (List.pairwise_mergeSort
      (le := fun a b : Nat => decide (a ≤ b))
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact Nat.le_trans hab hbc)
      (fun a b => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Nat.le_total a b)
      (DivisorEnumeration.values F.raw.factors))

/-- The product formula agrees with divisor enumeration. -/
theorem numDivisors_eq_size {n : Nat} (F : CheckedFactorization n) :
    numDivisors F = (divisors F).size := by
  simp [numDivisors, divisors, DivisorEnumeration.length_values]

private def geometricSum (q : Nat) : Nat → Nat
  | 0 => 1
  | e + 1 => 1 + q * geometricSum q e

private theorem sum_ones (xs : List Nat) :
    (xs.map fun _ => 1).sum = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_comm]

private theorem powers_sum (p e acc k : Nat) :
    ((DivisorEnumeration.powers p e acc).map fun q => q ^ k).sum =
      acc ^ k * geometricSum (p ^ k) e := by
  induction e generalizing acc with
  | zero => simp [DivisorEnumeration.powers, geometricSum]
  | succ e ih =>
      rw [DivisorEnumeration.powers, List.map_cons, List.sum_cons, ih,
        geometricSum, Nat.mul_add, Nat.mul_one, Nat.mul_pow]
      congr 1
      ac_rfl

private theorem geometricSum_spec {q : Nat} (hq : 1 < q) : ∀ e : Nat,
    (q - 1) * geometricSum q e = q ^ (e + 1) - 1
  | 0 => by simp [geometricSum]
  | e + 1 => by
      rw [geometricSum]
      calc
        (q - 1) * (1 + q * geometricSum q e) =
            (q - 1) + q * ((q - 1) * geometricSum q e) := by
          rw [Nat.mul_add, Nat.mul_one]
          congr 1
          ac_rfl
        _ = (q - 1) + q * (q ^ (e + 1) - 1) := by
          rw [geometricSum_spec hq e]
        _ = q ^ ((e + 1) + 1) - 1 := by
          have hpow : 0 < q ^ (e + 1) := Nat.pow_pos (by omega)
          have hle : q ≤ q ^ (e + 1) * q := Nat.le_mul_of_pos_left q hpow
          calc
            (q - 1) + q * (q ^ (e + 1) - 1) =
                (q - 1) + (q ^ (e + 1) * q - q) := by
              rw [Nat.mul_sub_left_distrib, Nat.mul_one,
                Nat.mul_comm q (q ^ (e + 1))]
            _ = q ^ (e + 1) * q - 1 := by omega
            _ = q ^ ((e + 1) + 1) - 1 := by simp only [Nat.pow_succ]

/-- The closed form equals the finite prime-power sum for every entry. -/
theorem sigmaEntry_eq_powerSum (entry : PrimePower) (k : Nat) :
    sigmaEntry entry k =
      ((DivisorEnumeration.powers entry.prime entry.exponent 1).map
        fun q => q ^ k).sum := by
  by_cases hk : k = 0
  · subst k
    rw [sigmaEntry, ite_eq_left rfl]
    simp only [Nat.pow_zero, sum_ones,
      DivisorEnumeration.length_powers]
  · rw [sigmaEntry, ite_eq_right hk, powers_sum]
    simp only [Nat.one_pow, Nat.one_mul]
    by_cases hq0 : entry.prime ^ k = 0
    · rw [ite_eq_left hq0, hq0]
      induction entry.exponent with
      | zero => rfl
      | succ e ih => simp [geometricSum, ih]
    · rw [ite_eq_right hq0]
      by_cases hq1 : entry.prime ^ k = 1
      · rw [ite_eq_left hq1, hq1]
        induction entry.exponent with
        | zero => simp [geometricSum]
        | succ e ih => simp [geometricSum, ih, Nat.add_comm]
      · have hq : 1 < entry.prime ^ k := by omega
        rw [ite_eq_right hq1, ← geometricSum_spec hq entry.exponent,
          Nat.mul_comm (entry.prime ^ k - 1), Nat.mul_div_left _ (by omega)]

private theorem sigmaEntries_eq (entries : List PrimePower) (k : Nat) :
    (entries.map fun entry => sigmaEntry entry k).prod =
      (entries.map fun entry =>
        ((DivisorEnumeration.powers entry.prime entry.exponent 1).map
          fun q => q ^ k).sum).prod := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
        sigmaEntry_eq_powerSum entry k, ih]

/-- `sigma` is the sum of `k`th powers over all divisors. -/
theorem sigma_eq_sum {n k : Nat} (F : CheckedFactorization n) :
    sigma F k = ((divisors F).toList.map (fun d => d ^ k)).sum := by
  by_cases hk : k = 0
  · subst k
    rw [sigma, ite_eq_left rfl, numDivisors_eq_size]
    simp only [Nat.pow_zero, sum_ones, Array.length_toList]
  · rw [sigma, ite_eq_right hk,
      sigmaEntries_eq F.raw.factors k,
      ← DivisorEnumeration.sum_pow_values]
    have hperm := List.mergeSort_perm
      (DivisorEnumeration.values F.raw.factors) (fun a b => decide (a ≤ b))
    have hsum := (hperm.map (fun d => d ^ k)).sum_nat
    simpa only [divisors, List.toList_toArray] using hsum.symm

/-- The factor-product formula counts residues coprime to `n`. -/
theorem totient_eq_count {n : Nat} (F : CheckedFactorization n) :
    totient F = ((List.range n).filter (fun a => Nat.Coprime a n)).length := by
  simp [totient]

private theorem prime_dvd_product {q : Nat} (hq : Prime q) :
    ∀ (entries : List PrimePower),
      (∀ e ∈ entries, Prime e.prime) →
      q ∣ (entries.map fun e => e.prime).prod →
      ∃ e ∈ entries, e.prime = q := by
  intro entries
  induction entries with
  | nil =>
      intro _ hd
      simp only [List.map_nil, List.prod_nil] at hd
      have heq := Nat.dvd_one.mp hd
      have := hq.two_le
      omega
  | cons e rest ih =>
      intro hall hdvd
      simp only [List.map_cons, List.prod_cons] at hdvd
      rcases hq.dvd_mul.mp hdvd with he | hr
      · have heprime := hall e (by simp)
        rcases heprime.2 q he with heq | heq
        · have := hq.two_le
          omega
        · exact ⟨e, by simp, heq.symm⟩
      · obtain ⟨x, hx, heq⟩ := ih (fun x hx => hall x (by simp [hx])) hr
        exact ⟨x, by simp [hx], heq⟩

private theorem entry_dvd_product : ∀ (entries : List PrimePower) (e : PrimePower),
    e ∈ entries → e.prime ∣ (entries.map fun x => x.prime).prod := by
  intro entries
  induction entries with
  | nil => simp
  | cons x rest ih =>
      intro e he
      simp only [List.map_cons, List.prod_cons]
      rcases List.mem_cons.mp he with rfl | he
      · exact Nat.dvd_mul_right _ _
      · exact Nat.dvd_trans (ih e he) (Nat.dvd_mul_left _ _)

/-- A prime divides the radical exactly when it divides the subject. -/
theorem prime_dvd_radical_iff {n q : Nat} (F : CheckedFactorization n)
    (hq : Prime q) : q ∣ radical F ↔ q ∣ n := by
  constructor
  · intro h
    obtain ⟨e, he, heq⟩ := prime_dvd_product hq F.raw.factors
      (checkFactorization_prime F.valid) (by simpa [radical] using h)
    have hraw := (checkFactorization_primeSupport F.valid hq).mpr
      ⟨e, he, heq⟩
    simpa [F.subject_eq] using hraw
  · intro hn
    have hraw : q ∣ F.raw.subject := by simpa [F.subject_eq] using hn
    obtain ⟨e, he, heq⟩ :=
      (checkFactorization_primeSupport F.valid hq).mp hraw
    unfold radical
    rw [← heq]
    exact entry_dvd_product F.raw.factors e he

private theorem squareEntry_decomp (entry : PrimePower) :
    entry.prime ^ (entry.exponent % 2) *
        (entry.prime ^ (entry.exponent / 2)) ^ 2 =
      entry.prime ^ entry.exponent := by
  rw [← Nat.pow_mul, ← Nat.pow_add]
  congr 1
  have h := Nat.mod_add_div entry.exponent 2
  omega

private theorem squareEntries_decomp : ∀ entries : List PrimePower,
    (entries.map fun e => e.prime ^ (e.exponent % 2)).prod *
        ((entries.map fun e => e.prime ^ (e.exponent / 2)).prod) ^ 2 =
      (entries.map fun e => e.prime ^ e.exponent).prod := by
  intro entries
  induction entries with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.map_cons, List.prod_cons, Nat.mul_pow]
      calc
        entry.prime ^ (entry.exponent % 2) *
              (rest.map fun e => e.prime ^ (e.exponent % 2)).prod *
              ((entry.prime ^ (entry.exponent / 2)) ^ 2 *
                ((rest.map fun e => e.prime ^ (e.exponent / 2)).prod) ^ 2) =
            (entry.prime ^ (entry.exponent % 2) *
              (entry.prime ^ (entry.exponent / 2)) ^ 2) *
              ((rest.map fun e => e.prime ^ (e.exponent % 2)).prod *
                ((rest.map fun e => e.prime ^ (e.exponent / 2)).prod) ^ 2) := by
          ac_rfl
        _ = entry.prime ^ entry.exponent *
              (rest.map fun e => e.prime ^ e.exponent).prod := by
          rw [squareEntry_decomp, ih]

private theorem prime_dvd_pow_factor {q a : Nat} (hq : Prime q) :
    ∀ {k : Nat}, q ∣ a ^ k → q ∣ a := by
  intro k
  induction k with
  | zero =>
      intro h
      exact absurd (Nat.dvd_one.mp h) hq.ne_one
  | succ k ih =>
      intro h
      rw [Nat.pow_succ] at h
      exact (hq.dvd_mul.mp h).elim ih id

private theorem prime_dvd_power_product {q : Nat} (hq : Prime q) :
    ∀ (entries : List PrimePower),
      (∀ e ∈ entries, Prime e.prime) →
      q ∣ (entries.map fun e => e.prime ^ e.exponent).prod →
      ∃ e ∈ entries, e.prime = q := by
  intro entries hprime hdvd
  induction entries with
  | nil => exact absurd (Nat.dvd_one.mp hdvd) hq.ne_one
  | cons entry rest ih =>
      simp only [List.map_cons, List.prod_cons] at hdvd
      rcases hq.dvd_mul.mp hdvd with he | hrest
      · have hbase := prime_dvd_pow_factor hq he
        have hp := hprime entry (by simp)
        rcases hp.2 q hbase with hq1 | heq
        · exact absurd hq1 hq.ne_one
        · exact ⟨entry, by simp, heq.symm⟩
      · obtain ⟨e, he, heq⟩ := ih
          (fun e he => hprime e (by simp [he])) hrest
        exact ⟨e, by simp [he], heq⟩

private theorem head_not_dvd_tail_product {entry : PrimePower}
    {rest : List PrimePower}
    (hprime : ∀ e ∈ entry :: rest, Prime e.prime)
    (hsorted : (entry :: rest).Pairwise fun a b => a.prime < b.prime) :
    ¬entry.prime ∣ (rest.map fun e => e.prime ^ e.exponent).prod := by
  intro hdvd
  obtain ⟨e, he, heq⟩ := prime_dvd_power_product
    (hprime entry (by simp)) rest
    (fun e he => hprime e (by simp [he])) hdvd
  have hlt := (List.pairwise_cons.mp hsorted).1 e he
  rw [heq] at hlt
  exact Nat.lt_irrefl _ hlt

private theorem squareRoot_dvd_primeProduct {p rest root : Nat}
    (hp : Prime p) (hnot : ¬p ∣ rest)
    (hrest : ∀ c, c ^ 2 ∣ rest → c ∣ root) :
    ∀ e d, d ^ 2 ∣ p ^ e * rest → d ∣ p ^ (e / 2) * root := by
  intro e
  induction e using Nat.strongRecOn with
  | ind e ih =>
    intro d hd
    by_cases hpd : p ∣ d
    · obtain ⟨c, rfl⟩ := hpd
      cases e with
      | zero =>
          exfalso
          apply hnot
          have hdsq : (p * c) ^ 2 ∣ rest := by simpa using hd
          exact Nat.dvd_trans
            ⟨c * (p * c), by simp [Nat.pow_two, Nat.mul_left_comm,
              Nat.mul_comm]⟩ hdsq
      | succ e =>
          cases e with
          | zero =>
              exfalso
              apply hnot
              have hcancel : p * c ^ 2 ∣ rest := by
                apply (Nat.mul_dvd_mul_iff_left hp.pos).mp
                simpa [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm,
                  Nat.mul_comm] using hd
              exact Nat.dvd_trans (Nat.dvd_mul_right p (c ^ 2)) hcancel
          | succ e =>
              have hcancel : c ^ 2 ∣ p ^ e * rest := by
                apply (Nat.mul_dvd_mul_iff_left
                  (Nat.pow_pos hp.pos : 0 < p ^ 2)).mp
                simpa [Nat.pow_succ, Nat.pow_two, Nat.mul_assoc,
                  Nat.mul_left_comm, Nat.mul_comm] using hd
              have hc := ih e (by omega) c hcancel
              have hmul := Nat.mul_dvd_mul_left p hc
              simpa [show (e + 1 + 1) / 2 = e / 2 + 1 by omega,
                Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
                Nat.mul_comm] using hmul
    · have hcop : Nat.Coprime (d ^ 2) (p ^ e) :=
        Nat.Coprime.pow 2 e (hp.coprime_of_not_dvd hpd).symm
      have hdrest : d ^ 2 ∣ rest := hcop.dvd_of_dvd_mul_left hd
      exact Nat.dvd_trans (hrest d hdrest) (Nat.dvd_mul_left _ _)

private theorem squareRoot_dvd_entries : ∀ (entries : List PrimePower),
    (∀ e ∈ entries, Prime e.prime) →
    entries.Pairwise (fun a b => a.prime < b.prime) →
    ∀ d, d ^ 2 ∣ (entries.map fun e => e.prime ^ e.exponent).prod →
      d ∣ (entries.map fun e => e.prime ^ (e.exponent / 2)).prod := by
  intro entries hprime hsorted
  induction entries with
  | nil =>
      intro d hd
      simp only [List.map_nil, List.prod_nil] at hd ⊢
      rw [Nat.pow_two] at hd
      exact Nat.dvd_trans (Nat.dvd_mul_right d d) hd
  | cons entry rest ih =>
      intro d hd
      simp only [List.map_cons, List.prod_cons] at hd ⊢
      apply squareRoot_dvd_primeProduct
        (hprime entry (by simp))
        (head_not_dvd_tail_product hprime hsorted)
        (fun c hc => ih
          (fun e he => hprime e (by simp [he]))
          (List.pairwise_cons.mp hsorted).2 c hc)
        entry.exponent d hd

private theorem squareDivisor_dvd_subject {n : Nat} (F : CheckedFactorization n) :
    squareDivisor F ^ 2 ∣ n := by
  refine ⟨squarefreePart F, ?_⟩
  rw [Nat.mul_comm, squarefreePart, squareDivisor, squareEntries_decomp,
    checkFactorization_prod F.valid, F.subject_eq]

/-- Canonical squarefree-times-square decomposition. -/
theorem squarefreePart_mul_square {n : Nat} (F : CheckedFactorization n) :
    squarefreePart F * squareDivisor F ^ 2 = n := by
  rw [squarefreePart, squareDivisor, squareEntries_decomp,
    checkFactorization_prod F.valid, F.subject_eq]

/-- `squareDivisor` is the largest square divisor root. -/
theorem squareDivisor_spec {n : Nat} (F : CheckedFactorization n) :
    squareDivisor F ^ 2 ∣ n ∧
      ∀ d, d ^ 2 ∣ n → d ∣ squareDivisor F := by
  refine ⟨squareDivisor_dvd_subject F, ?_⟩
  intro d hd
  apply squareRoot_dvd_entries F.raw.factors
    (checkFactorization_prime F.valid)
    (checkFactorization_sorted F.valid) d
  simpa [checkFactorization_prod F.valid, F.subject_eq] using hd

/-- Checked multiplicities characterize squarefreeness. -/
theorem isSquarefree_iff {n : Nat} (F : CheckedFactorization n) :
    isSquarefree F = true ↔
      ∀ q, Prime q → ¬(q ^ 2 ∣ n) := by
  constructor
  · intro hall q hq hq2
    have hq2raw : q ^ 2 ∣ F.raw.subject := by
      simpa [F.subject_eq] using hq2
    obtain ⟨e, he, heq⟩ := (checkFactorization_primeSupport F.valid hq).mp
      (Nat.dvd_trans (by exact ⟨q, by rw [Nat.pow_two]⟩) hq2raw)
    have hmult := (checkFactorization_multiplicity F.valid he (k := 2)).mp
      (heq ▸ hq2raw)
    have hexp := checkFactorization_exponent F.valid e he
    have hone : e.exponent = 1 := by
      exact beq_iff_eq.mp (List.all_eq_true.mp hall e he)
    omega
  · intro h
    simp only [isSquarefree, List.all_eq_true]
    intro e he
    have hpos := checkFactorization_exponent F.valid e he
    by_cases hone : e.exponent = 1
    · simp [hone]
    · have htwo : 2 ≤ e.exponent := by omega
      have hsquare := (checkFactorization_multiplicity F.valid he (k := 2)).mpr htwo
      exact False.elim (h e.prime (checkFactorization_prime F.valid e he)
        (by simpa [F.subject_eq] using hsquare))

end Nat

end Hex
