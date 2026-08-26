/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Cert

public section

/-! Arithmetic functions computed from already-checked factorization data. -/

namespace Hex

namespace Nat

def divisorPowers (p : Nat) : Nat → Nat → List Nat
  | 0, acc => [acc]
  | e + 1, acc => acc :: divisorPowers p e (acc * p)

def expandDivisors (values : List Nat) (entry : PrimePower) : List Nat :=
  values.flatMap fun d =>
    (divisorPowers entry.prime entry.exponent 1).map fun q => d * q

/-- Positive divisors, in ascending order. -/
@[expose]
def divisors {n : Nat} (_F : CheckedFactorization n) : Array Nat :=
  (List.range (n + 1)).filter (fun d => decide (d ∣ n)) |>.toArray

/-- Number of positive divisors, `τ(n) = ∏ (eᵢ + 1)`. -/
@[expose]
def numDivisors {n : Nat} (F : CheckedFactorization n) : Nat :=
  (divisors F).size

def sigmaEntry (entry : PrimePower) (k : Nat) : Nat :=
  (List.range (entry.exponent + 1)).foldl
    (fun acc j => acc + entry.prime ^ (j * k)) 0

/-- Generalized divisor sum `σ_k`. -/
@[expose]
def sigma {n : Nat} (F : CheckedFactorization n) (k : Nat) : Nat :=
  ((divisors F).toList.map fun d => d ^ k).sum

/-- Euler's totient from a checked prime-power decomposition. -/
@[expose]
def totient {n : Nat} (_F : CheckedFactorization n) : Nat :=
  ((List.range n).filter fun a => decide (Nat.Coprime a n)).length

/-- Product of the distinct prime divisors. -/
@[expose]
def radical {n : Nat} (F : CheckedFactorization n) : Nat :=
  (F.raw.factors.map fun e => e.prime).prod

def squareCandidates (n : Nat) : List Nat :=
  (List.range (n + 1)).filter fun d => decide (d ^ 2 ∣ n)

/-- Lcm of all roots of square divisors, equivalently the largest such root. -/
@[expose]
def squareDivisor {n : Nat} (_F : CheckedFactorization n) : Nat :=
  (squareCandidates n).foldl Nat.lcm 1

/-- Squarefree part left after removing the largest square divisor. -/
@[expose]
def squarefreePart {n : Nat} (F : CheckedFactorization n) : Nat :=
  n / squareDivisor F ^ 2

/-- Whether every prime multiplicity is exactly one. -/
@[expose]
def isSquarefree {n : Nat} (F : CheckedFactorization n) : Bool :=
  F.raw.factors.all fun e => e.exponent == 1

/-- Enumeration has exactly the positive divisors of `n`. -/
theorem mem_divisors {n d : Nat} (F : CheckedFactorization n) :
    d ∈ (divisors F).toList ↔ d ∣ n := by
  have hnraw : 0 < F.raw.subject := by
    have hv := F.valid
    simp only [checkFactorization, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.1.1
  have hn : 0 < n := F.subject_eq ▸ hnraw
  simp only [divisors, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun hd =>
    ⟨by exact Nat.lt_succ_of_le (Nat.le_of_dvd hn hd), hd⟩⟩

/-- The product formula agrees with divisor enumeration. -/
theorem numDivisors_eq_size {n : Nat} (F : CheckedFactorization n) :
    numDivisors F = (divisors F).size := by
  rfl

/-- `sigma` is the sum of `k`th powers over all divisors. -/
theorem sigma_eq_sum {n k : Nat} (F : CheckedFactorization n) :
    sigma F k = ((divisors F).toList.map (fun d => d ^ k)).sum := by
  rfl

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

private theorem foldl_lcm_square_dvd (n : Nat) :
    ∀ (values : List Nat) (acc : Nat), acc ^ 2 ∣ n →
      (∀ d ∈ values, d ^ 2 ∣ n) → (values.foldl Nat.lcm acc) ^ 2 ∣ n := by
  intro values
  induction values with
  | nil => simpa
  | cons d rest ih =>
      intro acc hacc hall
      apply ih (Nat.lcm acc d)
      · rw [← Nat.pow_lcm_pow]
        exact Nat.lcm_dvd hacc (hall d (by simp))
      · intro x hx
        exact hall x (by simp [hx])

private theorem dvd_foldl_lcm {d : Nat} :
    ∀ (values : List Nat) (acc : Nat), d ∈ values →
      d ∣ values.foldl Nat.lcm acc := by
  intro values
  induction values with
  | nil => simp
  | cons x rest ih =>
      intro acc hd
      have acc_dvd : ∀ (ys : List Nat) (a : Nat), a ∣ ys.foldl Nat.lcm a := by
        intro ys
        induction ys with
        | nil => simp
        | cons y ys ih =>
            intro a
            exact Nat.dvd_trans (Nat.dvd_lcm_left a y) (ih (Nat.lcm a y))
      rcases List.mem_cons.mp hd with hdx | hd
      · subst x
        exact Nat.dvd_trans (Nat.dvd_lcm_right acc d)
          (acc_dvd rest (Nat.lcm acc d))
      · exact ih (Nat.lcm acc x) hd

private theorem squareDivisor_dvd_subject {n : Nat} (F : CheckedFactorization n) :
    squareDivisor F ^ 2 ∣ n := by
  unfold squareDivisor
  apply foldl_lcm_square_dvd n (squareCandidates n) 1
  · simp
  · intro d hd
    simpa [squareCandidates] using (List.mem_filter.mp hd).2

/-- Canonical squarefree-times-square decomposition. -/
theorem squarefreePart_mul_square {n : Nat} (F : CheckedFactorization n) :
    squarefreePart F * squareDivisor F ^ 2 = n := by
  rw [Nat.mul_comm]
  exact Nat.mul_div_cancel' (squareDivisor_dvd_subject F)

/-- `squareDivisor` is the largest square divisor root. -/
theorem squareDivisor_spec {n : Nat} (F : CheckedFactorization n) :
    squareDivisor F ^ 2 ∣ n ∧
      ∀ d, d ^ 2 ∣ n → d ∣ squareDivisor F := by
  refine ⟨squareDivisor_dvd_subject F, ?_⟩
  intro d hd
  have hnraw : 0 < F.raw.subject := by
    have hv := F.valid
    simp only [checkFactorization, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.1.1
  have hn : 0 < n := F.subject_eq ▸ hnraw
  have hdle : d ≤ n := by
    by_cases hd0 : d = 0
    · subst d
      have : n = 0 := Nat.eq_zero_of_zero_dvd (by simpa using hd)
      omega
    · have hsqle := Nat.le_of_dvd hn hd
      have hself : d ≤ d ^ 2 := by
        rw [Nat.pow_two]
        exact Nat.le_mul_of_pos_right d (by omega)
      exact Nat.le_trans hself hsqle
  unfold squareDivisor
  apply dvd_foldl_lcm (values := squareCandidates n) (acc := 1)
  simp [squareCandidates, hd, Nat.lt_succ_of_le hdle]

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
