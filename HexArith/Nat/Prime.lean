/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.Nat.ModArith

public section

/-!
Mathlib-free combinatorial and prime-number lemmas for `HexArith`.

This module owns the local `Hex.Nat.choose` and `Hex.Nat.Prime` surfaces that the
computational core needs for binomial divisibility and Fermat-style congruence
statements, without importing Mathlib into the root arithmetic layer.
-/

namespace Hex

namespace Nat

/--
Binomial coefficients on natural numbers, defined by the Pascal recursion.
-/
@[expose]
noncomputable def choose : Nat -> Nat -> Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- `choose n 0 = 1`: the zeroth column of Pascal's triangle. -/
@[simp, grind =] theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [choose]

/--
`choose 0 (k + 1) = 0`: nontrivial entries vanish in the top row of Pascal's
triangle.
-/
@[simp, grind =] theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := by
  rfl

/-- Pascal's recurrence: `choose (n + 1) (k + 1) = choose n k + choose n (k + 1)`. -/
@[simp, grind =] theorem choose_succ_succ (n k : Nat) :
    choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := by
  rfl

/--
Entries past the diagonal of Pascal's triangle vanish: `choose n k = 0`
whenever `n < k`.
-/
theorem choose_eq_zero_of_lt {n k : Nat} (h : n < k) : choose n k = 0 := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => rfl
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          simp [choose]
          by_cases hk : n < k
          · simp [ih hk]
            exact ih (by omega)
          · exfalso
            omega

/-- The diagonal of Pascal's triangle is constantly one: `choose n n = 1`. -/
@[simp, grind =] theorem choose_self (n : Nat) : choose n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [choose, ih, choose_eq_zero_of_lt (by omega : n < n + 1)]

/--
A natural number is prime when it is at least `2` and its positive divisors are
trivial. This is the Mathlib-free prime predicate used by downstream modular
arithmetic layers.
-/
@[expose]
def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

namespace Prime

/-- Every prime is at least `2`. -/
theorem two_le {p : Nat} (hp : Hex.Nat.Prime p) : 2 ≤ p := hp.1

/-- Every prime is greater than `1`. -/
theorem one_lt {p : Nat} (hp : Hex.Nat.Prime p) : 1 < p := hp.two_le

/-- Every prime is positive. -/
theorem pos {p : Nat} (hp : Hex.Nat.Prime p) : 0 < p :=
  Nat.lt_of_lt_of_le (by decide) hp.two_le

/-- Every prime is nonzero. -/
theorem ne_zero {p : Nat} (hp : Hex.Nat.Prime p) : p ≠ 0 := Nat.ne_of_gt hp.pos

/-- Every prime is distinct from `1`. -/
theorem ne_one {p : Nat} (hp : Hex.Nat.Prime p) : p ≠ 1 := Nat.ne_of_gt hp.one_lt

/-- Build coprimality between a prime and a number it does not divide. -/
theorem coprime_of_not_dvd {p a : Nat} (hp : Hex.Nat.Prime p)
    (ha : ¬ p ∣ a) : Nat.Coprime p a := by
  rw [Nat.Coprime]
  have hgcd_dvd_p : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  rcases hp.2 (Nat.gcd p a) hgcd_dvd_p with hgcd | hgcd
  · exact hgcd
  · exfalso
    apply ha
    rw [← hgcd]
    exact Nat.gcd_dvd_right p a

/--
Euclid's lemma for the local prime predicate, in iff form: a prime divides a
product iff it divides one of the factors.
-/
theorem dvd_mul {p a b : Nat} (hp : Hex.Nat.Prime p) :
    p ∣ a * b ↔ p ∣ a ∨ p ∣ b := by
  constructor
  · intro h
    by_cases hb : p ∣ b
    · exact Or.inr hb
    · exact Or.inl ((coprime_of_not_dvd hp hb).dvd_of_dvd_mul_right h)
  · intro h
    cases h with
    | inl ha => exact Nat.dvd_trans ha (Nat.dvd_mul_right a b)
    | inr hb => exact Nat.dvd_trans hb (Nat.dvd_mul_left b a)

end Prime

private theorem not_dvd_of_pos_lt {p k : Nat} (hk : 0 < k) (hk' : k < p) :
    ¬ p ∣ k := by
  intro hpk
  rcases hpk with ⟨c, hc⟩
  have hc_pos : 0 < c := by
    cases c with
    | zero => omega
    | succ c => exact Nat.succ_pos c
  have : p ≤ k := by
    rw [hc]
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left p hc_pos
  omega

private theorem choose_one_right (n : Nat) : choose n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [choose]
      rw [ih]
      omega

/-- Multiplicative Pascal identity used to move from row recurrence to prime divisibility. -/
private theorem choose_succ_mul_eq (n k : Nat) :
    (k + 1) * choose (n + 1) (k + 1) = (n + 1) * choose n k := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [choose]
  | succ n ih =>
      cases k with
      | zero =>
          simp [choose, choose_one_right]
          omega
      | succ k =>
          grind [choose]

/-- Within-row multiplicative recurrence `(k+1) · choose n (k+1) = (n - k) · choose n k`.
Reading it left to right computes one Pascal row in a single linear pass, which is
what `chooseFast` exploits. -/
theorem succ_mul_choose_succ (n k : Nat) :
    (k + 1) * choose n (k + 1) = (n - k) * choose n k := by
  have hcross := choose_succ_mul_eq n k
  have hpascal : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl
  rw [hpascal, Nat.mul_add] at hcross
  rcases Nat.lt_or_ge n k with hlt | hge
  · rw [choose_eq_zero_of_lt hlt, choose_eq_zero_of_lt (Nat.lt_succ_of_lt hlt),
      Nat.mul_zero, Nat.mul_zero]
  · have hsplit : (n + 1) * choose n k
        = (n - k) * choose n k + (k + 1) * choose n k := by
      rw [← Nat.add_mul]
      congr 1
      omega
    rw [hsplit] at hcross
    omega

/--
Linear-time binomial coefficient.

`chooseFast n k` walks a single Pascal row from `choose n 0 = 1` using the
multiplicative recurrence `succ_mul_choose_succ`, so it costs `O(k)` natural-number
operations.  The proof-facing `choose` is the exponential Pascal double recursion
(`choose n k` spawns `Θ(choose n k)` calls); `chooseFast` is proven equal to it and
registered `@[csimp]`, so every compiled caller of `choose` runs this instead.
-/
@[expose]
def chooseFast (n k : Nat) : Nat :=
  if n < k then 0
  else (List.range k).foldl (fun acc j => acc * (n - j) / (j + 1)) 1

/-- The single-row multiplicative fold `acc * (n - j) / (j + 1)` over
`List.range k` computes the Pascal `choose n k` for `k ≤ n`. This is the shared
kernel behind `chooseFast` and any other executable single-row binomial. -/
theorem chooseFast_foldl (n : Nat) :
    ∀ k, k ≤ n →
      (List.range k).foldl (fun acc j => acc * (n - j) / (j + 1)) 1 = choose n k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      rw [List.range_succ, List.foldl_append, ih (Nat.le_of_succ_le hk)]
      simp only [List.foldl_cons, List.foldl_nil]
      have hid : choose n k * (n - k) = (k + 1) * choose n (k + 1) := by
        rw [Nat.mul_comm, succ_mul_choose_succ]
      rw [hid, Nat.mul_div_cancel_left _ (Nat.succ_pos k)]

/-- `chooseFast` agrees with the proof-facing Pascal `choose`. -/
theorem chooseFast_eq (n k : Nat) : chooseFast n k = choose n k := by
  unfold chooseFast
  by_cases h : n < k
  · rw [if_pos h]; exact (choose_eq_zero_of_lt h).symm
  · rw [if_neg h]; exact chooseFast_foldl n k (Nat.le_of_not_lt h)

@[csimp] theorem choose_eq_chooseFast : @choose = @chooseFast := by
  funext n k
  exact (chooseFast_eq n k).symm

/-- The row of Pascal's triangle increases up to its centre: `choose k j ≤
choose k (j + 1)` while `2 * (j + 1) ≤ k`. -/
theorem choose_le_succ_left {k j : Nat} (h : 2 * (j + 1) ≤ k) :
    choose k j ≤ choose k (j + 1) := by
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos j)
  rw [succ_mul_choose_succ k j]
  exact Nat.mul_le_mul_right (choose k j) (by omega)

/-- Everything on the left half of a row is at most the central entry:
`choose k j ≤ choose k (k / 2)` for `2 * j ≤ k`. -/
theorem choose_le_center (k : Nat) :
    ∀ (fuel j : Nat), k / 2 - j ≤ fuel → 2 * j ≤ k →
      choose k j ≤ choose k (k / 2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro j hfuel hj
      have : j = k / 2 := by omega
      subst this; exact Nat.le_refl _
  | succ fuel ih =>
      intro j hfuel hj
      by_cases hjc : j = k / 2
      · subst hjc; exact Nat.le_refl _
      · exact Nat.le_trans (choose_le_succ_left (by omega))
          (ih (j + 1) (by omega) (by omega))

/-- Even-row step for central-binomial monotonicity:
`choose (2t) t ≤ choose (2t+1) t`. -/
private theorem central_even (t : Nat) :
    choose (2 * t) t ≤ choose (2 * t + 1) t := by
  cases t with
  | zero => simp
  | succ s =>
      rw [choose_succ_succ (2 * (s + 1)) s]
      exact Nat.le_add_left _ _

/-- Odd-row step for central-binomial monotonicity:
`choose (2t+1) t ≤ choose (2t+2) (t+1)`. -/
private theorem central_odd (t : Nat) :
    choose (2 * t + 1) t ≤ choose (2 * t + 2) (t + 1) := by
  rw [show 2 * t + 2 = 2 * t + 1 + 1 from rfl, choose_succ_succ (2 * t + 1) t]
  exact Nat.le_add_right _ _

/-- The central binomial coefficient increases by one row at a time. -/
theorem centralChoose_le_succ (m : Nat) :
    choose m (m / 2) ≤ choose (m + 1) ((m + 1) / 2) := by
  rcases (by omega : m = 2 * (m / 2) ∨ m = 2 * (m / 2) + 1) with he | ho
  · have e2 : m + 1 = 2 * (m / 2) + 1 := by omega
    have e3 : (m + 1) / 2 = m / 2 := by omega
    rw [e3]
    calc choose m (m / 2)
        = choose (2 * (m / 2)) (m / 2) := by rw [← he]
      _ ≤ choose (2 * (m / 2) + 1) (m / 2) := central_even (m / 2)
      _ = choose (m + 1) (m / 2) := by rw [← e2]
  · have o2 : m + 1 = 2 * (m / 2) + 2 := by omega
    have o3 : (m + 1) / 2 = m / 2 + 1 := by omega
    rw [o3]
    calc choose m (m / 2)
        = choose (2 * (m / 2) + 1) (m / 2) := by rw [← ho]
      _ ≤ choose (2 * (m / 2) + 2) (m / 2 + 1) := central_odd (m / 2)
      _ = choose (m + 1) (m / 2 + 1) := by rw [← o2]

/-- The central binomial coefficient is monotone in the row index. -/
theorem centralChoose_mono {k n : Nat} (h : k ≤ n) :
    choose k (k / 2) ≤ choose n (n / 2) := by
  induction n with
  | zero =>
      have : k = 0 := Nat.le_zero.mp h
      subst this; exact Nat.le_refl _
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hlt | hge
      · exact Nat.le_trans (ih (Nat.le_of_lt_succ hlt)) (centralChoose_le_succ m)
      · have : k = m + 1 := Nat.le_antisymm h hge
        subst this; exact Nat.le_refl _

/-- Euclid-step bridge turning the multiplicative Pascal identity into `p ∣ choose p k`. -/
private theorem choose_prime_dvd_from_mul_identity {p k : Nat} (hp : Prime p)
    (hk : 0 < k) (hk' : k < p) : p ∣ choose p k := by
  cases k with
  | zero => omega
  | succ k =>
      cases p with
      | zero => omega
      | succ p =>
          have hmul : p + 1 ∣ (k + 1) * choose (p + 1) (k + 1) := by
            rw [choose_succ_mul_eq]
            exact Nat.dvd_mul_right (p + 1) (choose p k)
          rcases (Prime.dvd_mul hp).mp hmul with hdiv | hdiv
          · exact False.elim (not_dvd_of_pos_lt hk hk' hdiv)
          · exact hdiv

/-- The `k`th binomial term `choose n k * a^(n-k) * b^k` in `(a + b)^n`. -/
private def chooseTerm (n a b k : Nat) : Nat :=
  choose n k * a ^ (n - k) * b ^ k

/-- Partial sum of the first binomial terms used to prove `(a + b)^n`. -/
private def chooseSum (n a b : Nat) : Nat -> Nat
  | 0 => 0
  | k + 1 => chooseSum n a b k + chooseTerm n a b k

private theorem chooseSum_zero (a b : Nat) : chooseSum 0 a b 1 = 1 := by
  simp [chooseSum, chooseTerm]

/-- Row recurrence for binomial partial sums across adjacent Pascal rows. -/
private theorem chooseSum_succ_row (n a b m : Nat) (hm : m ≤ n + 1) :
    chooseSum (n + 1) a b (m + 1) =
      a * chooseSum n a b (m + 1) + b * chooseSum n a b m := by
  induction m with
  | zero =>
      simp [chooseSum, chooseTerm, Nat.pow_succ]
      rw [Nat.mul_comm]
  | succ m ih =>
      rw [chooseSum, ih (by omega)]
      unfold chooseTerm
      by_cases hlt : m < n
      · have hpow : a ^ (n - m) = a * a ^ (n - (m + 1)) := by
          have hsub' : n - m = n - (m + 1) + 1 := by omega
          rw [hsub', Nat.pow_succ, Nat.mul_comm]
        simp [chooseSum, chooseTerm, choose_succ_succ, hpow, Nat.pow_succ,
          Nat.mul_add, Nat.add_mul, Nat.add_assoc]
        ac_rfl
      · have hmn : m = n := by omega
        subst m
        have hzero : choose n (n + 1) = 0 := choose_eq_zero_of_lt (by omega)
        simp [chooseSum, chooseTerm, choose_succ_succ, hzero, Nat.pow_succ,
          Nat.mul_add, Nat.add_assoc]
        ac_rfl

/-- Binomial expansion packaged as equality with the full `chooseSum` row. -/
private theorem add_pow_chooseSum (n a b : Nat) :
    (a + b) ^ n = chooseSum n a b (n + 1) := by
  induction n with
  | zero =>
      simp [chooseSum, chooseTerm]
  | succ n ih =>
      calc
        (a + b) ^ (n + 1) = (a + b) ^ n * (a + b) := Nat.pow_succ (a + b) n
        _ = (a + b) ^ n * a + (a + b) ^ n * b := by rw [Nat.mul_add]
        _ = a * chooseSum n a b (n + 1) + b * chooseSum n a b (n + 1) := by
            rw [ih]
            ac_rfl
        _ = a * chooseSum n a b (n + 1 + 1) + b * chooseSum n a b (n + 1) := by
            have hzero : choose n (n + 1) = 0 := choose_eq_zero_of_lt (by omega)
            have htail : chooseSum n a b (n + 1 + 1) = chooseSum n a b (n + 1) := by
              simp [chooseSum, chooseTerm, hzero]
            rw [htail]
        _ = chooseSum (n + 1) a b (n + 1 + 1) :=
            (chooseSum_succ_row n a b (n + 1) (by omega)).symm

/-- Middle binomial terms are divisible by `p` once their coefficients are. -/
private theorem chooseTerm_dvd_of_middle {p a b k : Nat}
    (hchoose : ∀ k, 0 < k → k < p → p ∣ choose p k)
    (hk0 : 0 < k) (hkp : k < p) : p ∣ chooseTerm p a b k := by
  unfold chooseTerm
  simpa [Nat.mul_assoc] using
    Nat.dvd_mul_right_of_dvd (hchoose k hk0 hkp) (a ^ (p - k) * b ^ k)

/-- Middle binomial terms vanish modulo `p` under the prime-row divisibility hypothesis. -/
private theorem chooseTerm_mod_eq_zero_of_middle {p a b k : Nat}
    (hchoose : ∀ k, 0 < k → k < p → p ∣ choose p k)
    (hk0 : 0 < k) (hkp : k < p) : chooseTerm p a b k % p = 0 := by
  exact Nat.mod_eq_zero_of_dvd (chooseTerm_dvd_of_middle hchoose hk0 hkp)

/-- Prefix sums modulo `p` reduce to the leading term after erasing middle terms. -/
private theorem chooseSum_prefix_mod {p a b m : Nat}
    (hchoose : ∀ k, 0 < k → k < p → p ∣ choose p k)
    (hm0 : 0 < m) (hmp : m ≤ p) : chooseSum p a b m % p = a ^ p % p := by
  induction m with
  | zero => omega
  | succ m ih =>
      cases m with
      | zero =>
          simp [chooseSum, chooseTerm]
      | succ m =>
          have hprev : chooseSum p a b (m + 1) % p = a ^ p % p := by
            exact ih (by omega) (by omega)
          have hterm :
              chooseTerm p a b (m + 1) % p = 0 :=
            chooseTerm_mod_eq_zero_of_middle hchoose (by omega) (by omega)
          calc
            chooseSum p a b (m + 1 + 1) % p
                = (chooseSum p a b (m + 1) + chooseTerm p a b (m + 1)) % p := by
                    rfl
            _ = (chooseSum p a b (m + 1) % p
                  + chooseTerm p a b (m + 1) % p) % p := Nat.add_mod _ _ _
            _ = a ^ p % p := by
                  rw [hprev, hterm, Nat.add_zero, Nat.mod_mod]

/-- Freshman's-dream step modulo `p`, abstracted over binomial divisibility. -/
private theorem add_pow_prime_mod_of_choose_dvd {p : Nat} (hp : Prime p) (a b : Nat)
    (hchoose : ∀ k, 0 < k → k < p → p ∣ choose p k) :
    (a + b) ^ p % p = (a ^ p + b ^ p) % p := by
  have hp_pos : 0 < p := by
    have htwo := hp.1
    omega
  have hprefix : chooseSum p a b p % p = a ^ p % p :=
    chooseSum_prefix_mod hchoose hp_pos (Nat.le_refl p)
  have hlast : chooseTerm p a b p = b ^ p := by
    simp [chooseTerm, choose_self]
  calc
    (a + b) ^ p % p = chooseSum p a b (p + 1) % p := by
      rw [add_pow_chooseSum]
    _ = (chooseSum p a b p + chooseTerm p a b p) % p := by
      rfl
    _ = (chooseSum p a b p % p + chooseTerm p a b p % p) % p := Nat.add_mod _ _ _
    _ = (a ^ p % p + b ^ p % p) % p := by
      rw [hprefix, hlast]
    _ = (a ^ p + b ^ p) % p := by
      rw [← Nat.add_mod]

/-- Derives Fermat's little theorem by induction from the Freshman's-dream step. -/
private theorem pow_prime_mod_from_add_pow {p : Nat} (hp : Prime p) (a : Nat)
    (hadd : ∀ a b, (a + b) ^ p % p = (a ^ p + b ^ p) % p) :
    a ^ p % p = a % p := by
  have hp_pos : 0 < p := by
    have htwo := hp.1
    omega
  induction a with
  | zero => simp [Nat.zero_pow hp_pos]
  | succ a ih =>
      have h := hadd a 1
      simp [Nat.one_pow] at h
      calc
        (a + 1) ^ p % p = (a ^ p + 1) % p := h
        _ = (a ^ p % p + 1) % p := (Nat.mod_add_mod (a ^ p) p 1).symm
        _ = (a % p + 1) % p := by rw [ih]
        _ = (a + 1) % p := Nat.mod_add_mod a p 1

/--
Every nontrivial binomial coefficient in the `p`th row of Pascal's triangle is
divisible by `p` when `p` is prime. This is the binomial-divisibility fact used
to erase the middle terms in `add_pow_prime_mod`.
-/
theorem choose_prime_dvd {p k : Nat} (hp : Prime p) (hk : 0 < k) (hk' : k < p) :
    p ∣ choose p k := by
  exact choose_prime_dvd_from_mul_identity hp hk hk'

/--
Freshman's dream modulo a prime: `(a + b)^p` is congruent to `a^p + b^p`
modulo `p`, because all middle binomial terms vanish.
-/
theorem add_pow_prime_mod {p : Nat} (hp : Prime p) (a b : Nat) :
    (a + b) ^ p % p = (a ^ p + b ^ p) % p := by
  exact add_pow_prime_mod_of_choose_dvd hp a b (fun k hk hk' =>
    choose_prime_dvd hp hk hk')

/--
Fermat's little theorem in the residue form used by downstream modular
arithmetic code: raising a natural number to the `p`th power preserves its
residue modulo a prime `p`.
-/
theorem pow_prime_mod {p : Nat} (hp : Prime p) (a : Nat) :
    a ^ p % p = a % p := by
  exact pow_prime_mod_from_add_pow hp a (fun a b => add_pow_prime_mod hp a b)

/--
Executable trial-division primality test. Returns `true` only when `2 ≤ n`
and no integer in `[2, n)` divides `n`. Used by downstream prime-search
extensions to produce primality witnesses for candidates beyond any fixed
list, without depending on `Mathlib` or `native_decide`.
-/
@[expose]
def isPrimeTrial (n : Nat) : Bool :=
  decide (2 ≤ n) &&
    (List.range n).all (fun k => decide (k < 2) || decide (n % k ≠ 0))

private theorem range_all_eq_true_of_isPrimeTrial {n : Nat}
    (h : isPrimeTrial n = true) :
    ∀ k, k < n → 2 ≤ k → n % k ≠ 0 := by
  unfold isPrimeTrial at h
  rw [Bool.and_eq_true] at h
  obtain ⟨_, hall⟩ := h
  rw [List.all_eq_true] at hall
  intro k hk hk2
  have hmem : k ∈ List.range n := List.mem_range.mpr hk
  have := hall k hmem
  rw [Bool.or_eq_true] at this
  rcases this with hlt | hmod
  · have : k < 2 := of_decide_eq_true hlt
    omega
  · exact of_decide_eq_true hmod

private theorem two_le_of_isPrimeTrial {n : Nat} (h : isPrimeTrial n = true) :
    2 ≤ n := by
  unfold isPrimeTrial at h
  rw [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

/--
Soundness of the trial-division primality test against the project-local
`Hex.Nat.Prime` predicate. Used by the BZ extended prime search to lift a
runtime candidate into a `SmallPrimeCandidate` with explicit primality
evidence, without falling back to a hardcoded list.
-/
theorem isPrimeTrial_isPrime {n : Nat} (h : isPrimeTrial n = true) :
    Prime n := by
  refine ⟨two_le_of_isPrimeTrial h, ?_⟩
  intro m hm
  have h2n : 2 ≤ n := two_le_of_isPrimeTrial h
  have hno : ∀ k, k < n → 2 ≤ k → n % k ≠ 0 :=
    range_all_eq_true_of_isPrimeTrial h
  have hn_pos : 0 < n := by omega
  have hm_le_n : m ≤ n := Nat.le_of_dvd hn_pos hm
  by_cases hm0 : m = 0
  · subst hm0
    have : n = 0 := Nat.eq_zero_of_zero_dvd hm
    omega
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  by_cases hmn : m = n
  · exact Or.inr hmn
  exfalso
  have hm2 : 2 ≤ m := by
    rcases m with _ | _ | m
    · exact absurd rfl hm0
    · exact absurd rfl hm1
    · omega
  have hmlt : m < n := Nat.lt_of_le_of_ne hm_le_n hmn
  have hmod : n % m = 0 := by
    rcases hm with ⟨k, hk⟩
    rw [hk]
    exact Nat.mul_mod_right m k
  exact hno m hmlt hm2 hmod

end Nat

end Hex
