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
what `binom` exploits. -/
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

/-- Pascal's triangle is symmetric across each row: `choose n (n - k) = choose n k`
for `k ≤ n`. This is the symmetry the min-optimized `binom` fold exploits to walk
the shorter half of the row. -/
theorem choose_symm : ∀ {n k : Nat}, k ≤ n → choose n (n - k) = choose n k := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have : k = 0 := Nat.le_zero.mp hk
      subst this; rfl
  | succ n ih =>
      intro k hk
      cases k with
      | zero => rw [Nat.sub_zero, choose_self, choose_zero_right]
      | succ j =>
          have hj : j ≤ n := Nat.le_of_succ_le_succ hk
          rw [Nat.succ_sub_succ]
          rcases Nat.lt_or_ge j n with hlt | hge
          · have hnj : n - j = (n - (j + 1)) + 1 := by omega
            rw [hnj]
            simp only [choose_succ_succ]
            have e : (n - (j + 1)) + 1 = n - j := by omega
            rw [ih hlt, e, ih hj, Nat.add_comm]
          · have hjn : j = n := Nat.le_antisymm hj hge
            subst hjn
            rw [Nat.sub_self, choose_zero_right, choose_self]

/--
Linear-time binomial coefficient.

`binom n k` walks a single Pascal row from `choose n 0 = 1` using the
multiplicative recurrence `succ_mul_choose_succ`, folding over the shorter half
`min k (n - k)` of the row (the row is symmetric, `choose_symm`), so it costs
`O(min k (n - k))` natural-number operations.  The proof-facing `choose` is the
exponential Pascal double recursion (`choose n k` spawns `Θ(choose n k)` calls);
`binom` is proven equal to it (`binom_eq_choose`) and registered `@[csimp]`, so
every compiled caller of `choose` runs this instead. -/
@[expose]
def binom (n k : Nat) : Nat :=
  if n < k then 0
  else (List.range (min k (n - k))).foldl (fun acc i => acc * (n - i) / (i + 1)) 1

/-- The multiplicative fold over `List.range m` computes `choose n m` for `m ≤ n`. -/
private theorem binom_foldl (n : Nat) :
    ∀ m, m ≤ n →
      (List.range m).foldl (fun acc i => acc * (n - i) / (i + 1)) 1 = choose n m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
      intro hm
      rw [List.range_succ, List.foldl_append, ih (Nat.le_of_succ_le hm)]
      simp only [List.foldl_cons, List.foldl_nil]
      have hid : choose n m * (n - m) = (m + 1) * choose n (m + 1) := by
        rw [Nat.mul_comm, succ_mul_choose_succ]
      rw [hid, Nat.mul_div_cancel_left _ (Nat.succ_pos m)]

/-- The min-optimized `binom` fold agrees with the proof-facing Pascal `choose`. -/
theorem binom_eq_choose (n k : Nat) : binom n k = choose n k := by
  unfold binom
  by_cases h : n < k
  · rw [if_pos h]; exact (choose_eq_zero_of_lt h).symm
  · rw [if_neg h]
    have hkn : k ≤ n := Nat.le_of_not_lt h
    rcases Nat.le_total k (n - k) with hle | hle
    · rw [Nat.min_eq_left hle]; exact binom_foldl n k hkn
    · rw [Nat.min_eq_right hle, binom_foldl n (n - k) (Nat.sub_le n k)]
      exact choose_symm hkn

@[csimp] theorem choose_eq_binom : @choose = @binom := by
  funext n k
  exact (binom_eq_choose n k).symm

/-- Choosing `0` elements always gives `1`. -/
@[simp, grind =] theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by
  simp [binom]

/-- Choosing `k + 1` elements from `0` is impossible. -/
@[simp, grind =] theorem binom_zero_succ (k : Nat) : binom 0 (k + 1) = 0 := by
  simp [binom]

/-- The binomial coefficient `binom n k` vanishes when `n < k`. -/
theorem binom_eq_zero_of_lt {n k : Nat} (h : n < k) : binom n k = 0 := by
  simp [binom, h]

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
Balanced trial division over the `2 ^ fuel` candidates starting at `k`.
The square guard is checked before descending into an interval, so no
candidate with `n < k * k` is tested. Splitting the interval in half keeps
kernel reduction depth logarithmic in the number of candidate divisors.
This helper is a primality test only with a range large enough to cover every
small divisor; `isPrimeTrial` is the supported entry point.
-/
@[expose] def isPrimeTrialAux (n : Nat) : Nat → Nat → Bool
  | 0, k =>
      if n < k * k then
        true
      else
        decide (n % k ≠ 0)
  | fuel + 1, k =>
      if n < k * k then
        true
      else
        isPrimeTrialAux n fuel k &&
          isPrimeTrialAux n fuel (k + 2 ^ fuel)

/--
Executable bounded trial-division primality test. Returns `true` exactly when
`n` is prime. Candidate divisors start at `2`, and the loop stops before
testing the first `k` whose square exceeds `n`; thus it performs at most
`⌊√n⌋ - 1` remainder tests. It remains pure Lean so emitted primality
certificates can be replayed by the kernel without `Mathlib`, `native_decide`,
or a fixed prime table.
-/
@[expose]
def isPrimeTrial (n : Nat) : Bool :=
  decide (2 ≤ n) && isPrimeTrialAux n (n.log2 + 1) 2

private theorem two_le_of_isPrimeTrial {n : Nat} (h : isPrimeTrial n = true) :
    2 ≤ n := by
  unfold isPrimeTrial at h
  rw [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

private theorem no_divisor_of_isPrimeTrialAux {n fuel k : Nat}
    (h : isPrimeTrialAux n fuel k = true) :
    ∀ d, k ≤ d → d < k + 2 ^ fuel → d * d ≤ n → n % d ≠ 0 := by
  induction fuel generalizing k with
  | zero =>
      rw [isPrimeTrialAux] at h
      by_cases hstop : n < k * k
      · rw [if_pos hstop] at h
        intro d hkd hd hsq
        have hdk : d = k := by
          simp only [Nat.pow_zero] at hd
          omega
        subst d
        omega
      · rw [if_neg hstop] at h
        intro d hkd hd _
        have hdk : d = k := by
          simp only [Nat.pow_zero] at hd
          omega
        subst d
        exact of_decide_eq_true h
  | succ fuel ih =>
      rw [isPrimeTrialAux] at h
      by_cases hstop : n < k * k
      · rw [if_pos hstop] at h
        intro d hkd _ hsq
        have hkk : k * k ≤ d * d := Nat.mul_le_mul hkd hkd
        omega
      · rw [if_neg hstop, Bool.and_eq_true] at h
        intro d hkd hd hsq
        have hpow : 2 ^ (fuel + 1) = 2 ^ fuel + 2 ^ fuel := by
          rw [Nat.pow_succ]
          omega
        by_cases hleft : d < k + 2 ^ fuel
        · exact ih h.1 d hkd hleft hsq
        · apply ih h.2 d (by omega) ?_ hsq
          rw [hpow] at hd
          omega

private theorem exists_trial_divisor {n m : Nat} (hn : 0 < n) (hm : m ∣ n)
    (hm1 : m ≠ 1) (hmn : m ≠ n) :
    ∃ d, 2 ≤ d ∧ d * d ≤ n ∧ d ∣ n := by
  rcases hm with ⟨c, hc⟩
  have hm0 : m ≠ 0 := by
    intro h
    subst m
    simp at hc
    omega
  have hm2 : 2 ≤ m := by omega
  have hc0 : c ≠ 0 := by
    intro h
    subst c
    simp at hc
    omega
  have hc1 : c ≠ 1 := by
    intro h
    subst c
    simp at hc
    exact hmn hc.symm
  have hc2 : 2 ≤ c := by omega
  by_cases hmc : m ≤ c
  · refine ⟨m, hm2, ?_, ⟨c, hc⟩⟩
    rw [hc]
    exact Nat.mul_le_mul_left m hmc
  · have hcm : c ≤ m := Nat.le_of_not_ge hmc
    refine ⟨c, hc2, ?_, ⟨m, ?_⟩⟩
    · rw [hc]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left c hcm
    · simpa [Nat.mul_comm] using hc

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
  have hn_pos : 0 < n := by omega
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  by_cases hmn : m = n
  · exact Or.inr hmn
  exfalso
  obtain ⟨d, hd2, hdsq, hdvd⟩ :=
    exists_trial_divisor hn_pos hm hm1 hmn
  have hd_le_sq : d ≤ d * d := Nat.le_mul_of_pos_right d (by omega)
  have hd_le_n : d ≤ n := Nat.le_trans hd_le_sq hdsq
  have haux : isPrimeTrialAux n (n.log2 + 1) 2 = true := by
    unfold isPrimeTrial at h
    rw [Bool.and_eq_true] at h
    exact h.2
  have hn_lt_pow : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  have hno : n % d ≠ 0 :=
    no_divisor_of_isPrimeTrialAux haux d hd2 (by omega) hdsq
  exact hno (Nat.mod_eq_zero_of_dvd hdvd)

private theorem isPrimeTrialAux_of_prime {n : Nat} (hn : Prime n) :
    ∀ fuel k, 2 ≤ k → isPrimeTrialAux n fuel k = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro k hk2
      rw [isPrimeTrialAux]
      by_cases hstop : n < k * k
      · rw [if_pos hstop]
      · rw [if_neg hstop]
        apply decide_eq_true
        intro hmod
        have hdvd : k ∣ n := Nat.dvd_of_mod_eq_zero hmod
        rcases hn.2 k hdvd with hk1 | hkn
        · omega
        · subst k
          have hnn : n * n ≤ n := Nat.le_of_not_gt hstop
          have hn_lt_mul : n < n * n := by
            simpa using (Nat.mul_lt_mul_left hn.pos).2 hn.one_lt
          omega
  | succ fuel ih =>
      intro k hk2
      rw [isPrimeTrialAux]
      by_cases hstop : n < k * k
      · rw [if_pos hstop]
      · rw [if_neg hstop, Bool.and_eq_true]
        exact ⟨ih k hk2,
          ih (k + 2 ^ fuel) (Nat.le_trans hk2 (Nat.le_add_right k _))⟩

/--
Completeness of the executable trial-division test: every project-local prime
witness makes the Boolean checker return `true`.
-/
theorem isPrimeTrial_of_prime {n : Nat} (h : Prime n) :
    isPrimeTrial n = true := by
  unfold isPrimeTrial
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true h.two_le,
    isPrimeTrialAux_of_prime h (n.log2 + 1) 2 (by decide)⟩

/-! Regression coverage for the bounded checker: small inputs, primes, perfect
squares, and semiprimes whose least factor is close to the square root. -/

#guard isPrimeTrial 0 = false
#guard isPrimeTrial 1 = false
#guard isPrimeTrial 2 = true
#guard isPrimeTrial 3 = true
#guard isPrimeTrial 4 = false
#guard isPrimeTrial 97 = true
#guard isPrimeTrial 49 = false
#guard isPrimeTrial 121 = false
#guard isPrimeTrial 899 = false
#guard ((List.range 1000).filter isPrimeTrial).length = 168

end Nat

end Hex
