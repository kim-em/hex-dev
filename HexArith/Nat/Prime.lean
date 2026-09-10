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
computational library needs for binomial divisibility and Fermat-style congruence
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

/-- A prime that divides a power divides its base. -/
theorem dvd_of_dvd_pow {p a k : Nat} (hp : Hex.Nat.Prime p)
    (h : p ∣ a ^ k) : p ∣ a := by
  induction k with
  | zero =>
      exact absurd (Nat.dvd_one.mp h) hp.ne_one
  | succ k ih =>
      rw [Nat.pow_succ] at h
      exact (hp.dvd_mul.mp h).elim ih id

end Prime

/-- Primality as a bounded search: for `p ≥ 2`, having only trivial divisors is
the same as having no divisor strictly between `1` and `p`. The point of the
restatement is that the right-hand side quantifies over a finite range, which is
what makes the decidability instance below possible. -/
theorem prime_iff_forall_lt (p : Nat) :
    Prime p ↔ 2 ≤ p ∧ ∀ m, m < p → 2 ≤ m → ¬ m ∣ p := by
  constructor
  · rintro ⟨hp, hdiv⟩
    refine ⟨hp, ?_⟩
    intro m hmlt hm2 hmdvd
    rcases hdiv m hmdvd with rfl | rfl <;> omega
  · rintro ⟨hp, hno⟩
    refine ⟨hp, ?_⟩
    intro m hmdvd
    have hppos : 0 < p := by omega
    have hmle : m ≤ p := Nat.le_of_dvd hppos hmdvd
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · rcases Nat.lt_or_ge m 1 with hm1 | hm1
      · have hm0 : m = 0 := by omega
        subst hm0
        have : p = 0 := Nat.zero_dvd.mp hmdvd
        omega
      · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge m p with hmlt | hmge
      · exact absurd hmdvd (hno m hmlt hm2)
      · exact Or.inr (Nat.le_antisymm hmle hmge)

/-- Primality by trial division up to the square root.

A composite has a nontrivial divisor `d` with `d * d ≤ p`: of any factor pair
`p = d * e`, the smaller one qualifies. Bounding the search that way is what
makes `decide` practical. The linear form above needs `p` steps, which is fine
for a two-digit modulus and is not fine beyond that — `decide` on
`Prime 3221` takes about fourteen seconds through it, and the primes that turn
up in `p ^ n - 1` for the committed Conway table run to five digits. This form
needs about `√p` steps instead. -/
theorem prime_iff_forall_le_sqrt (p : Nat) :
    Prime p ↔ 2 ≤ p ∧ ∀ m, m < Nat.sqrt p + 1 → 2 ≤ m → ¬ m ∣ p := by
  -- Core supplies `sqrt k * sqrt k ≤ k` and `k < (sqrt k + 1) ^ 2`; everything
  -- here is derived from those two, since `HexArith` is Mathlib-free.
  have sq_le_of_lt_succ : ∀ {a k : Nat}, a * a ≤ k → a < Nat.sqrt k + 1 := by
    intro a k hak
    rcases Nat.lt_or_ge a (Nat.sqrt k + 1) with h | h
    · exact h
    · exact absurd hak (by
        have hmul : (Nat.sqrt k + 1) * (Nat.sqrt k + 1) ≤ a * a :=
          Nat.mul_le_mul h h
        have hlt : k < (Nat.sqrt k + 1) * (Nat.sqrt k + 1) := Nat.lt_succ_sqrt k
        omega)
  have sqrt_lt : ∀ k : Nat, 2 ≤ k → Nat.sqrt k < k := by
    intro k hk
    rcases Nat.lt_or_ge (Nat.sqrt k) k with h | h
    · exact h
    · exact absurd (Nat.sqrt_le k) (by
        have hmul : k * k ≤ Nat.sqrt k * Nat.sqrt k := Nat.mul_le_mul h h
        have hkk : k * 2 ≤ k * k := Nat.mul_le_mul_left k hk
        omega)
  constructor
  · rintro ⟨hp, hdiv⟩
    refine ⟨hp, ?_⟩
    intro m hmlt hm2 hmdvd
    rcases hdiv m hmdvd with rfl | rfl
    · omega
    · have := sqrt_lt m (by omega)
      omega
  · rintro ⟨hp, hno⟩
    refine ⟨hp, ?_⟩
    intro d hd
    obtain ⟨e, he⟩ := hd
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    by_cases hdp : d = p
    · exact Or.inr hdp
    exfalso
    have hd0 : d ≠ 0 := by
      intro h
      rw [h, Nat.zero_mul] at he
      omega
    have he0 : e ≠ 0 := by
      intro h
      rw [h, Nat.mul_zero] at he
      omega
    have hd2 : 2 ≤ d := by omega
    have he2 : 2 ≤ e := by
      rcases Nat.lt_or_ge e 2 with h | h
      · have he1 : e = 1 := by omega
        rw [he1, Nat.mul_one] at he
        omega
      · exact h
    rcases Nat.le_total d e with h | h
    · have hdd : d * d ≤ p := by
        calc d * d ≤ d * e := Nat.mul_le_mul_left d h
          _ = p := he.symm
      exact hno d (sq_le_of_lt_succ hdd) hd2 ⟨e, he⟩
    · have hee : e * e ≤ p := by
        calc e * e ≤ d * e := Nat.mul_le_mul_right e h
          _ = p := he.symm
      exact hno e (sq_le_of_lt_succ hee) he2 ⟨d, by rw [he, Nat.mul_comm]⟩

/--
Primality from trial division up to a caller-supplied bound.

`prime_iff_forall_le_sqrt` cannot drive a `decide`: core's `Nat.sqrt` is
defined by well-founded recursion, so the kernel will not evaluate it. Taking
the bound as data instead keeps everything the kernel sees structural. The
caller supplies `b` with `p < (b + 1) ^ 2`, which `decide` checks in one
multiplication, and then only `b + 1` divisors have to be ruled out rather
than `p` of them.

The `Decidable` instance now routes through `isPrimeTrial` (defined below), so
`decide` is `O (√p)` remainder tests; this lemma remains for callers that
already hold an explicit bound and want the divisor obligations alone.
-/
theorem prime_of_bounded (p b : Nat) (hp : 2 ≤ p)
    (hb : p < (b + 1) * (b + 1))
    (h : ∀ m, m < b + 1 → 2 ≤ m → ¬ m ∣ p) :
    Prime p := by
  refine (prime_iff_forall_le_sqrt p).mpr ⟨hp, ?_⟩
  intro m hmlt hm2 hmdvd
  refine h m ?_ hm2 hmdvd
  -- `m ≤ sqrt p` gives `m * m ≤ p < (b + 1) ^ 2`, hence `m < b + 1`.
  have hmsq : m * m ≤ p := by
    have hle : m ≤ Nat.sqrt p := by omega
    have := Nat.mul_le_mul hle hle
    have hs := Nat.sqrt_le p
    omega
  rcases Nat.lt_or_ge m (b + 1) with hlt | hge
  · exact hlt
  · exact absurd hmsq (by
      have := Nat.mul_le_mul hge hge
      omega)

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

{name}`Hex.Nat.binom` walks a single Pascal row from
`choose n 0 = 1` using the multiplicative recurrence
{name}`Hex.Nat.succ_mul_choose_succ`, folding over the shorter half
`min k (n - k)` of the row using {name}`Hex.Nat.choose_symm`. It therefore
costs `O(min k (n - k))` natural-number operations. The proof-facing
{name}`Hex.Nat.choose` is the exponential Pascal recursion; the forward
correctness theorem `binom_eq_choose`, registered with `@[csimp]`, makes
compiled callers use this linear fold.
-/
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
  · rw [ite_eq_left h]; exact (choose_eq_zero_of_lt h).symm
  · rw [ite_eq_right h]
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

/-- Euclid-step correspondence turning the multiplicative Pascal identity into `p ∣ choose p k`. -/
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
      · rw [ite_eq_left hstop] at h
        intro d hkd hd hsq
        have hdk : d = k := by
          simp only [Nat.pow_zero] at hd
          omega
        subst d
        omega
      · rw [ite_eq_right hstop] at h
        intro d hkd hd _
        have hdk : d = k := by
          simp only [Nat.pow_zero] at hd
          omega
        subst d
        exact of_decide_eq_true h
  | succ fuel ih =>
      rw [isPrimeTrialAux] at h
      by_cases hstop : n < k * k
      · rw [ite_eq_left hstop] at h
        intro d hkd _ hsq
        have hkk : k * k ≤ d * d := Nat.mul_le_mul hkd hkd
        omega
      · rw [ite_eq_right hstop, Bool.and_eq_true] at h
        intro d hkd hd hsq
        have hpow : 2 ^ (fuel + 1) = 2 ^ fuel + 2 ^ fuel := by
          rw [Nat.pow_succ]
          omega
        by_cases hleft : d < k + 2 ^ fuel
        · exact ih h.1 d hkd hleft hsq
        · apply ih h.2 d (by omega) ?_ hsq
          rw [hpow] at hd
          omega

/-- A nontrivial divisor yields a divisor at most the square root: of `m` and
its cofactor, the smaller one squares to at most `n`. -/
theorem exists_trial_divisor {n m : Nat} (hn : 0 < n) (hm : m ∣ n)
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
Soundness of the trial-division primality test against the Mathlib-free
{name}`Hex.Nat.Prime` predicate. It turns a successful runtime test into
explicit primality evidence without relying on a hardcoded prime table.
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
      · rw [ite_eq_left hstop]
      · rw [ite_eq_right hstop]
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
      · rw [ite_eq_left hstop]
      · rw [ite_eq_right hstop, Bool.and_eq_true]
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

/-- Primality is decidable through {name}`isPrimeTrial`, so `decide` costs
`O (√p)` remainder tests with kernel reduction depth logarithmic in the
candidate count. -/
instance instDecidablePrime (p : Nat) : Decidable (Prime p) :=
  decidable_of_iff (isPrimeTrial p = true)
    ⟨isPrimeTrial_isPrime, isPrimeTrial_of_prime⟩

private theorem exists_small_divisor_of_not_prime {d : Nat} (h2 : 2 ≤ d)
    (hnp : ¬ Prime d) : ∃ m, 2 ≤ m ∧ m < d ∧ m ∣ d := by
  have hfail : ¬ ∀ m, m < d → 2 ≤ m → ¬ m ∣ d := by
    intro hall
    exact hnp ((prime_iff_forall_lt d).mpr ⟨h2, hall⟩)
  rcases Classical.not_forall.mp hfail with ⟨m, hm⟩
  by_cases hmlt : m < d
  · by_cases hm2 : 2 ≤ m
    · by_cases hdvd : m ∣ d
      · exact ⟨m, hm2, hmlt, hdvd⟩
      · exact absurd (fun _ _ => hdvd) hm
    · exact absurd (fun _ h2m => absurd h2m hm2) hm
  · exact absurd (fun hlt => absurd hlt hmlt) hm

/-- Every natural number at least `2` has a prime divisor. -/
theorem exists_prime_dvd {d : Nat} (h : 2 ≤ d) : ∃ q, Prime q ∧ q ∣ d := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    by_cases hp : Prime d
    · exact ⟨d, hp, Nat.dvd_refl d⟩
    · obtain ⟨m, hm2, hmlt, hmdvd⟩ := exists_small_divisor_of_not_prime h hp
      obtain ⟨q, hq, hqm⟩ := ih m hmlt hm2
      exact ⟨q, hq, Nat.dvd_trans hqm hmdvd⟩

/-- A composite number has a prime divisor whose square is at most the
number. This is the small-divisor witness the Pocklington argument finishes
with. -/
theorem exists_prime_le_sqrt {n : Nat} (h : 2 ≤ n) (hcomp : ¬ Prime n) :
    ∃ p, Prime p ∧ p ∣ n ∧ p * p ≤ n := by
  obtain ⟨m, hm2, hmlt, hmdvd⟩ := exists_small_divisor_of_not_prime h hcomp
  obtain ⟨d, hd2, hdsq, hddvd⟩ :=
    exists_trial_divisor (by omega : 0 < n) hmdvd (by omega) (by omega)
  obtain ⟨q, hq, hqd⟩ := exists_prime_dvd hd2
  refine ⟨q, hq, Nat.dvd_trans hqd hddvd, ?_⟩
  have hqle : q ≤ d := Nat.le_of_dvd (by omega) hqd
  have := Nat.mul_le_mul hqle hqle
  omega

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
