import HexArith.Nat.ModArith
import HexArith.UInt64.Wide

/-!
Nat-level Barrett reduction for `HexArith`.

This module states the pure arithmetic reduction used by the `UInt64` Barrett
implementation. It works with the radix `R = 2^64` abstractly at `Nat`, leaving
all machine-word encoding details to later layers.
-/

/-- The single-word radix used by the `UInt64` Barrett reduction. -/
def barrettRadix : Nat := UInt64.word

/--
Barrett reduction at the Nat level.

Given `T = a * b` with `T < 2^64` and `pinv = floor(R / p)`, approximate the
quotient using one multiply-and-shift step and correct the remainder by at most
one subtraction.
-/
def barrettReduceNat (p pinv T : Nat) : Nat :=
  let q := T * pinv / barrettRadix
  let r := T - q * p
  if r ≥ p then r - p else r

/--
The Barrett quotient computed from `floor(R / p)` never exceeds the exact
quotient. This is the no-underflow fact needed when forming
`T - q * p`.
-/
theorem barrettQuotient_le_div (hp : 1 < p) (hpinv : pinv = barrettRadix / p) :
    T * pinv / barrettRadix ≤ T / p := by
  subst pinv
  have hp0 : 0 < p := by omega
  have hRpos : 0 < barrettRadix := by
    simp [barrettRadix, UInt64.word]
  refine (Nat.le_div_iff_mul_le hp0).2 ?_
  let q := T * (barrettRadix / p) / barrettRadix
  have hqR : q * barrettRadix ≤ T * (barrettRadix / p) := by
    simpa [q] using Nat.div_mul_le_self (T * (barrettRadix / p)) barrettRadix
  have hsP : (barrettRadix / p) * p ≤ barrettRadix :=
    Nat.div_mul_le_self barrettRadix p
  have hmul : (q * barrettRadix) * p ≤ T * barrettRadix := by
    calc
      (q * barrettRadix) * p ≤ (T * (barrettRadix / p)) * p :=
        Nat.mul_le_mul_right p hqR
      _ = T * ((barrettRadix / p) * p) := by
        simp [Nat.mul_assoc]
      _ ≤ T * barrettRadix := Nat.mul_le_mul_left T hsP
  have hmul' : (q * p) * barrettRadix ≤ T * barrettRadix := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  exact Nat.le_of_mul_le_mul_right hmul' hRpos

/--
The Barrett quotient computed from `floor(R / p)` is at most one below the
exact quotient while `T` fits in one radix word.
-/
theorem div_le_barrettQuotient_add_one (hp : 1 < p)
    (hpinv : pinv = barrettRadix / p) (hT : T < barrettRadix) :
    T / p ≤ T * pinv / barrettRadix + 1 := by
  subst pinv
  have hp0 : 0 < p := by omega
  have hRpos : 0 < barrettRadix := by
    simp [barrettRadix, UInt64.word]
  by_cases hpR : p ≤ barrettRadix
  · let s := barrettRadix / p
    have ha_le_s : T / p ≤ s := by
      exact Nat.div_le_div_right (Nat.le_of_lt hT)
    by_cases hzero : T / p = 0
    · rw [hzero]
      exact Nat.zero_le _
    · obtain ⟨a', ha⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have ha'_lt_s : a' < s := by
        have hs : a'.succ ≤ s := by
          simpa [ha] using ha_le_s
        exact Nat.lt_of_succ_le hs
      have hr_lt_p : barrettRadix % p < p := Nat.mod_lt barrettRadix hp0
      have hprod_lt : a' * (barrettRadix % p) < s * p := by
        exact Nat.mul_lt_mul_of_lt_of_le ha'_lt_s (Nat.le_of_lt hr_lt_p) hp0
      have hprod_le : a' * (barrettRadix % p) ≤ s * p := Nat.le_of_lt hprod_lt
      have hRdecomp : s * p + barrettRadix % p = barrettRadix := by
        simpa [s, Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div barrettRadix p
      have hTdecomp : p * (a' + 1) + T % p = T := by
        have h := Nat.mod_add_div T p
        rw [ha] at h
        simpa [Nat.add_comm] using h
      have hkey : a' * barrettRadix ≤ T * s := by
        calc
          a' * barrettRadix = a' * (s * p + barrettRadix % p) := by
            rw [hRdecomp]
          _ = a' * (s * p) + a' * (barrettRadix % p) := by
            simp [Nat.mul_add]
          _ ≤ a' * (s * p) + s * p := Nat.add_le_add_left hprod_le _
          _ = (a' + 1) * (s * p) := by
            simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
          _ = (p * (a' + 1)) * s := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          _ ≤ (p * (a' + 1) + T % p) * s := by
            exact Nat.mul_le_mul_right s (Nat.le_add_right _ _)
          _ = T * s := by
            rw [hTdecomp]
      have ha'_le_q : a' ≤ T * s / barrettRadix := by
        exact (Nat.le_div_iff_mul_le hRpos).2 hkey
      rw [ha]
      dsimp [s] at ha'_le_q ⊢
      exact Nat.succ_le_succ ha'_le_q
  · have hRp : barrettRadix < p := Nat.lt_of_not_ge hpR
    have hTp : T < p := Nat.lt_trans hT hRp
    have hdiv : T / p = 0 := Nat.div_eq_of_lt hTp
    rw [hdiv]
    exact Nat.zero_le _

/--
If the approximate quotient is exact, the uncorrected Barrett remainder is
already the ordinary remainder.
-/
private theorem barrett_remainder_eq_mod_of_quotient_eq (p T q : Nat)
    (hq : q = T / p) :
    T - q * p = T % p := by
  have hdecomp : T % p + q * p = T := by
    simpa [hq, Nat.mul_comm] using Nat.mod_add_div T p
  omega

/--
If the approximate quotient is one below exact, the uncorrected Barrett
remainder is the ordinary remainder plus one modulus.
-/
private theorem barrett_remainder_eq_mod_add_p_of_quotient_succ (p T q : Nat)
    (hq : T / p = q + 1) :
    T - q * p = T % p + p := by
  have hdecomp : T % p + p * (q + 1) = T := by
    simpa [hq] using Nat.mod_add_div T p
  have hsum : q * p + (T % p + p) = T := by
    calc
      q * p + (T % p + p) = T % p + p * (q + 1) := by
        simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
          Nat.mul_comm]
      _ = T := hdecomp
  omega

/--
With `pinv = floor(R / p)` and `T < R`, Nat-level Barrett reduction returns the
same value as `% p`.
-/
@[simp]
theorem barrettReduceNat_eq_mod (hp : 1 < p) (hpinv : pinv = barrettRadix / p)
    (hT : T < barrettRadix) :
    barrettReduceNat p pinv T = T % p := by
  have hp0 : 0 < p := by omega
  let q := T * pinv / barrettRadix
  have hq_le : q ≤ T / p := by
    simpa [q] using barrettQuotient_le_div (p := p) (pinv := pinv) (T := T) hp hpinv
  have hdiv_le : T / p ≤ q + 1 := by
    simpa [q] using div_le_barrettQuotient_add_one
      (p := p) (pinv := pinv) (T := T) hp hpinv hT
  have hq_cases : q = T / p ∨ T / p = q + 1 := by
    omega
  rcases hq_cases with hq | hq
  · have hr : T - q * p = T % p :=
      barrett_remainder_eq_mod_of_quotient_eq p T q hq
    have hlt : T % p < p := Nat.mod_lt T hp0
    simp [barrettReduceNat, q, hr, Nat.not_le_of_lt hlt]
  · have hr : T - q * p = T % p + p :=
      barrett_remainder_eq_mod_add_p_of_quotient_succ p T q hq
    have hcond : p ≤ T % p + p := Nat.le_add_left p (T % p)
    simp [barrettReduceNat, q, hr, hcond]

/-- Nat-level Barrett reduction always returns a canonical residue. -/
theorem barrettReduceNat_lt (hp : 1 < p) (hpinv : pinv = barrettRadix / p)
    (hT : T < barrettRadix) :
    barrettReduceNat p pinv T < p := by
  rw [barrettReduceNat_eq_mod hp hpinv hT]
  exact Nat.mod_lt T (by omega)

/--
Nat-level Barrett reduction fixes inputs that are already canonical residues
for a modulus fitting in one radix word.
-/
@[simp]
theorem barrettReduceNat_eq_self_of_lt (hp : 1 < p)
    (hpinv : pinv = barrettRadix / p) (hpRadix : p ≤ barrettRadix)
    (hT : T < p) :
    barrettReduceNat p pinv T = T := by
  rw [barrettReduceNat_eq_mod hp hpinv (Nat.lt_of_lt_of_le hT hpRadix)]
  exact Nat.mod_eq_of_lt hT
