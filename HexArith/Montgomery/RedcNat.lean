import HexArith.Nat.ModArith
import HexArith.UInt64.Wide

/-!
Nat-level Montgomery reduction for `HexArith`.

This file states the REDC computation purely over `Nat`, using the `UInt64`
word radix `R = 2^64`. The executable `UInt64` bridge in later modules is
proved against these definitions.
-/

/-- Nat-level Montgomery reduction with radix `R = 2^64`. -/
def redcNat (p p' T : Nat) : Nat :=
  let m := (T % UInt64.word) * p' % UInt64.word
  let u := (T + m * p) / UInt64.word
  if u < p then u else u - p

/-- Reducing `T` before multiplying by `p'` does not change the correction word. -/
private theorem redcNat_correction_eq (p' T : Nat) :
    T * p' % UInt64.word = (T % UInt64.word) * p' % UInt64.word := by
  rw [Nat.mul_mod T p' UInt64.word]
  rw [Nat.mul_mod (T % UInt64.word) p' UInt64.word]
  rw [Nat.mod_mod]

/-- A word-sized value plus its `R - 1` multiple vanishes modulo `R`. -/
private theorem redcNat_cancel_pred_word (a : Nat) (ha : a < UInt64.word) :
    (a + (a * (UInt64.word - 1)) % UInt64.word) % UInt64.word = 0 := by
  have hword_pos : 0 < UInt64.word := by
    simp [UInt64.word]
  have hmod : a % UInt64.word = a := Nat.mod_eq_of_lt ha
  calc
    (a + (a * (UInt64.word - 1)) % UInt64.word) % UInt64.word
        = (a % UInt64.word + (a * (UInt64.word - 1)) % UInt64.word) %
            UInt64.word := by
          rw [hmod]
    _ = (a + a * (UInt64.word - 1)) % UInt64.word := by
          rw [← Nat.add_mod]
    _ = 0 := by
          have hword : UInt64.word - 1 + 1 = UInt64.word :=
            Nat.sub_add_cancel hword_pos
          have hmul : a + a * (UInt64.word - 1) = a * UInt64.word := by
            rw [Nat.add_comm]
            rw [← Nat.mul_succ]
            have hs : (UInt64.word - 1).succ = UInt64.word := by
              simpa [Nat.succ_eq_add_one] using hword
            rw [hs]
          rw [hmul, Nat.mul_mod_left]

/-- The Montgomery correction makes the adjusted numerator exactly divisible by `R`. -/
private theorem redcNat_exact_dvd (p p' T : Nat)
    (hpp' : p * p' % UInt64.word = UInt64.word - 1) :
    UInt64.word ∣ T + ((T % UInt64.word) * p' % UInt64.word) * p := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have hword_pos : 0 < UInt64.word := by
    simp [UInt64.word]
  have hmul_mod :
      (((T % UInt64.word) * p' % UInt64.word) * p) % UInt64.word =
        (T % UInt64.word * (p' * p)) % UInt64.word := by
    calc
      (((T % UInt64.word) * p' % UInt64.word) * p) % UInt64.word
          = ((T % UInt64.word) * p' * p) % UInt64.word := by
            rw [Nat.mul_mod ((T % UInt64.word) * p' % UInt64.word) p
              UInt64.word]
            rw [Nat.mod_mod]
            rw [← Nat.mul_mod ((T % UInt64.word) * p') p UInt64.word]
      _ = (T % UInt64.word * (p' * p)) % UInt64.word := by
            rw [Nat.mul_assoc]
  calc
    (T + ((T % UInt64.word) * p' % UInt64.word) * p) % UInt64.word
        = (T % UInt64.word +
              (((T % UInt64.word) * p' % UInt64.word) * p) %
                UInt64.word) % UInt64.word := by
          rw [Nat.add_mod]
    _ = (T % UInt64.word + (T % UInt64.word * (p' * p)) %
              UInt64.word) % UInt64.word := by
          rw [hmul_mod]
    _ = (T % UInt64.word + (T % UInt64.word * (p * p')) %
              UInt64.word) % UInt64.word := by
          rw [Nat.mul_comm p' p]
    _ = (T % UInt64.word +
            (T % UInt64.word * ((p * p') % UInt64.word)) %
              UInt64.word) % UInt64.word := by
          rw [Nat.mul_mod]
          rw [Nat.mod_mod]
    _ = 0 := by
          rw [hpp']
          exact redcNat_cancel_pred_word (T % UInt64.word)
            (Nat.mod_lt T hword_pos)

/-- Core quotient bound before threading the inverse and modulus-size hypotheses. -/
private theorem redcNat_u_lt_two_p_core (hp_pos : 0 < p)
    (hT : T < p * UInt64.word) :
    (T + ((T % UInt64.word) * p' % UInt64.word) * p) / UInt64.word < 2 * p := by
  have hword_pos : 0 < UInt64.word := by
    simp [UInt64.word]
  have hm_lt : (T % UInt64.word) * p' % UInt64.word < UInt64.word :=
    Nat.mod_lt _ hword_pos
  have hmulp_lt :
      ((T % UInt64.word) * p' % UInt64.word) * p < UInt64.word * p :=
    Nat.mul_lt_mul_of_pos_right hm_lt hp_pos
  have hn_lt' :
      T + ((T % UInt64.word) * p' % UInt64.word) * p <
        p * UInt64.word + UInt64.word * p :=
    Nat.add_lt_add hT hmulp_lt
  have htarget : UInt64.word * (2 * p) = p * UInt64.word + UInt64.word * p := by
    rw [Nat.mul_comm UInt64.word (2 * p)]
    rw [Nat.mul_assoc]
    rw [Nat.two_mul]
    simp [Nat.mul_comm]
  have hn_lt :
      T + ((T % UInt64.word) * p' % UInt64.word) * p <
        UInt64.word * (2 * p) := by
    rw [htarget]
    exact hn_lt'
  exact Nat.div_lt_of_lt_mul hn_lt

/--
Montgomery reduction computes a residue congruent to `T * R⁻¹` modulo `p`.
-/
theorem redcNat_eq_mod (hp_pos : 0 < p) (hp_lt : p < UInt64.word)
    (hpp' : p * p' % UInt64.word = UInt64.word - 1) (hT : T < p * UInt64.word) :
    redcNat p p' T * UInt64.word % p = T % p := by
  have _hp_pos : 0 < p := hp_pos
  have _hp_lt : p < UInt64.word := hp_lt
  have _hT : T < p * UInt64.word := hT
  have hc := redcNat_correction_eq p' T
  have hdvd : UInt64.word ∣ T + (T * p' % UInt64.word) * p := by
    rw [hc]
    exact redcNat_exact_dvd p p' T hpp'
  let u := (T + (T * p' % UInt64.word) * p) / UInt64.word
  have hdiv : u * UInt64.word = T + (T * p' % UInt64.word) * p := by
    exact Nat.div_mul_cancel hdvd
  have hu_mod : u * UInt64.word % p = T % p := by
    calc
      u * UInt64.word % p = (T + (T * p' % UInt64.word) * p) % p := by
        rw [hdiv]
      _ = T % p := by
        rw [Nat.add_mul_mod_self_right]
  by_cases h : u < p
  · simp [redcNat, h, u]
    exact hu_mod
  · have hpu : p ≤ u := Nat.le_of_not_lt h
    have hsub : (u - p) * UInt64.word + p * UInt64.word = u * UInt64.word := by
      rw [← Nat.add_mul]
      rw [Nat.sub_add_cancel hpu]
    simp [redcNat, h, u]
    calc
      (u - p) * UInt64.word % p
          = ((u - p) * UInt64.word + p * UInt64.word) % p := by
            rw [Nat.add_mul_mod_self_left]
      _ = u * UInt64.word % p := by
        rw [hsub]
      _ = T % p := hu_mod

/-- Montgomery reduction lands in the canonical residue interval `[0, p)`. -/
theorem redcNat_lt (hp_pos : 0 < p) (hp_lt : p < UInt64.word)
    (hpp' : p * p' % UInt64.word = UInt64.word - 1) (hT : T < p * UInt64.word) :
    redcNat p p' T < p := by
  have _hp_lt : p < UInt64.word := hp_lt
  have _hpp' : p * p' % UInt64.word = UInt64.word - 1 := hpp'
  have hc := redcNat_correction_eq p' T
  have hu : (T + (T * p' % UInt64.word) * p) / UInt64.word < 2 * p := by
    rw [hc]
    exact redcNat_u_lt_two_p_core hp_pos hT
  by_cases h : (T + (T * p' % UInt64.word) * p) / UInt64.word < p
  · simp [redcNat, h]
  · simp [redcNat, h]
    omega

/--
The unreduced Montgomery quotient is always below `2p`, so one subtraction is
enough to normalize the result.
-/
theorem redcNat_u_lt_two_p (hp_pos : 0 < p) (hp_lt : p < UInt64.word)
    (hpp' : p * p' % UInt64.word = UInt64.word - 1) (hT : T < p * UInt64.word) :
    (T + ((T % UInt64.word) * p' % UInt64.word) * p) / UInt64.word < 2 * p := by
  have _hp_lt : p < UInt64.word := hp_lt
  have _hpp' : p * p' % UInt64.word = UInt64.word - 1 := hpp'
  exact redcNat_u_lt_two_p_core hp_pos hT
