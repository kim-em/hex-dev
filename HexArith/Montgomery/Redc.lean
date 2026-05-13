import HexArith.Montgomery.InvNat

/-!
Executable `UInt64` Montgomery reduction for `HexArith`.

This file packages the machine-word Montgomery parameters together with the
REDC bridge that consumes a two-word product `(Thi, Tlo)` and returns one
reduced residue.
-/

/-- Runtime Montgomery context for an odd `UInt64` modulus. -/
structure MontCtx (p : UInt64) where
  mkCtx ::
  p_odd : p % 2 = 1
  p' : UInt64
  p'_eq : (p'.toNat * p.toNat) % UInt64.word = UInt64.word - 1
  r2 : UInt64
  r2_eq : r2.toNat = (UInt64.word * UInt64.word) % p.toNat

/--
Executable Montgomery reduction from a two-word product `(Thi, Tlo)` encoded in
base `2^64`.
-/
def redc (ctx : MontCtx p) (Thi Tlo : UInt64) : UInt64 :=
  let m := Tlo * ctx.p'
  let (mhi, mlo) := UInt64.mulFull m p
  let (_, c1) := UInt64.addCarry Tlo mlo false
  let (addHi, c2) := UInt64.addCarry Thi mhi c1
  if c2 then
    addHi - p
  else if addHi ≥ p then
    addHi - p
  else
    addHi

/-- A word-sized value plus its `R - 1` multiple vanishes modulo `R`. -/
private theorem redc_cancel_pred_word (a : Nat) (ha : a < UInt64.word) :
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

/-- The low-word Montgomery correction makes the adjusted low word zero modulo `R`. -/
private theorem redc_low_correction_zero (ctx : MontCtx p) (Tlo : UInt64) :
    let m := Tlo * ctx.p'
    (Tlo.toNat + (m * p).toNat) % UInt64.word = 0 := by
  intro m
  have hm : m.toNat = Tlo.toNat * ctx.p'.toNat % UInt64.word := by
    simp [m, UInt64.toNat_mul, UInt64.word]
  have hpp' : ctx.p'.toNat * p.toNat % UInt64.word = UInt64.word - 1 := ctx.p'_eq
  have hTlo : Tlo.toNat < UInt64.word := by
    simpa [UInt64.word, UInt64.size] using UInt64.toNat_lt_size Tlo
  have hmul_mod :
      (((Tlo.toNat * ctx.p'.toNat % UInt64.word) * p.toNat) % UInt64.word) =
        (Tlo.toNat * (ctx.p'.toNat * p.toNat)) % UInt64.word := by
    calc
      (((Tlo.toNat * ctx.p'.toNat % UInt64.word) * p.toNat) % UInt64.word)
          = (Tlo.toNat * ctx.p'.toNat * p.toNat) % UInt64.word := by
            rw [Nat.mul_mod ((Tlo.toNat * ctx.p'.toNat) % UInt64.word) p.toNat
              UInt64.word]
            rw [Nat.mod_mod]
            rw [← Nat.mul_mod (Tlo.toNat * ctx.p'.toNat) p.toNat UInt64.word]
      _ = (Tlo.toNat * (ctx.p'.toNat * p.toNat)) % UInt64.word := by
            rw [Nat.mul_assoc]
  calc
    (Tlo.toNat + (m * p).toNat) % UInt64.word
        = (Tlo.toNat + (m.toNat * p.toNat) % UInt64.word) % UInt64.word := by
          simp [UInt64.toNat_mul, UInt64.word]
    _ = (Tlo.toNat + ((Tlo.toNat * ctx.p'.toNat % UInt64.word) * p.toNat) %
            UInt64.word) % UInt64.word := by
          rw [hm]
    _ = (Tlo.toNat + (Tlo.toNat * (ctx.p'.toNat * p.toNat)) %
            UInt64.word) % UInt64.word := by
          rw [hmul_mod]
    _ = (Tlo.toNat + (Tlo.toNat * ((ctx.p'.toNat * p.toNat) %
            UInt64.word)) % UInt64.word) % UInt64.word := by
          rw [Nat.mul_mod]
          rw [Nat.mod_eq_of_lt hTlo]
    _ = 0 := by
          rw [hpp']
          exact redc_cancel_pred_word Tlo.toNat hTlo

/-- The first add-with-carry step computes an exact carry and a zero low word. -/
private theorem redc_low_addCarry_exact (ctx : MontCtx p) (Tlo : UInt64) :
    let m := Tlo * ctx.p'
    let (lo, c1) := UInt64.addCarry Tlo (m * p) false
    lo.toNat = 0 ∧ Tlo.toNat + (m * p).toNat = c1.toNat * UInt64.word := by
  intro m
  cases hcarry_pair : UInt64.addCarry Tlo (m * p) false with
  | mk lo c1 =>
      have hcarry := UInt64.toNat_addCarry Tlo (m * p) false
      simp [hcarry_pair] at hcarry
      have hmod : (Tlo.toNat + (m * p).toNat) % UInt64.word = 0 := by
        simpa [m] using redc_low_correction_zero ctx Tlo
      have hmul_toNat : (m * p).toNat = m.toNat * p.toNat % UInt64.word := by
        simp [UInt64.toNat_mul, UInt64.word]
      have hlo : lo.toNat < UInt64.word := by
        simpa [UInt64.word, UInt64.size] using UInt64.toNat_lt_size lo
      have hmod_left : (lo.toNat + c1.toNat * UInt64.word) % UInt64.word = 0 := by
        rw [hcarry]
        exact hmod
      have hlo_zero : lo.toNat = 0 := by
        cases c1 <;> simp [Bool.toNat, Nat.mod_eq_of_lt hlo] at hmod_left
        · exact hmod_left
        · exact hmod_left
      constructor
      · exact hlo_zero
      · calc
          Tlo.toNat + (m * p).toNat = lo.toNat + c1.toNat * UInt64.word := by
            exact hcarry.symm
          _ = c1.toNat * UInt64.word := by
            rw [hlo_zero]
            simp

/-- View the odd-modulus assumption as a Nat-level parity fact inside this file. -/
private theorem MontCtx.p_odd_nat (ctx : MontCtx p) : p.toNat % 2 = 1 := by
  have h := congrArg UInt64.toNat ctx.p_odd
  simpa [UInt64.toNat_mod, UInt64.toNat_ofNat, UInt64.size] using h

/-- An odd modulus is positive at the Nat level. -/
private theorem MontCtx.p_pos (ctx : MontCtx p) : 0 < p.toNat := by
  have hodd := ctx.p_odd_nat
  omega

/-- Every `UInt64` modulus is below the Montgomery radix `R = 2^64`. -/
private theorem MontCtx.p_lt_word (_ctx : MontCtx p) : p.toNat < UInt64.word := by
  simpa [UInt64.word, UInt64.size] using UInt64.toNat_lt_size p

/-- The low-word multiply computes the Montgomery correction factor `m`. -/
@[simp]
theorem redc_m_spec (ctx : MontCtx p) (_Thi Tlo : UInt64) :
    let m := Tlo * ctx.p'
    m.toNat = (Tlo.toNat * ctx.p'.toNat) % UInt64.word := by
  simp [UInt64.toNat_mul, UInt64.word]

/-- The carry pair `(c2, addHi)` represents the exact quotient `u`. -/
theorem redc_u_spec (ctx : MontCtx p) (Thi Tlo : UInt64) :
    let m := Tlo * ctx.p'
    let (_, c1) := UInt64.addCarry Tlo (m * p) false
    let (addHi, c2) := UInt64.addCarry Thi (UInt64.mulHi m p) c1
    addHi.toNat + c2.toNat * UInt64.word =
      (Tlo.toNat + Thi.toNat * UInt64.word + m.toNat * p.toNat) / UInt64.word := by
  intro m
  cases hlow_pair : UInt64.addCarry Tlo (m * p) false with
  | mk lo c1 =>
      have hlow : lo.toNat = 0 ∧
          Tlo.toNat + (m * p).toNat = c1.toNat * UInt64.word := by
        simpa [m, hlow_pair] using redc_low_addCarry_exact ctx Tlo
      cases hhi_pair : UInt64.addCarry Thi (UInt64.mulHi m p) c1 with
      | mk addHi c2 =>
          have hhi := UInt64.toNat_addCarry Thi (UInt64.mulHi m p) c1
          simp [hhi_pair] at hhi
          have hmul := UInt64.mulHi_mulLo m p
          have hword_pos : 0 < UInt64.word := by
            simp [UInt64.word]
          have hnum :
              Tlo.toNat + Thi.toNat * UInt64.word + m.toNat * p.toNat =
                UInt64.word * (Thi.toNat + (UInt64.mulHi m p).toNat + c1.toNat) := by
            have hlow_exact := hlow.2
            have hmul_exact := hmul
            rw [Nat.mul_add, Nat.mul_add]
            rw [Nat.mul_comm UInt64.word Thi.toNat]
            rw [Nat.mul_comm UInt64.word (UInt64.mulHi m p).toNat]
            rw [Nat.mul_comm UInt64.word c1.toNat]
            omega
          have hresult :
              addHi.toNat + c2.toNat * UInt64.word =
                (Tlo.toNat + Thi.toNat * UInt64.word + m.toNat * p.toNat) /
                  UInt64.word := by
            calc
            addHi.toNat + c2.toNat * UInt64.word
                = Thi.toNat + (UInt64.mulHi m p).toNat + c1.toNat := by
                  exact hhi
            _ = (Tlo.toNat + Thi.toNat * UInt64.word + m.toNat * p.toNat) /
                UInt64.word := by
                  rw [hnum, Nat.mul_div_right _ hword_pos]
          simpa [hlow_pair, hhi_pair] using hresult

/-- The final subtraction logic matches the Nat-level REDC normalization step. -/
theorem redc_sub_spec (ctx : MontCtx p) (Thi Tlo : UInt64)
    (hT : Tlo.toNat + Thi.toNat * UInt64.word < p.toNat * UInt64.word) :
    (redc ctx Thi Tlo).toNat =
      redcNat p.toNat ctx.p'.toNat (Tlo.toNat + Thi.toNat * UInt64.word) := by
  let m := Tlo * ctx.p'
  have hfull : UInt64.mulFull m p = (UInt64.mulHi m p, m * p) :=
    UInt64.mulFull_eq_mulHi_mul m p
  have hTmod :
      (Tlo.toNat + Thi.toNat * UInt64.word) % UInt64.word = Tlo.toNat := by
    have hTlo : Tlo.toNat < UInt64.word := by
      simpa [UInt64.word, UInt64.size] using UInt64.toNat_lt_size Tlo
    rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hTlo
  have hm :
      m.toNat =
        ((Tlo.toNat + Thi.toNat * UInt64.word) % UInt64.word) * ctx.p'.toNat %
          UInt64.word := by
    rw [hTmod]
    exact redc_m_spec ctx Thi Tlo
  unfold redc
  change
    (match UInt64.mulFull m p with
      | (mhi, mlo) =>
        match UInt64.addCarry Tlo mlo false with
        | (_, c1) =>
          match UInt64.addCarry Thi mhi c1 with
          | (addHi, c2) =>
            if c2 then addHi - p else if addHi ≥ p then addHi - p else addHi).toNat =
      redcNat p.toNat ctx.p'.toNat (Tlo.toNat + Thi.toNat * UInt64.word)
  rw [hfull]
  cases hlow_pair : UInt64.addCarry Tlo (m * p) false with
  | mk lo c1 =>
      cases hhi_pair : UInt64.addCarry Thi (UInt64.mulHi m p) c1 with
      | mk addHi c2 =>
          have hu := redc_u_spec ctx Thi Tlo
          simp [m, hlow_pair, hhi_pair] at hu
          have hp_pos := ctx.p_pos
          have hp_lt := ctx.p_lt_word
          have hpp' : p.toNat * ctx.p'.toNat % UInt64.word = UInt64.word - 1 := by
            simpa [Nat.mul_comm] using ctx.p'_eq
          have hu_lt :
              addHi.toNat + c2.toNat * UInt64.word < 2 * p.toNat := by
            rw [hu]
            simpa [hTmod] using redcNat_u_lt_two_p hp_pos hp_lt hpp' hT
          simp [redcNat, hTmod]
          simp only [UInt64.word] at hu ⊢
          rw [← hu]
          cases c2
          · simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero]
            by_cases hge : p ≤ addHi
            · have hgeNat : p.toNat ≤ addHi.toNat := by
                simpa [UInt64.le_iff_toNat_le] using hge
              have hnotlt : ¬ addHi.toNat < p.toNat := by
                omega
              have hsub : (addHi - p).toNat = addHi.toNat - p.toNat :=
                UInt64.toNat_sub_of_le addHi p hge
              simp [hlow_pair, hhi_pair, hge, hnotlt, hsub]
            · have hltNat : addHi.toNat < p.toNat := by
                have hn : ¬ p.toNat ≤ addHi.toNat := by
                  intro hle
                  apply hge
                  rw [UInt64.le_iff_toNat_le]
                  exact hle
                omega
              simp [hlow_pair, hhi_pair, hge, hltNat]
          · simp only [hlow_pair, hhi_pair, if_true, Bool.toNat_true]
            have hp_lt_lit : p.toNat < 2 ^ 64 := by
              simpa [UInt64.word] using hp_lt
            have hu_lt_lit : addHi.toNat + 2 ^ 64 < 2 * p.toNat := by
              simpa [UInt64.word] using hu_lt
            have hnotlt : ¬ addHi.toNat + 2 ^ 64 < p.toNat := by
              omega
            have hsub_lt : 2 ^ 64 - p.toNat + addHi.toNat < 2 ^ 64 := by
              omega
            have hsub_mod :
                (2 ^ 64 - p.toNat + addHi.toNat) % 2 ^ 64 =
                  2 ^ 64 - p.toNat + addHi.toNat :=
              Nat.mod_eq_of_lt hsub_lt
            simp only [UInt64.toNat_sub, hsub_mod]
            simp only [hnotlt, if_false, Nat.one_mul]
            rw [Nat.add_comm addHi.toNat (2 ^ 64)]
            exact (Nat.sub_add_comm (Nat.le_of_lt hp_lt_lit)).symm

/-- The executable REDC bridge agrees with the Nat-level specification. -/
theorem toNat_redc (ctx : MontCtx p) (Thi Tlo : UInt64)
    (hT : Tlo.toNat + Thi.toNat * UInt64.word < p.toNat * UInt64.word) :
    (redc ctx Thi Tlo).toNat =
      redcNat p.toNat ctx.p'.toNat (Tlo.toNat + Thi.toNat * UInt64.word) := by
  exact redc_sub_spec ctx Thi Tlo hT

/-- Executable REDC returns a canonical residue below the modulus. -/
theorem redc_lt (ctx : MontCtx p) (Thi Tlo : UInt64)
    (hT : Tlo.toNat + Thi.toNat * UInt64.word < p.toNat * UInt64.word) :
    redc ctx Thi Tlo < p := by
  rw [UInt64.lt_iff_toNat_lt, toNat_redc ctx Thi Tlo hT]
  have hpp' : p.toNat * ctx.p'.toNat % UInt64.word = UInt64.word - 1 := by
    simpa [Nat.mul_comm] using ctx.p'_eq
  exact redcNat_lt ctx.p_pos ctx.p_lt_word hpp' hT

/--
Executable REDC represents division by the Montgomery radix modulo `p`.

This is the direct bridge form of `redcNat_eq_mod`, avoiding an explicit
unfolding through the Nat-level REDC definition for downstream callers.
-/
theorem redc_mul_word_mod (ctx : MontCtx p) (Thi Tlo : UInt64)
    (hT : Tlo.toNat + Thi.toNat * UInt64.word < p.toNat * UInt64.word) :
    (redc ctx Thi Tlo).toNat * UInt64.word % p.toNat =
      (Tlo.toNat + Thi.toNat * UInt64.word) % p.toNat := by
  rw [toNat_redc ctx Thi Tlo hT]
  have hpp' : p.toNat * ctx.p'.toNat % UInt64.word = UInt64.word - 1 := by
    simpa [Nat.mul_comm] using ctx.p'_eq
  exact redcNat_eq_mod ctx.p_pos ctx.p_lt_word hpp' hT
