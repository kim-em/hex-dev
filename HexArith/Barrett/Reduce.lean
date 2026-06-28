/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.Barrett.ReduceNat

public section

/-!
Executable `UInt64` Barrett reduction for `HexArith`.

This layer packages the modulus and its reciprocal in `BarrettCtx`, defines the
single-word executable reduction step, and states the equality relating
the `UInt64` code to `barrettReduceNat`.
-/

/--
Context for Barrett reduction modulo `p`, specialized to the small-modulus
regime `p < 2^32` where products of residues still fit in one `UInt64`.
-/
structure BarrettCtx (p : UInt64) where
  mkCtx ::
  /-- The modulus is at least `2`. -/
  p_gt : p.toNat > 1
  /-- The small-modulus bound `p < 2^32`, so products of residues fit in one word. -/
  p_lt : p.toNat < 2 ^ 32
  /-- The precomputed reciprocal word `⌊R / p⌋`. -/
  pinv : UInt64
  /-- The reciprocal field is exactly `⌊R / p⌋`. -/
  pinv_eq : pinv = .ofNat (barrettRadix / p.toNat)

namespace BarrettCtx

/-- Build the executable Barrett context for a small `UInt64` modulus. -/
@[expose]
def mk (p : UInt64) (hp : p.toNat > 1) (hlt : p.toNat < 2 ^ 32) : BarrettCtx p :=
  { p_gt := hp
    p_lt := hlt
    pinv := UInt64.ofNat (barrettRadix / p.toNat)
    pinv_eq := by rfl }

end BarrettCtx

/--
Executable Barrett reduction on a single machine word, using the reciprocal
stored in `ctx`.
-/
@[expose]
def barrettReduce (ctx : BarrettCtx p) (T : UInt64) : UInt64 :=
  let q := UInt64.mulHi T ctx.pinv
  let r := T - q * p
  if r ≥ p then r - p else r

/--
The reciprocal stored in a Barrett context is the Nat-level
`floor(barrettRadix / p)`, not just propositionally equal as a `UInt64`.
-/
@[simp, grind =]
theorem BarrettCtx.toNat_pinv (ctx : BarrettCtx p) :
    ctx.pinv.toNat = barrettRadix / p.toNat := by
  rw [ctx.pinv_eq]
  have hRpos : 0 < barrettRadix := by
    simp [barrettRadix, UInt64.word]
  have hlt : barrettRadix / p.toNat < UInt64.word := by
    have hdiv_lt : barrettRadix / p.toNat < barrettRadix :=
      Nat.div_lt_self hRpos ctx.p_gt
    simpa [barrettRadix] using hdiv_lt
  simpa [UInt64.toNat_ofNat, UInt64.size, barrettRadix, UInt64.word]
    using Nat.mod_eq_of_lt hlt

/--
Multiplication of two `UInt64` values agrees with Nat multiplication when the
Nat-level product fits in one machine word.
-/
private theorem UInt64.toNat_mul_of_lt_word (a b : UInt64)
    (h : a.toNat * b.toNat < UInt64.word) :
    (a * b).toNat = a.toNat * b.toNat := by
  simpa [UInt64.toNat_mul, UInt64.size, UInt64.word] using Nat.mod_eq_of_lt h

/--
The executable Barrett reduction agrees with the Nat-level reduction when the
input word is in the small-product range guaranteed by the context hypotheses.
-/
theorem toNat_barrettReduce (ctx : BarrettCtx p) (T : UInt64)
    (hT : T.toNat < p.toNat * p.toNat) :
    (barrettReduce ctx T).toNat =
      barrettReduceNat p.toNat ctx.pinv.toNat T.toNat := by
  have hp0 : 0 < p.toNat := Nat.lt_trans (by decide : 0 < 1) ctx.p_gt
  have hT_word : T.toNat < barrettRadix := by
    have hp_word : p.toNat * p.toNat < UInt64.word := by
      calc
        p.toNat * p.toNat < 2 ^ 32 * 2 ^ 32 :=
          Nat.mul_lt_mul'' ctx.p_lt ctx.p_lt
        _ = UInt64.word := by
          rw [UInt64.word, ← Nat.pow_add]
    simpa [barrettRadix] using Nat.lt_trans hT hp_word
  let q := UInt64.mulHi T ctx.pinv
  have hpinv : ctx.pinv.toNat = barrettRadix / p.toNat := ctx.toNat_pinv
  have hq_eq : q.toNat = T.toNat * ctx.pinv.toNat / barrettRadix := by
    simpa [q, barrettRadix] using UInt64.toNat_mulHi T ctx.pinv
  have hq_le_div : q.toNat ≤ T.toNat / p.toNat := by
    rw [hq_eq]
    exact barrettQuotient_le_div
      (p := p.toNat) (pinv := ctx.pinv.toNat) (T := T.toNat) ctx.p_gt hpinv
  have hq_mul_le : q.toNat * p.toNat ≤ T.toNat := by
    calc
      q.toNat * p.toNat ≤ (T.toNat / p.toNat) * p.toNat :=
        Nat.mul_le_mul_right p.toNat hq_le_div
      _ ≤ T.toNat := Nat.div_mul_le_self T.toNat p.toNat
  have hq_mul_word : q.toNat * p.toNat < UInt64.word := by
    exact Nat.lt_of_le_of_lt hq_mul_le (by simpa [barrettRadix] using hT_word)
  have hqmul_toNat : (q * p).toNat = q.toNat * p.toNat :=
    UInt64.toNat_mul_of_lt_word q p hq_mul_word
  let r := T - q * p
  have hr_toNat : r.toNat = T.toNat - q.toNat * p.toNat := by
    have hleNat : (q * p).toNat ≤ T.toNat := by
      simpa [hqmul_toNat] using hq_mul_le
    have hle : q * p ≤ T := by
      rw [UInt64.le_iff_toNat_le]
      exact hleNat
    simpa [r, hqmul_toNat] using UInt64.toNat_sub_of_le T (q * p) hle
  dsimp [barrettReduce, barrettReduceNat]
  change
    (if r ≥ p then r - p else r).toNat =
      if T.toNat - (T.toNat * ctx.pinv.toNat / barrettRadix) * p.toNat ≥ p.toNat then
        T.toNat - (T.toNat * ctx.pinv.toNat / barrettRadix) * p.toNat - p.toNat
      else
        T.toNat - (T.toNat * ctx.pinv.toNat / barrettRadix) * p.toNat
  rw [← hq_eq]
  by_cases hge : r ≥ p
  · have hcond : p.toNat ≤ T.toNat - q.toNat * p.toNat := by
      have hle : p ≤ r := hge
      rw [UInt64.le_iff_toNat_le] at hle
      simpa [hr_toNat] using hle
    have hsub_toNat : (r - p).toNat = r.toNat - p.toNat :=
      UInt64.toNat_sub_of_le r p hge
    simp [hge, hcond, hsub_toNat, hr_toNat]
  · have hnot_ge : ¬ r ≥ p := by
      exact hge
    have hcond : ¬ p.toNat ≤ T.toNat - q.toNat * p.toNat := by
      intro hnat
      apply hge
      change p ≤ r
      rw [UInt64.le_iff_toNat_le]
      simpa [hr_toNat] using hnat
    simp [hnot_ge, hcond, hr_toNat]

/--
The executable Barrett reducer returns the ordinary Nat remainder for every
input in the small-product range guaranteed by the context.
-/
@[simp, grind =]
theorem toNat_barrettReduce_eq_mod (ctx : BarrettCtx p) (T : UInt64)
    (hT : T.toNat < p.toNat * p.toNat) :
    (barrettReduce ctx T).toNat = T.toNat % p.toNat := by
  rw [toNat_barrettReduce ctx T hT]
  have hT_word : T.toNat < barrettRadix := by
    have hp_word : p.toNat * p.toNat < UInt64.word := by
      calc
        p.toNat * p.toNat < 2 ^ 32 * 2 ^ 32 :=
          Nat.mul_lt_mul'' ctx.p_lt ctx.p_lt
        _ = UInt64.word := by
          rw [UInt64.word, ← Nat.pow_add]
    exact Nat.lt_trans hT (by simpa [barrettRadix] using hp_word)
  exact barrettReduceNat_eq_mod ctx.p_gt ctx.toNat_pinv hT_word

/-- The executable Barrett reducer returns a canonical residue. -/
theorem barrettReduce_lt (ctx : BarrettCtx p) (T : UInt64)
    (hT : T.toNat < p.toNat * p.toNat) :
    barrettReduce ctx T < p := by
  rw [UInt64.lt_iff_toNat_lt, toNat_barrettReduce_eq_mod ctx T hT]
  exact Nat.mod_lt _ (Nat.lt_trans (by decide : 0 < 1) ctx.p_gt)

/-- Barrett reduction fixes inputs that are already canonical residues. -/
@[simp, grind =]
theorem barrettReduce_eq_self_of_lt (ctx : BarrettCtx p) (T : UInt64)
    (hT : T < p) :
    barrettReduce ctx T = T := by
  apply UInt64.toNat_inj.mp
  have hTNat : T.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using hT
  have hTprod : T.toNat < p.toNat * p.toNat := by
    calc
      T.toNat < p.toNat := hTNat
      _ = p.toNat * 1 := by omega
      _ ≤ p.toNat * p.toNat := Nat.mul_le_mul_left p.toNat (by omega : 1 ≤ p.toNat)
  rw [toNat_barrettReduce_eq_mod ctx T hTprod]
  exact Nat.mod_eq_of_lt hTNat

/--
The executable Barrett reducer agrees with reducing the input word and
re-encoding the canonical residue as a `UInt64`.
-/
theorem barrettReduce_eq (ctx : BarrettCtx p) (T : UInt64)
    (hT : T.toNat < p.toNat * p.toNat) :
    barrettReduce ctx T = .ofNat (T.toNat % p.toNat) := by
  apply UInt64.toNat_inj.mp
  rw [toNat_barrettReduce_eq_mod ctx T hT]
  have hmod_lt : T.toNat % p.toNat < p.toNat :=
    Nat.mod_lt _ (Nat.lt_trans (by decide : 0 < 1) ctx.p_gt)
  have hmod_word : T.toNat % p.toNat < UInt64.word := by
    exact Nat.lt_trans hmod_lt (Nat.lt_trans ctx.p_lt (by decide))
  change T.toNat % p.toNat = (T.toNat % p.toNat) % UInt64.size
  simpa [UInt64.size, UInt64.word] using (Nat.mod_eq_of_lt hmod_word).symm
