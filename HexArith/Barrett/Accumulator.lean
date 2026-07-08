/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.Barrett.Reduce

public section

/-!
Wide-accumulator layer for delayed-reduction Barrett multiplication.

The single-multiply Barrett reducer `barrettReduce` reduces after every product.
A delayed-reduction dot product instead accumulates several products in a
two-word (`128`-bit) accumulator and reduces modulo `p` only periodically. This
module provides the verified pieces that make that sound:

* `barrettReduce` is correct on the **whole** `UInt64` range, not just on inputs
  below `p^2` (`toNat_barrettReduce_mod`): every `UInt64` is already below the
  radix `2^64`, which is the only bound the reducer needs.
* a two-word accumulator `accVal lo hi := lo + hi * 2^64`, an add-a-product step
  `accAddWord`, and its exact-value lemma under the no-carry-overflow bound
  (`accVal_accAddWord`);
* a two-word reduction `accReduce` that returns `(lo + hi * 2^64) % p` using the
  precomputed constant `2^64 % p` (`toNat_accReduce`, `accReduce_lt`).

`BarrettCtx` keeps `p < 2^32`, so each residue product fits in one `UInt64` and a
bounded run of them fits below `2^128` between reductions; that is why the
accumulator never overflows and periodic reduction is exact for every inner
length.
-/

namespace BarrettCtx

variable {p : UInt64}

/--
`barrettReduce` computes `T % p` for **every** input word, not only for inputs
below `p^2`. The single-word reducer only needs `T < 2^64`, which holds for every
`UInt64`; the `p^2` bound in `toNat_barrettReduce_eq_mod` is stronger than
necessary. This is the reduction the wide accumulator flushes through.
-/
@[grind =]
theorem toNat_barrettReduce_mod (ctx : BarrettCtx p) (T : UInt64) :
    (barrettReduce ctx T).toNat = T.toNat % p.toNat := by
  have hp0 : 0 < p.toNat := Nat.lt_trans (by decide : 0 < 1) ctx.p_gt
  have hT_word : T.toNat < barrettRadix := by
    simpa [barrettRadix] using UInt64.toNat_lt_word T
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
  have hqmul_toNat : (q * p).toNat = q.toNat * p.toNat := by
    simpa [UInt64.toNat_mul, UInt64.size, UInt64.word] using
      Nat.mod_eq_of_lt hq_mul_word
  let r := T - q * p
  have hr_toNat : r.toNat = T.toNat - q.toNat * p.toNat := by
    have hleNat : (q * p).toNat ≤ T.toNat := by
      simpa [hqmul_toNat] using hq_mul_le
    have hle : q * p ≤ T := by
      rw [UInt64.le_iff_toNat_le]
      exact hleNat
    simpa [r, hqmul_toNat] using UInt64.toNat_sub_of_le T (q * p) hle
  have hmain : (barrettReduce ctx T).toNat =
      barrettReduceNat p.toNat ctx.pinv.toNat T.toNat := by
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
    · have hcond : ¬ p.toNat ≤ T.toNat - q.toNat * p.toNat := by
        intro hnat
        apply hge
        change p ≤ r
        rw [UInt64.le_iff_toNat_le]
        simpa [hr_toNat] using hnat
      simp [hge, hcond, hr_toNat]
  rw [hmain, barrettReduceNat_eq_mod ctx.p_gt ctx.toNat_pinv hT_word]

/-- The full-range reducer returns a canonical residue for every input word. -/
@[grind =>]
theorem barrettReduce_lt_mod (ctx : BarrettCtx p) (T : UInt64) :
    barrettReduce ctx T < p := by
  rw [UInt64.lt_iff_toNat_lt, toNat_barrettReduce_mod ctx T]
  exact Nat.mod_lt _ (Nat.lt_trans (by decide : 0 < 1) ctx.p_gt)

/-! ### Two-word accumulator -/

/-- The value carried by a two-word accumulator `(lo, hi)` in radix `2^64`. -/
@[expose]
def accVal (lo hi : UInt64) : Nat :=
  lo.toNat + hi.toNat * UInt64.word

/-- Add a single product word `q` into the two-word accumulator `(lo, hi)`,
propagating the carry into the high word. -/
@[expose]
def accAddWord (lo hi q : UInt64) : UInt64 × UInt64 :=
  let (lo', c) := UInt64.addCarry lo q false
  (lo', if c then hi + 1 else hi)

/-- Adding a product word to the accumulator increases its value by exactly the
product, provided the high word does not overflow (`hi.toNat + 1 < 2^64`). -/
theorem accVal_accAddWord (lo hi q : UInt64) (hhi : hi.toNat + 1 < UInt64.word) :
    accVal (accAddWord lo hi q).1 (accAddWord lo hi q).2 = accVal lo hi + q.toNat := by
  have hcarry := UInt64.toNat_addCarry_proj lo q false
  simp only [Bool.toNat_false, Nat.add_zero] at hcarry
  dsimp [accAddWord]
  by_cases hc : (UInt64.addCarry lo q false).2 = true
  · have hc' : (UInt64.addCarry lo q false).2 = true := hc
    simp only [hc', if_true]
    have hhi1 : (hi + 1).toNat = hi.toNat + 1 := by
      rw [UInt64.toNat_add]
      simp only [UInt64.toNat_one]
      exact Nat.mod_eq_of_lt hhi
    dsimp [accVal]
    rw [hhi1]
    have hcarry1 : (UInt64.addCarry lo q false).1.toNat + 1 * UInt64.word =
        lo.toNat + q.toNat := by
      have := hcarry
      rw [hc'] at this
      simpa using this
    -- lo'.toNat + word = lo + q
    have hcarry1' : (UInt64.addCarry lo q false).1.toNat + UInt64.word =
        lo.toNat + q.toNat := by
      simpa [Nat.one_mul] using hcarry1
    -- goal: lo'.toNat + (hi.toNat + 1) * word = lo.toNat + hi.toNat*word + q.toNat
    grind
  · have hc' : (UInt64.addCarry lo q false).2 = false := by
      simpa using hc
    simp only [hc']
    dsimp [accVal]
    have hcarry0 : (UInt64.addCarry lo q false).1.toNat = lo.toNat + q.toNat := by
      have := hcarry
      rw [hc'] at this
      simpa using this
    rw [hcarry0]
    grind

/-! ### Two-word reduction -/

/-- Reduce the two-word accumulator `(lo, hi)` modulo `p`, using the precomputed
constant `cR = 2^64 % p`. The scheme reduces each half, folds the high half in
through `cR`, and reduces once more:
`(lo + hi * 2^64) % p = ((hi % p) * (2^64 % p) + lo % p) % p`. -/
@[expose]
def accReduce (ctx : BarrettCtx p) (cR lo hi : UInt64) : UInt64 :=
  let hHi := barrettReduce ctx hi
  let hLo := barrettReduce ctx lo
  let t := barrettReduce ctx (hHi * cR)
  barrettReduce ctx (t + hLo)

/-- The Nat identity behind `accReduce`: reducing the two halves and folding the
high half through `2^64 % p` recovers the full residue. -/
private theorem nat_acc_mod (p lo hi cR : Nat) (hcR : cR = UInt64.word % p) :
    (hi % p * cR % p + lo % p) % p = (lo + hi * UInt64.word) % p := by
  rw [hcR, Nat.add_mod lo (hi * UInt64.word) p, Nat.mul_mod hi UInt64.word p,
    Nat.add_comm (lo % p)]

/-- `accReduce` computes `(lo + hi * 2^64) % p`, the residue of the full two-word
accumulator value. -/
@[grind =]
theorem toNat_accReduce (ctx : BarrettCtx p) (cR lo hi : UInt64)
    (hcR : cR.toNat = UInt64.word % p.toNat) :
    (accReduce ctx cR lo hi).toNat = accVal lo hi % p.toNat := by
  have hp0 : 0 < p.toNat := Nat.lt_trans (by decide : 0 < 1) ctx.p_gt
  -- Bounds: reduced residues are below `p < 2^32`, so the intermediate product
  -- and sum stay within one word.
  have hHi_lt : (barrettReduce ctx hi).toNat < p.toNat := by
    rw [toNat_barrettReduce_mod]; exact Nat.mod_lt _ hp0
  have hLo_lt : (barrettReduce ctx lo).toNat < p.toNat := by
    rw [toNat_barrettReduce_mod]; exact Nat.mod_lt _ hp0
  have hcR_lt : cR.toNat < p.toNat := by
    rw [hcR]; exact Nat.mod_lt _ hp0
  have hp_word : p.toNat < 2 ^ 32 := ctx.p_lt
  -- `p * p` fits in one word, and `2 * p ≤ p * p` since `p ≥ 2`.
  have hpp_word : p.toNat * p.toNat < UInt64.word := by
    calc
      p.toNat * p.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hp_word hp_word
      _ = UInt64.word := by rw [UInt64.word, ← Nat.pow_add]
  have h2p : 2 * p.toNat ≤ p.toNat * p.toNat :=
    Nat.mul_le_mul_right p.toNat ctx.p_gt
  -- `hHi * cR` fits in one word.
  have hprod_word : (barrettReduce ctx hi).toNat * cR.toNat < UInt64.word := by
    have : (barrettReduce ctx hi).toNat * cR.toNat < p.toNat * p.toNat :=
      Nat.mul_lt_mul'' hHi_lt hcR_lt
    omega
  have hprod_toNat : ((barrettReduce ctx hi) * cR).toNat =
      (barrettReduce ctx hi).toNat * cR.toNat := by
    simpa [UInt64.toNat_mul, UInt64.size, UInt64.word] using
      Nat.mod_eq_of_lt hprod_word
  -- `t = (hHi * cR) % p`.
  have ht_lt : (barrettReduce ctx ((barrettReduce ctx hi) * cR)).toNat < p.toNat := by
    rw [toNat_barrettReduce_mod]; exact Nat.mod_lt _ hp0
  -- `t + hLo` fits in one word.
  have hsum_word :
      (barrettReduce ctx ((barrettReduce ctx hi) * cR)).toNat +
        (barrettReduce ctx lo).toNat < UInt64.word := by
    omega
  have hsum_toNat :
      ((barrettReduce ctx ((barrettReduce ctx hi) * cR)) + (barrettReduce ctx lo)).toNat =
        (barrettReduce ctx ((barrettReduce ctx hi) * cR)).toNat +
          (barrettReduce ctx lo).toNat := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by simpa [UInt64.size, UInt64.word] using hsum_word)
  -- Now compute.
  dsimp [accReduce]
  rw [toNat_barrettReduce_mod, hsum_toNat, toNat_barrettReduce_mod, hprod_toNat,
    toNat_barrettReduce_mod, toNat_barrettReduce_mod]
  dsimp [accVal]
  rw [nat_acc_mod p.toNat lo.toNat hi.toNat cR.toNat hcR]

/-- `accReduce` returns a canonical residue below `p`. -/
@[grind =>]
theorem accReduce_lt (ctx : BarrettCtx p) (cR lo hi : UInt64)
    (hcR : cR.toNat = UInt64.word % p.toNat) :
    accReduce ctx cR lo hi < p := by
  rw [UInt64.lt_iff_toNat_lt, toNat_accReduce ctx cR lo hi hcR]
  exact Nat.mod_lt _ (Nat.lt_trans (by decide : 0 < 1) ctx.p_gt)

/-! ### The radix residue as a context-level constant

`accReduce` needs the constant `2^64 % p`; storing it on the context (rather than
threading a `cR` word plus its `hcR` proof through every caller) keeps the
delayed-reduction fold below free of that plumbing. -/

/-- `2^32 < 2^64`, the radix headroom that keeps a reduced residue and the
window inside a single machine word. -/
private theorem two_pow_32_lt_word : (2 : Nat) ^ 32 < UInt64.word := by
  rw [UInt64.word]; exact Nat.pow_lt_pow_right (by decide) (by decide)

/-- The radix residue `2^64 % p`, stored as a context-level constant so callers
of `accReduce`/`foldReduce` need not carry the word and its correctness proof.
Computed with a `Nat` reduction of the `2^64` radix (done once per context), so
no `128`-bit machine literal is required. -/
@[expose]
def radixResidue (_ctx : BarrettCtx p) : UInt64 :=
  UInt64.ofNat (UInt64.word % p.toNat)

/-- `radixResidue` stores exactly `2^64 % p`, the `hcR` side condition every
`accReduce`/`foldReduce` lemma needs. -/
@[grind =]
theorem toNat_radixResidue (ctx : BarrettCtx p) :
    (radixResidue ctx).toNat = UInt64.word % p.toNat := by
  have hp0 : 0 < p.toNat := Nat.lt_trans (by decide : 0 < 1) ctx.p_gt
  have hlt : UInt64.word % p.toNat < p.toNat := Nat.mod_lt _ hp0
  have hpw : p.toNat < UInt64.word := Nat.lt_trans ctx.p_lt two_pow_32_lt_word
  have hb : UInt64.word % p.toNat < UInt64.size := by
    simpa [UInt64.size, UInt64.word] using Nat.lt_trans hlt hpw
  rw [radixResidue, UInt64.toNat_ofNat_of_lt' hb]

/-! ### Periodic-reduction fold

A delayed-reduction dot product accumulates one-word products into the two-word
accumulator and flushes through `accReduce` every `barrettWindow` additions. The
window is fixed and independent of the inner dimension, so a run of any length
stays below `2^128`: each add grows the high word by at most one, and a flush
resets it, so the high word never reaches the wraparound boundary
(`accFold_spec`, the per-window no-overflow invariant). This is why periodic
reduction is correct for *every* inner length, where a single end reduction is
not. -/

/-- Number of one-word products accumulated between reductions. Any value below
`2^64` keeps the two-word accumulator's high word from overflowing (the add
grows it by at most one per step); `2^32` sits comfortably above every realistic
inner dimension, so a base-kernel dot product reduces exactly once. -/
@[irreducible]
def barrettWindow : Nat := 2 ^ 32

theorem barrettWindow_pos : 0 < barrettWindow := by
  unfold barrettWindow; exact Nat.two_pow_pos 32

theorem barrettWindow_lt_word : barrettWindow < UInt64.word := by
  unfold barrettWindow; exact two_pow_32_lt_word

/-- One delayed-reduction step: add the product word `q` into the accumulator
`(lo, hi)`, and when the window count reaches `barrettWindow` flush the two-word
value through `accReduce` back to a single reduced word, resetting the count.

Deliberately *not* `@[expose]`: leaving the body opaque to the kernel keeps
reductions of `foldl accStep …` from unfolding the `accReduce`/`barrettReduce`
machinery (which mentions the `2^64` radix) during defeq checks; all reasoning
goes through `accFold_spec`, never kernel reduction of `accStep`. -/
def accStep (ctx : BarrettCtx p) : UInt64 × UInt64 × Nat → UInt64 → UInt64 × UInt64 × Nat
  | (lo, hi, count), q =>
    let r := accAddWord lo hi q
    if count + 1 = barrettWindow then
      (accReduce ctx (radixResidue ctx) r.1 r.2, 0, 0)
    else
      (r.1, r.2, count + 1)

/-- Sum of the `Nat` values of a list of accumulator product words. -/
@[expose]
def wordsSum (ws : List UInt64) : Nat :=
  ws.foldr (fun w a => w.toNat + a) 0

@[simp] theorem wordsSum_nil : wordsSum [] = 0 := rfl

@[simp] theorem wordsSum_cons (q : UInt64) (ws : List UInt64) :
    wordsSum (q :: ws) = q.toNat + wordsSum ws := rfl

/-- **Per-window no-overflow invariant** for the delayed-reduction fold. From any
in-window start state (`hi ≤ count < barrettWindow`), folding `accStep` over a
list of product words keeps the state in-window (`hi ≤ count < barrettWindow`,
so the next add cannot overflow the high word) and preserves the residue: the
accumulator's value modulo `p` equals the starting value plus the sum of the
added words modulo `p`. -/
theorem accFold_spec (ctx : BarrettCtx p) (ws : List UInt64) :
    ∀ (lo hi : UInt64) (count : Nat), hi.toNat ≤ count → count < barrettWindow →
      (ws.foldl (accStep ctx) (lo, hi, count)).2.1.toNat ≤
          (ws.foldl (accStep ctx) (lo, hi, count)).2.2 ∧
        (ws.foldl (accStep ctx) (lo, hi, count)).2.2 < barrettWindow ∧
        accVal (ws.foldl (accStep ctx) (lo, hi, count)).1
            (ws.foldl (accStep ctx) (lo, hi, count)).2.1 % p.toNat =
          (accVal lo hi + wordsSum ws) % p.toNat := by
  induction ws with
  | nil =>
    intro lo hi count h1 h2
    refine ⟨h1, h2, ?_⟩
    rw [List.foldl_nil, wordsSum_nil, Nat.add_zero]
  | cons q rest ih =>
    intro lo hi count h1 h2
    -- The next add cannot overflow the high word.
    have hnw : hi.toNat + 1 < UInt64.word := by
      have := barrettWindow_lt_word
      omega
    -- The add's exact value and its bounded high-word growth.
    have hval : accVal (accAddWord lo hi q).1 (accAddWord lo hi q).2 =
        accVal lo hi + q.toNat := accVal_accAddWord lo hi q hnw
    have hgrow : (accAddWord lo hi q).2.toNat ≤ hi.toNat + 1 := by
      dsimp [accAddWord]
      by_cases hc : (UInt64.addCarry lo q false).2 = true
      · rw [if_pos hc]
        have hh : (hi + 1).toNat = hi.toNat + 1 := by
          rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]
          exact Nat.mod_eq_of_lt hnw
        omega
      · rw [if_neg hc]; omega
    rw [List.foldl_cons]
    by_cases hcase : count + 1 = barrettWindow
    · have hstep : accStep ctx (lo, hi, count) q =
          (accReduce ctx (radixResidue ctx) (accAddWord lo hi q).1 (accAddWord lo hi q).2,
            0, 0) := by
        simp only [accStep]; rw [if_pos hcase]
      rw [hstep]
      have hres := ih (accReduce ctx (radixResidue ctx) (accAddWord lo hi q).1
        (accAddWord lo hi q).2) 0 0 (Nat.le_of_eq UInt64.toNat_zero) barrettWindow_pos
      refine ⟨hres.1, hres.2.1, ?_⟩
      rw [hres.2.2]
      have hR : accVal (accReduce ctx (radixResidue ctx) (accAddWord lo hi q).1
          (accAddWord lo hi q).2) 0 = (accVal lo hi + q.toNat) % p.toNat := by
        rw [accVal]
        simp only [UInt64.toNat_zero, Nat.zero_mul, Nat.add_zero]
        rw [toNat_accReduce ctx _ _ _ (toNat_radixResidue ctx), hval]
      rw [hR, wordsSum_cons, Nat.mod_add_mod, Nat.add_assoc]
    · have hstep : accStep ctx (lo, hi, count) q =
          ((accAddWord lo hi q).1, (accAddWord lo hi q).2, count + 1) := by
        simp only [accStep]; rw [if_neg hcase]
      rw [hstep]
      have hcount : count + 1 < barrettWindow := by omega
      have hhi : (accAddWord lo hi q).2.toNat ≤ count + 1 := by omega
      have hres := ih (accAddWord lo hi q).1 (accAddWord lo hi q).2 (count + 1) hhi hcount
      refine ⟨hres.1, hres.2.1, ?_⟩
      rw [hres.2.2, hval, wordsSum_cons, Nat.add_assoc]

/-- Reduce a list of product words modulo `p` with periodic reduction: fold
`accStep` from an empty accumulator and flush the final partial window. -/
@[expose]
def foldReduce (ctx : BarrettCtx p) (ws : List UInt64) : UInt64 :=
  let s := ws.foldl (accStep ctx) (0, 0, 0)
  accReduce ctx (radixResidue ctx) s.1 s.2.1

/-- `foldReduce` computes `(Σ words) % p`: the delayed-reduction fold is exact for
a run of any length, matching the residue of the fully-accumulated sum. -/
@[grind =]
theorem toNat_foldReduce (ctx : BarrettCtx p) (ws : List UInt64) :
    (foldReduce ctx ws).toNat = wordsSum ws % p.toNat := by
  have hspec := accFold_spec ctx ws 0 0 0 (by decide) barrettWindow_pos
  rw [foldReduce, toNat_accReduce ctx _ _ _ (toNat_radixResidue ctx), hspec.2.2]
  simp [accVal]

end BarrettCtx
