/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.Montgomery.Redc

public section
set_option backward.proofsInPublic true
set_option maxHeartbeats 1000000

/-!
User-facing Montgomery modular arithmetic for `HexArith`.

This module exposes `MontCtx.mk`, conversion to and from Montgomery form,
Montgomery multiplication, and the `powMod` API that uses the Montgomery path
when the modulus is an odd `UInt64`.
-/

namespace MontCtx

/-- Double a reduced residue without leaving `UInt64` arithmetic. -/
private def doubleMod (p acc : UInt64) : UInt64 :=
  let gap := p - acc
  if acc ≥ gap then
    acc - gap
  else
    acc + acc

/-- Compute `R^2 mod p` by repeated doubling in native-word arithmetic. -/
def r2Loop (p : UInt64) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | n + 1, acc => r2Loop p n (doubleMod p acc)

/-- The `R^2 mod p` constant used to enter Montgomery form. -/
@[expose]
def r2OfModulus (p : UInt64) : UInt64 :=
  if p ≤ 1 then
    0
  else
    let rModP := r2Loop p 64 1
    UInt64.ofNat ((rModP.toNat * rModP.toNat) % p.toNat)

/--
One `doubleMod` step doubles a canonical residue modulo `p`, using the
branch condition to avoid word overflow.
-/
private theorem toNat_doubleMod (p acc : UInt64) (hacc : acc.toNat < p.toNat) :
    (doubleMod p acc).toNat = (2 * acc.toNat) % p.toNat := by
  have hp_pos : 0 < p.toNat := by omega
  have hgap_toNat : (p - acc).toNat = p.toNat - acc.toNat :=
    UInt64.toNat_sub_of_le p acc (by
      rw [UInt64.le_iff_toNat_le]
      exact Nat.le_of_lt hacc)
  unfold doubleMod
  by_cases hbranch : p - acc ≤ acc
  · have hgap_le : p.toNat - acc.toNat ≤ acc.toNat := by
      simpa [UInt64.le_iff_toNat_le, hgap_toNat] using hbranch
    have hsub :
        (acc - (p - acc)).toNat = acc.toNat - (p.toNat - acc.toNat) := by
      simpa [hgap_toNat] using UInt64.toNat_sub_of_le acc (p - acc) hbranch
    have htwo_ge : p.toNat ≤ 2 * acc.toNat := by omega
    have htwo_lt : 2 * acc.toNat < 2 * p.toNat := by omega
    have hsub_lt : 2 * acc.toNat - p.toNat < p.toNat := by omega
    have hmod : (2 * acc.toNat) % p.toNat = 2 * acc.toNat - p.toNat := by
      calc
        (2 * acc.toNat) % p.toNat
            = (2 * acc.toNat - p.toNat) % p.toNat :=
              Nat.mod_eq_sub_mod htwo_ge
        _ = 2 * acc.toNat - p.toNat := Nat.mod_eq_of_lt hsub_lt
    simp [hbranch, hsub, hmod]
    omega
  · have hgap_gt : acc.toNat < p.toNat - acc.toNat := by
      have hnot : ¬ (p - acc).toNat ≤ acc.toNat := by
        intro hle
        exact hbranch (by
          rw [UInt64.le_iff_toNat_le]
          exact hle)
      omega
    have htwo_lt_p : 2 * acc.toNat < p.toNat := by omega
    have htwo_lt_word : 2 * acc.toNat < UInt64.word := by
      have hp_lt : p.toNat < UInt64.word := by
        simpa [UInt64.word, UInt64.size] using UInt64.toNat_lt_size p
      omega
    have hadd : (acc + acc).toNat = 2 * acc.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt]
      · omega
      · simpa [UInt64.word, Nat.two_mul] using htwo_lt_word
    have hmod : (2 * acc.toNat) % p.toNat = 2 * acc.toNat :=
      Nat.mod_eq_of_lt htwo_lt_p
    simp [hbranch, hadd, hmod]

/-- The `r2Loop` accumulator equals repeated doubling modulo `p`. -/
private theorem toNat_r2Loop (p : UInt64) :
    ∀ n acc, acc.toNat < p.toNat →
      (r2Loop p n acc).toNat = (acc.toNat * 2 ^ n) % p.toNat := by
  intro n
  induction n with
  | zero =>
      intro acc hacc
      simp [r2Loop, Nat.mod_eq_of_lt hacc]
  | succ n ih =>
      intro acc hacc
      have hp_pos : 0 < p.toNat := by omega
      have hstep_eq := toNat_doubleMod p acc hacc
      have hstep_lt : (doubleMod p acc).toNat < p.toNat := by
        rw [hstep_eq]
        exact Nat.mod_lt _ hp_pos
      calc
        (r2Loop p (n + 1) acc).toNat
            = (r2Loop p n (doubleMod p acc)).toNat := by
              rfl
        _ = ((doubleMod p acc).toNat * 2 ^ n) % p.toNat := ih _ hstep_lt
        _ = (((2 * acc.toNat) % p.toNat) * 2 ^ n) % p.toNat := by
              rw [hstep_eq]
        _ = (acc.toNat * 2 ^ (n + 1)) % p.toNat := by
              rw [Nat.mod_mul_mod]
              congr 1
              rw [Nat.pow_succ]
              ac_rfl

/-- The executable `r2OfModulus` computes `R^2 mod p` for positive moduli. -/
theorem toNat_r2OfModulus (p : UInt64) (hp_pos : 0 < p.toNat) :
    (r2OfModulus p).toNat = (UInt64.word * UInt64.word) % p.toNat := by
  have hp_lt_word : p.toNat < UInt64.word := by
    simpa [UInt64.word, UInt64.size] using UInt64.toNat_lt_size p
  by_cases hle_one : p ≤ 1
  · have hp_le_one : p.toNat ≤ 1 := by
      have hle_nat : p.toNat ≤ (1 : UInt64).toNat := by
        simpa [UInt64.le_iff_toNat_le] using hle_one
      simpa using hle_nat
    have hp_eq_one : p.toNat = 1 := by omega
    unfold r2OfModulus
    simp [hle_one, hp_eq_one, Nat.mod_one]
  · have hp_gt_one : 1 < p.toNat := by
      have hnot_nat : ¬ p.toNat ≤ 1 := by
        intro hle
        exact hle_one (by
          rw [UInt64.le_iff_toNat_le]
          simpa using hle)
      omega
    have hloop :
        (r2Loop p 64 1).toNat = UInt64.word % p.toNat := by
      have hone_lt : (1 : UInt64).toNat < p.toNat := by
        simpa using hp_gt_one
      have h := toNat_r2Loop p 64 1 hone_lt
      simpa [UInt64.word, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using h
    have hsquare_lt : ((r2Loop p 64 1).toNat * (r2Loop p 64 1).toNat) % p.toNat <
        UInt64.word := by
      exact Nat.lt_trans (Nat.mod_lt _ hp_pos) hp_lt_word
    unfold r2OfModulus
    simp [hle_one]
    rw [Nat.mod_eq_of_lt]
    · rw [hloop, Nat.mod_mul_mod]
      calc
        UInt64.word * (UInt64.word % p.toNat) % p.toNat
            = (UInt64.word % p.toNat * ((UInt64.word % p.toNat) % p.toNat)) %
                p.toNat := Nat.mul_mod UInt64.word (UInt64.word % p.toNat) p.toNat
        _ = (UInt64.word % p.toNat * (UInt64.word % p.toNat)) % p.toNat := by
              rw [Nat.mod_mod]
        _ = UInt64.word * UInt64.word % p.toNat := by
              simp
    · simpa [UInt64.word] using hsquare_lt

/-- Build the executable Montgomery context for an odd `UInt64` modulus. -/
@[expose]
def mk (p : UInt64) (hp : p % 2 = 1) : MontCtx p :=
  { p_odd := hp
    p' := montInv p
    p'_eq := by
      have hp_nat : p.toNat % 2 = 1 := by
        have h := congrArg UInt64.toNat hp
        simpa [UInt64.toNat_mod, UInt64.toNat_ofNat, UInt64.size] using h
      have hspec := montInv_spec p hp_nat
      simpa [UInt64.word, Nat.mul_comm] using hspec
    r2 := r2OfModulus p
    r2_eq := by
      have hp_nat : p.toNat % 2 = 1 := by
        have h := congrArg UInt64.toNat hp
        simpa [UInt64.toNat_mod, UInt64.toNat_ofNat, UInt64.size] using h
      have hp_pos : 0 < p.toNat := by
        omega
      exact toNat_r2OfModulus p hp_pos }

/-- The oddness witness stored by `MontCtx.mk`. -/
@[simp, grind =]
theorem mk_p_odd (p : UInt64) (hp : p % 2 = 1) :
    (mk p hp).p_odd = hp := rfl

/-- The Montgomery inverse word stored by `MontCtx.mk`. -/
@[simp, grind =]
theorem mk_p' (p : UInt64) (hp : p % 2 = 1) :
    (mk p hp).p' = montInv p := rfl

/-- The inverse-word correctness fact specialized to `MontCtx.mk`. -/
@[simp, grind =]
theorem mk_p'_eq (p : UInt64) (hp : p % 2 = 1) :
    ((mk p hp).p'.toNat * p.toNat) % UInt64.word = UInt64.word - 1 :=
  (mk p hp).p'_eq

/-- The `R^2 mod p` word stored by `MontCtx.mk`. -/
@[simp, grind =]
theorem mk_r2 (p : UInt64) (hp : p % 2 = 1) :
    (mk p hp).r2 = r2OfModulus p := rfl

/-- The `R^2 mod p` correctness fact specialized to `MontCtx.mk`. -/
@[simp, grind =]
theorem mk_r2_eq (p : UInt64) (hp : p % 2 = 1) :
    (mk p hp).r2.toNat = (UInt64.word * UInt64.word) % p.toNat :=
  (mk p hp).r2_eq

/-- View the odd-modulus assumption as a Nat-level parity fact. -/
@[simp]
theorem p_odd_nat (ctx : MontCtx p) : p.toNat % 2 = 1 := by
  have h := congrArg UInt64.toNat ctx.p_odd
  simpa [UInt64.toNat_mod, UInt64.toNat_ofNat, UInt64.size] using h

/-- An odd `UInt64` modulus is positive at the Nat level. -/
@[simp]
theorem p_pos (ctx : MontCtx p) : 0 < p.toNat := by
  have hodd := ctx.p_odd_nat
  omega

/-- Every `UInt64` modulus is below the Montgomery radix `R = 2^64`. -/
@[simp]
theorem p_lt_R (_ctx : MontCtx p) : p.toNat < UInt64.word := by
  simpa [UInt64.word, UInt64.size] using UInt64.toNat_lt_size p

/-- The Nat-level oddness fact specialized to `MontCtx.mk`. -/
@[simp, grind =]
theorem mk_p_odd_nat (p : UInt64) (hp : p % 2 = 1) :
    p.toNat % 2 = 1 :=
  (mk p hp).p_odd_nat

/-- Positivity of a modulus equipped with `MontCtx.mk`. -/
@[simp]
theorem mk_p_pos (p : UInt64) (hp : p % 2 = 1) :
    0 < p.toNat :=
  (mk p hp).p_pos

/-- The radix bound for a modulus equipped with `MontCtx.mk`. -/
@[simp]
theorem mk_p_lt_R (p : UInt64) (hp : p % 2 = 1) :
    p.toNat < UInt64.word :=
  (mk p hp).p_lt_R

/-- Convert a standard residue into Montgomery form. -/
@[expose]
def toMont (ctx : MontCtx p) (a : UInt64) : UInt64 :=
  let (hi, lo) := UInt64.mulFull a ctx.r2
  montgomeryReduce ctx hi lo

/-- Convert a Montgomery residue back to the standard representation. -/
@[expose]
def fromMont (ctx : MontCtx p) (a : UInt64) : UInt64 :=
  montgomeryReduce ctx 0 a

/-- Multiply two Montgomery residues, staying inside the Montgomery domain. -/
@[expose]
def mulMont (ctx : MontCtx p) (a b : UInt64) : UInt64 :=
  let (hi, lo) := UInt64.mulFull a b
  montgomeryReduce ctx hi lo

/--
For reduced inputs `a, b < p`, the two-word product `a * b` (encoded as
`lo + hi * word`) stays below `p * word`. This is the range precondition
`montgomeryReduce` needs to behave as Montgomery reduction on the `mulMont` product.
-/
private theorem twoWordProduct_lt_p_word (ctx : MontCtx p) (a b : UInt64)
    (ha : a.toNat < p.toNat) (hb : b.toNat < p.toNat) :
    (UInt64.mulFull a b).2.toNat + (UInt64.mulFull a b).1.toNat * UInt64.word <
      p.toNat * UInt64.word := by
  have hprod_lt_p2 : a.toNat * b.toNat < p.toNat * p.toNat :=
    Nat.mul_lt_mul'' ha hb
  have hp2_lt_pword : p.toNat * p.toNat < p.toNat * UInt64.word :=
    Nat.mul_lt_mul_of_pos_left ctx.p_lt_R ctx.p_pos
  calc
    (UInt64.mulFull a b).2.toNat + (UInt64.mulFull a b).1.toNat * UInt64.word
        = a.toNat * b.toNat := by grind
    _ < p.toNat * p.toNat := hprod_lt_p2
    _ < p.toNat * UInt64.word := hp2_lt_pword

/--
Reducing the two-word product through `montgomeryReduce` produces the Montgomery
representative: multiplying the result back by `word` recovers `a * b` modulo
`p`. The `p * p' ≡ -1 (mod word)` hypothesis is the Montgomery inverse
condition that makes the reduction exact.
-/
private theorem montgomeryReduce_mulFull_repr_word (ctx : MontCtx p) (a b : UInt64)
    (hT :
      (UInt64.mulFull a b).2.toNat + (UInt64.mulFull a b).1.toNat * UInt64.word <
        p.toNat * UInt64.word)
    (hpp' : p.toNat * ctx.p'.toNat % UInt64.word = UInt64.word - 1) :
    (montgomeryReduce ctx (UInt64.mulFull a b).1 (UInt64.mulFull a b).2).toNat *
        UInt64.word % p.toNat =
      (a.toNat * b.toNat) % p.toNat := by
  rw [toNat_montgomeryReduce ctx (UInt64.mulFull a b).1 (UInt64.mulFull a b).2 hT]
  have hmontgomeryReduce := montgomeryReduceNat_eq_mod ctx.p_pos ctx.p_lt_R hpp' hT
  calc
    montgomeryReduceNat p.toNat ctx.p'.toNat
          ((UInt64.mulFull a b).2.toNat + (UInt64.mulFull a b).1.toNat * UInt64.word) *
        UInt64.word % p.toNat
        = ((UInt64.mulFull a b).2.toNat + (UInt64.mulFull a b).1.toNat *
            UInt64.word) % p.toNat := hmontgomeryReduce
    _ = (a.toNat * b.toNat) % p.toNat := by grind

/--
Reducing the two-word product through `montgomeryReduce` lands strictly below the modulus,
so `mulMont` returns an already-reduced residue with no extra conditional
subtraction.
-/
private theorem montgomeryReduce_mulFull_lt (ctx : MontCtx p) (a b : UInt64)
    (hT :
      (UInt64.mulFull a b).2.toNat + (UInt64.mulFull a b).1.toNat * UInt64.word <
        p.toNat * UInt64.word)
    (hpp' : p.toNat * ctx.p'.toNat % UInt64.word = UInt64.word - 1) :
    (montgomeryReduce ctx (UInt64.mulFull a b).1 (UInt64.mulFull a b).2).toNat < p.toNat := by
  rw [toNat_montgomeryReduce ctx (UInt64.mulFull a b).1 (UInt64.mulFull a b).2 hT]
  exact montgomeryReduceNat_lt ctx.p_pos ctx.p_lt_R hpp' hT

/--
Multiplication by `word` is injective on residues modulo `p`: since `p` is odd
it is coprime to `word = 2 ^ 64`, so two reduced values `x, y < p` with
`x * word ≡ y * word (mod p)` are equal. This is what lets the
representative-mod-word characterisation pin down a unique `mulMont` value.

Public because any word-modular residue layer built on this context (for
example a Montgomery-form residue ring) needs the same cancellation to prove
that its additive operations preserve the represented value.
-/
theorem cancel_word_mod_of_lt (ctx : MontCtx p) {x y : Nat}
    (hx : x < p.toNat) (hy : y < p.toNat)
    (h : x * UInt64.word % p.toNat = y * UInt64.word % p.toNat) :
    x = y := by
  have hp_pos := ctx.p_pos
  have hcop : Nat.Coprime p.toNat UInt64.word := by
    simpa [UInt64.word] using Nat.coprime_pow_two_of_odd (p := p.toNat) (k := 64)
      ctx.p_odd_nat
  have hle_case :
      ∀ {x y : Nat}, x < p.toNat → y < p.toNat →
        x * UInt64.word % p.toNat = y * UInt64.word % p.toNat →
        y ≤ x → x = y := by
    intro x y hx hy h hxy
    have hsub_mod : (x * UInt64.word - y * UInt64.word) % p.toNat = 0 :=
      Nat.sub_mod_eq_zero_of_mod_eq h
    have hdvd_sub_mul : p.toNat ∣ (x - y) * UInt64.word := by
      have hsub_mul : (x - y) * UInt64.word = x * UInt64.word - y * UInt64.word := by
        exact Nat.mul_sub_right_distrib x y UInt64.word
      rw [hsub_mul]
      exact Nat.dvd_of_mod_eq_zero hsub_mod
    have hpdvd_sub : p.toNat ∣ x - y :=
      hcop.dvd_of_dvd_mul_right hdvd_sub_mul
    have hsub_lt : x - y < p.toNat := by omega
    have hsub_zero : x - y = 0 := by
      rcases hpdvd_sub with ⟨k, hk⟩
      cases k with
      | zero =>
          simpa using hk
      | succ k =>
          have hp_le : p.toNat ≤ x - y := by
            calc
              p.toNat ≤ p.toNat * (k + 1) := by
                exact Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
              _ = x - y := hk.symm
          omega
    omega
  by_cases hxy : y ≤ x
  · exact hle_case hx hy h hxy
  · exact (hle_case hy hx h.symm (Nat.le_of_not_ge hxy)).symm

/-- Converting a reduced Montgomery residue back to standard form is canonical. -/
@[grind =>]
theorem fromMont_lt (ctx : MontCtx p) (a : UInt64) (ha : a < p) :
    ctx.fromMont a < p := by
  rw [UInt64.lt_iff_toNat_lt]
  have haNat : a.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using ha
  have hT : a.toNat + 0 * UInt64.word < p.toNat * UInt64.word := by
    have hword_pos : 0 < UInt64.word := by
      simp [UInt64.word]
    calc
      a.toNat + 0 * UInt64.word = a.toNat := by simp
      _ ≤ a.toNat * UInt64.word := Nat.le_mul_of_pos_right _ hword_pos
      _ < p.toNat * UInt64.word := Nat.mul_lt_mul_of_pos_right haNat hword_pos
  have hpp' : p.toNat * ctx.p'.toNat % UInt64.word = UInt64.word - 1 := by
    simpa [Nat.mul_comm] using ctx.p'_eq
  unfold fromMont
  rw [toNat_montgomeryReduce ctx 0 a hT]
  exact montgomeryReduceNat_lt ctx.p_pos ctx.p_lt_R hpp' hT

/--
`fromMont` removes one Montgomery radix factor from a reduced Montgomery
residue.
-/
theorem fromMont_repr (ctx : MontCtx p) (a : UInt64) (ha : a < p) :
    (ctx.fromMont a).toNat * UInt64.word % p.toNat = a.toNat := by
  have haNat : a.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using ha
  have hT : a.toNat + 0 * UInt64.word < p.toNat * UInt64.word := by
    have hword_pos : 0 < UInt64.word := by
      simp [UInt64.word]
    calc
      a.toNat + 0 * UInt64.word = a.toNat := by simp
      _ ≤ a.toNat * UInt64.word := Nat.le_mul_of_pos_right _ hword_pos
      _ < p.toNat * UInt64.word := Nat.mul_lt_mul_of_pos_right haNat hword_pos
  have hpp' : p.toNat * ctx.p'.toNat % UInt64.word = UInt64.word - 1 := by
    simpa [Nat.mul_comm] using ctx.p'_eq
  unfold fromMont
  rw [toNat_montgomeryReduce ctx 0 a hT]
  have hmontgomeryReduce := montgomeryReduceNat_eq_mod ctx.p_pos ctx.p_lt_R hpp' hT
  simpa [Nat.mod_eq_of_lt haNat] using hmontgomeryReduce

/-- The `Nat` value of `toMont` is multiplication by the Montgomery radix. -/
@[simp, grind =]
theorem toNat_toMont (ctx : MontCtx p) (a : UInt64) (ha : a < p) :
    (ctx.toMont a).toNat = (a.toNat * UInt64.word) % p.toNat := by
  have haNat : a.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using ha
  have hr2Nat : ctx.r2.toNat < p.toNat := by
    rw [ctx.r2_eq]
    exact Nat.mod_lt _ ctx.p_pos
  have hT := twoWordProduct_lt_p_word ctx a ctx.r2 haNat hr2Nat
  have hpp' : p.toNat * ctx.p'.toNat % UInt64.word = UInt64.word - 1 := by
    simpa [Nat.mul_comm] using ctx.p'_eq
  have hraw :
      (ctx.toMont a).toNat * UInt64.word % p.toNat =
        (a.toNat * ctx.r2.toNat) % p.toNat := by
    simpa [toMont] using montgomeryReduce_mulFull_repr_word ctx a ctx.r2 hT hpp'
  have hto_lt_nat : (ctx.toMont a).toNat < p.toNat := by
    simpa [toMont] using montgomeryReduce_mulFull_lt ctx a ctx.r2 hT hpp'
  apply cancel_word_mod_of_lt ctx
  · exact hto_lt_nat
  · exact Nat.mod_lt _ ctx.p_pos
  calc
    (ctx.toMont a).toNat * UInt64.word % p.toNat
        = (a.toNat * ctx.r2.toNat) % p.toNat := hraw
    _ = (a.toNat * (UInt64.word * UInt64.word % p.toNat)) % p.toNat := by
          rw [ctx.r2_eq]
    _ = (a.toNat * (UInt64.word * UInt64.word)) % p.toNat := by
          rw [Nat.mul_mod_mod]
    _ = ((a.toNat * UInt64.word) % p.toNat * UInt64.word) % p.toNat := by
          calc
            a.toNat * (UInt64.word * UInt64.word) % p.toNat
                = (a.toNat * UInt64.word) * (UInt64.word % p.toNat) % p.toNat := by
                  rw [← Nat.mul_assoc]
                  exact (Nat.mul_mod_mod (a.toNat * UInt64.word) UInt64.word p.toNat).symm
            _ = (a.toNat * UInt64.word) * UInt64.word % p.toNat := by
                  exact Nat.mul_mod_mod (a.toNat * UInt64.word) UInt64.word p.toNat
            _ = ((a.toNat * UInt64.word) % p.toNat * (UInt64.word % p.toNat)) %
                  p.toNat := by
                  exact Nat.mul_mod (a.toNat * UInt64.word) UInt64.word p.toNat
            _ = ((a.toNat * UInt64.word) % p.toNat * UInt64.word) % p.toNat := by
                  rw [Nat.mul_mod_mod]

/--
The Montgomery product `mulMont a b` represents `a * b` scaled by `word`:
its representative multiplied back by `word` equals `a * b` modulo `p`. This
is the core algebraic identity from which the user-facing `mulMont`
correctness lemmas are derived.
-/
private theorem mulMont_repr_word (ctx : MontCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.mulMont a b).toNat * UInt64.word % p.toNat =
      (a.toNat * b.toNat) % p.toNat := by
  have haNat : a.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using ha
  have hbNat : b.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using hb
  have hT := twoWordProduct_lt_p_word ctx a b haNat hbNat
  have hpp' : p.toNat * ctx.p'.toNat % UInt64.word = UInt64.word - 1 := by
    simpa [Nat.mul_comm] using ctx.p'_eq
  simpa [mulMont] using montgomeryReduce_mulFull_repr_word ctx a b hT hpp'

/-- Montgomery conversion returns a canonical residue. -/
@[grind =>]
theorem toMont_lt (ctx : MontCtx p) (a : UInt64) (ha : a < p) :
    ctx.toMont a < p := by
  rw [UInt64.lt_iff_toNat_lt]
  have haNat : a.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using ha
  have hr2Nat : ctx.r2.toNat < p.toNat := by
    rw [ctx.r2_eq]
    exact Nat.mod_lt _ ctx.p_pos
  have hT := twoWordProduct_lt_p_word ctx a ctx.r2 haNat hr2Nat
  have hpp' : p.toNat * ctx.p'.toNat % UInt64.word = UInt64.word - 1 := by
    simpa [Nat.mul_comm] using ctx.p'_eq
  simpa [toMont] using montgomeryReduce_mulFull_lt ctx a ctx.r2 hT hpp'

/-- Montgomery multiplication returns a canonical residue. -/
@[grind =>]
theorem mulMont_lt (ctx : MontCtx p) (a b : UInt64) (ha : a < p) (hb : b < p) :
    ctx.mulMont a b < p := by
  rw [UInt64.lt_iff_toNat_lt]
  have haNat : a.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using ha
  have hbNat : b.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using hb
  have hT := twoWordProduct_lt_p_word ctx a b haNat hbNat
  have hpp' : p.toNat * ctx.p'.toNat % UInt64.word = UInt64.word - 1 := by
    simpa [Nat.mul_comm] using ctx.p'_eq
  simpa [mulMont] using montgomeryReduce_mulFull_lt ctx a b hT hpp'

/-- Montgomery multiplication preserves the represented residue product. -/
@[grind =]
theorem mulMont_repr (ctx : MontCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.fromMont (ctx.mulMont a b)).toNat =
      ((ctx.fromMont a).toNat * (ctx.fromMont b).toNat) % p.toNat := by
  let fa := (ctx.fromMont a).toNat
  let fb := (ctx.fromMont b).toNat
  let y := (fa * fb) % p.toNat
  have hmul_lt : ctx.mulMont a b < p := mulMont_lt ctx a b ha hb
  have hmulNat_lt : (ctx.mulMont a b).toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using hmul_lt
  have hfrom_mul_lt : (ctx.fromMont (ctx.mulMont a b)).toNat < p.toNat := by
    have hlt := fromMont_lt ctx (ctx.mulMont a b) hmul_lt
    simpa [UInt64.lt_iff_toNat_lt] using hlt
  have hy_lt : y < p.toNat := Nat.mod_lt _ ctx.p_pos
  have hfa : fa * UInt64.word % p.toNat = a.toNat := by
    simpa [fa] using fromMont_repr ctx a ha
  have hfb : fb * UInt64.word % p.toNat = b.toNat := by
    simpa [fb] using fromMont_repr ctx b hb
  have hy_twice :
      (y * UInt64.word % p.toNat) * UInt64.word % p.toNat =
        (a.toNat * b.toNat) % p.toNat := by
    calc
      (y * UInt64.word % p.toNat) * UInt64.word % p.toNat
          = (((fa * fb) % p.toNat * UInt64.word) % p.toNat) *
              UInt64.word % p.toNat := by rfl
      _ = ((fa * fb * UInt64.word) % p.toNat) * UInt64.word % p.toNat := by
            exact congrArg (fun z => z * UInt64.word % p.toNat)
              (Nat.mod_mul_mod (fa * fb) UInt64.word p.toNat)
      _ = (fa * (fb * UInt64.word) % p.toNat) * UInt64.word % p.toNat := by
            rw [Nat.mul_assoc]
      _ = (fa * (fb * UInt64.word % p.toNat) % p.toNat) *
            UInt64.word % p.toNat := by
            rw [Nat.mul_mod_mod]
      _ = (fa * b.toNat % p.toNat) * UInt64.word % p.toNat := by
            rw [hfb]
      _ = (b.toNat * (fa * UInt64.word)) % p.toNat := by
            calc
              (fa * b.toNat % p.toNat) * UInt64.word % p.toNat
                  = (fa * b.toNat * UInt64.word) % p.toNat := by
                    exact Nat.mod_mul_mod (fa * b.toNat) UInt64.word p.toNat
              _ = (b.toNat * (fa * UInt64.word)) % p.toNat := by
                    rw [Nat.mul_comm fa b.toNat, Nat.mul_assoc]
      _ = (b.toNat * (fa * UInt64.word % p.toNat)) % p.toNat := by
            exact (Nat.mul_mod_mod b.toNat (fa * UInt64.word) p.toNat).symm
      _ = (b.toNat * a.toNat) % p.toNat := by
            rw [hfa]
      _ = (a.toNat * b.toNat) % p.toNat := by
            rw [Nat.mul_comm]
  have hyR_eq_mul : y * UInt64.word % p.toNat = (ctx.mulMont a b).toNat := by
    apply cancel_word_mod_of_lt ctx
    · exact Nat.mod_lt _ ctx.p_pos
    · exact hmulNat_lt
    calc
      (y * UInt64.word % p.toNat) * UInt64.word % p.toNat
          = (a.toNat * b.toNat) % p.toNat := hy_twice
      _ = (ctx.mulMont a b).toNat * UInt64.word % p.toNat :=
            (mulMont_repr_word ctx a b ha hb).symm
  apply cancel_word_mod_of_lt ctx hfrom_mul_lt hy_lt
  calc
    (ctx.fromMont (ctx.mulMont a b)).toNat * UInt64.word % p.toNat
        = (ctx.mulMont a b).toNat := fromMont_repr ctx (ctx.mulMont a b) hmul_lt
    _ = y * UInt64.word % p.toNat := hyR_eq_mul.symm

/-- Converting into Montgomery form and back is the identity on reduced inputs. -/
@[simp, grind =]
theorem fromMont_toMont (ctx : MontCtx p) (a : UInt64) (ha : a < p) :
    ctx.fromMont (ctx.toMont a) = a := by
  apply UInt64.toNat_inj.mp
  have haNat : a.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using ha
  have hto_lt : ctx.toMont a < p := toMont_lt ctx a ha
  have hfrom_lt_nat : (ctx.fromMont (ctx.toMont a)).toNat < p.toNat := by
    have hlt := fromMont_lt ctx (ctx.toMont a) hto_lt
    simpa [UInt64.lt_iff_toNat_lt] using hlt
  apply cancel_word_mod_of_lt ctx hfrom_lt_nat haNat
  calc
    (ctx.fromMont (ctx.toMont a)).toNat * UInt64.word % p.toNat
        = (ctx.toMont a).toNat := fromMont_repr ctx (ctx.toMont a) hto_lt
    _ = a.toNat * UInt64.word % p.toNat := toNat_toMont ctx a ha

/-- Montgomery multiplication computes modular multiplication after conversion. -/
@[simp, grind =]
theorem toNat_mulMont (ctx : MontCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b))).toNat =
      (a.toNat * b.toNat) % p.toNat := by
  have hto_a_lt : ctx.toMont a < p := toMont_lt ctx a ha
  have hto_b_lt : ctx.toMont b < p := toMont_lt ctx b hb
  calc
    (ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b))).toNat
        = ((ctx.fromMont (ctx.toMont a)).toNat *
            (ctx.fromMont (ctx.toMont b)).toNat) % p.toNat :=
          mulMont_repr ctx (ctx.toMont a) (ctx.toMont b) hto_a_lt hto_b_lt
    _ = (a.toNat * b.toNat) % p.toNat := by
          rw [fromMont_toMont ctx a ha, fromMont_toMont ctx b hb]

/-- User-facing equality form of Montgomery multiplication. -/
@[grind =]
theorem mulMont_eq (ctx : MontCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b)) =
      UInt64.ofNat ((a.toNat * b.toNat) % p.toNat) := by
  apply UInt64.toNat_inj.mp
  rw [toNat_mulMont ctx a b ha hb]
  have hmod_lt_word : (a.toNat * b.toNat) % p.toNat < UInt64.size := by
    exact Nat.lt_trans (Nat.mod_lt _ ctx.p_pos) (by
      simpa [UInt64.word] using ctx.p_lt_R)
  simp [Nat.mod_eq_of_lt hmod_lt_word]

/-- Multiplying by zero on the left in Montgomery form converts back to zero. -/
@[simp, grind =]
theorem fromMont_mulMont_toMont_zero_left
    (ctx : MontCtx p) (a : UInt64) (ha : a < p) :
    ctx.fromMont (ctx.mulMont (ctx.toMont 0) (ctx.toMont a)) = 0 := by
  have hzero : (0 : UInt64) < p := by
    rw [UInt64.lt_iff_toNat_lt]
    simpa using ctx.p_pos
  rw [mulMont_eq ctx (0 : UInt64) a hzero ha]
  simp

/-- Multiplying by zero on the right in Montgomery form converts back to zero. -/
@[simp, grind =]
theorem fromMont_mulMont_toMont_zero_right
    (ctx : MontCtx p) (a : UInt64) (ha : a < p) :
    ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont 0)) = 0 := by
  have hzero : (0 : UInt64) < p := by
    rw [UInt64.lt_iff_toNat_lt]
    simpa using ctx.p_pos
  rw [mulMont_eq ctx a (0 : UInt64) ha hzero]
  simp

end MontCtx

namespace HexArith

/-- Number of binary digits in a natural number. -/
def bitLength (n : Nat) : Nat :=
  if n = 0 then 0 else n.log2 + 1

private theorem lt_two_pow_bitLength (n : Nat) : n < 2 ^ bitLength n := by
  unfold bitLength
  by_cases hn : n = 0
  · simp [hn]
  · simpa [hn] using Nat.lt_log2_self (n := n)

private theorem testBit_eq_true_iff_shiftRight_mod_two {n bit : Nat} :
    n.testBit bit = true ↔ (n >>> bit) % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  simp

private theorem testBit_eq_false_iff_shiftRight_mod_two {n bit : Nat} :
    n.testBit bit = false ↔ (n >>> bit) % 2 = 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  cases Nat.mod_two_eq_zero_or_one (n / 2 ^ bit) <;> simp_all

/-- Tail-recursive exponentiation by repeated squaring in Montgomery form. -/
private def powMontBitsGo (ctx : MontCtx p) (k : Nat) :
    Nat → Nat → UInt64 → UInt64 → UInt64
  | 0, _, acc, _ => acc
  | remaining + 1, bit, acc, base =>
      let acc' := if k.testBit bit then ctx.mulMont acc base else acc
      let base' := ctx.mulMont base base
      powMontBitsGo ctx k remaining (bit + 1) acc' base'

/-- Exponentiate a Montgomery-form base by repeated squaring. -/
def powMont (ctx : MontCtx p) (base : UInt64) (n : Nat) : UInt64 :=
  powMontBitsGo ctx n (bitLength n) 0 (ctx.toMont (UInt64.ofNat (1 % p.toNat))) base

/-- Word-sized odd-modulus modular exponentiation via Montgomery arithmetic. -/
@[expose]
def powModWordOdd (a n : Nat) (p : UInt64) (hp : p % 2 = 1) : Nat :=
  let ctx := MontCtx.mk p hp
  let base := ctx.toMont (UInt64.ofNat (a % p.toNat))
  (ctx.fromMont (powMont ctx base n)).toNat

/-- Tail-recursive Nat fallback for modular exponentiation. -/
def powModNatGo (n p : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, acc, _ => acc
  | remaining + 1, bit, acc, base =>
      let acc' := if n.testBit bit then (acc * base) % p else acc
      let base' := (base * base) % p
      powModNatGo n p remaining (bit + 1) acc' base'

/-- Nat-level fallback modular exponentiation by repeated squaring. -/
@[expose]
def powModNat (a n p : Nat) : Nat :=
  powModNatGo n p (bitLength n) 0 (1 % p) (a % p)

/-- `pow_sq`: an even power `base ^ (2 * q)` equals the squared base `(base * base) ^ q`. -/
private theorem pow_sq (base q : Nat) :
    base ^ (2 * q) = (base * base) ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ, Nat.pow_add, ih]
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc]

/-- `pow_sq_succ`: an odd power `base ^ (2 * q + 1)` peels one factor of `base` off the squared base `(base * base) ^ q`. -/
private theorem pow_sq_succ (base q : Nat) :
    base ^ (2 * q + 1) = base * (base * base) ^ q := by
  rw [Nat.pow_succ, pow_sq]
  simp [Nat.mul_comm]

/-- `powModNatGo_eq`: the `Nat`-level square-and-multiply loop preserves the invariant `acc * base ^ (n >>> bit) ≡ a ^ n (mod p)`, so it terminates at `a ^ n % p`. -/
private theorem powModNatGo_eq (a n p remaining bit acc base : Nat) (hp : 0 < p)
    (hbound : n >>> bit < 2 ^ remaining)
    (hacc : acc < p)
    (hinv : acc * base ^ (n >>> bit) % p = a ^ n % p) :
    powModNatGo n p remaining bit acc base = a ^ n % p := by
  induction remaining generalizing bit acc base with
  | zero =>
      have hshift : n >>> bit = 0 := by
        simpa using hbound
      have hacc_mod : acc % p = acc := Nat.mod_eq_of_lt hacc
      calc
        powModNatGo n p 0 bit acc base = acc := rfl
        _ = acc % p := hacc_mod.symm
        _ = a ^ n % p := by simpa [hshift] using hinv
  | succ remaining ih =>
      let q := n >>> bit
      have hq_decomp : q = 2 * (q / 2) + (q % 2) := by
        rw [Nat.add_comm]
        exact (Nat.mod_add_div q 2).symm
      have htail_bound : n >>> (bit + 1) < 2 ^ remaining := by
        have hq_lt : q < 2 ^ (remaining + 1) := hbound
        have hq_div_lt : q / 2 < 2 ^ remaining := by
          have htwo_pow_succ : 2 ^ (remaining + 1) = 2 * 2 ^ remaining := by
            rw [Nat.pow_succ, Nat.mul_comm]
          rw [htwo_pow_succ] at hq_lt
          exact Nat.div_lt_of_lt_mul hq_lt
        simpa [q, Nat.shiftRight_succ, Nat.add_comm] using hq_div_lt
      unfold powModNatGo
      by_cases hbit : n.testBit bit = true
      · have hq_mod : q % 2 = 1 :=
          testBit_eq_true_iff_shiftRight_mod_two.mp hbit
        have hq_eq : q = 2 * (n >>> (bit + 1)) + 1 := by
          calc
            q = 2 * (q / 2) + q % 2 := hq_decomp
            _ = 2 * (q / 2) + 1 := by rw [hq_mod]
            _ = 2 * (n >>> (bit + 1)) + 1 := by
                  simp [q, Nat.shiftRight_succ, Nat.add_comm]
        have hacc' : (acc * base) % p < p := Nat.mod_lt _ hp
        have hinv' :
            ((acc * base) % p) * ((base * base) % p) ^ (n >>> (bit + 1)) % p =
              a ^ n % p := by
          calc
            ((acc * base) % p) * ((base * base) % p) ^ (n >>> (bit + 1)) % p
                = (acc * base * (base * base) ^ (n >>> (bit + 1))) % p := by
                  simpa [Nat.pow_mod, Nat.mul_assoc] using
                    (Nat.mul_mod (acc * base) ((base * base) ^ (n >>> (bit + 1))) p).symm
            _ = acc * (base * (base * base) ^ (n >>> (bit + 1))) % p := by
                  rw [Nat.mul_assoc]
            _ = acc * base ^ (n >>> bit) % p := by
                  change acc * (base * (base * base) ^ (n >>> (bit + 1))) % p =
                    acc * base ^ q % p
                  rw [hq_eq, pow_sq_succ]
            _ = a ^ n % p := hinv
        simpa [hbit] using ih (bit + 1) ((acc * base) % p) ((base * base) % p)
          htail_bound hacc' hinv'
      · have hbit_false : n.testBit bit = false := by
          cases h : n.testBit bit <;> simp_all
        have hq_mod : q % 2 = 0 :=
          testBit_eq_false_iff_shiftRight_mod_two.mp hbit_false
        have hq_eq : q = 2 * (n >>> (bit + 1)) := by
          calc
            q = 2 * (q / 2) + q % 2 := hq_decomp
            _ = 2 * (q / 2) := by rw [hq_mod, Nat.add_zero]
            _ = 2 * (n >>> (bit + 1)) := by
                  simp [q, Nat.shiftRight_succ]
        have hinv' :
            acc * ((base * base) % p) ^ (n >>> (bit + 1)) % p =
              a ^ n % p := by
          calc
            acc * ((base * base) % p) ^ (n >>> (bit + 1)) % p
                = acc * (base * base) ^ (n >>> (bit + 1)) % p := by
                  simpa [Nat.pow_mod, Nat.mul_mod_mod] using
                    (Nat.mul_mod_mod acc ((base * base) ^ (n >>> (bit + 1))) p)
            _ = acc * base ^ (n >>> bit) % p := by
                  change acc * (base * base) ^ (n >>> (bit + 1)) % p =
                    acc * base ^ q % p
                  rw [hq_eq, pow_sq]
            _ = a ^ n % p := hinv
        simpa [hbit] using ih (bit + 1) acc ((base * base) % p)
          htail_bound hacc hinv'

/-- `powModNat_eq`: the `Nat`-level fallback exponentiation `powModNat a n p` computes `a ^ n % p`. -/
private theorem powModNat_eq (a n p : Nat) (hp : 0 < p) :
    powModNat a n p = a ^ n % p := by
  unfold powModNat
  apply powModNatGo_eq a n p (bitLength n) 0 (1 % p) (a % p) hp
  · simpa using lt_two_pow_bitLength n
  · exact Nat.mod_lt _ hp
  · calc
      1 % p * (a % p) ^ (n >>> 0) % p
          = 1 * (a % p) ^ n % p := by
            simp
      _ = a ^ n % p := by
            simp [Nat.pow_mod]

/-- `UInt64.toNat_ofNat_mod_lt_word`: when `p` is below the word size, the residue `x % p` survives a round trip through `UInt64.ofNat` unchanged. -/
private theorem UInt64.toNat_ofNat_mod_lt_word {x p : Nat}
    (hp : 0 < p)
    (hpw : p < UInt64.word) :
    (UInt64.ofNat (x % p)).toNat = x % p := by
  have hlt : x % p < UInt64.size := by
    exact Nat.lt_trans (Nat.mod_lt _ hp) (by
      simpa [UInt64.word] using hpw)
  simpa [UInt64.toNat_ofNat, UInt64.size] using Nat.mod_eq_of_lt hlt

/-- `powMontBitsGo_eq`: the Montgomery-domain bit loop preserves the de-Montgomeryised invariant `fromMont acc * fromMont base ^ (n >>> bit) ≡ a ^ n (mod p)`, so it terminates at `a ^ n % p.toNat`. -/
private theorem powMontBitsGo_eq (ctx : MontCtx p) (a n remaining bit : Nat)
    (acc base : UInt64)
    (hbound : n >>> bit < 2 ^ remaining)
    (hacc : acc < p)
    (hbase : base < p)
    (hinv :
      ((ctx.fromMont acc).toNat * (ctx.fromMont base).toNat ^ (n >>> bit)) %
          p.toNat = a ^ n % p.toNat) :
    (ctx.fromMont (powMontBitsGo ctx n remaining bit acc base)).toNat =
      a ^ n % p.toNat := by
  induction remaining generalizing bit acc base with
  | zero =>
      have hshift : n >>> bit = 0 := by
        simpa using hbound
      have hfrom_lt : (ctx.fromMont acc).toNat < p.toNat := by
        have hlt := MontCtx.fromMont_lt ctx acc hacc
        simpa [UInt64.lt_iff_toNat_lt] using hlt
      calc
        (ctx.fromMont (powMontBitsGo ctx n 0 bit acc base)).toNat =
            (ctx.fromMont acc).toNat := rfl
        _ = (ctx.fromMont acc).toNat % p.toNat := (Nat.mod_eq_of_lt hfrom_lt).symm
        _ = a ^ n % p.toNat := by simpa [hshift] using hinv
  | succ remaining ih =>
      let q := n >>> bit
      have hq_decomp : q = 2 * (q / 2) + (q % 2) := by
        rw [Nat.add_comm]
        exact (Nat.mod_add_div q 2).symm
      have htail_bound : n >>> (bit + 1) < 2 ^ remaining := by
        have hq_lt : q < 2 ^ (remaining + 1) := hbound
        have hq_div_lt : q / 2 < 2 ^ remaining := by
          have htwo_pow_succ : 2 ^ (remaining + 1) = 2 * 2 ^ remaining := by
            rw [Nat.pow_succ, Nat.mul_comm]
          rw [htwo_pow_succ] at hq_lt
          exact Nat.div_lt_of_lt_mul hq_lt
        simpa [q, Nat.shiftRight_succ, Nat.add_comm] using hq_div_lt
      have hbase' : ctx.mulMont base base < p :=
        MontCtx.mulMont_lt ctx base base hbase hbase
      unfold powMontBitsGo
      by_cases hbit : n.testBit bit = true
      · have hq_mod : q % 2 = 1 :=
          testBit_eq_true_iff_shiftRight_mod_two.mp hbit
        have hq_eq : q = 2 * (n >>> (bit + 1)) + 1 := by
          calc
            q = 2 * (q / 2) + q % 2 := hq_decomp
            _ = 2 * (q / 2) + 1 := by rw [hq_mod]
            _ = 2 * (n >>> (bit + 1)) + 1 := by
                  simp [q, Nat.shiftRight_succ, Nat.add_comm]
        have hacc' : ctx.mulMont acc base < p :=
          MontCtx.mulMont_lt ctx acc base hacc hbase
        have hmul_acc :
            (ctx.fromMont (ctx.mulMont acc base)).toNat =
              ((ctx.fromMont acc).toNat * (ctx.fromMont base).toNat) % p.toNat :=
          MontCtx.mulMont_repr ctx acc base hacc hbase
        have hmul_base :
            (ctx.fromMont (ctx.mulMont base base)).toNat =
              ((ctx.fromMont base).toNat * (ctx.fromMont base).toNat) % p.toNat :=
          MontCtx.mulMont_repr ctx base base hbase hbase
        have hinv' :
            ((ctx.fromMont (ctx.mulMont acc base)).toNat *
                (ctx.fromMont (ctx.mulMont base base)).toNat ^ (n >>> (bit + 1))) %
              p.toNat = a ^ n % p.toNat := by
          calc
            ((ctx.fromMont (ctx.mulMont acc base)).toNat *
                (ctx.fromMont (ctx.mulMont base base)).toNat ^ (n >>> (bit + 1))) %
              p.toNat
                = (((ctx.fromMont acc).toNat * (ctx.fromMont base).toNat) %
                    p.toNat *
                    (((ctx.fromMont base).toNat * (ctx.fromMont base).toNat) %
                      p.toNat) ^ (n >>> (bit + 1))) % p.toNat := by
                  rw [hmul_acc, hmul_base]
            _ = ((ctx.fromMont acc).toNat * (ctx.fromMont base).toNat *
                    ((ctx.fromMont base).toNat * (ctx.fromMont base).toNat) ^
                      (n >>> (bit + 1))) % p.toNat := by
                  simpa [Nat.pow_mod, Nat.mul_assoc] using
                    (Nat.mul_mod
                      ((ctx.fromMont acc).toNat * (ctx.fromMont base).toNat)
                      (((ctx.fromMont base).toNat * (ctx.fromMont base).toNat) ^
                        (n >>> (bit + 1))) p.toNat).symm
            _ = ((ctx.fromMont acc).toNat *
                    ((ctx.fromMont base).toNat *
                      ((ctx.fromMont base).toNat * (ctx.fromMont base).toNat) ^
                        (n >>> (bit + 1)))) % p.toNat := by
                  rw [Nat.mul_assoc]
            _ = ((ctx.fromMont acc).toNat *
                    (ctx.fromMont base).toNat ^ (n >>> bit)) % p.toNat := by
                  change ((ctx.fromMont acc).toNat *
                    ((ctx.fromMont base).toNat *
                      ((ctx.fromMont base).toNat * (ctx.fromMont base).toNat) ^
                        (n >>> (bit + 1)))) % p.toNat =
                    ((ctx.fromMont acc).toNat * (ctx.fromMont base).toNat ^ q) % p.toNat
                  rw [hq_eq, pow_sq_succ]
            _ = a ^ n % p.toNat := hinv
        simpa [hbit] using ih (bit + 1) (ctx.mulMont acc base) (ctx.mulMont base base)
          htail_bound hacc' hbase' hinv'
      · have hbit_false : n.testBit bit = false := by
          cases h : n.testBit bit <;> simp_all
        have hq_mod : q % 2 = 0 :=
          testBit_eq_false_iff_shiftRight_mod_two.mp hbit_false
        have hq_eq : q = 2 * (n >>> (bit + 1)) := by
          calc
            q = 2 * (q / 2) + q % 2 := hq_decomp
            _ = 2 * (q / 2) := by rw [hq_mod, Nat.add_zero]
            _ = 2 * (n >>> (bit + 1)) := by
                  simp [q, Nat.shiftRight_succ]
        have hmul_base :
            (ctx.fromMont (ctx.mulMont base base)).toNat =
              ((ctx.fromMont base).toNat * (ctx.fromMont base).toNat) % p.toNat :=
          MontCtx.mulMont_repr ctx base base hbase hbase
        have hinv' :
            ((ctx.fromMont acc).toNat *
                (ctx.fromMont (ctx.mulMont base base)).toNat ^ (n >>> (bit + 1))) %
              p.toNat = a ^ n % p.toNat := by
          calc
            ((ctx.fromMont acc).toNat *
                (ctx.fromMont (ctx.mulMont base base)).toNat ^ (n >>> (bit + 1))) %
              p.toNat
                = ((ctx.fromMont acc).toNat *
                    ((ctx.fromMont base).toNat * (ctx.fromMont base).toNat) ^
                      (n >>> (bit + 1))) % p.toNat := by
                  rw [hmul_base]
                  simpa [Nat.pow_mod, Nat.mul_mod_mod] using
                    (Nat.mul_mod_mod (ctx.fromMont acc).toNat
                      (((ctx.fromMont base).toNat * (ctx.fromMont base).toNat) ^
                        (n >>> (bit + 1))) p.toNat)
            _ = ((ctx.fromMont acc).toNat *
                    (ctx.fromMont base).toNat ^ (n >>> bit)) % p.toNat := by
                  change ((ctx.fromMont acc).toNat *
                    ((ctx.fromMont base).toNat * (ctx.fromMont base).toNat) ^
                      (n >>> (bit + 1))) % p.toNat =
                    ((ctx.fromMont acc).toNat * (ctx.fromMont base).toNat ^ q) % p.toNat
                  rw [hq_eq, pow_sq]
            _ = a ^ n % p.toNat := hinv
        simpa [hbit] using ih (bit + 1) acc (ctx.mulMont base base)
          htail_bound hacc hbase' hinv'

/-- `powModWordOdd_eq`: the word-level Montgomery exponentiation `powModWordOdd a n p hp` computes `a ^ n % p.toNat` for odd `p`. -/
private theorem powModWordOdd_eq (a n : Nat) (p : UInt64) (hp : p % 2 = 1) :
    powModWordOdd a n p hp = a ^ n % p.toNat := by
  let ctx := MontCtx.mk p hp
  let acc0 := ctx.toMont (UInt64.ofNat (1 % p.toNat))
  let base0 := ctx.toMont (UInt64.ofNat (a % p.toNat))
  have hp_pos : 0 < p.toNat := ctx.p_pos
  have hp_lt_word : p.toNat < UInt64.word := ctx.p_lt_R
  have hacc_arg_nat : (UInt64.ofNat (1 % p.toNat)).toNat = 1 % p.toNat :=
    UInt64.toNat_ofNat_mod_lt_word (x := 1) hp_pos hp_lt_word
  have hbase_arg_nat : (UInt64.ofNat (a % p.toNat)).toNat = a % p.toNat :=
    UInt64.toNat_ofNat_mod_lt_word (x := a) hp_pos hp_lt_word
  have hacc_arg_lt : UInt64.ofNat (1 % p.toNat) < p := by
    rw [UInt64.lt_iff_toNat_lt, hacc_arg_nat]
    exact Nat.mod_lt _ hp_pos
  have hbase_arg_lt : UInt64.ofNat (a % p.toNat) < p := by
    rw [UInt64.lt_iff_toNat_lt, hbase_arg_nat]
    exact Nat.mod_lt _ hp_pos
  have hacc0 : acc0 < p := MontCtx.toMont_lt ctx _ hacc_arg_lt
  have hbase0 : base0 < p := MontCtx.toMont_lt ctx _ hbase_arg_lt
  have hfrom_acc0 :
      (ctx.fromMont acc0).toNat = 1 % p.toNat := by
    rw [show acc0 = ctx.toMont (UInt64.ofNat (1 % p.toNat)) by rfl,
      MontCtx.fromMont_toMont ctx _ hacc_arg_lt, hacc_arg_nat]
  have hfrom_base0 :
      (ctx.fromMont base0).toNat = a % p.toNat := by
    rw [show base0 = ctx.toMont (UInt64.ofNat (a % p.toNat)) by rfl,
      MontCtx.fromMont_toMont ctx _ hbase_arg_lt, hbase_arg_nat]
  unfold powModWordOdd powMont
  change (ctx.fromMont (powMontBitsGo ctx n (bitLength n) 0 acc0 base0)).toNat =
    a ^ n % p.toNat
  apply powMontBitsGo_eq ctx a n (bitLength n) 0 acc0 base0
  · simpa using lt_two_pow_bitLength n
  · exact hacc0
  · exact hbase0
  · rw [hfrom_acc0, hfrom_base0]
    calc
      1 % p.toNat * (a % p.toNat) ^ (n >>> 0) % p.toNat
          = 1 * (a % p.toNat) ^ n % p.toNat := by
            simp
      _ = a ^ n % p.toNat := by
            simp [Nat.pow_mod]

/--
Modular exponentiation by repeated squaring, using Montgomery arithmetic for
odd `UInt64` moduli and a direct Nat fallback otherwise.
-/
@[expose]
def powMod (a n p : Nat) : Nat :=
  if _hp0 : p = 0 then
    0
  else
    let p64 := UInt64.ofNat p
    if _hfit : p64.toNat = p then
      if hodd : p64 % 2 = 1 then
        powModWordOdd a n p64 hodd
      else
        powModNat a n p
    else
      powModNat a n p

/-- `powMod` agrees with ordinary modular exponentiation. -/
@[grind =]
theorem powMod_eq (a n p : Nat) (hp : p > 0) :
    powMod a n p = a ^ n % p := by
  unfold powMod
  split
  · omega
  · rename_i hp0
    by_cases hfit_lt : p < UInt64.size
    · have hfit : (UInt64.ofNat p).toNat = p := by
        simpa [UInt64.toNat_ofNat, UInt64.size] using
          Nat.mod_eq_of_lt hfit_lt
      by_cases hodd : UInt64.ofNat p % 2 = 1
      · simp [hfit, hodd, powModWordOdd_eq a n (UInt64.ofNat p) hodd]
      · simp [hfit_lt, hodd, powModNat_eq a n p hp]
    · have hfit : ¬ (UInt64.ofNat p).toNat = p := by
        intro h
        have hmodlt : p % UInt64.size < UInt64.size := Nat.mod_lt _ (by decide)
        have hpmod : p % UInt64.size = p := by
          simpa [UInt64.toNat_ofNat] using h
        exact hfit_lt (by simpa [hpmod] using hmodlt)
      simp [hfit_lt, powModNat_eq a n p hp]

/-- Modular exponentiation modulo zero returns zero. -/
@[simp, grind =]
theorem powMod_modulus_zero (a n : Nat) :
    powMod a n 0 = 0 := by
  rfl

/-- Modular exponentiation with exponent zero returns the residue of `1`. -/
@[simp, grind =]
theorem powMod_zero_exp (a p : Nat) (hp : p > 0) :
    powMod a 0 p = 1 % p := by
  simpa using powMod_eq a 0 p hp

/-- Modular exponentiation with exponent one returns the reduced base. -/
@[simp, grind =]
theorem powMod_one_exp (a p : Nat) (hp : p > 0) :
    powMod a 1 p = a % p := by
  simpa using powMod_eq a 1 p hp

/-- Modular exponentiation with base zero returns the residue of `0 ^ n`. -/
@[simp, grind =]
theorem powMod_zero_base (n p : Nat) (hp : p > 0) :
    powMod 0 n p = 0 ^ n % p := by
  simpa using powMod_eq 0 n p hp

/-- A positive power of zero is zero modulo any positive modulus. -/
@[simp, grind =]
theorem powMod_zero_base_of_pos_exp (n p : Nat) (hn : n > 0) (hp : p > 0) :
    powMod 0 n p = 0 := by
  cases n with
  | zero => omega
  | succ n => simp [powMod_eq 0 (n + 1) p hp]

/-- Modular exponentiation with base one returns the residue of `1`. -/
@[simp, grind =]
theorem powMod_one_base (n p : Nat) (hp : p > 0) :
    powMod 1 n p = 1 % p := by
  simpa using powMod_eq 1 n p hp

/-- Modular exponentiation modulo one returns zero. -/
@[simp, grind =]
theorem powMod_modulus_one (a n : Nat) :
    powMod a n 1 = 0 := by
  rw [powMod_eq a n 1 (by decide)]
  exact Nat.mod_one (a ^ n)

/-- Successor-exponent expansion for `powMod`: multiply by the base on the left
and reduce. -/
@[grind =>]
theorem powMod_succ (a n p : Nat) (hp : p > 0) :
    powMod a (n + 1) p = (a * powMod a n p) % p := by
  rw [powMod_eq a (n + 1) p hp, powMod_eq a n p hp, Nat.pow_succ,
    Nat.mul_comm (a ^ n) a, Nat.mul_mod_mod]

/-- Reducing the base before modular exponentiation does not change `powMod`. -/
@[simp, grind =]
theorem powMod_mod_base (a n p : Nat) (hp : p > 0) :
    powMod (a % p) n p = powMod a n p := by
  rw [powMod_eq (a % p) n p hp, powMod_eq a n p hp]
  simp [Nat.pow_mod]

/-- Modular exponentiation is compatible with multiplying bases. -/
@[grind =>]
theorem powMod_mul_base (a b n p : Nat) (hp : p > 0) :
    powMod (a * b) n p = (powMod a n p * powMod b n p) % p := by
  rw [powMod_eq (a * b) n p hp, powMod_eq a n p hp, powMod_eq b n p hp,
    Nat.mul_pow, Nat.mul_mod]

/-- Exponent-addition expansion for `powMod`: combine two exponentiation phases
by multiplying their reduced results. -/
@[grind =>]
theorem powMod_add_exp (a m n p : Nat) (hp : p > 0) :
    powMod a (m + n) p = (powMod a m p * powMod a n p) % p := by
  rw [powMod_eq a (m + n) p hp, powMod_eq a m p hp, powMod_eq a n p hp,
    Nat.pow_add, Nat.mul_mod]

/-- Left-oriented companion of `powMod_add_exp`. -/
@[grind =>]
theorem powMod_add_exp_left (a m n p : Nat) (hp : p > 0) :
    powMod a (m + n) p = (powMod a n p * powMod a m p) % p := by
  rw [powMod_add_exp a m n p hp, Nat.mul_comm]

/-- Exponent-multiplication composition for `powMod`: an exponent product is a
two-stage modular exponentiation. -/
@[grind =>]
theorem powMod_mul_exp (a m n p : Nat) (hp : p > 0) :
    powMod a (m * n) p = powMod (powMod a m p) n p := by
  rw [powMod_eq a (m * n) p hp, powMod_eq (powMod a m p) n p hp,
    powMod_eq a m p hp, Nat.pow_mul]
  exact Nat.pow_mod (a ^ m) n p

/-- Swap-oriented companion of `powMod_mul_exp`. -/
@[grind =>]
theorem powMod_mul_exp_swap (a m n p : Nat) (hp : p > 0) :
    powMod a (m * n) p = powMod (powMod a n p) m p := by
  rw [Nat.mul_comm m n, powMod_mul_exp a n m p hp]

end HexArith
