/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.Montgomery.Context
public import HexArith.UInt64.Wide

public section
set_option backward.proofsInPublic true

/-!
`WordMod ctx`: residues modulo an odd `m < 2^64`, stored in Montgomery form on
top of `HexArith.MontCtx`. Multiplication is a single Montgomery reduction
(`mulMont`); addition and subtraction are full-range modular operations built
from `UInt64.addCarry`/`subBorrow`, so the whole odd-`m < 2^64` range is
supported (unlike `ZMod64`, which caps at `2^31`). The represented residue of
an element is `ctx.fromMont a.val`, and every operation is proven to compute the
right residue modulo `m` via that map.

This is the scalar layer for the word-sized poly-mod-`p^a` arithmetic of the
Berlekamp-Zassenhaus lattice tier (issue #8691): an odd prime power `p^a < 2^64`
is a valid modulus here.
-/

namespace Hex

/-- Full-range modular addition of two residues below `m`. -/
@[inline] def addModWord (m a b : UInt64) : UInt64 :=
  if (UInt64.addCarry a b false).2 || m ≤ (UInt64.addCarry a b false).1 then
    (UInt64.subBorrow (UInt64.addCarry a b false).1 m false).1
  else
    (UInt64.addCarry a b false).1

/-- Full-range modular subtraction of two residues below `m`. -/
@[inline] def subModWord (m a b : UInt64) : UInt64 :=
  if (UInt64.subBorrow a b false).2 then
    (UInt64.addCarry (UInt64.subBorrow a b false).1 m false).1
  else
    (UInt64.subBorrow a b false).1

/-- `addModWord` computes the modular sum. -/
theorem toNat_addModWord (m a b : UInt64) (hm : m.toNat ≤ UInt64.word)
    (ha : a.toNat < m.toNat) (hb : b.toNat < m.toNat) :
    (addModWord m a b).toNat = (a.toNat + b.toNat) % m.toNat := by
  have haw : a.toNat < UInt64.word := UInt64.toNat_lt_word a
  have hbw : b.toNat < UInt64.word := UInt64.toNat_lt_word b
  have hfst : (UInt64.addCarry a b false).1.toNat = (a.toNat + b.toNat) % UInt64.word := by
    rw [UInt64.toNat_addCarry_fst]; simp
  have hsnd : (UInt64.addCarry a b false).2 = decide (UInt64.word ≤ a.toNat + b.toNat) := by
    rw [UInt64.addCarry_snd]; simp
  unfold addModWord
  by_cases hge : m.toNat ≤ a.toNat + b.toNat
  · -- sum ≥ m, so the modular result is `a + b - m`
    have hmod : (a.toNat + b.toNat) % m.toNat = a.toNat + b.toNat - m.toNat := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    have hcond : ((UInt64.addCarry a b false).2 || m ≤ (UInt64.addCarry a b false).1) = true := by
      rw [hsnd]
      rcases Nat.lt_or_ge (a.toNat + b.toNat) UInt64.word with hlt | hle
      · have hs : (UInt64.addCarry a b false).1.toNat = a.toNat + b.toNat := by
          rw [hfst, Nat.mod_eq_of_lt hlt]
        have : m ≤ (UInt64.addCarry a b false).1 := by
          rw [UInt64.le_iff_toNat_le, hs]; exact hge
        simp [this]
      · simp [hle]
    rw [if_pos hcond, UInt64.toNat_subBorrow_fst]
    simp only [Bool.toNat_false, Nat.add_zero]
    rw [hfst, hmod]
    rcases Nat.lt_or_ge (a.toNat + b.toNat) UInt64.word with hlt | hle
    · rw [Nat.mod_eq_of_lt hlt]
      have he : UInt64.word + (a.toNat + b.toNat) - m.toNat
          = UInt64.word + (a.toNat + b.toNat - m.toNat) := by omega
      rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    · have hk : (a.toNat + b.toNat) % UInt64.word = a.toNat + b.toNat - UInt64.word := by
        rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)]
      rw [hk]
      have he : UInt64.word + (a.toNat + b.toNat - UInt64.word) - m.toNat
          = a.toNat + b.toNat - m.toNat := by omega
      rw [he, Nat.mod_eq_of_lt (by omega)]
  · -- sum < m, no reduction needed
    have hlt_word : a.toNat + b.toNat < UInt64.word := by omega
    have hmod : (a.toNat + b.toNat) % m.toNat = a.toNat + b.toNat := Nat.mod_eq_of_lt (by omega)
    have hs : (UInt64.addCarry a b false).1.toNat = a.toNat + b.toNat := by
      rw [hfst, Nat.mod_eq_of_lt hlt_word]
    have hcond : ((UInt64.addCarry a b false).2 || m ≤ (UInt64.addCarry a b false).1) = false := by
      rw [hsnd]
      have hc1 : ¬ UInt64.word ≤ a.toNat + b.toNat := by omega
      have hc2 : ¬ m ≤ (UInt64.addCarry a b false).1 := by
        rw [UInt64.le_iff_toNat_le, hs]; omega
      simp [hc1, hc2]
    rw [if_neg (by rw [hcond]; simp), hs, hmod]

/-- `addModWord` stays below `m`. -/
theorem addModWord_lt (m a b : UInt64) (hm : 0 < m.toNat) (hmw : m.toNat ≤ UInt64.word)
    (ha : a.toNat < m.toNat) (hb : b.toNat < m.toNat) :
    (addModWord m a b).toNat < m.toNat := by
  rw [toNat_addModWord m a b hmw ha hb]
  exact Nat.mod_lt _ hm

/-- `subModWord` computes the modular difference. -/
theorem toNat_subModWord (m a b : UInt64) (hm : m.toNat ≤ UInt64.word)
    (ha : a.toNat < m.toNat) (hb : b.toNat < m.toNat) :
    (subModWord m a b).toNat = (a.toNat + (m.toNat - b.toNat)) % m.toNat := by
  have haw : a.toNat < UInt64.word := UInt64.toNat_lt_word a
  have hbw : b.toNat < UInt64.word := UInt64.toNat_lt_word b
  have hfst : (UInt64.subBorrow a b false).1.toNat
      = (UInt64.word + a.toNat - b.toNat) % UInt64.word := by
    rw [UInt64.toNat_subBorrow_fst]; simp
  have hsnd : (UInt64.subBorrow a b false).2 = decide (a.toNat < b.toNat) := by
    rw [UInt64.subBorrow_snd]; simp
  unfold subModWord
  by_cases hlt : a.toNat < b.toNat
  · -- borrow: result wraps up by `m`
    have hcond : (UInt64.subBorrow a b false).2 = true := by rw [hsnd]; simp [hlt]
    rw [if_pos hcond, UInt64.toNat_addCarry_fst]
    simp only [Bool.toNat_false, Nat.add_zero]
    rw [hfst]
    have hs : (UInt64.word + a.toNat - b.toNat) % UInt64.word
        = UInt64.word + a.toNat - b.toNat := Nat.mod_eq_of_lt (by omega)
    rw [hs]
    have hrhs : (a.toNat + (m.toNat - b.toNat)) % m.toNat = a.toNat + (m.toNat - b.toNat) :=
      Nat.mod_eq_of_lt (by omega)
    rw [hrhs]
    have he : UInt64.word + a.toNat - b.toNat + m.toNat
        = UInt64.word + (a.toNat + (m.toNat - b.toNat)) := by omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  · -- no borrow: plain difference
    have hcond : (UInt64.subBorrow a b false).2 = false := by rw [hsnd]; simp [hlt]
    rw [if_neg (by rw [hcond]; simp), hfst]
    have hs : (UInt64.word + a.toNat - b.toNat) % UInt64.word = a.toNat - b.toNat := by
      have he : UInt64.word + a.toNat - b.toNat = UInt64.word + (a.toNat - b.toNat) := by omega
      rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hs]
    have hrhs : (a.toNat + (m.toNat - b.toNat)) % m.toNat = a.toNat - b.toNat := by
      have he : a.toNat + (m.toNat - b.toNat) = (a.toNat - b.toNat) + m.toNat := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hrhs]

theorem subModWord_lt (m a b : UInt64) (hm : 0 < m.toNat) (hmw : m.toNat ≤ UInt64.word)
    (ha : a.toNat < m.toNat) (hb : b.toNat < m.toNat) :
    (subModWord m a b).toNat < m.toNat := by
  rw [toNat_subModWord m a b hmw ha hb]
  exact Nat.mod_lt _ hm

/-- `(x + y % M) % M = (x + y) % M`. -/
private theorem add_mod_inner (x y M : Nat) : (x + y % M) % M = (x + y) % M := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/-- Modular negation commutes with multiplication by `w`: since `(M-X)*w` and
`X*w` sum to `M*w ≡ 0`, they are additive inverses modulo `M`. -/
private theorem sub_mul_word_mod (M w X : Nat) (hM : 0 < M) (hXM : X ≤ M) :
    (M - X) * w % M = (M - (X * w % M)) % M := by
  have hsum : (M - X) * w + X * w = M * w := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hXM]
  have hmod0 : ((M - X) * w % M + X * w % M) % M = 0 := by
    rw [← Nat.add_mod, hsum, Nat.mul_mod_right]
  have hylt : (M - X) * w % M < M := Nat.mod_lt _ hM
  have hbvlt : X * w % M < M := Nat.mod_lt _ hM
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod0
  have hk2 : k < 2 := by
    rcases Nat.lt_or_ge k 2 with h | h
    · exact h
    · exfalso
      have hle : M * 2 ≤ M * k := Nat.mul_le_mul (Nat.le_refl M) h
      omega
  have hkcases : k = 0 ∨ k = 1 := by omega
  rcases hkcases with hk0 | hk1
  · rw [hk0, Nat.mul_zero] at hk
    have hA : (M - X) * w % M = 0 := by omega
    have hB : X * w % M = 0 := by omega
    rw [hA, hB, Nat.sub_zero, Nat.mod_self]
  · rw [hk1, Nat.mul_one] at hk
    have hAB : (M - X) * w % M = M - X * w % M := by omega
    rw [hAB]
    exact (Nat.mod_eq_of_lt (by rw [← hAB]; exact hylt)).symm

/-- Residues modulo an odd `m < 2^64`, stored in Montgomery form. `val` is the
Montgomery representative; the represented residue is `ctx.fromMont val`. -/
structure WordMod {m : UInt64} (ctx : _root_.MontCtx m) where
  /-- Montgomery-form representative. -/
  val : UInt64
  /-- The representative is reduced. -/
  isLt : val < m

namespace WordMod

variable {m : UInt64} {ctx : _root_.MontCtx m}

@[ext] theorem ext {a b : WordMod ctx} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

instance : DecidableEq (WordMod ctx) := fun a b =>
  if h : a.val = b.val then isTrue (ext h)
  else isFalse (fun hab => h (congrArg WordMod.val hab))

/-- Represented residue as a `Nat` in `[0, m)`. -/
@[inline] def toNat (a : WordMod ctx) : Nat := (ctx.fromMont a.val).toNat

theorem val_toNat_lt (a : WordMod ctx) : a.val.toNat < m.toNat := by
  rw [← UInt64.lt_iff_toNat_lt]; exact a.isLt

theorem m_le_word (ctx : _root_.MontCtx m) : m.toNat ≤ UInt64.word :=
  Nat.le_of_lt (_root_.MontCtx.p_lt_R ctx)

theorem toNat_lt (a : WordMod ctx) : a.toNat < m.toNat :=
  UInt64.lt_iff_toNat_lt.mp (ctx.fromMont_lt a.val a.isLt)

/-- Multiplication by `word` recovers the Montgomery representative: the key
input to the word-cancellation used by the additive specs. -/
theorem toNat_mul_word (a : WordMod ctx) :
    a.toNat * UInt64.word % m.toNat = a.val.toNat :=
  ctx.fromMont_repr a.val a.isLt

/-- Reduce a `Nat` into `WordMod ctx`. -/
@[inline] def ofNat (n : Nat) : WordMod ctx :=
  ⟨ctx.toMont (UInt64.ofNat (n % m.toNat)), by
    apply ctx.toMont_lt
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_mod_word]
    have h1 : n % m.toNat < m.toNat := Nat.mod_lt _ ctx.p_pos
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h1 (m_le_word ctx))]
    exact h1⟩

@[simp] theorem toNat_ofNat (n : Nat) : (ofNat (ctx := ctx) n).toNat = n % m.toNat := by
  have h1 : n % m.toNat < m.toNat := Nat.mod_lt _ ctx.p_pos
  have hlt : UInt64.ofNat (n % m.toNat) < m := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_mod_word,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h1 (m_le_word ctx))]
    exact h1
  show (ctx.fromMont (ctx.toMont (UInt64.ofNat (n % m.toNat)))).toNat = n % m.toNat
  rw [ctx.fromMont_toMont _ hlt, UInt64.toNat_ofNat_mod_word,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h1 (m_le_word ctx))]

instance : Zero (WordMod ctx) := ⟨ofNat 0⟩
instance : One (WordMod ctx) := ⟨ofNat 1⟩
instance : NatCast (WordMod ctx) := ⟨ofNat⟩

/-- Division, defined only where it is used: by the leading coefficient of a
monic divisor, which is `1`. Dividing by `1` is the identity (`div_one`);
other divisors return `0` and are never exercised by monic `divMod`. -/
@[inline] def div (a b : WordMod ctx) : WordMod ctx := if b = 1 then a else 0

instance : Div (WordMod ctx) := ⟨div⟩

@[simp] theorem div_one (a : WordMod ctx) : a / 1 = a := if_pos rfl

@[simp] theorem toNat_zero : (0 : WordMod ctx).toNat = 0 := by
  show (ofNat (ctx := ctx) 0).toNat = 0
  rw [toNat_ofNat]; simp

@[simp] theorem toNat_one : (1 : WordMod ctx).toNat = 1 % m.toNat := by
  show (ofNat (ctx := ctx) 1).toNat = 1 % m.toNat
  rw [toNat_ofNat]

/-- Montgomery multiplication: one reduction. -/
@[inline] def mul (a b : WordMod ctx) : WordMod ctx :=
  ⟨ctx.mulMont a.val b.val, ctx.mulMont_lt a.val b.val a.isLt b.isLt⟩

instance : Mul (WordMod ctx) := ⟨mul⟩

@[simp] theorem toNat_mul (a b : WordMod ctx) :
    (a * b).toNat = (a.toNat * b.toNat) % m.toNat :=
  ctx.mulMont_repr a.val b.val a.isLt b.isLt

/-- Full-range modular addition. -/
@[inline] def add (a b : WordMod ctx) : WordMod ctx :=
  ⟨addModWord m a.val b.val, by
    rw [UInt64.lt_iff_toNat_lt]
    exact addModWord_lt m a.val b.val ctx.p_pos (m_le_word ctx) (val_toNat_lt a) (val_toNat_lt b)⟩

instance : Add (WordMod ctx) := ⟨add⟩

/-- Full-range modular subtraction. -/
@[inline] def sub (a b : WordMod ctx) : WordMod ctx :=
  ⟨subModWord m a.val b.val, by
    rw [UInt64.lt_iff_toNat_lt]
    exact subModWord_lt m a.val b.val ctx.p_pos (m_le_word ctx) (val_toNat_lt a) (val_toNat_lt b)⟩

instance : Sub (WordMod ctx) := ⟨sub⟩

/-- Modular negation, as subtraction from zero. -/
@[inline] def neg (a : WordMod ctx) : WordMod ctx := (0 : WordMod ctx) - a

instance : Neg (WordMod ctx) := ⟨neg⟩

@[simp] theorem toNat_add (a b : WordMod ctx) :
    (a + b).toNat = (a.toNat + b.toNat) % m.toNat := by
  have hs_lt : addModWord m a.val b.val < m := by
    rw [UInt64.lt_iff_toNat_lt]
    exact addModWord_lt m a.val b.val ctx.p_pos (m_le_word ctx) (val_toNat_lt a) (val_toNat_lt b)
  apply ctx.cancel_word_mod_of_lt (toNat_lt _) (Nat.mod_lt _ ctx.p_pos)
  calc (a + b).toNat * UInt64.word % m.toNat
      = (addModWord m a.val b.val).toNat := by
        show (ctx.fromMont (addModWord m a.val b.val)).toNat * UInt64.word % m.toNat = _
        exact ctx.fromMont_repr _ hs_lt
    _ = (a.val.toNat + b.val.toNat) % m.toNat :=
        toNat_addModWord m a.val b.val (m_le_word ctx) (val_toNat_lt a) (val_toNat_lt b)
    _ = ((a.toNat + b.toNat) % m.toNat) * UInt64.word % m.toNat := by
        rw [Nat.mod_mul_mod, Nat.add_mul,
          Nat.add_mod (a.toNat * UInt64.word) (b.toNat * UInt64.word) m.toNat,
          toNat_mul_word a, toNat_mul_word b]

@[simp] theorem toNat_sub (a b : WordMod ctx) :
    (a - b).toNat = (a.toNat + (m.toNat - b.toNat)) % m.toNat := by
  have hs_lt : subModWord m a.val b.val < m := by
    rw [UInt64.lt_iff_toNat_lt]
    exact subModWord_lt m a.val b.val ctx.p_pos (m_le_word ctx) (val_toNat_lt a) (val_toNat_lt b)
  apply ctx.cancel_word_mod_of_lt (toNat_lt _) (Nat.mod_lt _ ctx.p_pos)
  calc (a - b).toNat * UInt64.word % m.toNat
      = (subModWord m a.val b.val).toNat := by
        show (ctx.fromMont (subModWord m a.val b.val)).toNat * UInt64.word % m.toNat = _
        exact ctx.fromMont_repr _ hs_lt
    _ = (a.val.toNat + (m.toNat - b.val.toNat)) % m.toNat :=
        toNat_subModWord m a.val b.val (m_le_word ctx) (val_toNat_lt a) (val_toNat_lt b)
    _ = ((a.toNat + (m.toNat - b.toNat)) % m.toNat) * UInt64.word % m.toNat := by
        rw [Nat.mod_mul_mod, Nat.add_mul,
          Nat.add_mod (a.toNat * UInt64.word) ((m.toNat - b.toNat) * UInt64.word) m.toNat,
          toNat_mul_word a,
          sub_mul_word_mod m.toNat UInt64.word b.toNat ctx.p_pos (Nat.le_of_lt (toNat_lt b)),
          toNat_mul_word b, add_mod_inner]

@[simp] theorem toNat_neg (a : WordMod ctx) :
    (-a).toNat = (m.toNat - a.toNat) % m.toNat := by
  show (0 - a).toNat = (m.toNat - a.toNat) % m.toNat
  rw [toNat_sub, toNat_zero, Nat.zero_add]

end WordMod

end Hex
