/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHensel.Basic
public import HexModArith
public import HexPoly.Euclid.MonicUnique

public section

/-!
Mathlib-free foundation for transporting integer polynomial arithmetic (reduced
modulo a working modulus) into the word-sized Montgomery ring `WordMod ctx`.

This file provides the scalar bridge used by a word-sized Hensel step:
`WordMod.toNat` is injective and `WordMod.ofNat` inverts it (`ofNat_toNat`), and
`ZPoly.intModNat` (the canonical `[0, M)` residue) commutes with `+`, `*`, and the
full-range modular `-` of `WordMod` (`intModNat_add`/`intModNat_mul`/`intModNat_sub`).

These are the reusable, general pieces. The full polynomial ring-homomorphism
transport built on top (the multiplicative `toWP` law is the deep piece, requiring
a fold-congruence over the coefficient convolution) and the byte-identical Hensel
correspondence are follow-up work; see the discussion on issue #8854.
-/

namespace Hex
namespace WordMod

variable {m : UInt64} {ctx : _root_.MontCtx m}

/-- `toNat` is injective: the represented residue determines the element. Follows
from `toNat_mul_word` (`a.val.toNat = a.toNat * word % m`) with no Montgomery
round-trip lemma. -/
theorem toNat_injective {a b : WordMod ctx} (h : a.toNat = b.toNat) : a = b := by
  apply ext
  apply UInt64.toNat_inj.mp
  rw [← toNat_mul_word a, ← toNat_mul_word b, h]

theorem eq_iff_toNat {a b : WordMod ctx} : a = b ↔ a.toNat = b.toNat :=
  ⟨fun h => by rw [h], toNat_injective⟩

/-- Round trip: reducing the represented residue back in is the identity. -/
@[simp] theorem ofNat_toNat (a : WordMod ctx) : ofNat (ctx := ctx) a.toNat = a := by
  apply toNat_injective
  rw [toNat_ofNat, Nat.mod_eq_of_lt (toNat_lt a)]

@[simp] theorem sub_self (a : WordMod ctx) : a - a = 0 := by
  apply toNat_injective
  rw [toNat_sub, toNat_zero]
  have ha : a.toNat < m.toNat := toNat_lt a
  rw [Nat.add_sub_cancel' (Nat.le_of_lt ha), Nat.mod_self]

/-! ### `Lean.Grind.CommRing (WordMod ctx)`

The Montgomery residue ring is a commutative ring; the axioms transport through
`toNat` (which is `+`/`*`/`-`-compatible modulo `m`). This is what lets the
word-sized poly arithmetic reuse the generic `DensePoly` ring/division lemmas. -/

instance : Lean.Grind.Semiring (WordMod ctx) := by
  refine Lean.Grind.Semiring.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    apply toNat_injective
    rw [toNat_add, toNat_zero, Nat.add_zero, Nat.mod_eq_of_lt (toNat_lt a)]
  · intro a b
    apply toNat_injective
    rw [toNat_add, toNat_add, Nat.add_comm]
  · intro a b c
    apply toNat_injective
    rw [toNat_add, toNat_add, toNat_add, toNat_add, Nat.mod_add_mod, Nat.add_mod_mod,
      Nat.add_assoc]
  · intro a b c
    apply toNat_injective
    rw [toNat_mul, toNat_mul, toNat_mul, toNat_mul, Nat.mod_mul_mod, Nat.mul_mod_mod,
      Nat.mul_assoc]
  · intro a
    apply toNat_injective
    rw [toNat_mul, toNat_one, Nat.mul_mod_mod, Nat.mul_one, Nat.mod_eq_of_lt (toNat_lt a)]
  · intro a
    apply toNat_injective
    rw [toNat_mul, toNat_one, Nat.mod_mul_mod, Nat.one_mul, Nat.mod_eq_of_lt (toNat_lt a)]
  · intro a b c
    apply toNat_injective
    rw [toNat_mul, toNat_add, toNat_add, toNat_mul, toNat_mul, Nat.mul_mod_mod,
      Nat.mul_add, Nat.add_mod]
  · intro a b c
    apply toNat_injective
    rw [toNat_mul, toNat_add, toNat_add, toNat_mul, toNat_mul, Nat.mod_mul_mod,
      Nat.add_mul, Nat.add_mod]
  · intro a
    apply toNat_injective
    rw [toNat_mul, toNat_zero, Nat.zero_mul, Nat.zero_mod]
  · intro a
    apply toNat_injective
    rw [toNat_mul, toNat_zero, Nat.mul_zero, Nat.zero_mod]
  · intro a
    apply toNat_injective
    rw [toNat_pow, toNat_one, Nat.pow_zero]
  · intro a n
    apply toNat_injective
    rw [toNat_pow, toNat_mul, toNat_pow, Nat.pow_succ, Nat.mod_mul_mod]
  · intro n
    apply toNat_injective
    rw [show (OfNat.ofNat (n + 1) : WordMod ctx) = ofNat (n + 1) from rfl,
      toNat_ofNat, toNat_add, toNat_one,
      show (OfNat.ofNat n : WordMod ctx) = ofNat n from rfl, toNat_ofNat, ← Nat.add_mod]
  · intro n; rfl
  · intro n a
    apply toNat_injective
    rw [toNat_nsmul, toNat_mul, show ((n : WordMod ctx)).toNat = (ofNat n : WordMod ctx).toNat from rfl,
      toNat_ofNat]

theorem neg_neg' (a : WordMod ctx) : (- -a : WordMod ctx) = a := by
  apply toNat_injective
  rw [toNat_neg, toNat_neg]
  have ha : a.toNat < m.toNat := toNat_lt a
  rcases Nat.eq_zero_or_pos a.toNat with h0 | h0
  · rw [h0]; simp
  · rw [Nat.mod_eq_of_lt (show m.toNat - a.toNat < m.toNat by omega),
      Nat.sub_sub_self (Nat.le_of_lt ha), Nat.mod_eq_of_lt ha]

instance : Lean.Grind.Ring (WordMod ctx) where
  neg_add_cancel := by
    intro a
    apply toNat_injective
    rw [toNat_add, toNat_neg, toNat_zero]
    have ha : a.toNat < m.toNat := toNat_lt a
    rcases Nat.eq_zero_or_pos a.toNat with h0 | h0
    · rw [h0]; simp
    · rw [Nat.mod_eq_of_lt (show m.toNat - a.toNat < m.toNat by omega),
        Nat.sub_add_cancel (Nat.le_of_lt ha), Nat.mod_self]
  sub_eq_add_neg := by
    intro a b
    apply toNat_injective
    rw [toNat_sub, toNat_add, toNat_neg, Nat.add_mod_mod]
  neg_zsmul := by
    intro i a
    cases i with
    | ofNat n =>
        cases n with
        | zero =>
            show ((0 : Int) • a) = -((0 : Int) • a)
            apply toNat_injective
            change (ofNat 0 * a).toNat = (-(ofNat 0 * a)).toNat
            rw [toNat_neg, toNat_mul, toNat_ofNat]
            simp
        | succ n =>
            apply toNat_injective
            change ((-ofNat (n + 1)) * a).toNat = (-(ofNat (n + 1) * a)).toNat
            rw [toNat_neg_mul, toNat_neg, toNat_mul]
    | negSucc n =>
        change ofNat (n + 1) * a = -((-ofNat (n + 1)) * a)
        apply toNat_injective
        rw [toNat_neg, toNat_neg_mul, toNat_mul]
        generalize hx : (ofNat (ctx := ctx) (n + 1)).toNat * a.toNat % m.toNat = x
        have hlt : x < m.toNat := by
          rw [← hx]
          exact Nat.mod_lt _ ctx.p_pos
        rcases Nat.eq_zero_or_pos x with h0 | h0
        · rw [h0]; simp
        · rw [Nat.mod_eq_of_lt (show m.toNat - x < m.toNat by omega),
              Nat.sub_sub_self (Nat.le_of_lt hlt), Nat.mod_eq_of_lt hlt]
  intCast_neg := by
    intro i
    cases i with
    | ofNat n =>
        cases n with
        | zero =>
            show ((0 : Int) : WordMod ctx) = -((0 : Int) : WordMod ctx)
            apply toNat_injective
            change (ofNat 0 : WordMod ctx).toNat = (-(ofNat 0 : WordMod ctx)).toNat
            rw [toNat_neg]; simp
        | succ n => rfl
    | negSucc n =>
        exact (neg_neg' (ofNat (n + 1))).symm

instance : Lean.Grind.CommRing (WordMod ctx) := by
  refine Lean.Grind.CommRing.mk ?_
  intro a b
  apply toNat_injective
  rw [toNat_mul, toNat_mul, Nat.mul_comm]

end WordMod

namespace ZPoly

/-- `intModNat` as an `Int` remainder (public form of the private
`intModNat_eq_emod`). -/
theorem intModNat_cast (z : Int) {M : Nat} (hM : 0 < M) :
    (intModNat z M : Int) = z % (M : Int) := by
  unfold intModNat
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hM)))

theorem intModNat_lt' (z : Int) {M : Nat} (hM : 0 < M) : intModNat z M < M := by
  have hc := intModNat_cast z hM
  have h1 : z % (M : Int) < M := Int.emod_lt_of_pos z (by exact_mod_cast hM)
  omega

/-- `intModNat` commutes with addition modulo `M`. -/
theorem intModNat_add (x y : Int) {M : Nat} (hM : 0 < M) :
    intModNat (x + y) M = (intModNat x M + intModNat y M) % M := by
  have hh : (intModNat (x + y) M : Int) = (((intModNat x M + intModNat y M) % M : Nat) : Int) := by
    rw [intModNat_cast (x + y) hM,
      show (((intModNat x M + intModNat y M) % M : Nat) : Int)
          = ((intModNat x M : Int) + intModNat y M) % M from by exact_mod_cast rfl,
      intModNat_cast x hM, intModNat_cast y hM, ← Int.add_emod]
  exact_mod_cast hh

/-- `intModNat` commutes with multiplication modulo `M`. -/
theorem intModNat_mul (x y : Int) {M : Nat} (hM : 0 < M) :
    intModNat (x * y) M = (intModNat x M * intModNat y M) % M := by
  have hh : (intModNat (x * y) M : Int) = (((intModNat x M * intModNat y M) % M : Nat) : Int) := by
    rw [intModNat_cast (x * y) hM,
      show (((intModNat x M * intModNat y M) % M : Nat) : Int)
          = ((intModNat x M : Int) * intModNat y M) % M from by exact_mod_cast rfl,
      intModNat_cast x hM, intModNat_cast y hM, ← Int.mul_emod]
  exact_mod_cast hh

/-- `intModNat` commutes with the full-range modular subtraction used by `WordMod`
(`x + (M - y)`), matching `WordMod.toNat_sub`. -/
theorem intModNat_sub (x y : Int) {M : Nat} (hM : 0 < M) :
    intModNat (x - y) M = (intModNat x M + (M - intModNat y M)) % M := by
  have hylt := intModNat_lt' y hM
  have hh : (intModNat (x - y) M : Int)
      = (((intModNat x M + (M - intModNat y M)) % M : Nat) : Int) := by
    rw [intModNat_cast (x - y) hM,
      show (((intModNat x M + (M - intModNat y M)) % M : Nat) : Int)
          = ((intModNat x M : Int) + ((M : Int) - intModNat y M)) % M from by
        have : intModNat y M ≤ M := Nat.le_of_lt hylt
        exact_mod_cast rfl,
      intModNat_cast x hM, intModNat_cast y hM,
      show (x % (M:Int)) + ((M:Int) - y % M) = (x % M - y % M) + M from by omega,
      Int.add_emod_right, ← Int.sub_emod]
  exact_mod_cast hh

end ZPoly
end Hex
