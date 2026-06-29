/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.Barrett.Context
public import HexArith.Montgomery.Context
public import HexModArith.Basic
public import HexModArith.Ring

public section

/-!
Hot-loop optimization wrappers for `hex-mod-arith`.

This module lifts the `UInt64`-level Barrett and Montgomery contexts from
`hex-arith` to the `Hex.ZMod64` surface promised by the `hex-mod-arith` spec.
The wrappers keep the executable contexts explicit while providing typed entry
and exit points for standard residues and Montgomery-form loop temporaries.
-/
namespace Hex

/--
Barrett reduction context specialized to a `ZMod64` modulus.

The stored `UInt64` modulus must agree with the Nat-indexed `ZMod64` modulus;
the underlying `HexArith` context then provides the small-modulus fast path.
-/
structure BarrettCtx (p : Nat) [ZMod64.Bounds p] where
  /-- The executable machine-word modulus used by the underlying context. -/
  modulus : UInt64
  /-- The stored word modulus agrees with the Nat-indexed `ZMod64` modulus. -/
  modulus_eq : modulus.toNat = p
  /-- The underlying `UInt64` Barrett context from `HexArith`. -/
  toUInt64Ctx : _root_.BarrettCtx modulus

/--
Montgomery reduction context specialized to a `ZMod64` modulus.

As with `BarrettCtx`, the executable context stores the machine-word modulus
used by the underlying `HexArith` Montgomery code.
-/
structure MontCtx (p : Nat) [ZMod64.Bounds p] where
  /-- The executable machine-word modulus used by the underlying context. -/
  modulus : UInt64
  /-- The stored word modulus agrees with the Nat-indexed `ZMod64` modulus. -/
  modulus_eq : modulus.toNat = p
  /-- The underlying `UInt64` Montgomery context from `HexArith`. -/
  toUInt64Ctx : _root_.MontCtx modulus

/--
Temporary Montgomery-form residue for hot loops.

This is intentionally distinct from `ZMod64`: values are still reduced into
`[0, p)`, but they represent residues in Montgomery form rather than the
canonical standard representative.
-/
structure MontResidue (p : Nat) [ZMod64.Bounds p] where
  /-- Backing word for the Montgomery-form representative. -/
  val : UInt64
  /-- The backing word remains reduced modulo `p`. -/
  isLt : val.toNat < p

namespace MontResidue

variable {p : Nat} [ZMod64.Bounds p]

/-- View a Montgomery-form residue as its backing machine word. -/
@[expose]
def toUInt64 (a : MontResidue p) : UInt64 :=
  a.val

/-- View a Montgomery-form residue as its reduced Nat representative. -/
@[expose]
def toNat (a : MontResidue p) : Nat :=
  a.val.toNat

instance : CoeOut (MontResidue p) UInt64 where
  coe := toUInt64

instance : CoeOut (MontResidue p) Nat where
  coe := toNat

/-- The `UInt64` view of a Montgomery residue is its backing word. -/
@[simp, grind =] theorem toUInt64_eq_val (a : MontResidue p) : a.toUInt64 = a.val := rfl

/-- The Nat view of a Montgomery residue is the Nat value of its backing word. -/
@[simp, grind =] theorem toNat_eq_val (a : MontResidue p) : a.toNat = a.val.toNat := rfl

/-- The Nat view of a Montgomery residue is reduced modulo its indexed modulus. -/
@[simp] theorem toNat_lt (a : MontResidue p) : a.toNat < p := a.isLt

/-- Montgomery residues are equal when their backing words are equal. -/
@[ext] theorem ext {a b : MontResidue p} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Extensionality for Montgomery residues via their canonical Nat representatives. -/
theorem ext_toNat {a b : MontResidue p} (h : a.toNat = b.toNat) : a = b :=
  ext (UInt64.toNat_inj.mp h)

/-- Two Montgomery residues are equal exactly when their canonical representatives agree. -/
theorem eq_iff_toNat_eq (a b : MontResidue p) : a = b ↔ a.toNat = b.toNat :=
  ⟨fun h => h ▸ rfl, ext_toNat⟩

end MontResidue

namespace BarrettCtx

variable {p : Nat} [ZMod64.Bounds p]

/-- Build a Barrett hot-loop context from the indexed small modulus. -/
@[expose]
def ofModulus (hp : 1 < p) (hlt : p < 2 ^ 32) : BarrettCtx p := by
  let m := UInt64.ofNat p
  have hm : m.toNat = p := by
    have hword : p < UInt64.word := Nat.lt_trans hlt (by decide : 2 ^ 32 < UInt64.word)
    simpa [m, UInt64.toNat_ofNat, UInt64.size, UInt64.word] using Nat.mod_eq_of_lt hword
  exact
    { modulus := m
      modulus_eq := hm
      toUInt64Ctx := _root_.BarrettCtx.mk m (by simpa [hm] using hp) (by simpa [hm] using hlt) }

/-- The smart constructor stores the indexed modulus as a machine word. -/
@[simp, grind =] theorem ofModulus_modulus (hp : 1 < p) (hlt : p < 2 ^ 32) :
    (ofModulus (p := p) hp hlt).modulus = UInt64.ofNat p := rfl

/-- The smart constructor's stored word modulus agrees with the indexed modulus. -/
@[simp, grind =] theorem ofModulus_modulus_eq (hp : 1 < p) (hlt : p < 2 ^ 32) :
    (ofModulus (p := p) hp hlt).modulus.toNat = p :=
  (ofModulus (p := p) hp hlt).modulus_eq

/-- The smart constructor delegates to the underlying `UInt64` Barrett context. -/
theorem ofModulus_toUInt64Ctx (hp : 1 < p) (hlt : p < 2 ^ 32) :
    (ofModulus (p := p) hp hlt).toUInt64Ctx =
      _root_.BarrettCtx.mk (UInt64.ofNat p)
        (by
          have hword : p < UInt64.word :=
            Nat.lt_trans hlt (by decide : 2 ^ 32 < UInt64.word)
          have hm : (UInt64.ofNat p).toNat = p := by
            simpa [UInt64.toNat_ofNat, UInt64.size, UInt64.word] using
              Nat.mod_eq_of_lt hword
          simpa [hm] using hp)
        (by
          have hword : p < UInt64.word :=
            Nat.lt_trans hlt (by decide : 2 ^ 32 < UInt64.word)
          have hm : (UInt64.ofNat p).toNat = p := by
            simpa [UInt64.toNat_ofNat, UInt64.size, UInt64.word] using
              Nat.mod_eq_of_lt hword
          simpa [hm] using hlt) := by
  simp [ofModulus]

/--
The smart constructor's underlying Barrett context stores the reciprocal for
the indexed modulus.
-/
@[simp, grind =] theorem ofModulus_toUInt64Ctx_pinv (hp : 1 < p) (hlt : p < 2 ^ 32) :
    ((ofModulus (p := p) hp hlt).toUInt64Ctx).pinv =
      UInt64.ofNat (barrettRadix / p) := by
  rw [show ((ofModulus (p := p) hp hlt).toUInt64Ctx).pinv =
      UInt64.ofNat (barrettRadix / (ofModulus (p := p) hp hlt).modulus.toNat) from rfl]
  rw [ofModulus_modulus_eq]

private theorem residue_lt_modulus (ctx : BarrettCtx p) (a : ZMod64 p) :
    a.toUInt64 < ctx.modulus :=
  UInt64.lt_iff_toNat_lt.mpr <| by
    simpa [ctx.modulus_eq] using a.toNat_lt

/--
Multiply two standard residues using the Barrett context and repackage the
result as a `ZMod64`.
-/
@[expose]
def mulMod (ctx : BarrettCtx p) (a b : ZMod64 p) : ZMod64 p :=
  ZMod64.ofNat p ((_root_.BarrettCtx.mulMod ctx.toUInt64Ctx a.toUInt64 b.toUInt64).toNat)

/--
The `ZMod64` Barrett wrapper computes the ordinary modular product on reduced
representatives.
-/
@[simp, grind =] theorem toNat_mulMod (ctx : BarrettCtx p) (a b : ZMod64 p) :
    (ctx.mulMod a b).toNat = (a.toNat * b.toNat) % p := by
  have ha := residue_lt_modulus ctx a
  have hb := residue_lt_modulus ctx b
  have hlt : (_root_.BarrettCtx.mulMod ctx.toUInt64Ctx a.toUInt64 b.toUInt64).toNat < p := by
    have hlt64 :
        _root_.BarrettCtx.mulMod ctx.toUInt64Ctx a.toUInt64 b.toUInt64 < ctx.modulus :=
      _root_.BarrettCtx.mulMod_lt ctx.toUInt64Ctx a.toUInt64 b.toUInt64 ha hb
    simpa [ctx.modulus_eq] using UInt64.lt_iff_toNat_lt.mp hlt64
  rw [mulMod, ZMod64.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  simpa [ctx.modulus_eq] using
    (_root_.BarrettCtx.toNat_mulMod ctx.toUInt64Ctx a.toUInt64 b.toUInt64 ha hb)

/--
Barrett hot-loop multiplication agrees with the ordinary `ZMod64`
multiplication surface.
-/
@[simp, grind =] theorem mulMod_eq_mul (ctx : BarrettCtx p) (a b : ZMod64 p) :
    ctx.mulMod a b = a * b := by
  exact
    (ZMod64.eq_iff_toNat_eq (ctx.mulMod a b) (a * b)).mpr (by
      rw [toNat_mulMod]
      exact (ZMod64.toNat_mul a b).symm)

/--
Barrett hot-loop multiplication by one on the left returns the original
standard residue.
-/
@[simp, grind =] theorem mulMod_one_left (ctx : BarrettCtx p) (a : ZMod64 p) :
    ctx.mulMod 1 a = a := by
  rw [mulMod_eq_mul]
  apply (ZMod64.eq_iff_toNat_eq (1 * a) a).mpr
  change (ZMod64.mul 1 a).toNat = a.toNat
  rw [ZMod64.toNat_mul]
  change ((ZMod64.one : ZMod64 p).toNat * a.toNat) % p = a.toNat
  rw [ZMod64.toNat_one]
  simpa [ZMod64.toNat_eq_val] using Nat.mod_eq_of_lt a.toNat_lt

/--
Barrett hot-loop multiplication by zero on the left returns zero.
-/
@[simp, grind =] theorem mulMod_zero_left (ctx : BarrettCtx p) (a : ZMod64 p) :
    ctx.mulMod 0 a = 0 := by
  rw [mulMod_eq_mul]
  apply (ZMod64.eq_iff_toNat_eq (0 * a) 0).mpr
  change (ZMod64.mul 0 a).toNat = (ZMod64.zero : ZMod64 p).toNat
  rw [ZMod64.toNat_mul, ZMod64.toNat_zero]
  change ((0 : ZMod64 p).toNat * a.toNat) % p = 0
  have hzero : (0 : ZMod64 p).toNat = 0 := ZMod64.toNat_zero (p := p)
  rw [hzero, Nat.zero_mul, Nat.zero_mod]

/--
Barrett hot-loop multiplication by one on the right returns the original
standard residue.
-/
@[simp, grind =] theorem mulMod_one_right (ctx : BarrettCtx p) (a : ZMod64 p) :
    ctx.mulMod a 1 = a := by
  rw [mulMod_eq_mul]
  apply (ZMod64.eq_iff_toNat_eq (a * 1) a).mpr
  change (ZMod64.mul a 1).toNat = a.toNat
  rw [ZMod64.toNat_mul]
  change (a.toNat * (ZMod64.one : ZMod64 p).toNat) % p = a.toNat
  rw [ZMod64.toNat_one]
  simpa [ZMod64.toNat_eq_val] using Nat.mod_eq_of_lt a.toNat_lt

/--
Barrett hot-loop multiplication by zero on the right returns zero.
-/
@[simp, grind =] theorem mulMod_zero_right (ctx : BarrettCtx p) (a : ZMod64 p) :
    ctx.mulMod a 0 = 0 := by
  rw [mulMod_eq_mul]
  apply (ZMod64.eq_iff_toNat_eq (a * 0) 0).mpr
  change (ZMod64.mul a 0).toNat = (ZMod64.zero : ZMod64 p).toNat
  rw [ZMod64.toNat_mul, ZMod64.toNat_zero]
  change (a.toNat * (0 : ZMod64 p).toNat) % p = 0
  have hzero : (0 : ZMod64 p).toNat = 0 := ZMod64.toNat_zero (p := p)
  rw [hzero, Nat.mul_zero, Nat.zero_mod]

/-- Barrett hot-loop multiplication is commutative on standard residues. -/
theorem mulMod_comm (ctx : BarrettCtx p) (a b : ZMod64 p) :
    ctx.mulMod a b = ctx.mulMod b a := by
  rw [mulMod_eq_mul, mulMod_eq_mul]
  apply (ZMod64.eq_iff_toNat_eq (a * b) (b * a)).mpr
  change (ZMod64.mul a b).toNat = (ZMod64.mul b a).toNat
  rw [ZMod64.toNat_mul, ZMod64.toNat_mul]
  exact Nat.mul_comm a.toNat b.toNat ▸ rfl

/-- Barrett hot-loop multiplication is associative on standard residues. -/
theorem mulMod_assoc (ctx : BarrettCtx p) (a b c : ZMod64 p) :
    ctx.mulMod (ctx.mulMod a b) c = ctx.mulMod a (ctx.mulMod b c) := by
  rw [mulMod_eq_mul, mulMod_eq_mul, mulMod_eq_mul, mulMod_eq_mul]
  exact Lean.Grind.Semiring.mul_assoc a b c

end BarrettCtx

namespace MontCtx

variable {p : Nat} [ZMod64.Bounds p]

/--
Build a Montgomery hot-loop context from the indexed modulus and the
word-level odd-modulus side condition required by the underlying `HexArith`
context.
-/
@[expose]
def ofOddModulus (hp : p < UInt64.word)
    (hodd : ZMod64.modulusWord p hp % 2 = 1) : MontCtx p :=
  { modulus := ZMod64.modulusWord p hp
    modulus_eq := by simp [ZMod64.modulusWord]
    toUInt64Ctx := _root_.MontCtx.mk (ZMod64.modulusWord p hp) hodd }

/-- The smart constructor stores the canonical machine-word modulus. -/
@[simp, grind =] theorem modulus_ofOddModulus (hp : p < UInt64.word)
    (hodd : ZMod64.modulusWord p hp % 2 = 1) :
    (ofOddModulus (p := p) hp hodd).modulus = ZMod64.modulusWord p hp := rfl

/-- The smart constructor's stored word modulus agrees with the indexed modulus. -/
@[simp, grind =] theorem modulus_toNat_ofOddModulus (hp : p < UInt64.word)
    (hodd : ZMod64.modulusWord p hp % 2 = 1) :
    (ofOddModulus (p := p) hp hodd).modulus.toNat = p :=
  (ofOddModulus (p := p) hp hodd).modulus_eq

/-- The smart constructor delegates to the underlying `UInt64` Montgomery context. -/
@[simp, grind =] theorem toUInt64Ctx_ofOddModulus (hp : p < UInt64.word)
    (hodd : ZMod64.modulusWord p hp % 2 = 1) :
    (ofOddModulus (p := p) hp hodd).toUInt64Ctx =
      _root_.MontCtx.mk (ZMod64.modulusWord p hp) hodd := rfl

private theorem zmod64_lt_modulus (ctx : MontCtx p) (a : ZMod64 p) :
    a.toUInt64 < ctx.modulus :=
  UInt64.lt_iff_toNat_lt.mpr <| by
    simpa [ctx.modulus_eq] using a.toNat_lt

private theorem montResidue_lt_modulus (ctx : MontCtx p) (a : MontResidue p) :
    a.toUInt64 < ctx.modulus :=
  UInt64.lt_iff_toNat_lt.mpr <| by
    simpa [ctx.modulus_eq] using a.toNat_lt

/-- Convert a standard residue into Montgomery form. -/
@[expose]
def toMont (ctx : MontCtx p) (a : ZMod64 p) : MontResidue p :=
  let w := _root_.MontCtx.toMont ctx.toUInt64Ctx a.toUInt64
  have hw : w.toNat < p := by
    have ha := zmod64_lt_modulus ctx a
    have hlt : w < ctx.modulus := _root_.MontCtx.toMont_lt ctx.toUInt64Ctx a.toUInt64 ha
    exact by
      simpa [ctx.modulus_eq] using UInt64.lt_iff_toNat_lt.mp hlt
  ⟨w, hw⟩

/-- Multiply two Montgomery-form residues, staying inside the Montgomery domain. -/
@[expose]
def mulMont (ctx : MontCtx p) (a b : MontResidue p) : MontResidue p :=
  let w := _root_.MontCtx.mulMont ctx.toUInt64Ctx a.toUInt64 b.toUInt64
  have hw : w.toNat < p := by
    have ha := montResidue_lt_modulus ctx a
    have hb := montResidue_lt_modulus ctx b
    have hlt : w < ctx.modulus := _root_.MontCtx.mulMont_lt ctx.toUInt64Ctx a.toUInt64 b.toUInt64 ha hb
    exact by
      simpa [ctx.modulus_eq] using UInt64.lt_iff_toNat_lt.mp hlt
  ⟨w, hw⟩

/--
Convert a Montgomery-form loop temporary back to the standard `ZMod64`
representation.
-/
@[expose]
def fromMont (ctx : MontCtx p) (a : MontResidue p) : ZMod64 p :=
  ZMod64.ofNat p ((_root_.MontCtx.fromMont ctx.toUInt64Ctx a.toUInt64).toNat)

/-- `toMont` delegates to the underlying `UInt64` Montgomery conversion. -/
theorem toUInt64_toMont (ctx : MontCtx p) (a : ZMod64 p) :
    (ctx.toMont a).toUInt64 = _root_.MontCtx.toMont ctx.toUInt64Ctx a.toUInt64 := by
  simp [toMont, MontResidue.toUInt64_eq_val]

/-- `mulMont` delegates to the underlying `UInt64` Montgomery multiplication. -/
theorem toUInt64_mulMont (ctx : MontCtx p) (a b : MontResidue p) :
    (ctx.mulMont a b).toUInt64 =
      _root_.MontCtx.mulMont ctx.toUInt64Ctx a.toUInt64 b.toUInt64 := by
  simp [mulMont, MontResidue.toUInt64_eq_val]

/-- `fromMont` exposes the reduced Nat value computed by the underlying context. -/
theorem toNat_fromMont (ctx : MontCtx p) (a : MontResidue p) :
    (ctx.fromMont a).toNat =
      (_root_.MontCtx.fromMont ctx.toUInt64Ctx a.toUInt64).toNat := by
  have ha := montResidue_lt_modulus ctx a
  have hlt64 : _root_.MontCtx.fromMont ctx.toUInt64Ctx a.toUInt64 < ctx.modulus :=
    _root_.MontCtx.fromMont_lt ctx.toUInt64Ctx a.toUInt64 ha
  have hlt :
      (_root_.MontCtx.fromMont ctx.toUInt64Ctx a.toUInt64).toNat < p := by
    simpa [ctx.modulus_eq] using UInt64.lt_iff_toNat_lt.mp hlt64
  rw [fromMont, ZMod64.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- The Nat value of `toMont` is multiplication by the Montgomery radix. -/
@[simp, grind =] theorem toNat_toMont (ctx : MontCtx p) (a : ZMod64 p) :
    (ctx.toMont a).toNat = (a.toNat * UInt64.word) % p := by
  have ha := zmod64_lt_modulus ctx a
  simpa [ctx.modulus_eq, toMont, ZMod64.toUInt64_eq_val, ZMod64.toNat_eq_val,
      MontResidue.toNat_eq_val, MontResidue.toUInt64_eq_val] using
    (_root_.MontCtx.toNat_toMont ctx.toUInt64Ctx a.toUInt64 ha)

/--
`fromMont` removes one Montgomery radix factor from a Montgomery-form loop
temporary.
-/
theorem fromMont_repr (ctx : MontCtx p) (a : MontResidue p) :
    (ctx.fromMont a).toNat * UInt64.word % p = a.toNat := by
  have ha := montResidue_lt_modulus ctx a
  rw [toNat_fromMont]
  simpa [ctx.modulus_eq, MontResidue.toUInt64_eq_val, MontResidue.toNat_eq_val] using
    (_root_.MontCtx.fromMont_repr ctx.toUInt64Ctx a.toUInt64 ha)

/-- Converting a standard residue into Montgomery form and back is the identity. -/
@[simp, grind =] theorem fromMont_toMont (ctx : MontCtx p) (a : ZMod64 p) :
    ctx.fromMont (ctx.toMont a) = a := by
  have hnat : (ctx.fromMont (ctx.toMont a)).toNat = a.toNat := by
    have ha := zmod64_lt_modulus ctx a
    have hword := congrArg UInt64.toNat (_root_.MontCtx.fromMont_toMont ctx.toUInt64Ctx a.toUInt64 ha)
    calc
      (ctx.fromMont (ctx.toMont a)).toNat
          = ((_root_.MontCtx.fromMont ctx.toUInt64Ctx (ctx.toMont a).toUInt64).toNat) % p := by
              simp [fromMont]
      _ = ((_root_.MontCtx.fromMont ctx.toUInt64Ctx
            (_root_.MontCtx.toMont ctx.toUInt64Ctx a.toUInt64)).toNat) % p := by
              simp [toMont, MontResidue.toUInt64_eq_val]
      _ = a.toNat % p := by
            simpa [ctx.modulus_eq, ZMod64.toUInt64_eq_val, ZMod64.toNat_eq_val] using
              congrArg (fun n => n % p) hword
      _ = a.toNat := Nat.mod_eq_of_lt a.toNat_lt
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  simpa [ZMod64.toNat_eq_val] using hnat

/--
Multiplying two standard residues by entering Montgomery form, multiplying, and
leaving Montgomery form computes the ordinary modular product.
-/
@[simp, grind =] theorem toNat_mulMont (ctx : MontCtx p) (a b : ZMod64 p) :
    (ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b))).toNat =
      (a.toNat * b.toNat) % p := by
  have ha := zmod64_lt_modulus ctx a
  have hb := zmod64_lt_modulus ctx b
  have hEq := _root_.MontCtx.toNat_mulMont ctx.toUInt64Ctx a.toUInt64 b.toUInt64 ha hb
  calc
    (ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b))).toNat
        = ((_root_.MontCtx.fromMont ctx.toUInt64Ctx
            (ctx.mulMont (ctx.toMont a) (ctx.toMont b)).toUInt64).toNat) % p := by
              simp [fromMont]
    _ = ((_root_.MontCtx.fromMont ctx.toUInt64Ctx
          (_root_.MontCtx.mulMont ctx.toUInt64Ctx
            (_root_.MontCtx.toMont ctx.toUInt64Ctx a.toUInt64)
            (_root_.MontCtx.toMont ctx.toUInt64Ctx b.toUInt64))).toNat) % p := by
              simp [mulMont, toMont, MontResidue.toUInt64_eq_val]
    _ = ((a.toNat * b.toNat) % p) % p := by
          simpa [ctx.modulus_eq, ZMod64.toUInt64_eq_val, ZMod64.toNat_eq_val] using congrArg (fun n => n % p) hEq
    _ = (a.toNat * b.toNat) % p := by rw [Nat.mod_mod]

/--
Montgomery multiplication preserves the represented standard-residue product
when converted back out of Montgomery form.
-/
@[simp, grind =] theorem mulMont_repr (ctx : MontCtx p) (a b : MontResidue p) :
    (ctx.fromMont (ctx.mulMont a b)).toNat =
      ((ctx.fromMont a).toNat * (ctx.fromMont b).toNat) % p := by
  have ha := montResidue_lt_modulus ctx a
  have hb := montResidue_lt_modulus ctx b
  have hmul :=
    _root_.MontCtx.mulMont_repr ctx.toUInt64Ctx a.toUInt64 b.toUInt64 ha hb
  have hmulWord :
      (ctx.mulMont a b).toUInt64 =
        _root_.MontCtx.mulMont ctx.toUInt64Ctx a.toUInt64 b.toUInt64 := by
    rw [toUInt64_mulMont]
  rw [toNat_fromMont, toNat_fromMont, toNat_fromMont]
  simpa [ctx.modulus_eq, hmulWord, MontResidue.toUInt64_eq_val] using hmul

/--
Multiplying two standard residues by entering Montgomery form, multiplying, and
leaving Montgomery form agrees with ordinary `ZMod64` multiplication.
-/
@[simp, grind =] theorem fromMont_mulMont_toMont (ctx : MontCtx p) (a b : ZMod64 p) :
    ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b)) = a * b := by
  exact
    (ZMod64.eq_iff_toNat_eq
      (ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b))) (a * b)).mpr (by
        rw [toNat_mulMont]
        exact (ZMod64.toNat_mul a b).symm)

/--
The Montgomery round trip for a wrapped product returns the original residue
when the left standard input is one.
-/
@[simp, grind =] theorem fromMont_mulMont_toMont_one_left (ctx : MontCtx p) (a : ZMod64 p) :
    ctx.fromMont (ctx.mulMont (ctx.toMont 1) (ctx.toMont a)) = a := by
  rw [fromMont_mulMont_toMont]
  apply (ZMod64.eq_iff_toNat_eq (1 * a) a).mpr
  change (ZMod64.mul 1 a).toNat = a.toNat
  rw [ZMod64.toNat_mul]
  change ((ZMod64.one : ZMod64 p).toNat * a.toNat) % p = a.toNat
  rw [ZMod64.toNat_one]
  simpa [ZMod64.toNat_eq_val] using Nat.mod_eq_of_lt a.toNat_lt

/--
The Montgomery round trip for a wrapped product returns zero when the left
standard input is zero.
-/
@[simp, grind =] theorem fromMont_mulMont_toMont_zero_left (ctx : MontCtx p) (a : ZMod64 p) :
    ctx.fromMont (ctx.mulMont (ctx.toMont 0) (ctx.toMont a)) = 0 := by
  rw [fromMont_mulMont_toMont]
  apply (ZMod64.eq_iff_toNat_eq (0 * a) 0).mpr
  change (ZMod64.mul 0 a).toNat = (ZMod64.zero : ZMod64 p).toNat
  rw [ZMod64.toNat_mul, ZMod64.toNat_zero]
  change ((0 : ZMod64 p).toNat * a.toNat) % p = 0
  have hzero : (0 : ZMod64 p).toNat = 0 := ZMod64.toNat_zero (p := p)
  rw [hzero, Nat.zero_mul, Nat.zero_mod]

/--
The Montgomery round trip for a wrapped product returns the original residue
when the right standard input is one.
-/
@[simp, grind =] theorem fromMont_mulMont_toMont_one_right (ctx : MontCtx p) (a : ZMod64 p) :
    ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont 1)) = a := by
  rw [fromMont_mulMont_toMont]
  apply (ZMod64.eq_iff_toNat_eq (a * 1) a).mpr
  change (ZMod64.mul a 1).toNat = a.toNat
  rw [ZMod64.toNat_mul]
  change (a.toNat * (ZMod64.one : ZMod64 p).toNat) % p = a.toNat
  rw [ZMod64.toNat_one]
  simpa [ZMod64.toNat_eq_val] using Nat.mod_eq_of_lt a.toNat_lt

/--
The Montgomery round trip for a wrapped product returns zero when the right
standard input is zero.
-/
@[simp, grind =] theorem fromMont_mulMont_toMont_zero_right (ctx : MontCtx p) (a : ZMod64 p) :
    ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont 0)) = 0 := by
  rw [fromMont_mulMont_toMont]
  apply (ZMod64.eq_iff_toNat_eq (a * 0) 0).mpr
  change (ZMod64.mul a 0).toNat = (ZMod64.zero : ZMod64 p).toNat
  rw [ZMod64.toNat_mul, ZMod64.toNat_zero]
  change (a.toNat * (0 : ZMod64 p).toNat) % p = 0
  have hzero : (0 : ZMod64 p).toNat = 0 := ZMod64.toNat_zero (p := p)
  rw [hzero, Nat.mul_zero, Nat.zero_mod]

/--
The Montgomery round trip for a wrapped product is commutative on standard
residue inputs.
-/
theorem fromMont_mulMont_toMont_comm (ctx : MontCtx p) (a b : ZMod64 p) :
    ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b)) =
      ctx.fromMont (ctx.mulMont (ctx.toMont b) (ctx.toMont a)) := by
  rw [fromMont_mulMont_toMont, fromMont_mulMont_toMont]
  apply (ZMod64.eq_iff_toNat_eq (a * b) (b * a)).mpr
  change (ZMod64.mul a b).toNat = (ZMod64.mul b a).toNat
  rw [ZMod64.toNat_mul, ZMod64.toNat_mul]
  exact Nat.mul_comm a.toNat b.toNat ▸ rfl

/--
The Montgomery round trip for wrapped products is associative on standard
residue inputs.
-/
theorem fromMont_mulMont_toMont_assoc (ctx : MontCtx p) (a b c : ZMod64 p) :
    ctx.fromMont (ctx.mulMont (ctx.toMont
        (ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b))))
      (ctx.toMont c)) =
    ctx.fromMont (ctx.mulMont (ctx.toMont a)
      (ctx.toMont
        (ctx.fromMont (ctx.mulMont (ctx.toMont b) (ctx.toMont c))))) := by
  rw [fromMont_mulMont_toMont, fromMont_mulMont_toMont,
    fromMont_mulMont_toMont, fromMont_mulMont_toMont]
  exact Lean.Grind.Semiring.mul_assoc a b c

end MontCtx

end Hex
