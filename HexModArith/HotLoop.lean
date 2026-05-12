import HexArith.Barrett.Context
import HexArith.Montgomery.Context
import HexModArith.Basic

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
def toUInt64 (a : MontResidue p) : UInt64 :=
  a.val

/-- View a Montgomery-form residue as its reduced Nat representative. -/
def toNat (a : MontResidue p) : Nat :=
  a.val.toNat

instance : CoeOut (MontResidue p) UInt64 where
  coe := toUInt64

instance : CoeOut (MontResidue p) Nat where
  coe := toNat

/-- The `UInt64` view of a Montgomery residue is its backing word. -/
@[simp] theorem toUInt64_eq_val (a : MontResidue p) : a.toUInt64 = a.val := rfl

/-- The Nat view of a Montgomery residue is the Nat value of its backing word. -/
@[simp] theorem toNat_eq_val (a : MontResidue p) : a.toNat = a.val.toNat := rfl

/-- The Nat view of a Montgomery residue is reduced modulo its indexed modulus. -/
@[simp] theorem toNat_lt (a : MontResidue p) : a.toNat < p := a.isLt

/-- Montgomery residues are equal when their backing words are equal. -/
@[ext] theorem ext {a b : MontResidue p} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  cases h
  rfl

end MontResidue

namespace BarrettCtx

variable {p : Nat} [ZMod64.Bounds p]

private theorem residue_lt_modulus (ctx : BarrettCtx p) (a : ZMod64 p) :
    a.toUInt64 < ctx.modulus :=
  UInt64.lt_iff_toNat_lt.mpr <| by
    simpa [ctx.modulus_eq] using a.toNat_lt

/--
Multiply two standard residues using the Barrett context and repackage the
result as a `ZMod64`.
-/
def mulMod (ctx : BarrettCtx p) (a b : ZMod64 p) : ZMod64 p :=
  ZMod64.ofNat p ((_root_.BarrettCtx.mulMod ctx.toUInt64Ctx a.toUInt64 b.toUInt64).toNat)

/--
The `ZMod64` Barrett wrapper computes the ordinary modular product on reduced
representatives.
-/
@[simp] theorem toNat_mulMod (ctx : BarrettCtx p) (a b : ZMod64 p) :
    (ctx.mulMod a b).toNat = (a.toNat * b.toNat) % p := by
  have ha := residue_lt_modulus ctx a
  have hb := residue_lt_modulus ctx b
  have hlt : (_root_.BarrettCtx.mulMod ctx.toUInt64Ctx a.toUInt64 b.toUInt64).toNat < p := by
    have hlt64 :
        _root_.BarrettCtx.mulMod ctx.toUInt64Ctx a.toUInt64 b.toUInt64 < ctx.modulus :=
      _root_.BarrettCtx.mulMod_lt ctx.toUInt64Ctx a.toUInt64 b.toUInt64 ha hb
    simpa [ctx.modulus_eq] using UInt64.lt_iff_toNat_lt.mp hlt64
  rw [mulMod, ZMod64.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hlt]
  simpa [ctx.modulus_eq] using
    (_root_.BarrettCtx.toNat_mulMod ctx.toUInt64Ctx a.toUInt64 b.toUInt64 ha hb)

/--
Barrett hot-loop multiplication agrees with the ordinary `ZMod64`
multiplication surface.
-/
@[simp] theorem mulMod_eq_mul (ctx : BarrettCtx p) (a b : ZMod64 p) :
    ctx.mulMod a b = a * b := by
  exact
    (ZMod64.eq_iff_toNat_eq (ctx.mulMod a b) (a * b)).mpr (by
      rw [toNat_mulMod]
      exact (ZMod64.toNat_mul a b).symm)

end BarrettCtx

namespace MontCtx

variable {p : Nat} [ZMod64.Bounds p]

private theorem zmod64_lt_modulus (ctx : MontCtx p) (a : ZMod64 p) :
    a.toUInt64 < ctx.modulus :=
  UInt64.lt_iff_toNat_lt.mpr <| by
    simpa [ctx.modulus_eq] using a.toNat_lt

private theorem montResidue_lt_modulus (ctx : MontCtx p) (a : MontResidue p) :
    a.toUInt64 < ctx.modulus :=
  UInt64.lt_iff_toNat_lt.mpr <| by
    simpa [ctx.modulus_eq] using a.toNat_lt

/-- Convert a standard residue into Montgomery form. -/
def toMont (ctx : MontCtx p) (a : ZMod64 p) : MontResidue p :=
  let w := _root_.MontCtx.toMont ctx.toUInt64Ctx a.toUInt64
  have hw : w.toNat < p := by
    have ha := zmod64_lt_modulus ctx a
    have hlt : w < ctx.modulus := _root_.MontCtx.toMont_lt ctx.toUInt64Ctx a.toUInt64 ha
    exact by
      simpa [ctx.modulus_eq] using UInt64.lt_iff_toNat_lt.mp hlt
  ⟨w, hw⟩

/-- Multiply two Montgomery-form residues, staying inside the Montgomery domain. -/
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
def fromMont (ctx : MontCtx p) (a : MontResidue p) : ZMod64 p :=
  ZMod64.ofNat p ((_root_.MontCtx.fromMont ctx.toUInt64Ctx a.toUInt64).toNat)

/-- The Nat value of `toMont` is multiplication by the Montgomery radix. -/
@[simp] theorem toNat_toMont (ctx : MontCtx p) (a : ZMod64 p) :
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
  have hlt64 : _root_.MontCtx.fromMont ctx.toUInt64Ctx a.toUInt64 < ctx.modulus :=
    _root_.MontCtx.fromMont_lt ctx.toUInt64Ctx a.toUInt64 ha
  have hlt :
      (_root_.MontCtx.fromMont ctx.toUInt64Ctx a.toUInt64).toNat < p := by
    simpa [ctx.modulus_eq] using UInt64.lt_iff_toNat_lt.mp hlt64
  have hfrom :
      (ctx.fromMont a).toNat =
        (_root_.MontCtx.fromMont ctx.toUInt64Ctx a.toUInt64).toNat := by
    rw [fromMont, ZMod64.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [hfrom]
  simpa [ctx.modulus_eq, MontResidue.toUInt64_eq_val, MontResidue.toNat_eq_val] using
    (_root_.MontCtx.fromMont_repr ctx.toUInt64Ctx a.toUInt64 ha)

/-- Converting a standard residue into Montgomery form and back is the identity. -/
@[simp] theorem fromMont_toMont (ctx : MontCtx p) (a : ZMod64 p) :
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
@[simp] theorem toNat_mulMont (ctx : MontCtx p) (a b : ZMod64 p) :
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
@[simp] theorem mulMont_repr (ctx : MontCtx p) (a b : MontResidue p) :
    (ctx.fromMont (ctx.mulMont a b)).toNat =
      ((ctx.fromMont a).toNat * (ctx.fromMont b).toNat) % p := by
  have ha := montResidue_lt_modulus ctx a
  have hb := montResidue_lt_modulus ctx b
  have hmul :=
    _root_.MontCtx.mulMont_repr ctx.toUInt64Ctx a.toUInt64 b.toUInt64 ha hb
  have hfrom (x : MontResidue p) :
      (ctx.fromMont x).toNat =
        (_root_.MontCtx.fromMont ctx.toUInt64Ctx x.toUInt64).toNat := by
    have hx := montResidue_lt_modulus ctx x
    have hlt64 : _root_.MontCtx.fromMont ctx.toUInt64Ctx x.toUInt64 < ctx.modulus :=
      _root_.MontCtx.fromMont_lt ctx.toUInt64Ctx x.toUInt64 hx
    have hlt :
        (_root_.MontCtx.fromMont ctx.toUInt64Ctx x.toUInt64).toNat < p := by
      simpa [ctx.modulus_eq] using UInt64.lt_iff_toNat_lt.mp hlt64
    rw [fromMont, ZMod64.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hmulWord :
      (ctx.mulMont a b).toUInt64 =
        _root_.MontCtx.mulMont ctx.toUInt64Ctx a.toUInt64 b.toUInt64 := by
    simp [mulMont, MontResidue.toUInt64_eq_val]
  rw [hfrom (ctx.mulMont a b), hfrom a, hfrom b]
  simpa [ctx.modulus_eq, hmulWord, MontResidue.toUInt64_eq_val] using hmul

/--
Multiplying two standard residues by entering Montgomery form, multiplying, and
leaving Montgomery form agrees with ordinary `ZMod64` multiplication.
-/
@[simp] theorem fromMont_mulMont_toMont (ctx : MontCtx p) (a b : ZMod64 p) :
    ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b)) = a * b := by
  exact
    (ZMod64.eq_iff_toNat_eq
      (ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b))) (a * b)).mpr (by
        rw [toNat_mulMont]
        exact (ZMod64.toNat_mul a b).symm)

end MontCtx

end Hex
