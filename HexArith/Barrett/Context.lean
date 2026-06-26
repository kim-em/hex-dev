module

public import HexArith.Barrett.Reduce

public section

/-!
User-facing Barrett modular multiplication for `HexArith`.

This module exposes `BarrettCtx.mulMod` together with the public theorems that
connect the executable `UInt64` code to ordinary modular arithmetic on `Nat`.
-/

namespace BarrettCtx

/-- The small-modulus lower-bound proof stored by `BarrettCtx.mk`. -/
@[simp, grind =]
theorem mk_p_gt (p : UInt64) (hp : p.toNat > 1) (hlt : p.toNat < 2 ^ 32) :
    (mk p hp hlt).p_gt = hp := rfl

/-- The small-modulus upper-bound proof stored by `BarrettCtx.mk`. -/
@[simp, grind =]
theorem mk_p_lt (p : UInt64) (hp : p.toNat > 1) (hlt : p.toNat < 2 ^ 32) :
    (mk p hp hlt).p_lt = hlt := rfl

/-- The reciprocal word stored by `BarrettCtx.mk`. -/
@[simp, grind =]
theorem mk_pinv (p : UInt64) (hp : p.toNat > 1) (hlt : p.toNat < 2 ^ 32) :
    (mk p hp hlt).pinv = UInt64.ofNat (barrettRadix / p.toNat) := rfl

/-- The Nat value of the reciprocal word stored by `BarrettCtx.mk`. -/
@[simp, grind =]
theorem mk_pinv_toNat (p : UInt64) (hp : p.toNat > 1) (hlt : p.toNat < 2 ^ 32) :
    (mk p hp hlt).pinv.toNat = barrettRadix / p.toNat := by
  simpa using (toNat_pinv (mk p hp hlt))

/--
Multiply two residues modulo `p` using the Barrett reduction context. The
caller-side condition `a, b < p < 2^32` ensures the product fits in one
`UInt64`.
-/
@[expose]
def mulMod (ctx : BarrettCtx p) (a b : UInt64) : UInt64 :=
  barrettReduce ctx (a * b)

/--
For residues below a Barrett modulus, the machine-word product has no
`UInt64` wraparound.
-/
private theorem product_toNat_eq (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (a * b).toNat = a.toNat * b.toNat := by
  have haNat : a.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using ha
  have hbNat : b.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using hb
  have hprod_lt_p2 : a.toNat * b.toNat < p.toNat * p.toNat :=
    Nat.mul_lt_mul'' haNat hbNat
  have hp2_lt_word : p.toNat * p.toNat < UInt64.word := by
    calc
      p.toNat * p.toNat < 2 ^ 32 * 2 ^ 32 :=
        Nat.mul_lt_mul'' ctx.p_lt ctx.p_lt
      _ = UInt64.word := by
        rw [UInt64.word, ← Nat.pow_add]
  have hprod_lt_word : a.toNat * b.toNat < UInt64.word :=
    Nat.lt_trans hprod_lt_p2 hp2_lt_word
  simpa [UInt64.toNat_mul, UInt64.size, UInt64.word] using
    Nat.mod_eq_of_lt hprod_lt_word

/--
The product of two residues is below `p^2`, which is the bound required by
the Barrett reducer.
-/
private theorem product_toNat_lt_p2 (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (a * b).toNat < p.toNat * p.toNat := by
  have haNat : a.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using ha
  have hbNat : b.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using hb
  rw [product_toNat_eq ctx a b ha hb]
  exact Nat.mul_lt_mul'' haNat hbNat

/--
The `Nat` value of Barrett modular multiplication is the ordinary modular
product.
-/
@[simp, grind =]
theorem toNat_mulMod (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.mulMod a b).toNat = (a.toNat * b.toNat) % p.toNat := by
  unfold mulMod
  rw [toNat_barrettReduce_eq_mod ctx (a * b) (product_toNat_lt_p2 ctx a b ha hb)]
  rw [product_toNat_eq ctx a b ha hb]

/-- Barrett modular multiplication returns a residue strictly below the modulus. -/
@[grind =>]
theorem mulMod_lt (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.mulMod a b < p := by
  rw [UInt64.lt_iff_toNat_lt]
  rw [toNat_mulMod ctx a b ha hb]
  exact Nat.mod_lt _ (Nat.lt_trans (by decide : 0 < 1) ctx.p_gt)

/--
Barrett modular multiplication agrees with reducing the Nat-level product and
re-encoding it as a `UInt64`.
-/
@[grind =]
theorem mulMod_eq (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.mulMod a b = .ofNat ((a.toNat * b.toNat) % p.toNat) := by
  unfold mulMod
  rw [barrettReduce_eq ctx (a * b) (product_toNat_lt_p2 ctx a b ha hb)]
  rw [product_toNat_eq ctx a b ha hb]

/--
Barrett modular multiplication fixes products that are already canonical
residues.
-/
@[simp, grind =]
theorem mulMod_eq_mul_of_mul_lt (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) (hmul : a.toNat * b.toNat < p.toNat) :
    ctx.mulMod a b = a * b := by
  have hprod_lt : a * b < p := by
    rw [UInt64.lt_iff_toNat_lt, product_toNat_eq ctx a b ha hb]
    exact hmul
  simpa [mulMod] using barrettReduce_eq_self_of_lt ctx (a * b) hprod_lt

/-- Zero is a left absorbing element for Barrett modular multiplication. -/
@[simp, grind =]
theorem mulMod_zero_left (ctx : BarrettCtx p) (b : UInt64) (hb : b < p) :
    ctx.mulMod 0 b = 0 := by
  have hzero : (0 : UInt64) < p := by
    rw [UInt64.lt_iff_toNat_lt]
    exact Nat.lt_trans (by decide : 0 < 1) ctx.p_gt
  simpa using mulMod_eq ctx 0 b hzero hb

/-- Zero is a right absorbing element for Barrett modular multiplication. -/
@[simp, grind =]
theorem mulMod_zero_right (ctx : BarrettCtx p) (a : UInt64) (ha : a < p) :
    ctx.mulMod a 0 = 0 := by
  have hzero : (0 : UInt64) < p := by
    rw [UInt64.lt_iff_toNat_lt]
    exact Nat.lt_trans (by decide : 0 < 1) ctx.p_gt
  simpa using mulMod_eq ctx a 0 ha hzero

/-- One is a left identity for Barrett modular multiplication on reduced residues. -/
@[simp, grind =]
theorem mulMod_one_left (ctx : BarrettCtx p) (a : UInt64) (ha : a < p) :
    ctx.mulMod 1 a = a := by
  have hone : (1 : UInt64) < p := by
    rw [UInt64.lt_iff_toNat_lt]
    simpa using ctx.p_gt
  have ha' : a.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using ha
  apply UInt64.toNat_inj.mp
  rw [toNat_mulMod ctx 1 a hone ha]
  simp [Nat.mod_eq_of_lt ha']

/-- One is a right identity for Barrett modular multiplication on reduced residues. -/
@[simp, grind =]
theorem mulMod_one_right (ctx : BarrettCtx p) (a : UInt64) (ha : a < p) :
    ctx.mulMod a 1 = a := by
  have hone : (1 : UInt64) < p := by
    rw [UInt64.lt_iff_toNat_lt]
    simpa using ctx.p_gt
  have ha' : a.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using ha
  apply UInt64.toNat_inj.mp
  rw [toNat_mulMod ctx a 1 ha hone]
  simp [Nat.mod_eq_of_lt ha']

/-- Barrett modular multiplication is commutative on reduced residues. -/
@[grind =]
theorem mulMod_comm (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.mulMod a b = ctx.mulMod b a := by
  apply UInt64.toNat_inj.mp
  rw [toNat_mulMod ctx a b ha hb, toNat_mulMod ctx b a hb ha, Nat.mul_comm]

end BarrettCtx
