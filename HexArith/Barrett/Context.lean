import HexArith.Barrett.Reduce

/-!
User-facing Barrett modular multiplication for `HexArith`.

This module exposes `BarrettCtx.mulMod` together with the public theorems that
connect the executable `UInt64` code to ordinary modular arithmetic on `Nat`.
-/

namespace BarrettCtx

/--
Multiply two residues modulo `p` using the Barrett reduction context. The
caller-side condition `a, b < p < 2^32` ensures the product fits in one
`UInt64`.
-/
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
the Barrett reducer bridge.
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
The product of two residues below a Barrett modulus fits below the Barrett
radix `2^64`.
-/
private theorem product_toNat_lt_radix (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (a * b).toNat < barrettRadix := by
  have hprod_lt_p2 := product_toNat_lt_p2 ctx a b ha hb
  have hp2_lt_word : p.toNat * p.toNat < UInt64.word := by
    calc
      p.toNat * p.toNat < 2 ^ 32 * 2 ^ 32 :=
        Nat.mul_lt_mul'' ctx.p_lt ctx.p_lt
      _ = UInt64.word := by
        rw [UInt64.word, ← Nat.pow_add]
  simpa [barrettRadix] using Nat.lt_trans hprod_lt_p2 hp2_lt_word

/--
The `Nat` value of Barrett modular multiplication is the ordinary modular
product.
-/
@[simp]
theorem toNat_mulMod (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.mulMod a b).toNat = (a.toNat * b.toNat) % p.toNat := by
  unfold mulMod
  rw [toNat_barrettReduce ctx (a * b) (product_toNat_lt_p2 ctx a b ha hb)]
  rw [barrettReduceNat_eq_mod ctx.p_gt (toNat_pinv ctx) (product_toNat_lt_radix ctx a b ha hb)]
  rw [product_toNat_eq ctx a b ha hb]

/-- Barrett modular multiplication returns a residue strictly below the modulus. -/
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
theorem mulMod_eq (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.mulMod a b = .ofNat ((a.toNat * b.toNat) % p.toNat) := by
  apply UInt64.toNat_inj.mp
  rw [toNat_mulMod ctx a b ha hb]
  have hmod_lt : (a.toNat * b.toNat) % p.toNat < p.toNat :=
    Nat.mod_lt _ (Nat.lt_trans (by decide : 0 < 1) ctx.p_gt)
  have hmod_word : (a.toNat * b.toNat) % p.toNat < UInt64.word := by
    exact Nat.lt_trans hmod_lt (Nat.lt_trans ctx.p_lt (by decide))
  change (a.toNat * b.toNat) % p.toNat =
    ((a.toNat * b.toNat) % p.toNat) % UInt64.size
  simpa [UInt64.size, UInt64.word] using (Nat.mod_eq_of_lt hmod_word).symm

end BarrettCtx
