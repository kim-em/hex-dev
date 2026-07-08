/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Strassen
public import HexModArith.HotLoop
public import HexArith.Barrett.Accumulator

public section

/-!
Delayed-reduction Barrett base kernel as a demonstration `StrassenConfig`.

The default `StrassenConfig` base kernel (`strassenDefault`) reduces modulo `p`
after every multiply-add. This module supplies the SPEC's demonstration
non-default config for the Barrett-reduced prime field `ZMod64 p`: a base kernel
whose dot product accumulates one-word residue products in the two-word
accumulator and reduces modulo `p` only periodically (`delayedDot`, built on the
`HexArith.Barrett.Accumulator` fold `foldReduce`).

It lives here, above both `HexMatrix` and the Barrett layer, because the kernel
needs `Matrix`/`StrassenConfig` *and* `Hex.BarrettCtx` in scope, and the placement
rule forbids `hex-arith`/`hex-mod-arith` from importing `HexMatrix` (that would
invert the released dependency order). `HexBerlekamp` already imports `HexMatrix`
and is the library that consumes the prime-field multiply.

`delayedDot_eq_dotProduct` proves the delayed dot product equals the naive
`Vector.dotProduct` on `ZMod64 p`, from which `strassenBarrett_valid` follows: the
config is `Valid`, so `mulStrassen (strassenBarrett ctx)` still equals the
reference `mul`.

**Measured outcome (honesty constraint (b)).** The delayed kernel is verified
correct but does not beat the default base kernel here: benchmarked against
default-base `mulStrassen` on the prime field it is roughly `7`–`10×` slower
across `64…256`, because the two-word accumulator's per-term Lean-level
bookkeeping (a boxed `(UInt64 × UInt64 × Nat)` accumulator threaded through
`Fin.foldl`, plus a `UInt64.addCarry` extern call per term) costs more than the
modular reductions it defers, relative to the tight single-extern `ZMod64.mul` of
the default. So the shipped demonstration config is the trivial `strassenDemo`
(naive base kernel, non-default cutoff), which still exercises the pluggable-
kernel path; `strassenBarrett` stays as verified follow-up work. The committed
comparison lives in `reports/figures/strassen-base-kernel-comparison.svg`.
-/

namespace Hex

open Hex.Matrix

variable {p : Nat} [ZMod64.Bounds p] {m : Nat}

/-- The one-word residue product `a * b` has no `UInt64` wraparound: both factors
are below `p < 2^31`, so the product is below `2^62 < 2^64`. -/
private theorem toNat_prodWord (a b : ZMod64 p) :
    (a.toUInt64 * b.toUInt64).toNat = a.toNat * b.toNat := by
  have hp : p < 2 ^ 31 := ZMod64.Bounds.pLtR (p := p)
  have ha : a.toNat < 2 ^ 31 := Nat.lt_trans a.toNat_lt hp
  have hb : b.toNat < 2 ^ 31 := Nat.lt_trans b.toNat_lt hp
  have hlt : a.toNat * b.toNat < UInt64.word := by
    have h1 : a.toNat * b.toNat < 2 ^ 31 * 2 ^ 31 := Nat.mul_lt_mul'' ha hb
    have h2 : (2 : Nat) ^ 31 * 2 ^ 31 ≤ UInt64.word := by
      rw [UInt64.word, ← Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide) (by decide)
    omega
  simpa [UInt64.toNat_mul, UInt64.size, UInt64.word, ZMod64.toUInt64_eq_val,
    ZMod64.toNat_eq_val] using Nat.mod_eq_of_lt hlt

/-- Bridge lemma: the `ZMod64` dot-product fold, read through `toNat`, is the
residue modulo `p` of the running accumulator plus the `Nat` sum of the remaining
one-word products (`wordsSum` of the mapped list). Proved by list induction with a
generalized accumulator. -/
private theorem toNat_dotFoldl (u v : Vector (ZMod64 p) m) :
    ∀ (l : List (Fin m)) (acc : ZMod64 p),
      (l.foldl (fun a i => a + u[i] * v[i]) acc).toNat =
        (acc.toNat +
          BarrettCtx.wordsSum (l.map (fun i => u[i].toUInt64 * v[i].toUInt64))) % p := by
  intro l
  induction l with
  | nil =>
    intro acc
    simp only [List.foldl_nil, List.map_nil, BarrettCtx.wordsSum_nil, Nat.add_zero]
    exact (Nat.mod_eq_of_lt acc.toNat_lt).symm
  | cons i rest ih =>
    intro acc
    have hstep : (acc + u[i] * v[i]).toNat = (acc.toNat + u[i].toNat * v[i].toNat) % p := by
      show (ZMod64.add acc (ZMod64.mul u[i] v[i])).toNat = _
      rw [ZMod64.toNat_add, ZMod64.toNat_mul, Nat.add_mod_mod]
    simp only [List.foldl_cons, List.map_cons, BarrettCtx.wordsSum_cons]
    rw [ih (acc + u[i] * v[i]), hstep, toNat_prodWord u[i] v[i], Nat.mod_add_mod,
      Nat.add_assoc]

/-- The naive `ZMod64` dot product, read through `toNat`, is the residue modulo
`p` of the `Nat` sum of the one-word products. -/
private theorem toNat_dotProduct (u v : Vector (ZMod64 p) m) :
    (Vector.dotProduct u v).toNat =
      BarrettCtx.wordsSum
        ((List.finRange m).map (fun i => u[i].toUInt64 * v[i].toUInt64)) % p := by
  have h := toNat_dotFoldl u v (List.finRange m) 0
  have hz : (0 : ZMod64 p).toNat = 0 := ZMod64.toNat_zero
  rw [hz, Nat.zero_add] at h
  exact h

/-- **Delayed-reduction Barrett dot product.** Accumulates each one-word residue
product `u[i] * v[i]` into the two-word accumulator and reduces modulo `p` only
every `barrettWindow` terms (`foldReduce`), then reduces the final partial window.
The window is fixed and independent of the length `m`, so this is correct for
every inner dimension. -/
@[expose]
def delayedDot (ctx : Hex.BarrettCtx p) (u v : Vector (ZMod64 p) m) : ZMod64 p :=
  ZMod64.ofNat p
    (BarrettCtx.foldReduce ctx.toUInt64Ctx
      ((List.finRange m).map (fun i => u[i].toUInt64 * v[i].toUInt64))).toNat

/-- Allocation-free implementation of `delayedDot`: a `Fin.foldl` loop over the
indices that never materializes the `List.finRange m` product-word list. Swapped
in for compiled code by the `@[csimp]` below; `delayedDot` stays the list-based
reference form for proofs, mirroring `Vector.dotProduct`/`dotProductImpl`. -/
@[expose]
def delayedDotImpl (ctx : Hex.BarrettCtx p) (u v : Vector (ZMod64 p) m) : ZMod64 p :=
  let s := Fin.foldl m
    (fun st i => BarrettCtx.accStep ctx.toUInt64Ctx st (u[i].toUInt64 * v[i].toUInt64))
    ((0, 0, 0) : UInt64 × UInt64 × Nat)
  ZMod64.ofNat p (BarrettCtx.accReduce ctx.toUInt64Ctx
    (BarrettCtx.radixResidue ctx.toUInt64Ctx) s.1 s.2.1).toNat

@[csimp] theorem delayedDot_eq_impl : @delayedDot = @delayedDotImpl := by
  funext p inst m ctx u v
  have hfold :
      ((List.finRange m).map (fun i => u[i].toUInt64 * v[i].toUInt64)).foldl
          (BarrettCtx.accStep ctx.toUInt64Ctx) (0, 0, 0)
        = Fin.foldl m (fun st i => BarrettCtx.accStep ctx.toUInt64Ctx st
            (u[i].toUInt64 * v[i].toUInt64)) (0, 0, 0) := by
    rw [List.foldl_map, Fin.foldl_eq_finRange_foldl]
  -- Apply the fold equality under a fixed wrapper via `congrArg`, so the
  -- `accReduce`/`barrett` machinery is never reduced (a `rw` would `kabstract`
  -- into it and time out on the `2^64` radix). Both sides match the wrapper
  -- applied to the two fold forms definitionally.
  exact congrArg
    (fun s : UInt64 × UInt64 × Nat =>
      ZMod64.ofNat p (BarrettCtx.accReduce ctx.toUInt64Ctx
        (BarrettCtx.radixResidue ctx.toUInt64Ctx) s.1 s.2.1).toNat)
    hfold

/-- **Correctness of the delayed dot product.** The periodically-reduced dot
product equals the naive `Vector.dotProduct` on `ZMod64 p`: reduction modulo `p`
is a ring homomorphism, so reducing periodically has the same residue as reducing
at every step. -/
theorem delayedDot_eq_dotProduct (ctx : Hex.BarrettCtx p) (u v : Vector (ZMod64 p) m) :
    delayedDot ctx u v = Vector.dotProduct u v := by
  apply ZMod64.ext_toNat
  rw [delayedDot, ZMod64.toNat_ofNat, BarrettCtx.toNat_foldReduce, ctx.modulus_eq,
    Nat.mod_mod, toNat_dotProduct]

/-- **Delayed-reduction base kernel**, dispatching on the runtime inner dimension:
the delayed dot product is the fast path once the dot-product length is nontrivial
(`2 ≤ m`), and it falls back to the naive `mulImpl` on the trivial residual shapes.
Both branches equal the reference `mul`, so the config built from this is `Valid`. -/
@[expose]
def barrettBaseMul (ctx : Hex.BarrettCtx p) {n m k : Nat}
    (M : Matrix (ZMod64 p) n m) (N : Matrix (ZMod64 p) m k) : Matrix (ZMod64 p) n k :=
  if 2 ≤ m then
    Matrix.ofFn fun i j => delayedDot ctx (Matrix.row M i) (Matrix.col N j)
  else
    Matrix.mulImpl M N

/-- The delayed-reduction base kernel agrees with the reference `mul` on every
input and shape. -/
theorem barrettBaseMul_eq_mul (ctx : Hex.BarrettCtx p) {n m k : Nat}
    (M : Matrix (ZMod64 p) n m) (N : Matrix (ZMod64 p) m k) :
    barrettBaseMul ctx M N = Matrix.mul M N := by
  unfold barrettBaseMul
  split
  · apply Matrix.ext_getElem
    intro i j
    rw [Matrix.getElem_ofFn, delayedDot_eq_dotProduct]
    exact (Matrix.getElem_mul M N i j).symm
  · rw [Matrix.mul_eq_mulImpl]

/-- The **demonstration non-default `StrassenConfig`**: the delayed-reduction
Barrett base kernel over the prime field `ZMod64 p`, taking the `Hex.BarrettCtx`.
Its cutoff is pinned at `64`, the value the committed comparison was measured at
(the default cutoff is measured separately and may move); only the base kernel
differs from the default config. -/
@[expose]
def strassenBarrett (ctx : Hex.BarrettCtx p) : Matrix.StrassenConfig (ZMod64 p) where
  cutoff := 64
  baseMul {_n _m _k} M N := barrettBaseMul ctx M N

/-- The delayed config is `Valid`: its base kernel equals `mul`, so
`mulStrassen (strassenBarrett ctx)` still computes the reference product. -/
theorem strassenBarrett_valid (ctx : Hex.BarrettCtx p) :
    (strassenBarrett ctx).Valid := by
  intro n m k X Y
  exact barrettBaseMul_eq_mul ctx X Y

/-- **The shipped demonstration non-default config.** A trivial alternate config
that plugs the naive `mulImpl` base kernel into a non-default `StrassenConfig`
(with a distinct cutoff), exercising the pluggable-base-kernel path with a
verified-`Valid` config supplied by the caller.

Per honesty constraint (b) of `HexMatrix/SPEC/hex-matrix.md` § "A demonstration
non-default config": the delayed-reduction kernel `strassenBarrett` above is
verified correct but does **not** measurably beat the default base kernel on this
type (the two-word accumulator's per-term Lean-level bookkeeping — a boxed
`(UInt64 × UInt64 × Nat)` accumulator and a `UInt64.addCarry` extern call per term
— outweighs the modular reductions it saves against the tight single-extern
`ZMod64.mul`; see the committed comparison in `reports/figures/`). So the delayed
kernel is not shipped as the performance demonstration; optimizing its constants
(or a bit-packed GF(2) four-Russians kernel) is filed as follow-up work. -/
@[expose]
def strassenDemo : Matrix.StrassenConfig (ZMod64 p) where
  cutoff := 48
  baseMul := Matrix.mulImpl

/-- The shipped demonstration config is `Valid`: its naive base kernel equals
`mul` by `mul_eq_mulImpl`. -/
theorem strassenDemo_valid : (strassenDemo (p := p)).Valid := by
  intro n m k X Y
  show Matrix.mulImpl X Y = Matrix.mul X Y
  rw [Matrix.mul_eq_mulImpl]

end Hex
