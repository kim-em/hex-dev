/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexModArith

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexModArith: machine-word modular arithmetic" =>
%%%
tag := "hex-mod-arith"
%%%

# Introduction
%%%
tag := "hex-mod-arith-intro"
%%%

`HexModArith` is the modular-arithmetic layer of the stack: arithmetic
in `ℤ/pℤ` carried out on `UInt64`-backed coefficients. A residue is a
single machine word holding the standard representative in `[0, p)`,
bundled with a proof that the word is reduced. There is one residue
type, {name}`Hex.ZMod64`, parametrised by the modulus `p`; the Barrett
and Montgomery hot-loop routines are opt-in *operations* on that type,
not parallel residue types.

The modulus carries a side condition: it must be positive and fit in a
machine word. That condition is packaged as the typeclass
{name}`Hex.ZMod64.Bounds`, which every `ZMod64 p` value and operation
takes as an instance argument. `HexModArith` is Mathlib-free; it depends
only on `HexArith`, from which it borrows the Barrett and Montgomery
machine-word kernels. It underpins the finite-field and prime-field
polynomial layers (`HexGFqRing`, `HexPolyFp`, and beyond), which read
their coefficient arithmetic off this representation; see
{ref "hex-mod-arith-cross-references"}[Cross-references].

# Core types
%%%
tag := "hex-mod-arith-core-types"
%%%

The bounds typeclass states the two facts an `UInt64`-backed modulus
must satisfy: it is positive, and it does not exceed one machine word.

{docstring Hex.ZMod64.Bounds}

A residue is the backing word together with a proof that the word, read
as a `Nat`, is already reduced below the modulus. Because that proof
pins down a unique word for each residue value, structural equality on
{name}`Hex.ZMod64` coincides with equality of representatives.

{docstring Hex.ZMod64}

The canonical view of a residue is its `Nat` representative, and the two
extensionality principles let proofs reduce equality of residues to
equality of those representatives.

{docstring Hex.ZMod64.toNat}

{docstring Hex.ZMod64.ext_toNat}

{docstring Hex.ZMod64.eq_iff_toNat_eq}

# Constructors and conversions
%%%
tag := "hex-mod-arith-constructors"
%%%

The primitive constructor takes any `Nat`, reduces it modulo `p`, and
packages the result with its reduction proof. An {name}`OfNat` instance
routes numeric literals through it, so `(3 : ZMod64 7)` denotes the
residue of `3`.

{docstring Hex.ZMod64.ofNat}

Its defining property is that the representative of `ofNat p n` is `n`
reduced modulo `p` — the bridge every coefficient computation rewrites
across.

{docstring Hex.ZMod64.toNat_ofNat}

# Principal operations
%%%
tag := "hex-mod-arith-operations"
%%%

The ring operations add, subtract, negate, and multiply residues,
re-reducing each result so the output is again a standard
representative. The standard `Add`, `Sub`, `Neg`, and `Mul` instances on
{name}`Hex.ZMod64` dispatch to these, so `a + b`, `a - b`, `-a`, and
`a * b` work directly, and a `Lean.Grind.CommRing` instance exposes the
whole surface to the `grind` tactic.

{docstring Hex.ZMod64.add}

{docstring Hex.ZMod64.sub}

{docstring Hex.ZMod64.neg}

{docstring Hex.ZMod64.mul}

Exponentiation uses repeated squaring, and inversion runs the
extended-GCD helper from `HexArith`; for an element coprime to the
modulus the result is the modular inverse.

{docstring Hex.ZMod64.pow}

{docstring Hex.ZMod64.inv}

## Worked example: ring arithmetic
%%%
tag := "hex-mod-arith-worked-ring"
%%%

The block below works in `ZMod64 7`. After supplying the `Bounds 7`
instance it builds two residues and exercises the constructors and the
ring operations. Each `#guard` is checked when the chapter builds, so
the expected representatives are guaranteed to match what the executable
implementation produces.

```lean
open Hex Hex.ZMod64

namespace HexModArithChapterRing

instance : Bounds 7 := ⟨by decide, by decide⟩

-- a = 3 and b = 5 as residues mod 7.
def a : ZMod64 7 := ofNat 7 3
def b : ZMod64 7 := ofNat 7 5

-- Literals reduce: 10 ≡ 3 (mod 7).
#guard a.toNat = 3
#guard (10 : ZMod64 7).toNat = 3

-- 3 + 5 = 8 ≡ 1.
#guard (a + b).toNat = 1
-- 3 - 5 ≡ -2 ≡ 5.
#guard (a - b).toNat = 5
-- 3 · 5 = 15 ≡ 1.
#guard (a * b).toNat = 1
-- 3^5 = 243 ≡ 5.
#guard (a ^ 5).toNat = 5
-- 3⁻¹ ≡ 5, since 3 · 5 ≡ 1.
#guard (inv a).toNat = 5
#guard (inv a * a).toNat = 1

end HexModArithChapterRing
```

# Hot-loop operations
%%%
tag := "hex-mod-arith-hot-loop"
%%%

Inner loops that multiply many residues under one fixed modulus can
amortise the reduction by precomputing a context once. `HexModArith`
wraps the two `HexArith` kernels for this. Both contexts store the
machine-word modulus together with a proof that it agrees with the
indexed `p`, so their results repackage as ordinary {name}`Hex.ZMod64`
values.

Barrett reduction replaces the per-multiply division by a fixed-shift
multiply. The context is built from the small modulus, and its
multiplication agrees on the nose with the ordinary product.

{docstring Hex.BarrettCtx}

{docstring Hex.BarrettCtx.mulMod}

{docstring Hex.BarrettCtx.mulMod_eq_mul}

Montgomery multiplication works in a transformed domain. Values are
first mapped to Montgomery form — a distinct type {name}`Hex.MontResidue`
so the representation cannot be confused with a standard residue — then
multiplied repeatedly without leaving the domain, and converted back
once at the end.

{docstring Hex.MontResidue}

{docstring Hex.MontCtx}

{docstring Hex.MontCtx.toMont}

{docstring Hex.MontCtx.mulMont}

{docstring Hex.MontCtx.fromMont}

Entering Montgomery form, multiplying there, and leaving again computes
exactly the ordinary product — the correctness statement that licenses
swapping the hot loop in for the default multiply.

{docstring Hex.MontCtx.fromMont_mulMont_toMont}

## Worked example: Barrett and Montgomery
%%%
tag := "hex-mod-arith-worked-hot-loop"
%%%

This block builds both contexts for the prime `7` and checks that each
hot-loop product reproduces the ordinary residue product `3 · 5 ≡ 1`.
The Barrett smart constructor needs `1 < p` and `p < 2^32`; the
Montgomery one needs an odd modulus. Both side conditions are discharged
by `decide`.

```lean
open Hex Hex.ZMod64

namespace HexModArithChapterHotLoop

instance : Bounds 7 := ⟨by decide, by decide⟩

def a : ZMod64 7 := ofNat 7 3
def b : ZMod64 7 := ofNat 7 5

-- Barrett context for the small prime 7.
def bar : Hex.BarrettCtx 7 :=
  Hex.BarrettCtx.ofModulus (p := 7) (by decide) (by decide)

-- Montgomery context (7 is odd).
def mon : Hex.MontCtx 7 :=
  Hex.MontCtx.ofOddModulus (by decide) (by decide)

-- Barrett multiplication matches the ordinary product.
#guard (bar.mulMod a b).toNat = (a * b).toNat

-- A Montgomery round trip is the identity.
#guard (mon.fromMont (mon.toMont a)).toNat = a.toNat

-- Multiplying inside the Montgomery domain, then leaving,
-- agrees with the ordinary product.
#guard (mon.fromMont
    (mon.mulMont (mon.toMont a) (mon.toMont b))).toNat
  = (a * b).toNat

end HexModArithChapterHotLoop
```

# Key correctness theorems
%%%
tag := "hex-mod-arith-key-correctness"
%%%

Each ring operation is pinned down by a representativity law: its result
is the residue of the corresponding `Nat` operation on the
representatives, reduced modulo `p`. These are the lemmas downstream
proofs rewrite with.

{docstring Hex.ZMod64.toNat_add}

{docstring Hex.ZMod64.toNat_sub}

{docstring Hex.ZMod64.toNat_mul}

{docstring Hex.ZMod64.toNat_pow}

Inversion is characterised on the elements where it is meaningful: a
residue coprime to the modulus is a unit, with the computed inverse as
its two-sided inverse.

{docstring Hex.ZMod64.inv_mul_eq_one_of_coprime}

Over a prime modulus the residues form a field. Under the
{name}`Hex.ZMod64.PrimeModulus` assumption — equivalently a proof that
`p` is prime — there are no zero divisors, every nonzero residue is
invertible, and Fermat's little theorem holds.

{docstring Hex.ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero}

{docstring Hex.ZMod64.inv_mul_eq_one_of_prime}

{docstring Hex.ZMod64.pow_prime}

# Cross-references
%%%
tag := "hex-mod-arith-cross-references"
%%%

`HexModArith` sits one level above `HexArith` and below the finite-field
stack:

* `HexArith` supplies the machine-word Barrett and Montgomery kernels
  that the {ref "hex-mod-arith-hot-loop"}[hot-loop contexts] wrap. The
  `_root_.BarrettCtx` and `_root_.MontCtx` types referenced by
  {name}`Hex.BarrettCtx` and {name}`Hex.MontCtx` are the untyped
  `UInt64` kernels from that library.
* `HexModArithMathlib` is the correspondence layer: it re-exports the
  executable {name}`Hex.ZMod64` theory as theorems about Mathlib's
  `ZMod p`, so the computational results in this chapter transfer to the
  abstract setting. The Mathlib dependency lives entirely on that side
  of the boundary; see
  {ref "hex-mod-arith-mathlib"}[the HexModArithMathlib chapter].
* The finite-field layer `HexGFqRing` and the prime-field polynomial
  layer `HexPolyFp` consume `ZMod64 p` as their coefficient type,
  inheriting the ring structure and the
  {ref "hex-mod-arith-key-correctness"}[field facts] above for prime
  `p`.
