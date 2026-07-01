/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexArith

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexArith: low-level arithmetic foundations" =>
%%%
tag := "hex-arith"
%%%

# Introduction
%%%
tag := "hex-arith-intro"
%%%

`HexArith` is the low-level arithmetic the rest of the project is built
on. It has no dependencies, and everything above it (modular arithmetic,
polynomials, finite fields) uses these routines transitively.

It has four pieces. The wide-word `UInt64` operations give a two-word
view of machine arithmetic (full products and add/subtract-with-carry),
so higher libraries can build multi-word modular reduction in
native-word code. Two single-word modular reducers,
{name}`barrettReduce` and {name}`montgomeryReduce`, each come
with a `Nat`-level model stating the arithmetic before the machine-word
encoding is pinned down. {name}`HexArith.extGcd` is the extended
Euclidean algorithm in three flavours (`Nat`, GMP-backed `Int`, and
`UInt64`), and {name}`Hex.Nat.isPrimeTrial` is a trial-division
primality test that produces a primality witness without `native_decide`
or a hardcoded prime list.

Everything here is executable. Some wide-word operations carry an
`@[extern]` C implementation for speed, but each is defined by a Lean
model the C code is proved to match, so the library has a meaning
independent of the native binding; see
{ref "hex-arith-cross-references"}[Cross-references].

# Wide-word `UInt64` operations
%%%
tag := "hex-arith-wide"
%%%

These operations treat a `UInt64` as a digit in radix `R = 2^64`.
{name}`UInt64.word` names that radix, and the two structural facts below
(every word is below the radix, and `ofNat` reduces modulo it) connect
machine words to `Nat` reasoning.

{docstring UInt64.word}

{docstring UInt64.toNat_lt_word}

The multiply primitives compute the full two-word product of two
words: {name}`UInt64.mulHi` is the high half and {name}`UInt64.mulFull`
returns both halves at once.

{docstring UInt64.mulHi}

{docstring UInt64.mulFull}

Add- and subtract-with-carry thread a carry (resp. borrow) bit so that
multi-word sums and differences chain across words.

{docstring UInt64.addCarry}

{docstring UInt64.subBorrow}

Each primitive comes with the `Nat`-level laws downstream proofs use:
the low word is the exact result reduced modulo `R`, and the carry or
borrow bit records exactly whether the exact result overflowed the
single-word range.

{docstring UInt64.toNat_addCarry_fst}

{docstring UInt64.addCarry_snd}

{docstring UInt64.toNat_subBorrow_fst}

{docstring UInt64.subBorrow_snd}

These four operations are `@[extern]`-backed for speed, so they run
through a C implementation in compiled code; their Lean models are what
the manual's evaluated examples below avoid and what the laws above are
stated against.

# Extended GCD
%%%
tag := "hex-arith-extgcd"
%%%

The extended Euclidean algorithm returns a triple `(g, s, t)` with
`g = gcd a b` and the Bezout certificate `s · a + t · b = g`. The pure
`Nat` version is the reference implementation; an `Int` variant routes
through GMP's `mpz_gcdext` via `@[extern]`, and a `UInt64` variant
takes machine-word inputs. All three share the same name in their
respective namespaces.

{docstring HexArith.extGcd}

The combined correctness theorem packages both halves of the
specification (the gcd projection and the Bezout identity) for callers
that destructure the returned triple.

{docstring HexArith.extGcd_spec}

# Barrett reduction
%%%
tag := "hex-arith-barrett"
%%%

Barrett reduction computes `T mod p` for a small modulus `p` using a
single precomputed reciprocal, replacing the hardware division with one
multiply-and-shift and at most one corrective subtraction. The
`Nat`-level routine states the arithmetic abstractly over the radix
{name}`barrettRadix`; the reciprocal is `pinv = floor(R / p)`.

{docstring barrettRadix}

{docstring barrettReduceNat}

The reciprocal approximates the true quotient from below, never
overshooting by more than one; these two bounds make the single
corrective subtraction sufficient.

{docstring barrettQuotient_le_div}

{docstring div_le_barrettQuotient_add_one}

With those bounds, the reducer is proved to compute the residue exactly
and to land in the canonical interval `[0, p)`.

{docstring barrettReduceNat_eq_mod}

{docstring barrettReduceNat_lt}

The executable side packages the modulus and its reciprocal in a
{name}`BarrettCtx` built by {name}`BarrettCtx.mk`, which checks the
small-modulus side conditions once so they need not be re-proved at
each call.

{docstring BarrettCtx}

{docstring BarrettCtx.mk}

{docstring barrettReduce}

The machine-word reducer is proved to agree with the `Nat` model and to
return a canonical residue.

{docstring toNat_barrettReduce_eq_mod}

{docstring barrettReduce_lt}

# Montgomery reduction
%%%
tag := "hex-arith-montgomery"
%%%

Montgomery reduction is the alternative single-word reducer used when
many modular multiplications share one odd modulus. It works in the
Montgomery domain (residues scaled by `R`), where reduction becomes a
multiply-add-shift with no trial division at all. As with Barrett, a
`Nat`-level model states the computation before the machine-word
encoding.

{docstring montgomeryReduceNat}

The model is proved to compute the reduced residue exactly and to land
below the modulus, given the precomputed inverse word `p'` and an odd
modulus below the radix.

{docstring montgomeryReduceNat_eq_mod}

{docstring montgomeryReduceNat_lt}

The executable side carries the machine-word Montgomery parameters in
a {name}`MontCtx`; {name}`montgomeryReduce` consumes a two-word product `(Thi, Tlo)`
and returns one reduced residue, proved to match the `Nat` model and to
stay canonical.

{docstring MontCtx}

{docstring montgomeryReduce}

{docstring toNat_montgomeryReduce}

{docstring montgomeryReduce_lt}

# Trial-division primality
%%%
tag := "hex-arith-prime"
%%%

`HexArith` supplies a self-contained primality test. It checks that no
integer in `[2, n)` divides `n`, and its soundness theorem lifts a
`true` result to the project-local {name}`Hex.Nat.Prime` predicate: a
primality witness produced without `native_decide` or a fixed prime
table, so downstream prime searches can certify candidates beyond any
precomputed list.

{docstring Hex.Nat.Prime}

{docstring Hex.Nat.isPrimeTrial}

{docstring Hex.Nat.isPrimeTrial_isPrime}

# Worked example
%%%
tag := "hex-arith-worked"
%%%

The block below exercises the pure (non-`@[extern]`) computational
surface: the `Nat` extended GCD, the trial-division test, and the
`Nat`-level Barrett reducer. Each `#guard` is checked when the chapter
is built, so the expected outputs are guaranteed to match what the
executable implementation produces. The wide-word operations are
omitted here because their `@[extern]` C binding is not available to the
manual's evaluator; they are documented by signature and law above.

```lean
open HexArith Hex.Nat

namespace HexArithChapter

-- gcd(12, 18) = 6, with Bezout (-1)·12 + 1·18 = 6.
#guard extGcd 12 18 = (6, -1, 1)
-- gcd(240, 46) = 2, with (-9)·240 + 47·46 = 2.
#guard extGcd 240 46 = (2, -9, 47)

-- Soundness: 97 is prime, 91 = 7·13 is not, and the
-- test rejects 1 (it demands 2 ≤ n).
#guard isPrimeTrial 97 = true
#guard isPrimeTrial 91 = false
#guard isPrimeTrial 1 = false

-- Barrett reduction modulo 97 with pinv = ⌊2^64 / 97⌋
-- reproduces ordinary remainder: 1000 mod 97 = 30.
#guard barrettReduceNat 97 (barrettRadix / 97) 1000 = 30

end HexArithChapter
```

# Cross-references
%%%
tag := "hex-arith-cross-references"
%%%

`HexArith` has no dependencies:

* `HexModArith` is the immediate consumer: it builds the user-facing
  modular-arithmetic API (modular multiplication, exponentiation) on the
  Barrett and Montgomery reducers documented here. The polynomial and
  finite-field libraries reach these routines transitively through it.
* The wide-word multiply and carry primitives are `@[extern]`-backed by
  the C sources in `HexArith/ffi/` (`wide_arith.c`, `mpz_gcdext.c`), and
  the {ref "hex-arith-wide"}[`Nat`-level laws] above are the
  specification those bindings are proved against; the library's meaning
  does not depend on the native code being linked.
* The arithmetic here has no Mathlib correspondence library of its own.
  The Mathlib correspondences live in the consuming libraries' `*Mathlib`
  counterparts. `HexArith` itself imports only `Std` and never depends
  on Mathlib.
