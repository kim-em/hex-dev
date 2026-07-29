/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHensel.WordTransport

public section

/-!
# Packed polynomial multiplication over `WordMod`

The quadratic Hensel hot path works modulo an odd machine word in Montgomery
form.  Its proof-facing multiplication remains the generic verified
`DensePoly` convolution.  Compiled code uses one native convolution call,
keeping the same per-term Montgomery reduction and modular addition order but
avoiding the generic typeclass calls and boxed intermediate coefficients.
-/

namespace Hex.WordPoly

variable {m : UInt64}

/-- Dense addition over a full-word Montgomery ring, with a native array
kernel behind the exact Lean contract. -/
@[expose, extern "lean_hex_word_poly_add"]
def add (ctx : _root_.MontCtx m)
    (a b : DensePoly (WordMod ctx)) : DensePoly (WordMod ctx) :=
  a + b

/-- Dense subtraction over a full-word Montgomery ring, with a native array
kernel behind the exact Lean contract. -/
@[expose, extern "lean_hex_word_poly_sub"]
def sub (ctx : _root_.MontCtx m)
    (a b : DensePoly (WordMod ctx)) : DensePoly (WordMod ctx) :=
  a - b

/-- Dense multiplication over a full-word Montgomery ring.  The Lean body is
the exact logical contract; `lean_hex_word_poly_mul` is its allocation-light
runtime implementation. -/
@[expose, extern "lean_hex_word_poly_mul"]
def mul (ctx : _root_.MontCtx m)
    (a b : DensePoly (WordMod ctx)) : DensePoly (WordMod ctx) :=
  a * b

/-- Sum of two dense products over a full-word Montgomery ring.  The native
kernel fuses both convolutions and the final addition into one output pass. -/
@[expose, extern "lean_hex_word_poly_mul_add"]
def mulAdd (ctx : _root_.MontCtx m)
    (a b c d : DensePoly (WordMod ctx)) : DensePoly (WordMod ctx) :=
  a * b + c * d

/-- The packed runtime kernel has the ordinary dense product as its logical
value. -/
@[simp] theorem mul_eq (ctx : _root_.MontCtx m)
    (a b : DensePoly (WordMod ctx)) : mul ctx a b = a * b := rfl

@[simp] theorem mulAdd_eq (ctx : _root_.MontCtx m)
    (a b c d : DensePoly (WordMod ctx)) :
    mulAdd ctx a b c d = a * b + c * d := rfl

@[simp] theorem add_eq (ctx : _root_.MontCtx m)
    (a b : DensePoly (WordMod ctx)) : add ctx a b = a + b := rfl

@[simp] theorem sub_eq (ctx : _root_.MontCtx m)
    (a b : DensePoly (WordMod ctx)) : sub ctx a b = a - b := rfl

end Hex.WordPoly
