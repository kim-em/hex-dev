import VersoManual

import HexModArithMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexModArithMathlib: ZMod64 ↔ ZMod correspondence" =>
%%%
tag := "hex-mod-arith-mathlib"
%%%

# Introduction
%%%
tag := "hex-mod-arith-mathlib-intro"
%%%

`HexModArithMathlib` is the Mathlib correspondence layer for the
executable residue type {name}`Hex.ZMod64`. The executable library
`HexModArith` stores residues mod `p` in standard form as machine
words and provides the ring operations directly on that
representation; this bridge transfers those residues to Mathlib's
canonical quotient {name}`ZMod` and proves that every
operation is carried across faithfully.

What a Mathlib-side caller gets is the ability to treat an executable
{name}`Hex.ZMod64` value as an honest element of {name}`ZMod`:
the two are connected by a bundled ring equivalence, so any algebraic
identity proved on one side transfers to the other. A computation run
in the fast machine-word representation can therefore be given meaning
as a statement about `ZMod p`, and a `ZMod p` identity from Mathlib can
be pulled back to constrain the executable result.

The whole surface lives in namespace `HexModArithMathlib.ZMod64` and is
parameterised over a modulus `p` carrying the executable
{name}`Hex.ZMod64.Bounds` instance (`0 < p` and `p ≤ 2 ^ 64`); the
bridge adds the `NeZero p` instance that Mathlib's `ZMod p` API
expects.

# Transfer maps
%%%
tag := "hex-mod-arith-mathlib-transfer-maps"
%%%

The two primitive conversions are {name}`HexModArithMathlib.ZMod64.toZMod`,
which reads an executable residue as a Mathlib class, and
{name}`HexModArithMathlib.ZMod64.ofZMod`, which rebuilds an executable
residue from a class by taking its canonical `Nat` value back into the
machine-word representation.

{docstring HexModArithMathlib.ZMod64.toZMod}

{docstring HexModArithMathlib.ZMod64.ofZMod}

The bridge's lowest-level fact relates the Mathlib-side canonical
representative back to the executable residue: the `val` of a
transferred class is exactly the machine residue's `Nat` value, so a
caller reading `(toZMod a).val` recovers `a.toNat` without unfolding the
conversion.

{docstring HexModArithMathlib.ZMod64.val_toZMod}

# Principal results
%%%
tag := "hex-mod-arith-mathlib-principal-results"
%%%

The principal results split into two groups. First, the two transfer
maps are mutually inverse, which is what makes the bundled
{ref "hex-mod-arith-mathlib-equiv"}[ring equivalence] below
well-defined.

{docstring HexModArithMathlib.ZMod64.ofZMod_toZMod}

{docstring HexModArithMathlib.ZMod64.toZMod_ofZMod}

Second, {name}`HexModArithMathlib.ZMod64.toZMod` is a ring
homomorphism: it carries the executable constants and operations to the
matching `ZMod p` constants and operations. These are the lemmas a
caller rewrites with to push the conversion through an expression and so
move an identity across the bridge.

The additive and multiplicative identities transfer in both directions:

{docstring HexModArithMathlib.ZMod64.toZMod_zero}

{docstring HexModArithMathlib.ZMod64.ofZMod_zero}

{docstring HexModArithMathlib.ZMod64.toZMod_one}

{docstring HexModArithMathlib.ZMod64.ofZMod_one}

Addition, negation, subtraction, and multiplication all commute with
{name}`HexModArithMathlib.ZMod64.toZMod`:

{docstring HexModArithMathlib.ZMod64.toZMod_add}

{docstring HexModArithMathlib.ZMod64.toZMod_neg}

{docstring HexModArithMathlib.ZMod64.toZMod_sub}

{docstring HexModArithMathlib.ZMod64.toZMod_mul}

The scalar casts and exponentiation transfer as well, so numerals and
powers built on the executable side land on the matching `ZMod p`
values:

{docstring HexModArithMathlib.ZMod64.toZMod_natCast}

{docstring HexModArithMathlib.ZMod64.toZMod_intCast}

{docstring HexModArithMathlib.ZMod64.toZMod_pow}

Because every transfer lemma above is a `@[simp]` rewrite, `simp` alone
discharges the routine homomorphism obligations. For instance, pushing
the conversion through a sum or a product is immediate:

```lean
open HexModArithMathlib.ZMod64

variable {p : Nat} [Hex.ZMod64.Bounds p]

example (a b : Hex.ZMod64 p) :
    toZMod (a + b) = toZMod a + toZMod b := by simp

example (a b : Hex.ZMod64 p) :
    toZMod (a * b) = toZMod a * toZMod b := by simp

-- The round trip back through `ofZMod` is the identity.
example (a : Hex.ZMod64 p) :
    ofZMod (toZMod a) = a := by simp
```

# The ring equivalence
%%%
tag := "hex-mod-arith-mathlib-equiv"
%%%

The capstone packages the transfer maps and the homomorphism laws into
a single bundled ring equivalence {name}`HexModArithMathlib.ZMod64.equiv`
of type `Hex.ZMod64 p ≃+* ZMod p`. Its forward map is
{name}`HexModArithMathlib.ZMod64.toZMod` and its inverse is
{name}`HexModArithMathlib.ZMod64.ofZMod`; the mutual-inverse and
additive/multiplicative homomorphism fields are exactly the lemmas
above.

{docstring HexModArithMathlib.ZMod64.equiv}

Two unfolding lemmas connect the bundled equivalence back to the bare
conversions, so the transport `@[simp]` lemmas continue to fire on
`equiv` and `equiv.symm` applications:

{docstring HexModArithMathlib.ZMod64.equiv_apply}

{docstring HexModArithMathlib.ZMod64.equiv_symm_apply}

With {name}`HexModArithMathlib.ZMod64.equiv` in hand a downstream
Mathlib-side caller transports the full `CommRing` theory of
{name}`ZMod` onto the executable type for free, and reads
results back through the same equivalence.

# Cross-references
%%%
tag := "hex-mod-arith-mathlib-cross-references"
%%%

`HexModArithMathlib` is the Mathlib bridge for one executable library:

* `HexModArith` is the computational counterpart. It defines the
  residue type {name}`Hex.ZMod64` — a machine word `val` together with
  the proof `val.toNat < p` that it is in canonical standard form — and
  supplies the ring operations ({name}`Hex.ZMod64.add`,
  {name}`Hex.ZMod64.mul`, {name}`Hex.ZMod64.pow`, and the rest) that
  this chapter transfers. The executable side carries the runtime
  `@[extern]` paths and the `Bounds p` typeclass that admits a modulus
  only when it fits in a single machine word; the bridge re-expresses
  those same operations as theorems about `ZMod p`. The transfer lemmas
  here are the proof-side justification that the fast executable
  arithmetic computes the mathematically intended residues.
