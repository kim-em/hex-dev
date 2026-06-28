/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexGFqMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexGFqMathlib: GFq ↔ GaloisField correspondence" =>
%%%
tag := "hex-gfq-mathlib"
%%%

# Introduction
%%%
tag := "hex-gfq-mathlib-intro"
%%%

`HexGFqMathlib` is the Mathlib correspondence layer for the executable
finite-field model {name}`Hex.GFq`. The executable libraries represent an
element of `GF(pⁿ)` as a reduced polynomial over `Fₚ` modulo a committed
Conway polynomial; this bridge transfers the abstract structural facts a
Mathlib-side caller expects — finiteness, cardinality, the `Field`
instance, and identification with Mathlib's canonical
{name}`GaloisField` — onto that executable representation.

What a downstream caller gets is the ability to treat an executable
{name}`Hex.GFq` value as a member of an honest Mathlib finite field. The
two are connected by a bundled ring equivalence, so any algebraic fact
proved about `GaloisField p n` transfers to the executable model, and a
computation run on the fast representation can be given meaning as a
statement about the abstract field.

The bridge is built in two stages. First, a generic counting argument
gives every executable finite field over a prime modulus a `Fintype`
instance with the expected cardinality. Second, that cardinality is
matched against {name}`GaloisField`, and the
`FiniteField.ringEquivOfCardEq` uniqueness theorem promotes the equal
cardinalities to a ring isomorphism. A separate strand identifies the
optimized packed binary field {name}`Hex.GF2q` with the generic
characteristic-2 field over the same Conway modulus.

# Encoders
%%%
tag := "hex-gfq-mathlib-encoders"
%%%

The cardinality count rests on a concrete bijection between reduced
polynomials of bounded degree and a finite index type. The two halves of
the bijection are {name}`HexGFqMathlib.FpPoly.coeffIndex`, which reads the
first `degree` coefficients of an `FpPoly` as a base-`p` number, and
{name}`HexGFqMathlib.FpPoly.ofIndexBelowDegree`, which decodes such a
number back into a polynomial.

{docstring HexGFqMathlib.FpPoly.coeffIndex}

{docstring HexGFqMathlib.FpPoly.ofIndexBelowDegree}

# Reduced representatives
%%%
tag := "hex-gfq-mathlib-reduced-reps"
%%%

The encoder bijection is lifted to the executable field through the
subtype of reduced representatives — `FpPoly` values whose degree is
strictly below the modulus.

{docstring HexGFqMathlib.FiniteField.ReducedRep}

The field wrapper is equivalent to its reduced representatives, and those
representatives are in turn indexed by `Fin (p ^ degree f)`. Composing the
two equivalences transports `Fintype` support onto the executable field.

{docstring HexGFqMathlib.FiniteField.reducedRepEquiv}

{docstring HexGFqMathlib.FiniteField.reducedRepFinEquiv}

# Principal results
%%%
tag := "hex-gfq-mathlib-principal-results"
%%%

With the index equivalence in hand the cardinality follows. The generic
statement counts a finite field by its modulus degree; the canonical
Conway-backed `GFq p n` then reads the count off as `p ^ n`, because the
committed modulus has extension degree `n`.

{docstring HexGFqMathlib.FiniteField.fintype_card}

{docstring HexGFqMathlib.GFq.fintype_card_eq_pow}

Matching that cardinality against Mathlib's {name}`GaloisField` — whose
own cardinality is `p ^ n` — gives the cardinality bridge, and the
uniqueness of finite fields of a given size promotes it to the headline
ring equivalence.

{docstring HexGFqMathlib.GFq.card_eq_galoisField_card}

{docstring HexGFqMathlib.GFq.equivGaloisField}

# The packed binary bridge
%%%
tag := "hex-gfq-mathlib-packed-bridge"
%%%

The executable stack keeps the optimized packed binary field
{name}`Hex.GF2q` separate from the generic {name}`Hex.GFq` so the
representation choice stays explicit. Over characteristic 2 the two models
describe the same field, and `HexGFqMathlib/GF2q.lean` makes that precise:
the packed modulus, transported to `FpPoly 2`, is exactly the Conway
polynomial selected for the same committed entry, and the packed and
generic fields are ring-equivalent.

{docstring Hex.GF2q.modulusFpPoly_eq_conway}

{docstring Hex.GF2q.equivGFq}

# Cross-references
%%%
tag := "hex-gfq-mathlib-cross-references"
%%%

`HexGFqMathlib` is the Mathlib bridge built on top of the executable
finite-field stack:

* `HexGFq` is the computational counterpart. It defines the canonical
  field {name}`Hex.GFq` over a committed Conway modulus and the optimized
  packed binary field {name}`Hex.GF2q`, together with the operations and
  the `Lean.Grind.Field` structure that this chapter transports to
  Mathlib's typeclasses. The bridge re-expresses those executable fields
  as honest Mathlib finite fields without giving any computational library
  a Mathlib dependency.
* `HexGFqRing` supplies the quotient-ring layer underneath `HexGFq`; see
  {ref "hex-gfq-ring"}[the `HexGFqRing` chapter] for the
  canonical-representative invariant that the reduced-representative
  equivalence in this chapter relies on.
