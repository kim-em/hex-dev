/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.Basic

public section

/-!
The `HexResultant` library provides the fraction-free polynomial primitives
used to compute subresultant pseudo-remainder sequences, resultants, and
discriminants over exact coefficient rings. Its initial executable surface is
polynomial pseudo-division over `Hex.DensePoly`, with the computational
dependency surface kept at `HexPoly` alone.

Correctness and correspondence with Mathlib's `Polynomial.resultant` and
`Polynomial.discr` live in the companion `HexResultantMathlib` library.
-/
