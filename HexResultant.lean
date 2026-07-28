/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.Basic
public import HexResultant.ExactDiv
public import HexResultant.PseudoDivMod
public import HexResultant.FractionPoly
public import HexResultant.SubresultantMinor
public import HexResultant.DeterminantAlgebra
public import HexResultant.BlockDeterminant
public import HexResultant.Subresultant
public import HexResultant.Discriminant

public section

/-!
The `HexResultant` library provides the fraction-free polynomial primitives
used to compute subresultant pseudo-remainder sequences, resultants, and
discriminants over exact coefficient rings. Its initial executable surface is
polynomial pseudo-division over `Hex.DensePoly`, with the computational
dependency surface kept at `HexPoly` alone. Brown's nonzero PRS chain tracks
its corrected terminal principal-subresultant scalar separately, so defective
degree drops retain the exact resultant scale without matrix construction.
The standard discriminant is computed from the signed resultant with the
formal derivative and an exact leading-coefficient quotient.

Correctness and correspondence with Mathlib's `Polynomial.resultant` and
`Polynomial.discr` live in the companion `HexResultantMathlib` library.
-/

namespace Hex.DensePoly

/-- The executable Brown recurrence and the proof-only minor construction use
the same alternating sign convention. -/
theorem negOnePow_eq_sign {R : Type u} [Zero R] [One R] [Sub R] (n : Nat) :
    negOnePow (R := R) n = SubresultantMinor.sign (R := R) n := by
  rfl

end Hex.DensePoly
