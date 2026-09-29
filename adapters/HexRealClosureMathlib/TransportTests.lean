/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportQuery
public meta import HexPoly.Dense
public meta import HexPoly.Operations
public meta import HexRealClosureMathlib.TransportPolynomial
public meta import HexRealClosureMathlib.TransportProduct

public section

namespace Hex.RealClosure.Transport.Tests

private def read (a : Hex.DensePoly Rat) : Rat := a.eval 2
private def p : Hex.DensePoly (Hex.DensePoly Rat) :=
  Hex.DensePoly.ofCoeffs #[1, Hex.DensePoly.ofCoeffs #[-2, 1], 1]

/-- The interior raw representative is structurally nonzero but denotes zero. -/
example : read (p.coeff 1) = 0 ∧ p.coeff 1 ≠ 0 := by decide +kernel

example : ¬ (∀ i < p.size, read (p.coeff i) = 0 ↔ p.coeff i = 0) := by
  intro h
  have bad := (h 1 (by decide +kernel)).mp (by decide +kernel)
  exact (by decide +kernel : p.coeff 1 ≠ 0) bad

private theorem zero : read 0 = 0 := by decide +kernel
private theorem leading : 0 < p.size → read (p.coeff (p.size - 1)) ≠ 0 := by
  intro _
  decide +kernel

/-- Normalized size transports despite the noncanonical interior zero. -/
example : (polynomial read p).size = p.size := polynomial_size read zero p leading

example : polynomial read p = Hex.DensePoly.ofCoeffs #[1, 0, 1] := by decide +kernel

/-- Horner uses the finite reached accumulators, with no interior reflection. -/
example : read (p.eval (Hex.DensePoly.C 3)) =
    (polynomial read p).eval (read (Hex.DensePoly.C 3)) := by
  apply polynomial_eval read zero p (Hex.DensePoly.C 3) leading
  · intro i hi
    change i < 3 at hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> decide +kernel
  · intro i hi
    change i < 3 at hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> decide +kernel

end Hex.RealClosure.Transport.Tests
