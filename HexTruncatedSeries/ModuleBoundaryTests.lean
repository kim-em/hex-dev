/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeries.Revert

public section

/-!
Kernel-reduction regressions for truncated series.

These examples intentionally live downstream of the executable definitions.
They fail if tabulation, coefficient access, convolution, arithmetic, or
equality becomes opaque across a module boundary.
-/

namespace Hex.TSeries.ModuleBoundaryTests

open scoped Hex

private def a : TSeries Int 8 := ofFn fun i => if i = 0 then 1 else i
private def b : TSeries Int 8 := ofFn fun i => if i < 3 then i + 1 else 0

example : a * b = ofFn fun i =>
    match i with
    | 0 => 1
    | 1 => 3
    | 2 => 7
    | 3 => 10
    | 4 => 16
    | 5 => 22
    | 6 => 28
    | _ => 34 := by
  decide +kernel

example : mulUpTo 4 a b = ofFn fun i =>
    match i with
    | 0 => 1
    | 1 => 3
    | 2 => 7
    | 3 => 10
    | _ => 0 := by
  decide +kernel

example : Nat.log2 8 = 3 := by decide +kernel

example : steps 8 = 3 := by decide +kernel

/-- Precision two uses only the universally available inverse of one, even
when the subtraction in the class index remains visible downstream. -/
example : NatInverses Int (2 - 1) := inferInstance

private def oneMinusX : TSeries Int 8 :=
  ofFn fun i => if i = 0 then 1 else if i = 1 then -1 else 0

example : invOfUnit oneMinusX 1 = ofFn fun _ => 1 := by
  decide +kernel

/-- The successful-division law remains available to downstream modules
without unfolding the executable zero-prefix test. -/
example (c : TSeries Int 8) (k : Nat) :
    divXPow? (mulXPow c k) k =
      some (truncate c (8 - k) (Nat.sub_le 8 k)) := by
  exact divXPow?_mulXPow c k

/-- The valuation search exposes its complete mathematical contract across a
module boundary. -/
example (c : TSeries Int 8) (k : Nat) :
    valuation? c = some k ↔
      k < 8 ∧ c.coeff k ≠ 0 ∧ ∀ i, i < k → c.coeff i = 0 := by
  exact valuation?_eq_some_iff c k

/-- Bounded square-root lifting exposes its prefix contract downstream. -/
example (c : TSeries Rat 8) (r v : Rat)
    (hr : r * r = c.coeff 0) (hv : ((1 + 1) * r) * v = 1) :
    Agree 5 (sqrtUpTo 5 c r v) (sqrtOfRoot c r v) := by
  exact sqrtUpTo_agree 5 c r v hr hv

/-- Bounded logarithm exposes its prefix contract downstream. -/
example (c : TSeries Rat 8) (h0 : (c - 1).coeff 0 = 0) :
    Agree 5 (logUpTo 5 c) (log c) := by
  exact logUpTo_agree 5 c h0

/-- Bounded exponential exposes its prefix contract downstream. -/
example (c : TSeries Rat 8) (h0 : c.coeff 0 = 0) :
    Agree 5 (expUpTo 5 c) (exp c) := by
  exact expUpTo_agree 5 c h0

/-- Bounded reversion agrees with the full Newton result throughout the
requested prefix. -/
example (c : TSeries Int 8) (v : Int)
    (h0 : c.coeff 0 = 0) (hv : c.coeff 1 * v = 1) :
    Agree 5 (revUpTo 5 c v) (revOfUnit c v) := by
  exact revUpTo_agree 5 c v h0 hv

/-- Direct Lagrange inversion and Newton reversion expose the same public
result over a coefficient ring with the required natural inverses. -/
example (c : TSeries Rat 8) (v : Rat)
    (h0 : c.coeff 0 = 0) (hv : c.coeff 1 * v = 1) :
    revLagrange c v = revOfUnit c v := by
  exact revLagrange_eq c v h0 hv

end Hex.TSeries.ModuleBoundaryTests
