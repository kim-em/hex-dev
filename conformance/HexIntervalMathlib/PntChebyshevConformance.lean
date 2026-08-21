/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntChebyshev

/-!
# Source-pinned PNT+ Chebyshev conformance

The bounded replay covers every coordinate through `11723` and closes the
exact real-valued statement of `Chebyshev.psi_num_2`.  Boundary witnesses pin
the sequential chunk joins; mutation guards reject a composite claimed prime
and an incorrect prime-power base without a precision retry.
-/

namespace Hex.IntervalMathlib.PntChebyshevConformance

open Hex.IntervalMathlib.Experiment.PntChebyshevProbe

example : checkState 1024 = (10442, true) := Chunk00.state
example : checkState 6144 = (62451, true) := Chunk05.state
example : checkState 11723 = (118671, true) := fullState

#guard primeB 9 == false
#guard powerBase 121 == 11
#guard powerBase 121 != 13

/-- A mutation that treats the composite coordinate `9` as prime is rejected. -/
theorem rejectPrimeNine : primeB 9 ≠ true := by decide

/-- A mutation that assigns coordinate `121 = 11²` to base `13` is rejected. -/
theorem rejectPower121 : powerBase 121 ≠ 13 := by decide

/-- The source-shaped real theorem elaborates without a LeanCert import. -/
theorem sourceShape (x : Real) (hx : x > 0) (hx2 : x ≤ 11723) :
    Chebyshev.psi x ≤ 1.11 * x :=
  psi_num_2 x hx hx2

/--
info: 'Hex.IntervalMathlib.Experiment.PntChebyshevProbe.logData_log_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms logData_log_le

/--
info: 'Hex.IntervalMathlib.Experiment.PntChebyshevProbe.vonMangoldt_le_contribution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms vonMangoldt_le_contribution

/-- info: 'Hex.IntervalMathlib.Experiment.PntChebyshevProbe.fullState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fullState

/-- info: 'Hex.IntervalMathlib.Experiment.PntChebyshevProbe.psi_num_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms psi_num_2

end Hex.IntervalMathlib.PntChebyshevConformance
