/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib
public import HexSturm.Fixtures
public meta import HexSturm.Basic

public section
namespace HexSturmMathlib.ReplayTests
open Hex DensePoly Hex.Sturm.Fixtures

/-- Reject a false polynomial identity through the ordinary kernel. -/
theorem rejected : Sturm.check Sturm.orderSign 7 p 1 (.finite (-2)) (.finite 2) 2
    { literal with remainders := { literalChain with terminal := some (1, 1) } } = false := by
  simp only [Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- Context bindings remain literal even for otherwise valid evidence. -/
theorem stale : Sturm.check Sturm.orderSign 8 p 1 (.finite (-2)) (.finite 2) 2 literal = false := by
  decide +kernel

/-- info: 'HexSturmMathlib.ReplayTests.rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rejected
-- Keep the second print visible to sturm_mathlib_sweep.py's axiom parser.
#print axioms rejected
/-- info: 'HexSturmMathlib.ReplayTests.stale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stale
-- Keep the second print visible to sturm_mathlib_sweep.py's axiom parser.
#print axioms stale
end HexSturmMathlib.ReplayTests
