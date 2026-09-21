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

/-- Recheck the literal certificate in a fresh ordinary kernel build. -/
theorem accepted : Sturm.check Sturm.orderSign 7 p 1 (.finite (-2)) (.finite 2) 2 literal = true := by
  simp only [Sturm.check, TarskiCertificate.check, SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- Interpret the accepted literal squarefreeness and endpoint evidence. -/
theorem domain : Domain id (fun _ => Iff.rfl) p (.finite (-2)) (.finite 2) :=
  check_domain id (fun _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    Sturm.orderSign (fun x => (orderSign_spec x).2.1) (fun x => (orderSign_spec x).2.2.1)
    rfl (fun _ => rfl) (fun x => (orderSign_spec x).1)
    7 p 1 (.finite (-2)) (.finite 2) 2 literal accepted

/-- info: 'HexSturmMathlib.ReplayTests.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms accepted
-- Keep the second print visible to sturm_mathlib_sweep.py's axiom parser.
#print axioms accepted
/-- info: 'HexSturmMathlib.ReplayTests.domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms domain
-- Keep the second print visible to sturm_mathlib_sweep.py's axiom parser.
#print axioms domain
end HexSturmMathlib.ReplayTests
