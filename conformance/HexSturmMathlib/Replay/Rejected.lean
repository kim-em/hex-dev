/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib.Replay.Support

public section
namespace HexSturmMathlib.ReplayTests
open Hex DensePoly

/-- Reject a false polynomial identity through the ordinary kernel. -/
theorem rejected : Sturm.Replay.check Sturm.orderSign 7 p 1 (.finite (-2)) (.finite 2) 2
    { literal with remainders := { literalChain with terminal := some (1, 1) } } = false := by
  simp only [Sturm.Replay.check, QueryReplay.check, QueryChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- Context bindings remain literal even for otherwise valid evidence. -/
theorem stale : Sturm.Replay.check Sturm.orderSign 8 p 1 (.finite (-2)) (.finite 2) 2 literal = false := by
  decide +kernel

#print axioms rejected
#print axioms stale
end HexSturmMathlib.ReplayTests
