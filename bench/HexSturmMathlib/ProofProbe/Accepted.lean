/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib.ProofProbe.Support

public section
namespace HexSturmMathlib.ProofProbe
open Hex DensePoly

/-- Recheck the literal certificate in a fresh ordinary kernel build. -/
theorem accepted : Sturm.Replay.check Sturm.orderSign 7 p 1 (.finite (-2)) (.finite 2) 2 literal = true := by
  simp only [Sturm.Replay.check, QueryReplay.check, QueryChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- Interpret the accepted literal squarefreeness and endpoint evidence. -/
theorem domain : Domain id (fun _ => Iff.rfl) p (.finite (-2)) (.finite 2) :=
  check_domain id (fun _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    Sturm.orderSign (fun x => (orderSign_spec x).2.1) (fun x => (orderSign_spec x).2.2.1)
    rfl (fun _ => rfl) (fun x => (orderSign_spec x).1)
    7 p 1 (.finite (-2)) (.finite 2) 2 literal accepted

#print axioms accepted
#print axioms domain
end HexSturmMathlib.ProofProbe
