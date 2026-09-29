/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.ProofProbe.Nested.Fractions2
public meta import HexSignDet.Dag
public meta import HexSignDet.Replay

public section

namespace Hex.SignDetMathlib.ProofProbe.Nested.N2.FieldArithmetic
open Hex.SignDet

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- Addition with distinct nonunit denominators and division with polynomial cancellation. -/
theorem checked : (Fractions2.first + Fractions2.second = Fractions2.sum) ∧
    (Fractions2.first / Fractions2.first = 1) := by
  decide +kernel

/-- info: 'Hex.SignDetMathlib.ProofProbe.Nested.N2.FieldArithmetic.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked

-- The external runner reads this unguarded inventory.
#print axioms checked
end Hex.SignDetMathlib.ProofProbe.Nested.N2.FieldArithmetic
