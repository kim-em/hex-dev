/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.Diagnostics.Nested.Fractions
public meta import HexSignDet.Dag
public meta import HexSignDet.Replay

public section

namespace Hex.SignDetMathlib.Diagnostics.Nested.N1.FieldArithmetic
open Hex.SignDet

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- Addition with distinct nonunit denominators and division with polynomial cancellation. -/
theorem checked : (Fractions.first + Fractions.second = Fractions.sum) ∧
    (Fractions.first / Fractions.first = 1) := by
  decide +kernel

/-- info: 'Hex.SignDetMathlib.Diagnostics.Nested.N1.FieldArithmetic.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked

end Hex.SignDetMathlib.Diagnostics.Nested.N1.FieldArithmetic
