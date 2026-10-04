/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexSmithMathlib.Tactic

public section

set_option maxRecDepth 100000

theorem result : Nonempty (HexSmithMathlib.SmithQuotient !![1, 1; -1, 63] 2 ![1, 64]) := by smith

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
