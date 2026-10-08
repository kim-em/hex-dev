/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexRowReduceMathlib.Tactic

public section

set_option maxRecDepth 100000

theorem result : (!![0, 81; 90, 0] : Matrix (Fin 2) (Fin 2) ℚ) * !![0, (1 / 90); (1 / 81), 0] = 1 := by inverse

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
