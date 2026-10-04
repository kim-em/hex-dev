/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexRowReduceMathlib.Tactic

public section

set_option maxRecDepth 100000

noncomputable def result := solve% (!![(2 / 3), (2 / 3), (-2 / 3), (-2 / 3); (2 / 3), (4 / 3), (-4 / 3), (-4 / 3)] : Matrix (Fin 2) (Fin 4) ℚ) ![(8 / 9), (14 / 9)]

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
