/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRowReduceMathlib.Tactic

set_option maxRecDepth 100000

theorem result : ¬ ∃ x, (!![(41 / 65), (-41 / 65); (41 / 65), (-41 / 65)] : Matrix (Fin 2) (Fin 2) ℚ).mulVec x = ![(82 / 195), (277 / 195)] := by solve

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
