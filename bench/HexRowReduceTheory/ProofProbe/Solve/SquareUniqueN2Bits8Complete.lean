/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRowReduceTheory.Tactic

set_option maxRecDepth 100000

noncomputable def result := solve% (!![(6 / 11), (6 / 11); (6 / 11), (37 / 33)] : Matrix (Fin 2) (Fin 2) ℚ) ![(2 / 11), (-1 / 99)]

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
