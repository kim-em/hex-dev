/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRowReduceMathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 1000000
set_option trace.HexMatrix.certificate true

theorem result : (!![(409271353 / 536870913), (409271353 / 536870913); (409271353 / 536870913), (739403578 / 536870913)] : Matrix (Fin 2) (Fin 2) ℚ) * !![(132321424665442238 / 45037887464883475), (-178956971 / 110044075); (-178956971 / 110044075), (178956971 / 110044075)] = 1 := by inverse

#print axioms result
