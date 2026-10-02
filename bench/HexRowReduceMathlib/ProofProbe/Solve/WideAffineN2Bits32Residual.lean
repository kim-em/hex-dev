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

theorem result : (!![(477051622 / 536870913), (-477051622 / 536870913), (477051622 / 536870913), (-477051622 / 536870913); (-477051622 / 536870913), (886850105 / 536870913), (-22417713 / 178956971), (886850105 / 536870913)] : Matrix (Fin 2) (Fin 4) ℚ).mulVec ![(-2 / 3), (-1 / 3), (-2 / 3), (-1 / 3)] = ![(-954103244 / 1610612739), (-685090688 / 1610612739)] := by solve

#print axioms result
