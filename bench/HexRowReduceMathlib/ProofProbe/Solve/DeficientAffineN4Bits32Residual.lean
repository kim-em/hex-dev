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

theorem result : (!![(531112291 / 536870913), (531112291 / 536870913), (-531112291 / 536870913), (531112291 / 536870913); (-531112291 / 536870913), (-26819045 / 536870913), (345135179 / 178956971), (-26819045 / 536870913); (-531112291 / 536870913), (-26819045 / 536870913), (345135179 / 178956971), (-26819045 / 536870913); (-531112291 / 536870913), (-26819045 / 536870913), (345135179 / 178956971), (-26819045 / 536870913)] : Matrix (Fin 4) (Fin 4) ℚ).mulVec ![(1 / 3), (2 / 3), (-1 / 3), (-2 / 3)] = ![(1062224582 / 1610612739), (-1566517828 / 1610612739), (-1566517828 / 1610612739), (-1566517828 / 1610612739)] := by solve

#print axioms result
