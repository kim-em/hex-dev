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

theorem result : (!![(149796829 / 178956971), (149796829 / 178956971); (149796829 / 178956971), (931635055 / 536870913); (-149796829 / 178956971), (32854081 / 536870913); (149796829 / 178956971), (931635055 / 536870913)] : Matrix (Fin 4) (Fin 2) ℚ).mulVec ![(2 / 3), (-2 / 3)] = ![0, (-964489136 / 1610612739), (-964489136 / 1610612739), (-964489136 / 1610612739)] := by solve

#print axioms result
