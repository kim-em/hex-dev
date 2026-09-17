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

theorem result : (!![0, 0, 0, 0, 0, 0, 0, 1704283965; 0, 0, 0, 0, 0, 0, 359642461, 0; 0, 0, 0, 0, 0, 514309646, 0, 0; 0, 0, 0, 0, 970810167, 0, 0, 0; 0, 0, 0, 1787627811, 0, 0, 0, 0; 0, 0, 874515051, 0, 0, 0, 0, 0; 0, 908226306, 0, 0, 0, 0, 0, 0; 1805935779, 0, 0, 0, 0, 0, 0, 0] : Matrix (Fin 8) (Fin 8) ℚ)⁻¹ = !![0, 0, 0, 0, 0, 0, 0, (1 / 1805935779); 0, 0, 0, 0, 0, 0, (1 / 908226306), 0; 0, 0, 0, 0, 0, (1 / 874515051), 0, 0; 0, 0, 0, 0, (1 / 1787627811), 0, 0, 0; 0, 0, 0, (1 / 970810167), 0, 0, 0, 0; 0, 0, (1 / 514309646), 0, 0, 0, 0, 0; 0, (1 / 359642461), 0, 0, 0, 0, 0, 0; (1 / 1704283965), 0, 0, 0, 0, 0, 0, 0] := by inverse

#print axioms result
