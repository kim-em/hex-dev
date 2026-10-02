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

theorem result : (!![(134900498 / 268435457), (-134900498 / 268435457), (-134900498 / 268435457), (134900498 / 268435457); (134900498 / 268435457), (8175837 / 268435457), (8175837 / 268435457), (277976833 / 268435457); (134900498 / 268435457), (-277976833 / 268435457), (-35014519 / 268435457), (-251138151 / 268435457); (134900498 / 268435457), (-277976833 / 268435457), (-520939147 / 268435457), (375764603 / 268435457)] : Matrix (Fin 4) (Fin 4) ℚ).mulVec ![(-2 / 3), (2 / 3), (2 / 3), (-2 / 3)] = ![(-1079203984 / 805306371), (-264350438 / 268435457), (-23147494 / 47370963), (-873054054 / 268435457)] := by solve

#print axioms result
