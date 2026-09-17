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

noncomputable def result := solve% (!![(474995534 / 536870913), (474995534 / 536870913); (-474995534 / 536870913), (-3115174 / 178956971)] : Matrix (Fin 2) (Fin 2) ℚ) ![(474995534 / 536870913), (-493686578 / 1610612739)]

#print axioms result
