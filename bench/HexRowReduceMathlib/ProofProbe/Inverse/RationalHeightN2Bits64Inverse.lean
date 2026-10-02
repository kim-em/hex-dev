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

theorem result : (!![(441704140300138887 / 768614336404564651), (-441704140300138887 / 768614336404564651); (441704140300138887 / 768614336404564651), (162902945810394067 / 768614336404564651)] : Matrix (Fin 2) (Fin 2) ℚ)⁻¹ = !![(125209539592404791124198499888325617 / 267057453189825001285758079790382198), (768614336404564651 / 604607086110532954); (-768614336404564651 / 604607086110532954), (768614336404564651 / 604607086110532954)] := by inverse

#print axioms result
