/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPosDefTheory

/-! Complete-call positive-definiteness proof probe. -/

set_option maxHeartbeats 0

theorem result : (!![25, -16, 6, 32, -43, 14, 38, -37;
    -16, 114, -31, -34, 32, -49, -16, 24;
    6, -31, 61, -10, -22, 44, -34, -34;
    32, -34, -10, 57, -57, 14, 66, -39;
    -43, 32, -22, -57, 126, -36, -63, 117;
    14, -49, 44, 14, -36, 45, -6, -36;
    38, -16, -34, 66, -63, -6, 97, -45;
    -37, 24, -34, -39, 117, -36, -45, 122] : Matrix (Fin 8) (Fin 8) ℤ).PosDef := by
  pos_def

#print axioms result
