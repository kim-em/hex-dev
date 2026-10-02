/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality.ProofProbe.PMinusOne.Support

/-! One construction search with the production budget. -/
set_option maxHeartbeats 0
set_option maxRecDepth 10000
#eval Hex.PrimalityProofProbe.PMinusOne.run "parent-128-67" true
