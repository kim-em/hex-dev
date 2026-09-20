/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality.ProofProbe.PMinusOne.Support

/-! One traversal of the Parents512 construction corpus. -/
set_option maxHeartbeats 0
set_option maxRecDepth 10000
#eval Hex.PrimalityProofProbe.PMinusOne.run "Parents512" false
