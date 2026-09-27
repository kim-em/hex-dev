/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib.ProofProbe.Support17

example : Nat.Prime 17 := by
  ecpp using Hex.ECPP.Fixture17.cert
