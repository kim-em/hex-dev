/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPTheory.ProofProbe.Support

/-! Fresh-module 65-bit ECPP kernel replay. -/

example : Nat.Prime 18446744073709551629 := by
  ecpp using Hex.ECPP.Fixture65.cert
