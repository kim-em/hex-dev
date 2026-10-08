/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPPMathlib.ProofProbe.Support

public section

/-! Checker equation and kernel replay without elaborator reification. -/

theorem result : Nat.Prime 18446744073709551629 :=
  Hex.ECPP.natPrime_of_checkAt (cert := Hex.ECPP.Fixture65.cert) (by decide)

#print axioms result
