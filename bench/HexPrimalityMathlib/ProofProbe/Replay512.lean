/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPrimalityMathlib.ProofProbe.Support
namespace HexPrimalityMathlib.ProofProbe
/-! Kernel replay of the fixed ceiling certificate through the bridge theorem. -/
def input : Nat := prime512
def certificate : Hex.Nat.PrimeCert := cert512
theorem result : Nat.Prime prime512 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := cert512) (by decide +kernel)
#print axioms result
end HexPrimalityMathlib.ProofProbe
