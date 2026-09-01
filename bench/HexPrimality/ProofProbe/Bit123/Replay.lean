/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.ProofProbe.Support

public section

namespace Hex.PrimalityProofProbe.Bit123

open Hex.Nat Hex.PrimalityBench

def input : Nat := primalityInput123
def certificate : PrimeCert := primalityCert123

theorem result : Prime primalityInput123 :=
  prime_of_checkPrimeAt (c := primalityCert123) (by decide +kernel)

#print axioms result

end Hex.PrimalityProofProbe.Bit123
