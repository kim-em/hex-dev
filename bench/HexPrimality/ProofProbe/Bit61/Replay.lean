/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.ProofProbe.Support

public section

namespace Hex.PrimalityProofProbe.Bit61

open Hex.Nat Hex.PrimalityBench

def input : Nat := primalityInput61
def certificate : PrimeCert := primalityCert61

theorem result : Prime primalityInput61 :=
  prime_of_checkPrimeAt (c := primalityCert61) (by decide +kernel)

#print axioms result

end Hex.PrimalityProofProbe.Bit61
