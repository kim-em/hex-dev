/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.ProofProbe.Support

public section

namespace Hex.PrimalityProofProbe.Bit256

open Hex.Nat Hex.PrimalityBench

def input : Nat := primalityInput256
def certificate : PrimeCert := primalityCert256

end Hex.PrimalityProofProbe.Bit256
