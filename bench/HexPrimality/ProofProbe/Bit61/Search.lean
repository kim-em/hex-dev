/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.ProofProbe.Support
public meta import HexPrimality.ProofProbe.Support

public section

namespace Hex.PrimalityProofProbe.Bit61

open Hex.PrimalityBench

def input : Nat := primalityInput61

primality_search_probe bit61 : primalityInput61

end Hex.PrimalityProofProbe.Bit61
