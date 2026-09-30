/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.ProofProbe.Inputs

public section

namespace Hex.SignDetMathlib.ProofProbe.D5.Literal
open Hex.SignDet Hex.SignDetMathlib.ProofProbe.Inputs

@[expose] def evidence : Dag Rat Nat := graph 5

end Hex.SignDetMathlib.ProofProbe.D5.Literal
