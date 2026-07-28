/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.ProofProbe.Generated
public meta import HexRCF.ProofProbe.Generated

public section
/-! Elaboration of the pre-generated reflected input and certificate literal. -/

namespace Hex.RCF.ProofProbe.Degree10

def input : Sentence := rcfDegree10Sentence
def certificate : Certificate := rcfDegree10Certificate

end Hex.RCF.ProofProbe.Degree10
