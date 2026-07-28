/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.ProofProbe.Generated
public meta import HexRCF.ProofProbe.Generated

public section
/-! Kernel replay and soundness proof for the pre-generated literal certificate. -/

namespace Hex.RCF.ProofProbe.Degree10

def input : Sentence := rcfDegree10Sentence
def certificate : Certificate := rcfDegree10Certificate

theorem result : input.toProp :=
  rcf_replay% input with certificate

/-- info: 'Hex.RCF.ProofProbe.Degree10.result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result

-- The sweep harness parses this unguarded copy from Lake's captured output.
#print axioms result

end Hex.RCF.ProofProbe.Degree10
