/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.ProofProbe.Generated
public meta import HexRCF.ProofProbe.Generated

public section
/-! End-to-end proof through the public rcf tactic. -/

namespace Hex.RCF.ProofProbe.Quadratic

theorem result : rcfQuadraticGoal := by
  rcf

/-- info: 'Hex.RCF.ProofProbe.Quadratic.result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result

-- The sweep harness parses this unguarded copy from Lake's captured output.
#print axioms result

end Hex.RCF.ProofProbe.Quadratic
