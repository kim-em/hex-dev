/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.ProofProbe.Generated
public meta import HexRCF.ProofProbe.Generated

public section
/-! An expensive same-module null control for fresh-build calibration. -/

namespace Hex.RCF.ProofProbe.Control

theorem left : rcfDegree50Goal := by
  rcf

theorem right : rcfDegree50Goal := by
  rcf

theorem result : rcfDegree50Goal ∧ rcfDegree50Goal := ⟨left, right⟩

/-- info: 'Hex.RCF.ProofProbe.Control.result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result

-- The sweep harness parses this unguarded copy from Lake's captured output.
#print axioms result

end Hex.RCF.ProofProbe.Control
