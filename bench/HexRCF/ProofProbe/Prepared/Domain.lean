/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.Prepared.Support
public section

namespace Hex.RCF.ProofProbe.Prepared.Domain
open Hex.RCF.ProofProbe.Prepared
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

theorem goal : ∃ x ∈ Set.Ioc (1 : ℝ) 2, x ^ 2 = Real.sqrt 2 := by prepared_rcf

/-- info: 'Hex.RCF.ProofProbe.Prepared.Domain.goal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms goal

end Hex.RCF.ProofProbe.Prepared.Domain
