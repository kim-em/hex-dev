/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealFormulaMathlib.ProofProbe.Support
public meta import HexRealFormulaMathlib.ProofProbe.Support

public section
namespace Hex.RealFormula.ProofProbe

real_formula_probe alternation :
  ∀ a : ℝ, ((∃ x : ℝ, x ^ 2 + a * x < 0) ↔ (∀ x : ℝ, x ≥ a → x ^ 2 ≥ a ^ 2))
#print axioms alternation

end Hex.RealFormula.ProofProbe
