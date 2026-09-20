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

def scopedInput : Scoped 1 := .not (.iff
  (.quant .existsReal (.matrix (.atom ⟨MvPoly.X 0 * MvPoly.X 1, .lt⟩)))
  (.quant .forallReal (.matrix (.atom ⟨MvPoly.X 1 ^ 2 - MvPoly.X 0, .ge⟩))))

theorem normalization (ρ : Fin 1 → ℝ) :
    scopedInput.toPrenex.toProp ρ ↔ scopedInput.toProp ρ := scopedInput.toPrenex_correct ρ
#print axioms normalization

end Hex.RealFormula.ProofProbe
