/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.RealFormula

public section
namespace Hex.RCF.RealFormulaProbe

@[expose] def cubic : Sentence := .existsIoc (Dyadic.ofInt 1) (Dyadic.ofInt 2)
  (.atom ⟨DensePoly.ofCoeffs #[(-1 : Int), -1, 0, 1], .eq⟩)

end Hex.RCF.RealFormulaProbe
