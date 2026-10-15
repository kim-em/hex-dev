/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellRequestedConformance
namespace Hex.RCF.RealCoefficients.CellRequestedStress
open Hex Hex.RealFormula CellRequestedConformance
/-- Four distinct boundaries exercise the full union of domain and equation roots.
Run explicitly with `lake build HexRCFCellRequestedStress`. -/
#eval (show IO Unit from do
  let x : RealFormula.Poly 2 := MvPoly.X 1
  let guards : QF 2 := .and (.atom ⟨x-1,.gt⟩) (.atom ⟨2-x,.ge⟩)
  test (.and guards equation) 4 true false
  IO.println "four-boundary domain/equation union retains all sections, sectors and strict verdicts")
end Hex.RCF.RealCoefficients.CellRequestedStress
