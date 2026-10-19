/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.SelectedRoot.Data
import HexRCF.RealCoefficients.CellRead
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Schema
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
abbrev parent := Data.parent
noncomputable def original : Model parent ℝ := Data.original
def values : Fin 1 → parent.Value := fun _ => Data.alpha
def atom : RealFormula.Poly 2 := MvPoly.X 1 ^ 2 - MvPoly.X 0
def formula : QF 2 := .and (.atom ⟨atom, .ge⟩)
  (.and (.atom ⟨atom, .le⟩) (.atom ⟨0, .eq⟩))
def polynomial := RepresentationSpecialize.polynomial values atom

theorem coefficient : original.value (values 0) = Real.sqrt 2 := by
  exact Data.alpha_value
#print axioms coefficient
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Schema
