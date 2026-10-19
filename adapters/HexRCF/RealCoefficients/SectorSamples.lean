/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RootCells
public import HexRCF.RealCoefficients.BoundarySigns
public section
namespace Hex.RCF.RealCoefficients.SectorSamples
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable {p : DensePoly parent.Value}

/-- An ordinary point with selected-sign evidence at each adjacent root.
There is no boundary query at an infinite endpoint. -/
structure Sector (roots : RootReplay.Result p .negInf .posInf)
    (cut : Fin (roots.roots.length + 1)) where
  point : parent.Value
  left : (h : 0 < cut.val) → SelectedSigns
    (roots.roots.get ⟨cut.val - 1, by have := cut.isLt; omega⟩) [Isolation.pointQuery point]
  leftSign : ∀ h, (left h).value = -1
  right : (h : cut.val < roots.roots.length) → SelectedSigns
    (roots.roots.get ⟨cut.val, h⟩) [Isolation.pointQuery point]
  rightSign : ∀ h, (right h).value = 1

/-- Checked signs place the same ordinary point strictly between its actual
adjacent roots, including empty tables and either unbounded sector. -/
theorem Sector.inside {roots : RootReplay.Result p .negInf .posInf}
    {cut : Fin (roots.roots.length + 1)} (sector : Sector roots cut) (model : Model parent ℝ) :
    Cell.Region (RootCells.points roots model) (.open cut) (model.value sector.point) := by
  by_cases empty : roots.roots.length = 0
  · simp only [Cell.Region, empty, dite_true]
  · by_cases first : cut.val = 0
    · have bound : cut.val < roots.roots.length := by omega
      have upper := BoundarySigns.above model _ sector.point (sector.right bound) (sector.rightSign bound)
      simpa only [Cell.Region, empty, dite_false, first, dite_true, RootCells.points] using upper
    · have positive : 0 < cut.val := by omega
      have lower := BoundarySigns.below model _ sector.point (sector.left positive) (sector.leftSign positive)
      by_cases last : cut.val = roots.roots.length
      · simpa only [Cell.Region, empty, dite_false, first, last, dite_true, RootCells.points] using lower
      · have bound : cut.val < roots.roots.length := by have := cut.isLt; omega
        have upper := BoundarySigns.above model _ sector.point (sector.right bound) (sector.rightSign bound)
        simpa only [Cell.Region, empty, first, last, dite_false, RootCells.points] using And.intro lower upper
end Hex.RCF.RealCoefficients.SectorSamples
