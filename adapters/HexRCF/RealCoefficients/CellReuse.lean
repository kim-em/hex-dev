/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellReplay
public import HexRCF.RealCoefficients.RowOperations
public section
namespace Hex.RCF.RealCoefficients.CellReplay.Evidence
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable {p : DensePoly parent.Value} {roots : RootReplay.Result p .negInf .posInf}
variable {values : Fin n → parent.Value} {before after : QF (n+1)}

/-- Retain checked cell data when changing only the comparison/Boolean formula.
The complete ordered specialized polynomial list must be equal, including
zero, repeated and domain-guard occurrences. Source quotation still checks the
new original goal and every original divisor independently. -/
@[expose] def changeFormula
    (same : RepresentationSpecialize.prepare values before =
      RepresentationSpecialize.prepare values after)
    (source : Evidence roots values before) : Evidence roots values after :=
  ⟨fun i => RowOperations.retarget parent.sign parent.signature rfl same (source.sections i),
    source.sectors,
    fun cut => ⟨(source.sectorRows cut).root, (source.sectorRows cut).bound,
      RowOperations.retarget parent.sign parent.signature rfl same (source.sectorRows cut).signs⟩⟩

/-- Every section and sector retains its original complete stored sign row. -/
theorem changeFormula_row
    (same : RepresentationSpecialize.prepare values before =
      RepresentationSpecialize.prepare values after)
    (source : Evidence roots values before) (cell : Cell roots.roots.length) :
    (changeFormula same source).row cell = source.row cell := by
  cases cell <;> rfl
end Hex.RCF.RealCoefficients.CellReplay.Evidence
