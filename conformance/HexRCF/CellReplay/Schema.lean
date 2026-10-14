/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.RepresentationCells
import HexRCF.RootReplayConformance
import HexRealClosure.TowerContext
import HexRealClosure.BaseContext
import HexRealClosure.NumberField

namespace Hex.RCF.RealCoefficients.CellReplayTests.Schema
open Hex Hex.RealFormula Hex.RCF.SelectedRootTests
open RootReplayConformance HexPolyMathlib.Interpret
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

def values : Fin 0 → Data.base.Value := Fin.elim0
def atom : RealFormula.Poly 1 := MvPoly.X 0 ^ 2 - 2
def formula : QF 1 := .and (.atom ⟨atom, .ge⟩)
  (.and (.atom ⟨atom, .le⟩) (.atom ⟨0, .eq⟩))
def cert : RadicalCert Data.base.Value Hex.RealClosure.Tower.Signature :=
  ⟨Data.base.signature, polynomial, polynomial, polynomial, 1⟩

theorem radical_checked : cert.check Data.base.signature
    (RepresentationCarrier.product (RepresentationSpecialize.prepare values formula)) = true := by
  decide +kernel

theorem repeated_coverage :
    interpret Data.rational.value Data.rational.zero_iff
      (RepresentationSpecialize.polynomial values atom) = 0 ∨
      ∀ x, (interpret Data.rational.value Data.rational.zero_iff
        (RepresentationSpecialize.polynomial values atom)).IsRoot x →
        ∃ i, RootCells.points wholeResult Data.rational i = x := by
  exact RepresentationCells.atom_coverage values formula cert radical_checked wholeResult
    Data.rational atom (by simp [formula, RealFormula.QF.polys, RealFormula.QF.polys.go])

theorem zero_coverage :
    interpret Data.rational.value Data.rational.zero_iff
      (RepresentationSpecialize.polynomial values (0 : RealFormula.Poly 1)) = 0 ∨
      ∀ x, (interpret Data.rational.value Data.rational.zero_iff
        (RepresentationSpecialize.polynomial values (0 : RealFormula.Poly 1))).IsRoot x →
        ∃ i, RootCells.points wholeResult Data.rational i = x := by
  exact RepresentationCells.atom_coverage values formula cert radical_checked wholeResult
    Data.rational 0 (by simp [formula, RealFormula.QF.polys, RealFormula.QF.polys.go])

/-- A substituted core omitting both real roots fails the identity check. -/
theorem dropped_root : ({ cert with core := 1 }).check Data.base.signature
    (RepresentationCarrier.product (RepresentationSpecialize.prepare values formula)) = false := by
  decide +kernel

#print axioms repeated_coverage
#print axioms zero_coverage
end Hex.RCF.RealCoefficients.CellReplayTests.Schema
