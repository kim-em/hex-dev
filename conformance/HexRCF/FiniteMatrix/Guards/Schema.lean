/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Data
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema
open Hex Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Hex.RCF.RealCoefficients
def positive (entries : List (Packing FiniteTower.first)) : List (Element FiniteTower.first) :=
  let one := @One.one _ (Element.replayOne inferInstance rfl entries)
  [@Sub.sub _ (Element.replaySub inferInstance rfl entries) FiniteTower.generator one,
    @Neg.neg _ (Element.replayNeg (inferInstance : Sub Rat) rfl entries) one]
def guards (zero : Bool) (entries : List (Packing FiniteTower.first)) :=
  if zero then (0 : Element FiniteTower.first) :: (positive entries).tail else positive entries

/-- The source retains the closed zero quotient as a second coefficient. -/
def values (i : Fin 2) : Element FiniteTower.first :=
  if i.val = 0 then FiniteTower.generator else 0

def formula : RealFormula.QF 3 :=
  .and (.atom ⟨MvPoly.X 2 ^ 2 - (MvPoly.X 0 + MvPoly.X 1), .eq⟩)
    (.and (.atom ⟨1 - MvPoly.X 2, .lt⟩) (.atom ⟨MvPoly.X 2 - 2, .lt⟩))

def queries (entries : List (Packing FiniteTower.first)) :=
  @RepresentationSpecialize.prepare (Element FiniteTower.first) _ _
    (Element.replayOne inferInstance rfl entries) (Element.replayAdd inferInstance rfl entries)
    (Element.replayMul inferInstance inferInstance rfl rfl entries)
    (Element.replayNeg (inferInstance : Sub Rat) rfl entries)
    (Element.replayNatCast inferInstance rfl entries) _ values formula

def native := RepresentationSpecialize.prepare values formula

theorem queries_eq (entries : List (Packing FiniteTower.first)) : queries entries = native := by
  unfold queries native
  erw [Element.replayOne_eq inferInstance rfl entries,
    Element.replayAdd_eq inferInstance rfl entries,
    Element.replayMul_eq inferInstance inferInstance rfl rfl entries,
    Element.replayNeg_eq (inferInstance : Sub Rat) rfl entries,
    Element.replayNatCast_eq inferInstance rfl entries]
def allQueries (zero : Bool) (entries : List (Packing FiniteTower.first)) :=
  (guards zero entries).map DensePoly.C ++ queries entries
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema
