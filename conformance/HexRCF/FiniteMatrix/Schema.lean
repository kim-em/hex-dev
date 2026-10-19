/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import KernelReplay.FiniteJoint
public import HexRCF.RealCoefficients.RepresentationSpecialize
public section
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Schema
open Hex Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
/-- The exact shared frontend orientation of the three source atoms. -/
@[expose] def formula : RealFormula.QF 2 :=
  .and (.atom ⟨MvPoly.X 1 ^ 2 - MvPoly.X 0, .eq⟩)
    (.and (.atom ⟨1 - MvPoly.X 1, .lt⟩) (.atom ⟨MvPoly.X 1 - 2, .lt⟩))
@[expose] def values : Fin 1 → Element FiniteTower.first := fun _ => FiniteTower.generator
/-- Specialization uses only supplied coefficient packing records. -/
@[expose] def queries (entries : List (Packing FiniteTower.first)) :=
  @RepresentationSpecialize.prepare (Element FiniteTower.first) _ _
    (Element.replayOne inferInstance rfl entries) (Element.replayAdd inferInstance rfl entries)
    (Element.replayMul inferInstance inferInstance rfl rfl entries)
    (Element.replayNeg (inferInstance : Sub Rat) rfl entries)
    (Element.replayNatCast inferInstance rfl entries) _ values formula

theorem queries_eq (entries : List (Packing FiniteTower.first)) :
    queries entries = RepresentationSpecialize.prepare values formula := by
  unfold queries
  erw [Element.replayOne_eq inferInstance rfl entries,
    Element.replayAdd_eq inferInstance rfl entries,
    Element.replayMul_eq inferInstance inferInstance rfl rfl entries,
    Element.replayNeg_eq (inferInstance : Sub Rat) rfl entries,
    Element.replayNatCast_eq inferInstance rfl entries]

@[expose] def guard (entries : List (Packing FiniteTower.first)) : Element FiniteTower.first :=
  @One.one _ (Element.replayOne inferInstance rfl entries)
@[expose] def guards (guarded : Bool) (entries : List (Packing FiniteTower.first)) :=
  if guarded then [guard entries] else []
@[expose] def allQueries (guarded : Bool) (entries : List (Packing FiniteTower.first)) :=
  (guards guarded entries).map DensePoly.C ++ queries entries
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Schema
