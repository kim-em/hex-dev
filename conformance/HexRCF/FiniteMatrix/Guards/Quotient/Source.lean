/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Quotient.Records
open Hex Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Hex.RCF.RealCoefficients Hex.RCF.RealCoefficients.FiniteMatrixTests
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Source
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

def values (_ : Fin 1) : Element FiniteTower.first := Reader.entry.value

def formula : RealFormula.QF 2 :=
  .and (.atom ⟨MvPoly.X 1 ^ 2 - MvPoly.X 0 + 1, .eq⟩)
    (.and (.atom ⟨1 - MvPoly.X 1, .lt⟩) (.atom ⟨MvPoly.X 1 - 2, .lt⟩))

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

def program (entries : List (Packing FiniteTower.first)) : Bool :=
  Decidable.decide (queries entries = Guards.Schema.queries entries)
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Source

namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Source
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
theorem computed : program Records.entries = true := by decide +kernel
open Lean Meta in
run_meta do
  let type ← inferType (mkConst ``computed)
  Hex.RCF.SelectedRootTests.KernelCheck.addChecked
    `Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Source.queryDecision type
    (← mkDecideProof type) #[``Hex.SignDet.Descriptor.validate, ``Hex.SignDet.Descriptor.ofReplay?]
    #[``queries]
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Source
