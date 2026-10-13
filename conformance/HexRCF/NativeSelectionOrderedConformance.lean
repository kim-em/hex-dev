/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.NativeSelection
import HexRCF.RealCoefficients.Samples
import HexRCF.NativeSelectionLiterals
import HexRealClosure.RootReplay
import HexMvPoly.Basic
import HexPolyZ.IntegerPolynomial
import HexSignDet.Thom
open Hex Hex.RealClosure Hex.RealFormula
open Hex.RCF.RealCoefficients
namespace Hex.RCF.RealCoefficients.NativeSelectionOrderedConformance
open SignDet
open scoped Hex
private def root? := Algebraic.RootReplay.readDescriptor ValueCodec.rat ValueCodec.nat
  Hex.Sturm.orderSign 7 NativeSelectionLiterals.subject NativeSelectionLiterals.graph
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 32768 in
private theorem accepted : root?.toOption.isSome = true := by decide +kernel
private def root : Root 7 := root?.toOption.get accepted
set_option maxRecDepth 32768 in
private theorem subject : root.raw =
    ⟨7, #p[-2,0,1], .finite (7/5), .finite (3/2), [1,2], [1,1]⟩ := by decide +kernel

def selection : RealFormula.QF 1 := NativeSelection.selection 0 root.raw

/-- The owner constraints retain head, both derivatives and strict endpoints
in precisely the frozen subject order. -/
theorem ordered_constraints : root.raw.constraints =
    [#p[-2,0,1], #p[0,2], #p[2], #p[-(7/5),1], #p[-(3/2),1]] := by
  rw [subject]
  decide +kernel

theorem ordered_signs : root.raw.constraintSigns = [0,1,1,1,-1] := by
  rw [subject]
  rfl

/-- info: '_private.HexRCF.NativeSelectionOrderedConformance.0.Hex.RCF.RealCoefficients.NativeSelectionOrderedConformance.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted
/-- info: '_private.HexRCF.NativeSelectionOrderedConformance.0.Hex.RCF.RealCoefficients.NativeSelectionOrderedConformance.subject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms subject
/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionOrderedConformance.ordered_constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ordered_constraints
/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionOrderedConformance.ordered_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ordered_signs

#guard selection ==
    .and (.atom ⟨MvPoly.X 0 ^ 2 - 2, .eq⟩)
      (.and (.atom ⟨2 * MvPoly.X 0, .gt⟩)
        (.and (.atom ⟨2, .gt⟩)
          (.and (.atom ⟨5 * MvPoly.X 0 - 7, .gt⟩)
            (.and (.atom ⟨2 * MvPoly.X 0 - 3, .lt⟩) .tt))))

theorem identity (coordinates : Fin 1 → ℝ) :
    selection.toProp coordinates ↔ coordinates 0 = root.real :=
  NativeSelection.identity root 0 coordinates

theorem selected : selection.toProp (fun _ => root.real) :=
  NativeSelection.selected root

/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionOrderedConformance.identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms identity
/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionOrderedConformance.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selected

#guard root?.toOption.isSome
#guard Samples.Row.eval selection [0,1,1,1,-1] == some true
#guard (Samples.Row.eval selection [0,1,1,1]).isNone
#guard Samples.Row.eval selection [0,1,1,1,1] == some false
end Hex.RCF.RealCoefficients.NativeSelectionOrderedConformance
