/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.SourceSelection
import HexRCF.NativeSelectionLiterals
import HexRealClosure.RootReplay
import HexSignDet.Thom
import HexPolyZ.IntegerPolynomial

/-! Oracle: the existing frozen count-one positive square-root descriptor.
Production is not called. This construction module exposes its checked root
and constraints to the separate source-selection consumer. The construction
module uses non-module imports to expose the existing private fixture bodies. -/
namespace Hex.RCF.SourceSelectionCases
open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open scoped Hex

def reader := Algebraic.RootReplay.readDescriptor ValueCodec.rat ValueCodec.nat
  Hex.Sturm.orderSign 7 RealCoefficients.NativeSelectionLiterals.subject
    RealCoefficients.NativeSelectionLiterals.graph
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 32768 in
theorem accepted : reader.toOption.isSome = true := by decide +kernel
def root : Root 7 := reader.toOption.get accepted
set_option maxRecDepth 32768 in
theorem subject : root.raw =
    ⟨7, #p[-2,0,1], .finite (7/5), .finite (3/2), [1,2], [1,1]⟩ := by decide +kernel

/-- The selected value is the positive conjugate. -/
theorem selected : root.real = Real.sqrt 2 := by
  have constraints := (NativeSelection.identity root (0 : Fin 1) (fun _ => root.real)).mpr rfl
  have ordered : root.raw.constraints =
      [#p[-2,0,1], #p[0,2], #p[2], #p[-(7/5),1], #p[-(3/2),1]] := by
    rw [subject]
    decide +kernel
  have signs : root.raw.constraintSigns = [0,1,1,1,-1] := by rw [subject]; rfl
  rw [NativeSelection.selection, ordered, signs] at constraints
  change (NativeSelection.atom (0 : Fin 1) #p[-2,0,1] .eq).toProp (fun _ => root.real) ∧
    (NativeSelection.atom (0 : Fin 1) #p[0,2] .gt).toProp (fun _ => root.real) ∧ _ at constraints
  have polynomial := (NativeSelection.atom_correct (0 : Fin 1) #p[-2,0,1] .eq _).mp constraints.1
  have derivative := (NativeSelection.atom_correct (0 : Fin 1) #p[0,2] .gt _).mp constraints.2.1
  norm_num [RealFormula.Cmp.toProp, realPoly, HexPolyTheory.Interpret.interpret_map, DensePoly.Interpret.map_ofCoeffs,
    HexPolyTheory.toPolynomial_ofCoeffs, Finset.sum_range_succ, ratCast] at polynomial derivative
  have positive : 0 < root.real := by linarith
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]

end Hex.RCF.SourceSelectionCases
