/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.AlgebraicCells
public section
open Hex Hex.RealClosure Hex.RCF.RealCoefficients
namespace Hex.RCF.SourceAcceptanceTests

/-- Construct acceptance from an actual produced packet through ordinary
public imports, rather than assuming the existential predicate. -/
theorem empty (registry : BaseContext.Registry) :
    AlgebraicCells.accepts registry (fun i : Fin 0 => i.elim0)
      (fun i : Fin 0 => i.elim0) [] (.tt : RealFormula.QF 1) .forallReal := by
  unfold AlgebraicCells.accepts
  obtain ⟨sources, shared, packet, produced, accepted⟩ :=
    AlgebraicCells.build_complete registry (fun i : Fin 0 => i.elim0)
      (fun i : Fin 0 => i.elim0) [] (.tt : RealFormula.QF 1) (by simp)
  obtain ⟨verdict, checked, meaning⟩ := accepted .forallReal
  have truth : verdict = true := meaning.mpr (by intro x; trivial)
  exact ⟨⟨sources, shared, packet⟩, produced, by simpa only [truth] using checked⟩

/-- info: 'Hex.RCF.SourceAcceptanceTests.empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms empty

end Hex.RCF.SourceAcceptanceTests
