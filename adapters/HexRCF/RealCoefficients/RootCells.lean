/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RootReplay
public import HexRCF.Regions

public section
namespace Hex.RCF.RealCoefficients.RootCells
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet HexPolyTheory.Interpret
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable {p : DensePoly parent.Value}
variable (result : RootReplay.Result p .negInf .posInf) (original : Model parent ℝ)

@[expose] noncomputable def points (i : Fin result.roots.length) : ℝ :=
  (result.roots.get i).root original.value original.zero_iff original.one original.add
    original.sub original.mul original.nat original.sign

theorem ordered : StrictMono (points result original) := by
  intro i j h
  have sorted := List.pairwise_map.mp (result.ordered original)
  exact sorted.rel_get_of_lt h

include result in
/-- Accepted full replay entails a nonzero head, including empty root lists. -/
theorem nonzero : interpret original.value original.zero_iff p ≠ 0 := by
  exact (result.domain original).1

/-- Every carrier root occurs at one of the cell-defining points. -/
theorem complete (x : ℝ) (root : (interpret original.value original.zero_iff p).IsRoot x) :
    ∃ i, points result original i = x := by
  have in_table : x ∈ result.values original := (result.coverage original).1 x |>.mp (by
    change x ∈ HexRealRootsTheory.Tarski.rootsIn _ .negInf .posInf
    rw [HexRealRootsTheory.Tarski.mem_rootsIn_iff _ (nonzero result original)]
    exact ⟨root, by simp⟩)
  obtain ⟨d, member, value⟩ := List.mem_map.mp in_table
  obtain ⟨i, same⟩ := List.mem_iff_get.mp member
  refine ⟨i, ?_⟩
  simpa only [points, same] using value
end Hex.RCF.RealCoefficients.RootCells
