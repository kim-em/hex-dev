/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRootsTheory

public section

/-! Check the shared real instance and its generic odd-root API through the umbrella. -/

namespace HexRealRootsTheory.ProofProbe

theorem realClosed : IsRealClosed ℝ := inferInstance

theorem oddRoot (p : Polynomial ℝ) (hp : Odd p.natDegree) : ∃ x, p.IsRoot x :=
  IsRealClosed.exists_isRoot_of_odd_natDegree hp

/-- info: 'HexRealRootsTheory.ProofProbe.realClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms realClosed
/-- info: 'HexRealRootsTheory.ProofProbe.oddRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oddRoot


end HexRealRootsTheory.ProofProbe
