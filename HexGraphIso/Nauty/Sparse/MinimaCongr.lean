/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountParts
public import HexGraphIso.Nauty.Sparse.IndirectCongr
import all HexGraphIso.Nauty.Sparse.LoopRel

public section

namespace Hex.GraphIso.Nauty.Sparse.CountSort

/-- The initial equal-count scan has the same stopping position under
local key agreement, including exhaustion at the exclusive cell end. -/
theorem firstRun_congr (h : Sort.Agree y z first last lab) (hf : first < last) :
    firstRun lab y first last = firstRun lab z first last ∧
      first < firstRun lab y first last ∧ firstRun lab y first last ≤ last := by
  let P (i v : Nat) := v = i ∧ first < v ∧ v ≤ last
  let Q (v : Nat) := first < v ∧ v ≤ last
  have hk := h.keys first (Nat.le_refl _) hf
  unfold firstRun
  simp only [Id.run, bind, pure]
  apply Loop.indexed_congr (first + 1) last _ _ P Q (fun i v hv => hv.2) ?_
    ⟨rfl, by omega, by omega⟩
  intro i hi hb v hv
  have he := h.keys v (by have := hv.2; omega) (by have := hv.1; omega)
  constructor
  · rw [he, hk]
  · split <;> dsimp only [Loop.Preserves, P, Q]
    · exact hv.2
    · exact ⟨by have := hv.1; omega, by omega, by have := hv.1; omega⟩

/-- The literal three-way insertion, including aliasing reads after the
first write, observes only keys of vertices in the original cell. Its
returned cuts, minima and complete label array agree. -/
theorem minima_congr (h : Sort.Agree y z first last lab)
    (hb : first < begin ∧ begin ≤ last) (cap : Nat) :
    minima lab y cap first last begin = minima lab z cap first last begin ∧
      let r := minima lab y cap first last begin
      Sort.Agree y z first last r.2.2.2.2 ∧ first < r.2.1 ∧
        r.2.1 ≤ r.2.2.2.1 ∧ r.2.2.2.1 ≤ last := by
  let P (j : Nat) (r : Nat × Nat × Nat × Nat × Array Nat) :=
    Sort.Agree y z first last r.2.2.2.2 ∧ first < r.2.1 ∧
      r.2.1 ≤ r.2.2.2.1 ∧ r.2.2.2.1 ≤ j ∧ j ≤ last
  let Q (r : Nat × Nat × Nat × Nat × Array Nat) :=
    Sort.Agree y z first last r.2.2.2.2 ∧ first < r.2.1 ∧
      r.2.1 ≤ r.2.2.2.1 ∧ r.2.2.2.1 ≤ last
  have hk := h.keys first (Nat.le_refl _) (by omega)
  unfold minima
  simp only [Id.run, bind, pure]
  rw [← hk]
  apply Loop.indexed_congr begin last _ _ P Q
    (fun j r hr => ⟨hr.1, hr.2.1, hr.2.2.1, by have := hr.2.2.2; omega⟩) ?_
    (by dsimp only [P]; exact ⟨h, hb.1, Nat.le_refl _, Nat.le_refl _, hb.2⟩)
  intro j hj hj' a ha
  have bounds := ha.2
  have he := ha.1.keys j (by omega) hj'
  constructor
  · rw [he]
  · split
    · dsimp only [Loop.Preserves, P]
      have h1 := ha.1.write (ha.1.keys a.2.2.2.1 (by omega) (by omega)) j
      have h2 := h1.write (h1.keys a.2.1 (by omega) (by omega)) a.2.2.2.1
      exact ⟨h2.write he a.2.1, by omega, by omega, by omega, by omega⟩
    · split
      · dsimp only [Loop.Preserves, P]
        have h1 := ha.1.write (ha.1.keys a.2.2.2.1 (by omega) (by omega)) j
        exact ⟨h1.write he a.2.2.2.1, bounds.1, by omega, by omega, by omega⟩
      · split
        · dsimp only [Loop.Preserves, P]
          have h1 := ha.1.write (ha.1.keys a.2.1 (by omega) (by omega)) j
          have h2 := h1.write (h1.keys first (Nat.le_refl _) (by omega)) a.2.1
          exact ⟨h2.write he first, by omega, by omega, by omega, by omega⟩
        · split
          · dsimp only [Loop.Preserves, P]
            have h1 := ha.1.write (ha.1.keys a.2.1 (by omega) (by omega)) j
            exact ⟨h1.write he a.2.1, bounds.1, by omega, by omega, by omega⟩
          · dsimp only [Loop.Preserves, P]
            exact ⟨ha.1, bounds.1, bounds.2.1, by omega, by omega⟩

end Hex.GraphIso.Nauty.Sparse.CountSort
