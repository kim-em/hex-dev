/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Spec.Traced
import all HexGraphIso.Nauty.Spec.Traced

public import HexGraphIso.Nauty.Policy.MaxRules
import all HexGraphIso.Nauty.Policy.MaxRules
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxFrame
import all HexGraphIso.Nauty.Policy.FirstRun
import all HexGraphIso.Nauty.Policy.FirstEntry
import all HexGraphIso.Nauty.Policy.Partition
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.Maximum
import all HexGraphIso.Nauty.Policy.CodeState
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

namespace Max

/-- The actual coloured root, with no preceding refinement codes. -/
def root (G : Colored n k) : Frame n :=
  ⟨1, (initialPartition G).2.length, [], initial n (initialPartition G).1 (initialPartition G).2⟩

/-- The root supplies every input of the conditional maximum theorem. -/
theorem root_input (G : Colored n k) (hn0 : 0 < n) :
    NodeInput G { g := rowsOf G } 100 (n + 2) true (root G) [] [] (fun _ => none) := by
  refine ⟨⟨Nat.le_refl _, hn0, rfl, initial_ok G hn0⟩, by change n + 1 ≤ 1 + (n + 2); omega,
    ?_, Scope.root G { g := rowsOf G } 100 [] _, ?_, (by intro h; change 0 < 0 at h; omega)⟩
  · change FirstPre G { g := rowsOf G } 1 (initialPartition G).2.length
        (initial n (initialPartition G).1 (initialPartition G).2) ∧ _
    refine ⟨initial_firstPre G hn0, rfl, rfl, rfl, rfl, Array.size_replicate, ?_, ?_,
      by change 0 < 1; omega, by change 0 < 1; omega⟩
    · intro i hi
      cases hi
    · intro code hc
      change code ∈ ([] : List Nat) at hc
      cases hc
  · intro h
    change 1 < 1 at h
    omega

/-- The frozen root's subtree is precisely the nonempty specification. -/
theorem root_key (G : Colored n k) (hn0 : 0 < n) :
    (root G).key { g := rowsOf G } 100 = canonSpecKey G := by
  simp only [Frame.key, root, initial, prefixKey_nil, Nat.add_sub_cancel,
    canonSpecKey, canonSpec, beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hn0), Bool.false_eq_true, ↓reduceIte]

/-- The conditional local rules determine the engine's final incumbent.
No root invariant or final-state identification is an assumed parameter. -/
theorem root_best (G : Colored n k) (hn0 : 0 < n) (rules : Rules G 100) :
    (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).2.best
      { g := rowsOf G } = some (canonSpecKey G) := by
  have h := Generic.node_calls rules.calls true (n + 2) 1 (initialPartition G).2.length
    (initial n (initialPartition G).1 (initialPartition G).2) trivial
  have hr := h.1 [] [] [] (fun _ => none) (root_input G hn0)
  rw [← node_eq_generic] at hr
  have hrun : runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2 =
      node true { g := rowsOf G } (n + 2) 100 (n + 2) 1 (initialPartition G).2.length
        (initial n (initialPartition G).1 (initialPartition G).2) := by
    rw [runState, ite_eq_right (by simpa using Nat.ne_of_gt hn0)]
  rw [← hrun] at hr
  have hbest := hr.root (runState_noFuel G)
  change _ = some ((root G).key { g := rowsOf G } 100) at hbest
  rwa [root_key G hn0] at hbest

/-- The local maximum rules imply exactly the public nonempty key equality,
with the traced search replaced by the structured engine. -/
theorem key_eq (G : Colored n k) (hn0 : 0 < n) (rules : Rules G 100) :
    canonSpecKey G = Nauty.tracedKey G := by
  let out := (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).2
  have hb := root_best G hn0 rules
  change out.best { g := rowsOf G } = some (canonSpecKey G) at hb
  have hn : out.canonlevel ≠ 0 := by
    intro he
    simp only [Search.best, he, ↓reduceIte] at hb
    cases hb
  rw [Search.best, ite_eq_right hn] at hb
  have hk := (Option.some.inj hb).symm
  simpa only [Nauty.tracedKey, runColoredTraced, runTraced, finish,
    beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hn0), Bool.false_eq_true, ↓reduceIte, out] using hk

/-- The empty specification has no refinement code. -/
theorem spec_zero (G : Colored 0 k) : canonSpecKey G = ⟨[], []⟩ := rfl

/-- The empty trace still appends the sentinel, so its certificate uses
the separate empty-graph case rather than nonempty key equality. -/
theorem traced_zero (G : Colored 0 k) : Nauty.tracedKey G = ⟨[codeSentinel], []⟩ := by
  simp [Nauty.tracedKey, runColoredTraced, runTraced, finish, runState, leafRows]

end Max
end Hex.GraphIso.Nauty
