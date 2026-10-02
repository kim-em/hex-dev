/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.PartitionCongr
import all HexGraphIso.Nauty.Sparse.LoopRel
import all HexGraphIso.Nauty.Sparse.SortStack

public section

namespace Hex.GraphIso.Nauty.Sparse.Sort

private noncomputable def step (keys : Array Nat) (_ : Nat)
    (s : Array Nat × List (Nat × Nat)) : Id (ForInStep (Array Nat × List (Nat × Nat))) :=
  match s.2 with
  | [] => .done s
  | (lo, size) :: rest =>
    if size < 11 then .yield (insertion s.1 keys lo size, rest)
    else
      let r := partition s.1 keys lo size
      .yield (r.1, children lo size r.2.1 r.2.2 rest)

private def Valid (y z : Array Nat) (start last : Nat)
    (s : Array Nat × List (Nat × Nat)) : Prop :=
  Agree y z start last s.1 ∧ ∀ p ∈ s.2, start ≤ p.1 ∧ p.1 + p.2 ≤ last

private theorem step_congr (h : Valid y z start last s) (i : Nat) :
    step y i s = step z i s ∧
      Loop.Preserves (Valid y z start last) (Valid y z start last) (step y i s) := by
  rcases s with ⟨a, stack⟩
  cases stack with
  | nil => exact ⟨rfl, h⟩
  | cons p rest =>
    rcases p with ⟨lo, size⟩
    have hp := h.2 (lo, size) (by simp)
    have hb : lo + size ≤ a.size := by
      have ha : last ≤ a.size := h.1.bound
      omega
    have hk := h.1.mono hp.1 hp.2
    have hs : ∀ p ∈ rest, start ≤ p.1 ∧ p.1 + p.2 ≤ last :=
      fun p hm => h.2 p (by simp [hm])
    dsimp only [step]
    split
    · have he := insertion_congr hk
      refine ⟨congrArg (fun out => ForInStep.yield (out, rest)) he, ?_⟩
      refine ⟨h.1.window ⟨insertion_perm a y lo size hb, ?_⟩, hs⟩
      intro q hq
      exact insertion_outside a y lo size q (by omega)
    · have he := partition_congr hk (by omega)
      refine ⟨congrArg (fun r : Array Nat × Nat × Nat =>
        ForInStep.yield (r.1, children lo size r.2.1 r.2.2 rest)) he, ?_⟩
      have hr := partition_proper a y lo size hb (by omega)
      have bounds := partition_bounds a y lo size
      refine ⟨h.1.window ⟨partition_perm a y lo size, fun q hq => hr.2 q (by omega)⟩, ?_⟩
      intro p hm
      rcases children_inside lo size _ _ rest bounds.1 bounds.2 p hm with hm | hc
      · exact hs p hm
      · constructor <;> omega

private theorem indirect_eq (x y : Array Nat) (start len : Nat) :
    indirect x y start len =
      (forIn (m := Id) [0:2 * len + 1]
        (x, if len > 1 then [(start, len)] else []) (step y)).1 := by
  unfold indirect
  simp only [Id.run, bind, pure]
  congr 2
  funext i s
  rcases s with ⟨a, stack⟩
  cases stack with
  | nil => rfl
  | cons p rest =>
    rcases p with ⟨lo, size⟩
    dsimp only [step]
    split
    · rfl
    · simp only [children]
      split <;> split <;> split <;> rfl

/-- The full executed indirect sort returns literally equal arrays when
the key arrays agree on the requested segment. The proof follows the
actual bounded stack, including its exact push and tie order. -/
theorem indirect_congr (h : Agree y z start (start + len) x) :
    indirect x y start len = indirect x z start len := by
  have hr := Loop.range_congr 0 (2 * len + 1) (step y) (step z)
    (Valid y z start (start + len)) (Valid y z start (start + len)) (fun _ h => h)
    (fun i _ _ s hs => step_congr hs i)
    (show Valid y z start (start + len) (x, if len > 1 then [(start, len)] else []) from by
      refine ⟨h, ?_⟩
      split <;> simp)
  rw [indirect_eq, indirect_eq]
  exact congrArg Prod.fst hr.1

end Hex.GraphIso.Nauty.Sparse.Sort
