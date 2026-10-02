/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.PathFrame
import all HexGraphIso.Nauty.Equitable.Step

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A literal native child keeps every older singleton and its vertex. -/
theorem RefineSt.Ready.child_singleton {G : Hex.SparseGraph n} {level a : Nat} {s : RefineSt n}
    (h : RefineSt.Ready G level s) {tc len o : Nat}
    (hc : IsCell s.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len) (ho : o < len)
    (scratch : Scratch) (hs : Scratch.Bounded n scratch) (ha : IsCell s.ptn level a 1) :
    let out := s.child (.ofGraph G) level tc s.lab[tc + o]! scratch
    IsCell out.ptn (level + 1) a 1 ∧ out.lab[a]! = s.lab[a]! := by
  have hraw := h.spec.child h.equitable hc hb hn ho
  have hm := hraw.refine_singleton scratch hs (isCell_set_miss ha hc (by omega))
  refine ⟨hm.1, hm.2.trans ?_⟩
  apply breakout_misses_singleton
  · rw [h.spec.node.labSize]
    exact fun _ _ hi hj he => perm_injective h.spec.label hi hj he
  · rw [h.spec.node.labSize]
    omega
  · apply singleton_outside_cell ha hc ?_ ho
    intro he
    subst a
    rcases isCell_disjoint_or_eq ha hc with hleft | hright | he <;> omega

/-- Individualization creates a singleton holding the chosen vertex;
the actual cached refinement retains it at the target position. -/
theorem RefineSt.Ready.child_picked {G : Hex.SparseGraph n} {level : Nat} {s : RefineSt n}
    (h : RefineSt.Ready G level s) {tc len o : Nat}
    (hc : IsCell s.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len) (ho : o < len)
    (scratch : Scratch) (hs : Scratch.Bounded n scratch) :
    let out := s.child (.ofGraph G) level tc s.lab[tc + o]! scratch
    IsCell out.ptn (level + 1) tc 1 ∧ out.lab[tc]! = s.lab[tc + o]! := by
  have hraw := h.spec.child h.equitable hc hb hn ho
  have hm := hraw.refine_singleton scratch hs
    (isCell_breakout_target (by rw [h.spec.node.ptnSize]; omega) hc.2.1)
  refine ⟨hm.1, hm.2.trans ?_⟩
  apply breakout_at_target
  · rw [h.spec.node.labSize]
    exact fun _ _ hi hj he => perm_injective h.spec.label hi hj he
  · rw [h.spec.node.labSize]
    omega

/-- Every native descent keeps its entry singletons at their literal
positions, despite cached refinement and later individualizations. -/
theorem DescPath.singleton {G : Hex.SparseGraph n} {base last a : Nat} {root leaf : RefineSt n}
    {path : List (Nat × Nat)} (h : DescPath G base root path last leaf)
    (hr : RefineSt.Ready G base root) (ha : IsCell root.ptn base a 1) :
    IsCell leaf.ptn last a 1 ∧ leaf.lab[a]! = root.lab[a]! := by
  induction h with
  | refl => exact ⟨ha, rfl⟩
  | step tc len o scratch hc hb hn ho hs tail ih =>
    obtain ⟨hcell, hvertex⟩ := hr.child_singleton hc hb hn ho scratch hs ha
    obtain ⟨hend, he⟩ := ih (hr.child hc hb hn ho scratch hs) hcell
    exact ⟨hend, he.trans hvertex⟩

/-- A terminal native labelling records the first chosen vertex at its
target position. -/
theorem DescPath.picked {G : Hex.SparseGraph n} {base last tc o : Nat} {root leaf : RefineSt n}
    {path : List (Nat × Nat)} (h : DescPath G base root ((tc, o) :: path) last leaf)
    (hr : RefineSt.Ready G base root) : leaf.lab[tc]! = root.lab[tc + o]! := by
  cases h with
  | step _ len _ scratch hc hb hn ho hs tail =>
    obtain ⟨hcell, hvertex⟩ := hr.child_picked hc hb hn ho scratch hs
    exact (tail.singleton (hr.child hc hb hn ho scratch hs) hcell).2.trans hvertex

end Hex.GraphIso.Nauty.Sparse
