/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountResult

public section

namespace Hex.GraphIso.Nauty.Sparse.CountTrace

/-- The completed part of a tail trace, expressed as a continuation for
the still-unprocessed runs. -/
structure Progress (distance : Bool) (first last : Nat) (s : RefineSt n)
    (lab : Array Nat) (k : Nat) (c : Control n) (pos : Option Nat) (big : Nat) : Prop where
  bounds : first ≤ k ∧ k < last
  finish : ∀ out, Tail distance lab s.hits first last k c pos big out →
    Result distance first last s lab out

theorem Progress.next (h : Progress distance first last s lab k c pos big)
    (hk : k + 1 < last)
    (hr : Index.Run lab s.hits (k + 1) (last - 1) (k + 1) b) :
    Progress distance first last s lab b (c.advance distance k s.hits[lab[k + 1]!]!)
      ((c.advance distance k s.hits[lab[k + 1]!]!).choose pos big (b - (k + 1) + 1)).1
      ((c.advance distance k s.hits[lab[k + 1]!]!).choose pos big (b - (k + 1) + 1)).2 := by
  have bounds := h.bounds
  have hb := hr.bounds
  refine ⟨by omega, fun out ht => h.finish out (.step hk hr ht)⟩

theorem Progress.done (h : Progress distance first last s lab k c pos big)
    (hk : last ≤ k + 1) :
    Result distance first last s lab (c.finish distance first pos) :=
  h.finish _ (.done hk)

theorem Progress.initial {s : RefineSt n}
    (hn : ∃ q, first ≤ q ∧ q < last ∧ s.hits[s.lab[q]!]! ≠ s.hits[s.lab[first]!]!)
    (hm : Minima lab s.hits first v2 v3 last w1 w2) (hv : v2 < v3) (he : v3 < last) :
    let c := ((control s).base distance first w1 w2 v2).more distance first v2 v3
    Progress distance first last s lab (v3 - 1) c.1 c.2.1 c.2.2 := by
  have bounds := hm.bounds
  refine ⟨by omega, fun out ht => .divided hn hm hv ?_⟩
  simpa only [show v3 ≠ last by omega, ite_false] using ht

/-- Constant prefix and stopping information for the executed inner run scan.
The endpoint is inclusive; the two lengths come from its range cursor. -/
structure Scan (lab hits : Array Nat) (start last upto consumed remaining : Nat) : Prop where
  bounds : start ≤ upto ∧ upto ≤ last
  budget : upto + remaining ≤ last
  equal : ∀ q, start ≤ q → q ≤ upto → hits[lab[q]!]! = hits[lab[start]!]!
  cursor : upto = start + consumed ∨ hits[lab[upto + 1]!]! ≠ hits[lab[start]!]!

theorem Scan.initial (hb : start ≤ last) : Scan lab hits start last start 0 (last - start) := by
  refine ⟨⟨Nat.le_refl _, hb⟩, by omega, ?_, Or.inl (by omega)⟩
  intro q hq he
  have heq : q = start := by omega
  rw [heq]

theorem Scan.step (h : Scan lab hits start last upto consumed (remaining + 1))
    (he : hits[lab[upto + 1]!]! = hits[lab[start]!]!) :
    Scan lab hits start last (upto + 1) (consumed + 1) remaining := by
  have bounds := h.bounds
  have budget := h.budget
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro q hq hq'
    by_cases hh : q ≤ upto
    · exact h.equal q hq hh
    · have hq : q = upto + 1 := by omega
      simpa only [hq] using he
  · exact Or.inl (by have := h.cursor.resolve_right (fun hn => hn he); omega)

theorem Scan.stop (h : Scan lab hits start last upto consumed remaining)
    (he : hits[lab[upto + 1]!]! ≠ hits[lab[start]!]!) :
    Scan lab hits start last upto (last - start) 0 :=
  ⟨h.bounds, by have := h.bounds; omega, h.equal, Or.inr he⟩

theorem Scan.run (h : Scan lab hits start last upto (last - start) 0) :
    Index.Run lab hits start last start upto := by
  have bounds := h.bounds
  refine ⟨⟨Nat.le_refl _, bounds.1, bounds.2⟩, Or.inl rfl, h.equal, ?_⟩
  rcases h.cursor with he | he
  · exact Or.inl (by omega)
  · right
    rw [h.equal upto bounds.1 (Nat.le_refl _)]
    exact Ne.symm he

end Hex.GraphIso.Nauty.Sparse.CountTrace
