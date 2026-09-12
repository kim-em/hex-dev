/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Rotate

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The first two constant-count fragments and the larger counts already
scanned by nauty's three-way insertion. The second fragment may be empty. -/
structure Minima (lab hits : Array Nat) (first v2 v3 upto w1 w2 : Nat) : Prop where
  bounds : first < v2 ∧ v2 ≤ v3 ∧ v3 ≤ upto
  keys : w1 < w2
  minimum : ∀ q, first ≤ q → q < v2 → hits[lab[q]!]! = w1
  second : ∀ q, v2 ≤ q → q < v3 → hits[lab[q]!]! = w2
  larger : ∀ q, v3 ≤ q → q < upto → w2 < hits[lab[q]!]!

namespace Minima

theorem initial {lab hits : Array Nat} {first upto w1 w2 : Nat}
    (hb : first < upto) (hk : w1 < w2)
    (hm : ∀ q, first ≤ q → q < upto → hits[lab[q]!]! = w1) :
    Minima lab hits first upto upto upto w1 w2 :=
  ⟨⟨hb, Nat.le_refl _, Nat.le_refl _⟩, hk, hm,
    fun _ h₁ h₂ => by omega, fun _ h₁ h₂ => by omega⟩

theorem hit_min {lab hits : Array Nat} {first v2 v3 upto w1 w2 : Nat}
    (h : Minima lab hits first v2 v3 upto w1 w2) (hb : upto < lab.size)
    (hk : hits[lab[upto]!]! = w1) :
    Minima (((lab.set! upto lab[v3]!).set! v3 lab[v2]!).set! v2 lab[upto]!) hits
      first (v2 + 1) (v3 + 1) (upto + 1) w1 w2 := by
  obtain ⟨bounds, keys, hm, hs, hl⟩ := h
  refine ⟨by omega, keys, ?_, ?_, ?_⟩
  all_goals
    intro q hq hq'
    rw [get_set _ _ _ _ (by simp only [Array.size_set!]; omega),
      get_set _ _ _ _ (by simp only [Array.size_set!]; omega),
      get_set _ _ _ _ (by omega)]
    split <;> (try split) <;> (try split) <;> grind

theorem hit_second {lab hits : Array Nat} {first v2 v3 upto w1 w2 : Nat}
    (h : Minima lab hits first v2 v3 upto w1 w2) (hb : upto < lab.size)
    (hk : hits[lab[upto]!]! = w2) :
    Minima ((lab.set! upto lab[v3]!).set! v3 lab[upto]!) hits
      first v2 (v3 + 1) (upto + 1) w1 w2 := by
  obtain ⟨bounds, keys, hm, hs, hl⟩ := h
  refine ⟨by omega, keys, ?_, ?_, ?_⟩
  all_goals
    intro q hq hq'
    rw [get_set _ _ _ _ (by simp only [Array.size_set!]; omega),
      get_set _ _ _ _ (by omega)]
    split <;> (try split) <;> grind

theorem new_min {lab hits : Array Nat} {first v2 v3 upto w1 w2 : Nat}
    (h : Minima lab hits first v2 v3 upto w1 w2) (hb : upto < lab.size)
    (hk : hits[lab[upto]!]! < w1) :
    Minima (((lab.set! upto lab[v2]!).set! v2 lab[first]!).set! first lab[upto]!) hits
      first (first + 1) (v2 + 1) (upto + 1) hits[lab[upto]!]! w1 := by
  obtain ⟨bounds, keys, hm, hs, hl⟩ := h
  refine ⟨by omega, hk, ?_, ?_, ?_⟩
  all_goals
    intro q hq hq'
    rw [get_set _ _ _ _ (by simp only [Array.size_set!]; omega),
      get_set _ _ _ _ (by simp only [Array.size_set!]; omega),
      get_set _ _ _ _ (by omega)]
    split <;> (try split) <;> (try split) <;> grind

theorem new_second {lab hits : Array Nat} {first v2 v3 upto w1 w2 : Nat}
    (h : Minima lab hits first v2 v3 upto w1 w2) (hb : upto < lab.size)
    (hlo : w1 < hits[lab[upto]!]!) (hhi : hits[lab[upto]!]! < w2) :
    Minima ((lab.set! upto lab[v2]!).set! v2 lab[upto]!) hits
      first v2 (v2 + 1) (upto + 1) w1 hits[lab[upto]!]! := by
  obtain ⟨bounds, keys, hm, hs, hl⟩ := h
  refine ⟨by omega, hlo, ?_, ?_, ?_⟩
  all_goals
    intro q hq hq'
    rw [get_set _ _ _ _ (by simp only [Array.size_set!]; omega),
      get_set _ _ _ _ (by omega)]
    split <;> (try split) <;> grind

theorem above {lab hits : Array Nat} {first v2 v3 upto w1 w2 : Nat}
    (h : Minima lab hits first v2 v3 upto w1 w2) (hk : w2 < hits[lab[upto]!]!) :
    Minima lab hits first v2 v3 (upto + 1) w1 w2 := by
  obtain ⟨bounds, keys, hm, hs, hl⟩ := h
  refine ⟨by omega, keys, hm, hs, ?_⟩
  intro q hq hq'
  by_cases he : q = upto
  · simpa only [he] using hk
  · exact hl q hq (by omega)

end Minima

end Hex.GraphIso.Nauty.Sparse
