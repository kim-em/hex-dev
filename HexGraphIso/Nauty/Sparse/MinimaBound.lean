/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Minima

public section

namespace Hex.GraphIso.Nauty.Sparse.Minima

/-- Count insertion also retains the local key bound and the second-minimum
sentinel. Values outside this cell remain unrestricted. -/
structure Bounded (lab hits : Array Nat) (first last v2 v3 upto w1 w2 cap : Nat) : Prop
    extends Minima lab hits first v2 v3 upto w1 w2 where
  size : last ≤ lab.size
  scan : upto ≤ last
  values : ∀ q, first ≤ q → q < last → hits[lab[q]!]! < cap
  empty : v2 = v3 → w2 = cap

private theorem set_bound {lab hits : Array Nat} {first last cap value : Nat}
    (h : ∀ q, first ≤ q → q < last → hits[lab[q]!]! < cap)
    (hb : last ≤ lab.size) (hv : hits[value]! < cap) (i : Nat) :
    ∀ q, first ≤ q → q < last → hits[(lab.set! i value)[q]!]! < cap := by
  intro q hq hq'
  rw [get_set _ _ _ _ (by omega)]
  split
  · exact hv
  · exact h q hq hq'

namespace Bounded

theorem positions (h : Bounded lab hits first last v2 v3 upto w1 w2 cap) :
    first < v2 ∧ v2 ≤ v3 ∧ v3 ≤ upto := h.bounds

theorem initial {lab hits : Array Nat} {first last upto w1 cap : Nat}
    (hb : first < upto) (hu : upto ≤ last) (hs : last ≤ lab.size)
    (hv : ∀ q, first ≤ q → q < last → hits[lab[q]!]! < cap)
    (hm : ∀ q, first ≤ q → q < upto → hits[lab[q]!]! = w1) :
    Bounded lab hits first last upto upto upto w1 cap cap := by
  have hk := hv first (Nat.le_refl _) (by omega)
  rw [hm first (Nat.le_refl _) hb] at hk
  exact ⟨Minima.initial hb hk hm, hs, hu, hv, fun _ => rfl⟩

theorem hit_min (h : Bounded lab hits first last v2 v3 upto w1 w2 cap)
    (hu : upto < last) (hk : hits[lab[upto]!]! = w1) :
    Bounded (((lab.set! upto lab[v3]!).set! v3 lab[v2]!).set! v2 lab[upto]!) hits
      first last (v2 + 1) (v3 + 1) (upto + 1) w1 w2 cap := by
  have bounds := h.bounds
  refine ⟨h.toMinima.hit_min (by have := h.size; omega) hk,
    by simpa using h.size, by omega, ?_, fun he => h.empty (by omega)⟩
  apply set_bound
  · apply set_bound
    · exact set_bound h.values h.size (h.values v3 (by omega) (by omega)) upto
    · simpa using h.size
    · exact h.values v2 (by omega) (by omega)
  · simpa using h.size
  · exact h.values upto (by omega) hu

theorem hit_second (h : Bounded lab hits first last v2 v3 upto w1 w2 cap)
    (hu : upto < last) (hk : hits[lab[upto]!]! = w2) :
    Bounded ((lab.set! upto lab[v3]!).set! v3 lab[upto]!) hits
      first last v2 (v3 + 1) (upto + 1) w1 w2 cap := by
  have bounds := h.bounds
  refine ⟨h.toMinima.hit_second (by have := h.size; omega) hk,
    by simpa using h.size, by omega, ?_, fun he => by omega⟩
  apply set_bound
  · exact set_bound h.values h.size (h.values v3 (by omega) (by omega)) upto
  · simpa using h.size
  · exact h.values upto (by omega) hu

theorem new_min (h : Bounded lab hits first last v2 v3 upto w1 w2 cap)
    (hu : upto < last) (hk : hits[lab[upto]!]! < w1) :
    Bounded (((lab.set! upto lab[v2]!).set! v2 lab[first]!).set! first lab[upto]!) hits
      first last (first + 1) (v2 + 1) (upto + 1) hits[lab[upto]!]! w1 cap := by
  have bounds := h.bounds
  refine ⟨h.toMinima.new_min (by have := h.size; omega) hk,
    by simpa using h.size, by omega, ?_, fun he => by omega⟩
  apply set_bound
  · apply set_bound
    · exact set_bound h.values h.size (h.values v2 (by omega) (by omega)) upto
    · simpa using h.size
    · exact h.values first (by omega) (by omega)
  · simpa using h.size
  · exact h.values upto (by omega) hu

theorem new_second (h : Bounded lab hits first last v2 v3 upto w1 w2 cap)
    (hu : upto < last) (hlo : w1 < hits[lab[upto]!]!) (hhi : hits[lab[upto]!]! < w2) :
    Bounded ((lab.set! upto lab[v2]!).set! v2 lab[upto]!) hits
      first last v2 (v2 + 1) (upto + 1) w1 hits[lab[upto]!]! cap := by
  have bounds := h.bounds
  refine ⟨h.toMinima.new_second (by have := h.size; omega) hlo hhi,
    by simpa using h.size, by omega, ?_, fun he => by omega⟩
  apply set_bound
  · exact set_bound h.values h.size (h.values v2 (by omega) (by omega)) upto
  · simpa using h.size
  · exact h.values upto (by omega) hu

theorem above (h : Bounded lab hits first last v2 v3 upto w1 w2 cap)
    (hu : upto < last) (hk : w2 < hits[lab[upto]!]!) :
    Bounded lab hits first last v2 v3 (upto + 1) w1 w2 cap :=
  ⟨h.toMinima.above hk, h.size, by omega, h.values, h.empty⟩

/-- Once the whole cell is scanned, a nonconstant split has two nonempty
minimum fragments. The proof uses only this cell's bound, even when scratch
entries belonging to other cells have arbitrary values. -/
theorem second_pos (h : Bounded lab hits first last v2 v3 last w1 w2 cap)
    (hv : v2 < last) : v2 < v3 := by
  have bounds := h.bounds
  by_cases he : v2 = v3
  · have hk := h.larger v3 (Nat.le_refl _) (by omega)
    have hb := h.values v3 (by omega) (by omega)
    have hs := h.empty he
    omega
  · omega

end Bounded
end Hex.GraphIso.Nauty.Sparse.Minima
