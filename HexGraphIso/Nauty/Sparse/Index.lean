/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine
public import HexGraphIso.Nauty.Spec.CellPerm

public section

namespace Hex.GraphIso.Nauty.Sparse.Index

/-- The cache is correct for all cells starting before `upto`. Singleton
vertices carry the sentinel `n`; other vertices carry their cell's start. -/
structure Prefix (n : Nat) (lab ptn : Array Nat) (level upto : Nat)
    (starts ends : Array Nat) : Prop where
  starts_size : starts.size = n
  ends_size : ends.size = n
  ends_eq : ∀ a len, IsCell ptn level a len → a + len ≤ n → a < upto →
    ends[a]! = a + len - 1
  starts_eq : ∀ a len, IsCell ptn level a len → a + len ≤ n → a < upto →
    ∀ i, a ≤ i → i < a + len → starts[lab[i]!]! = if len = 1 then n else a

/-- A completed cache describes every bounded cell of the partition. -/
abbrev Valid (n : Nat) (lab ptn : Array Nat) (level : Nat)
    (starts ends : Array Nat) : Prop := Prefix n lab ptn level n starts ends

namespace Prefix

theorem zero (hs : starts.size = n) (he : ends.size = n) :
    Prefix n lab ptn level 0 starts ends :=
  ⟨hs, he, fun _ _ _ _ h => by omega, fun _ _ _ _ h => by omega⟩

/-- Writing one whole cell extends the cache through its last position.
Disjoint cells do not share vertices because the labelling is injective. -/
theorem extend {lab ptn starts ends out : Array Nat} {n level first last : Nat}
    (h : Prefix n lab ptn level first starts ends)
    (hc : IsCell ptn level first (last + 1 - first)) (hg : first ≤ last) (hb : last < n)
    (hs : out.size = n)
    (ho : ∀ i, i < n → out[lab[i]!]! =
      if first ≤ i ∧ i ≤ last then (if first < last then first else n) else starts[lab[i]!]!) :
    Prefix n lab ptn level (last + 1) out (ends.set! first last) := by
  refine ⟨hs, by simpa using h.ends_size, ?_, ?_⟩
  · intro a len ha hn hlt
    have hd := isCell_disjoint_or_eq hc ha
    have hpos := ha.1
    rcases hd with hd | hd | ⟨rfl, rfl⟩
    · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      exact h.ends_eq a len ha hn (by omega)
    · omega
    · rw [Array.getElem!_set!_self _ _ _ (by rw [h.ends_size]; omega)]
      omega
  · intro a len ha hn hlt i hi hj
    have hd := isCell_disjoint_or_eq hc ha
    have hpos := ha.1
    rw [ho i (by omega)]
    rcases hd with hd | hd | ⟨rfl, rfl⟩
    · rw [ite_eq_right (by omega)]
      exact h.starts_eq a len ha hn (by omega) i hi hj
    · omega
    · rw [ite_eq_left (by omega)]
      by_cases he : first < last <;> simp only [he, ite_true, ite_false]
      · rw [ite_eq_right (by omega)]
      · rw [ite_eq_left (by omega)]

end Prefix

/-- A partial scatter changes precisely the already traversed positions. -/
structure Scatter (n : Nat) (lab before after : Array Nat) (first upto value : Nat) : Prop where
  size : after.size = n
  get : ∀ i, i < n → after[lab[i]!]! =
    if first ≤ i ∧ i < upto then value else before[lab[i]!]!

namespace Scatter

theorem initial (h : before.size = n) : Scatter n lab before before first first value :=
  ⟨h, fun _ _ => by rw [ite_eq_right (by omega)]⟩

theorem step {lab before after : Array Nat} {n first upto value : Nat}
    (h : Scatter n lab before after first upto value)
    (hbound : ∀ i, i < n → lab[i]! < n)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlo : first ≤ upto) (hhi : upto < n) :
    Scatter n lab before (after.set! lab[upto]! value) first (upto + 1) value := by
  refine ⟨by simpa using h.size, ?_⟩
  intro i hi
  by_cases he : i = upto
  · subst i
    rw [Array.getElem!_set!_self _ _ _ (by rw [h.size]; exact hbound upto hhi),
      ite_eq_left (by omega)]
  · rw [Array.getElem!_set!_ne _ _ _ _ (fun hh => he (hinj _ _ hi hhi hh.symm)), h.get i hi]
    have hh : (first ≤ i ∧ i < upto + 1) ↔ (first ≤ i ∧ i < upto) := by omega
    simp only [hh]

end Scatter

end Hex.GraphIso.Nauty.Sparse.Index
