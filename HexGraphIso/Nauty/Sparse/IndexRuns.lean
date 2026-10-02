/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountRuns
public import HexGraphIso.Nauty.Sparse.Index

public section

namespace Hex.GraphIso.Nauty.Sparse.Index

/-- A maximal constant-count run inside one original cell. Both endpoints
are inclusive, as in the cached endpoint array. -/
structure Run (lab hits : Array Nat) (first last a b : Nat) : Prop where
  bounds : first ≤ a ∧ a ≤ b ∧ b ≤ last
  left : a = first ∨ hits[lab[a - 1]!]! ≠ hits[lab[a]!]!
  equal : ∀ q, a ≤ q → q ≤ b → hits[lab[q]!]! = hits[lab[a]!]!
  right : b = last ∨ hits[lab[b]!]! ≠ hits[lab[b + 1]!]!

namespace Run

theorem disjoint_or_eq (h : Run lab hits first last a b)
    (h' : Run lab hits first last a' b') :
    b < a' ∨ b' < a ∨ (a = a' ∧ b = b') := by
  have bounds := h.bounds
  have bounds' := h'.bounds
  by_cases he : a = a'
  · subst a'
    have hend : b = b' := by
      by_cases hlt : b < b'
      · have hl := h'.equal b (by omega) (by omega)
        have hr := h'.equal (b + 1) (by omega) (by omega)
        rcases h.right with hh | hh <;> (exfalso; solve | omega | exact hh (hl.trans hr.symm))
      · by_cases hlt' : b' < b
        · have hl := h.equal b' (by omega) (by omega)
          have hr := h.equal (b' + 1) (by omega) (by omega)
          rcases h'.right with hh | hh <;> (exfalso; solve | omega | exact hh (hl.trans hr.symm))
        · omega
    exact Or.inr (Or.inr ⟨rfl, hend⟩)
  · by_cases hlt : a < a'
    · apply Or.inl
      by_cases hb : b < a'
      · exact hb
      · have hl := h.equal (a' - 1) (by omega) (by omega)
        have hr := h.equal a' (by omega) (by omega)
        rcases h'.left with hh | hh <;> (exfalso; solve | omega | exact hh (hl.trans hr.symm))
    · apply Or.inr ∘ Or.inl
      by_cases hb : b' < a
      · exact hb
      · have hl := h'.equal (a - 1) (by omega) (by omega)
        have hr := h'.equal a (by omega) (by omega)
        rcases h.left with hh | hh <;> (exfalso; solve | omega | exact hh (hl.trans hr.symm))

theorem cell (h : CountPartition level first last lab hits before ptn)
    (hc : IsCell before level first (last + 1 - first))
    (ha : first ≤ a) (hab : a ≤ b) (hb : b ≤ last) :
    IsCell ptn level a (b + 1 - a) ↔ Run lab hits first last a b := by
  rw [h.cell_iff hc ha (by omega) (by omega)]
  have he : a + (b + 1 - a) = b + 1 := by omega
  simp only [he, Nat.add_sub_cancel]
  constructor
  · intro hh
    exact ⟨⟨ha, hab, hb⟩, hh.1, fun q hq hq' => hh.2.1 q hq (by omega), hh.2.2⟩
  · intro hh
    exact ⟨hh.left, fun q hq hq' => hh.equal q hq (by omega), hh.right⟩

end Run

/-- Cache entries for the completed runs of a count split. This invariant
does not require the next run's boundary to have been written yet. -/
structure Runs (n first last upto : Nat) (lab hits starts ends : Array Nat) : Prop where
  starts_size : starts.size = n
  ends_size : ends.size = n
  ends_eq : ∀ a b, Run lab hits first last a b → b < upto → ends[a]! = b
  starts_eq : ∀ a b, Run lab hits first last a b → b < upto →
    ∀ q, a ≤ q → q ≤ b → starts[lab[q]!]! = if a = b then n else a

namespace Runs

variable {n first last a b : Nat} {lab hits starts ends : Array Nat}

/-- The first completed run has no earlier run to preserve. -/
theorem of_first (hr : Run lab hits first last first b) (hb : b < n)
    (hs : starts.size = n) (he : ends.size = n)
    (hv : ∀ q, first ≤ q → q ≤ b → starts[lab[q]!]! = if first = b then n else first) :
    Runs n first last (b + 1) lab hits starts (ends.setIfInBounds first b) := by
  change Runs n first last (b + 1) lab hits starts (ends.set! first b)
  have bounds := hr.bounds
  refine ⟨hs, by simpa using he, ?_, ?_⟩
  · intro a c hc hcu
    have bd := hc.bounds
    rcases hr.disjoint_or_eq hc with hh | hh | ⟨rfl, rfl⟩
    · omega
    · omega
    · rw [Array.getElem!_set!_self _ _ _ (by rw [he]; omega)]
  · intro a c hc hcu q hq hq'
    have bd := hc.bounds
    rcases hr.disjoint_or_eq hc with hh | hh | ⟨rfl, rfl⟩
    · omega
    · omega
    · exact hv q hq hq'

theorem initial (hs : starts.size = n) (he : ends.size = n) :
    Runs n first last first lab hits starts ends := by
  refine ⟨hs, he, ?_, ?_⟩
  · intro a b hr hb
    have := hr.bounds
    omega
  · intro a b hr hb
    have := hr.bounds
    omega

/-- Scattering one whole run preserves every preceding run's entries and
extends the completed prefix through the newly stored endpoint. -/
theorem extend (h : Runs n first last a lab hits starts ends)
    (hr : Run lab hits first last a b) (hb : b < n) (hs : out.size = n)
    (ho : ∀ q, q < n → out[lab[q]!]! =
      if a ≤ q ∧ q ≤ b then (if a = b then n else a) else starts[lab[q]!]!) :
    Runs n first last (b + 1) lab hits out (ends.setIfInBounds a b) := by
  change Runs n first last (b + 1) lab hits out (ends.set! a b)
  have bounds := hr.bounds
  refine ⟨hs, by simpa using h.ends_size, ?_, ?_⟩
  · intro c d hc hd
    have bd := hc.bounds
    rcases hr.disjoint_or_eq hc with hcd | hdc | ⟨rfl, rfl⟩
    · omega
    · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      exact h.ends_eq c d hc hdc
    · rw [Array.getElem!_set!_self _ _ _ (by rw [h.ends_size]; omega)]
  · intro c d hc hd q hq hq'
    have bd := hc.bounds
    rw [ho q (by omega)]
    rcases hr.disjoint_or_eq hc with hcd | hdc | ⟨rfl, rfl⟩
    · omega
    · rw [ite_eq_right (by omega)]
      exact h.starts_eq c d hc hdc q hq hq'
    · rw [ite_eq_left (by omega)]

end Runs

namespace Scatter

/-- The tail scan writes positions after the run's first vertex. The final
first-vertex write completes that scatter, with the singleton sentinel. -/
theorem prepend (h : Scatter n lab before after (a + 1) (b + 1) a)
    (hbound : ∀ i, i < n → lab[i]! < n)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hab : a ≤ b) (hb : b < n) :
    Scatter n lab before (after.setIfInBounds lab[a]! (if a = b then n else a))
      a (b + 1) (if a = b then n else a) := by
  change Scatter n lab before (after.set! lab[a]! (if a = b then n else a))
    a (b + 1) (if a = b then n else a)
  refine ⟨by simpa using h.size, ?_⟩
  intro q hq
  by_cases he : q = a
  · subst q
    rw [Array.getElem!_set!_self _ _ _ (by rw [h.size]; exact hbound a (by omega)),
      ite_eq_left (by omega : a ≤ a ∧ a < b + 1)]
  · rw [Array.getElem!_set!_ne _ _ _ _ (fun hh => he (hinj _ _ hq (by omega) hh.symm)),
      h.get q hq]
    by_cases hae : a = b
    · simp only [ite_eq_left hae, ite_eq_right (by omega : ¬(a + 1 ≤ q ∧ q < b + 1)),
        ite_eq_right (by omega : ¬(a ≤ q ∧ q < b + 1))]
    · simp only [ite_eq_right hae]
      have heq : (a + 1 ≤ q ∧ q < b + 1) ↔ (a ≤ q ∧ q < b + 1) := by omega
      simp only [heq]

end Scatter

end Hex.GraphIso.Nauty.Sparse.Index

namespace Hex.GraphIso.Nauty.Sparse.Minima

theorem first_run (h : Minima lab hits first v2 v3 last w1 w2) (hv : v2 < v3) :
    Index.Run lab hits first (last - 1) first (v2 - 1) := by
  have bounds := h.bounds
  refine ⟨by omega, Or.inl rfl, ?_, Or.inr ?_⟩
  · intro q hq hq'
    rw [h.minimum q hq (by omega), h.minimum first (Nat.le_refl _) (by omega)]
  · rw [h.minimum _ (by omega) (by omega), h.second _ (by omega) (by omega)]
    have := h.keys
    omega

theorem second_run (h : Minima lab hits first v2 v3 last w1 w2) (hv : v2 < v3) :
    Index.Run lab hits first (last - 1) v2 (v3 - 1) := by
  have bounds := h.bounds
  refine ⟨by omega, Or.inr ?_, ?_, ?_⟩
  · rw [h.minimum _ (by omega) (by omega), h.second _ (Nat.le_refl _) hv]
    have := h.keys
    omega
  · intro q hq hq'
    rw [h.second q hq (by omega), h.second v2 (Nat.le_refl _) hv]
  · by_cases he : v3 = last
    · exact Or.inl (by omega)
    · exact Or.inr (h.next_different hv (by omega))

end Hex.GraphIso.Nauty.Sparse.Minima
