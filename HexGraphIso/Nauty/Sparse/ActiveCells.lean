/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CellCut
public import HexGraphIso.Nauty.Sparse.Refine

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Refining a cell activates all its fragments when it was active, and
leaves at most one inactive fragment otherwise. -/
structure CellActive (level first last : Nat) (before after : VSet n) (ptn : Array Nat) : Prop where
  all : before.mem first = true → ∀ u, first ≤ u → u < last →
    (u = first ∨ ptn[u - 1]! ≤ level) → after.mem u = true
  one : ∃ w, ∀ u, first ≤ u → u < last →
    (u = first ∨ ptn[u - 1]! ≤ level) → u ≠ w → after.mem u = true

namespace CellActive

variable {n : Nat} {active : VSet n}

theorem refl (hc : IsCell ptn level first (last - first)) :
    CellActive level first last active active ptn := by
  have starts : ∀ u, first ≤ u → u < last →
      (u = first ∨ ptn[u - 1]! ≤ level) → u = first := by
    intro u hu hu' hs
    rcases hs with he | hs
    · exact he
    · by_cases he : u = first
      · exact he
      · have := hc.2.2.1 (u - 1) (by omega) (by omega)
        omega
  exact ⟨fun h u hu hu' hs => starts u hu hu' hs ▸ h,
    first, fun u hu hu' hs hn => False.elim (hn (starts u hu hu' hs))⟩

theorem binary_starts (hc : IsCell ptn level first (last - first))
    (hf : first < cut) (hl : cut < last) (hu : first ≤ u) (hu' : u < last)
    (hs : u = first ∨ (ptn.setIfInBounds (cut - 1) level)[u - 1]! ≤ level) :
    u = first ∨ u = cut := by
  rcases hs with he | hs
  · exact Or.inl he
  · by_cases he : u = first
    · exact Or.inl he
    · by_cases he' : u = cut
      · exact Or.inr he'
      · change (ptn.set! (cut - 1) level)[u - 1]! ≤ level at hs
        rw [Array.getElem!_set!_ne _ _ _ _ (by omega)] at hs
        have := hc.2.2.1 (u - 1) (by omega) (by omega)
        omega

theorem binary_left (hc : IsCell ptn level first (last - first))
    (hf : first < cut) (hl : cut < last) (hb : last ≤ n)
    (ha : active.mem first = false) :
    CellActive level first last active (active.insert first) (ptn.setIfInBounds (cut - 1) level) := by
  refine ⟨by simp [ha], cut, ?_⟩
  intro u hu hu' hs hn
  have he := binary_starts hc hf hl hu hu' hs
  have heq : u = first := he.resolve_right hn
  subst u
  simp [VSet.mem_insert, show first < n by omega]

theorem binary_right (hc : IsCell ptn level first (last - first))
    (hf : first < cut) (hl : cut < last) (hb : last ≤ n) :
    CellActive level first last active (active.insert cut) (ptn.setIfInBounds (cut - 1) level) := by
  have cut_active : (active.insert cut).mem cut = true := by
    simp [VSet.mem_insert, show cut < n by omega]
  refine ⟨?_, first, ?_⟩
  · intro ha u hu hu' hs
    rcases binary_starts hc hf hl hu hu' hs with rfl | rfl
    · simp [VSet.mem_insert, ha]
    · exact cut_active
  · intro u hu hu' hs hn
    have he := (binary_starts hc hf hl hu hu' hs).resolve_left hn
    exact he ▸ cut_active

end CellActive

/-- The fragment-activation rule for every original cell of a pass. -/
@[expose] def Activation (n level : Nat) (before ptn : Array Nat) (active out : VSet n) : Prop :=
  ∀ a len, IsCell before level a len → a + len ≤ n →
    CellActive level a (a + len) active out ptn

namespace Activation

theorem refl (ptn : Array Nat) (active : VSet n) (level : Nat) :
    Activation n level ptn ptn active active := by
  intro a len hc hb
  exact CellActive.refl (by simpa using hc)

/-- A pass may process its original cells in any order: a local activation
proof composes with all guarantees already established on disjoint cells. -/
theorem step {n level first last : Nat} {before ptn out : Array Nat}
    {active current after : VSet n}
    (h : Activation n level before ptn active current)
    (hc : IsCell before level first (last - first))
    (hl : CellActive level first last current after out)
    (ha : ∀ u, u < first ∨ last ≤ u → after.mem u = current.mem u)
    (hp : ∀ q, q < first ∨ last - 1 ≤ q → out[q]! = ptn[q]!) :
    Activation n level before out active after := by
  have hpos := hc.1
  intro a len hd hbound
  have hold := h a len hd hbound
  rcases isCell_disjoint_or_eq hc hd with hdis | hdis | ⟨rfl, rfl⟩
  · have hstart (u : Nat) (hu : a ≤ u) (hu' : u < a + len)
        (hs : u = a ∨ out[u - 1]! ≤ level) : u = a ∨ ptn[u - 1]! ≤ level := by
      rcases hs with he | hs
      · exact Or.inl he
      · exact Or.inr (by rwa [hp (u - 1) (Or.inl (by omega))] at hs)
    refine ⟨fun h u hu hu' hs => ?_, ?_⟩
    · rw [ha u (Or.inl (by omega))]
      exact hold.all h u hu hu' (hstart u hu hu' hs)
    · obtain ⟨w, hw⟩ := hold.one
      refine ⟨w, fun u hu hu' hs hn => ?_⟩
      rw [ha u (Or.inl (by omega))]
      exact hw u hu hu' (hstart u hu hu' hs) hn
  · have hstart (u : Nat) (hu : a ≤ u) (hu' : u < a + len)
        (hs : u = a ∨ out[u - 1]! ≤ level) : u = a ∨ ptn[u - 1]! ≤ level := by
      rcases hs with he | hs
      · exact Or.inl he
      · exact Or.inr (by rwa [hp (u - 1) (Or.inr (by omega))] at hs)
    refine ⟨fun h u hu hu' hs => ?_, ?_⟩
    · rw [ha u (Or.inr (by omega))]
      exact hold.all h u hu hu' (hstart u hu hu' hs)
    · obtain ⟨w, hw⟩ := hold.one
      refine ⟨w, fun u hu hu' hs hn => ?_⟩
      rw [ha u (Or.inr (by omega))]
      exact hw u hu hu' (hstart u hu hu' hs) hn
  · have he : first + (last - first) = last := by omega
    rw [he] at hold ⊢
    exact ⟨fun ha => hl.all (hold.all ha first (Nat.le_refl _) (by omega) (Or.inl rfl)), hl.one⟩

/-- Activate the first fragment when the original cell is inactive. -/
theorem cut_left {n level first cut last : Nat} {before ptn : Array Nat}
    {active current : VSet n} (h : Activation n level before ptn active current)
    (hc : IsCell before level first (last - first))
    (ht : IsCell ptn level first (last - first))
    (hf : first < cut) (hl : cut < last) (hb : last ≤ n)
    (ha : current.mem first = false) :
    Activation n level before (ptn.setIfInBounds (cut - 1) level) active (current.insert first) := by
  apply h.step hc (CellActive.binary_left ht hf hl hb ha)
  · intro u hu
    simp [VSet.mem_insert, show first ≠ u by omega]
  · intro q hq
    exact Array.getElem!_set!_ne _ _ _ _ (by omega)

/-- Activate the second fragment; an already active first fragment stays active. -/
theorem cut_right {n level first cut last : Nat} {before ptn : Array Nat}
    {active current : VSet n} (h : Activation n level before ptn active current)
    (hc : IsCell before level first (last - first))
    (ht : IsCell ptn level first (last - first))
    (hf : first < cut) (hl : cut < last) (hb : last ≤ n) :
    Activation n level before (ptn.setIfInBounds (cut - 1) level) active (current.insert cut) := by
  apply h.step hc (CellActive.binary_right ht hf hl hb)
  · intro u hu
    simp [VSet.mem_insert, show cut ≠ u by omega]
  · intro q hq
    exact Array.getElem!_set!_ne _ _ _ _ (by omega)

end Activation
end Hex.GraphIso.Nauty.Sparse
