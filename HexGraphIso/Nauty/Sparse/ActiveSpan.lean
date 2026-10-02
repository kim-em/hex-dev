/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ActiveCells

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Before largest-fragment replacement, every new interior fragment is
active and the original cell start retains its incoming membership. -/
structure ActiveSpan (level first last : Nat) (before active : VSet n) (ptn : Array Nat) : Prop where
  outside : ∀ u, u < first ∨ last ≤ u → active.mem u = before.mem u
  head : active.mem first = before.mem first
  inner : ∀ u, first < u → u < last → ptn[u - 1]! ≤ level → active.mem u = true

namespace ActiveSpan

variable {n level first last cut : Nat} {before active : VSet n} {ptn : Array Nat}

theorem insert_outside (hf : first ≤ v) (hl : v < last) :
    ∀ u, u < first ∨ last ≤ u → (active.insert v).mem u = active.mem u := by
  intro u hu
  simp only [VSet.mem_insert, beq_eq_false_iff_ne.mpr (by omega : v ≠ u),
    Bool.false_and, Bool.or_false]

theorem initial (hc : IsCell ptn level first (last - first)) :
    ActiveSpan level first last active active ptn := by
  refine ⟨fun _ _ => rfl, rfl, ?_⟩
  intro u hu hu' hs
  have := hc.2.2.1 (u - 1) (by omega) (by omega)
  omega

theorem cut_push (h : ActiveSpan level first last before active ptn)
    (hf : first < cut) (hl : cut < last) (hb : last ≤ n) :
    ActiveSpan level first last before (active.insert cut) (ptn.setIfInBounds (cut - 1) level) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    simpa only [VSet.mem_insert, beq_eq_false_iff_ne.mpr (by omega : cut ≠ u),
      Bool.false_and, Bool.or_false] using h.outside u hu
  · simpa only [VSet.mem_insert, beq_eq_false_iff_ne.mpr (by omega : cut ≠ first),
      Bool.false_and, Bool.or_false] using h.head
  · intro u hu hu' hs
    by_cases he : u = cut
    · subst u
      simp [VSet.mem_insert, show cut < n by omega]
    · change (ptn.set! (cut - 1) level)[u - 1]! ≤ level at hs
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)] at hs
      simp [VSet.mem_insert, h.inner u hu hu' hs]

theorem cut_next (h : ActiveSpan level first last before active ptn)
    (hf : first ≤ cut) (hl : cut + 1 < last) (hb : last ≤ n) :
    ActiveSpan level first last before (active.insert (cut + 1)) (ptn.setIfInBounds cut level) := by
  simpa only [Nat.add_sub_cancel] using h.cut_push (by omega : first < cut + 1) hl hb

theorem finish (h : ActiveSpan level first last before active ptn) :
    CellActive level first last before active ptn := by
  refine ⟨?_, first, ?_⟩
  · intro ha u hu hu' hs
    by_cases he : u = first
    · subst u; exact h.head.trans ha
    · exact h.inner u (by omega) hu' (hs.resolve_left he)
  · intro u hu hu' hs hn
    exact h.inner u (by omega) hu' (hs.resolve_left hn)

/-- Replacing one interior fragment by the first fragment leaves exactly
that interior fragment as the sole possible inactive fragment. -/
theorem replace (h : ActiveSpan level first last before active ptn)
    (hf : first < v) (hl : v < last) (hb : last ≤ n) (ha : active.mem first = false) :
    CellActive level first last before ((active.erase v).insert first) ptn ∧
      ∀ u, u < first ∨ last ≤ u → ((active.erase v).insert first).mem u = before.mem u := by
  have hbefore : before.mem first = false := h.head.symm.trans ha
  refine ⟨⟨by simp [hbefore], v, ?_⟩, ?_⟩
  · intro u hu hu' hs hn
    by_cases he : u = first
    · subst u; simp [VSet.mem_insert, show first < n by omega]
    · have hactive := h.inner u (by omega) hu' (hs.resolve_left he)
      simp [VSet.mem_insert, VSet.mem_erase, hactive, Ne.symm hn]
  · intro u hu
    simpa only [VSet.mem_insert, VSet.mem_erase,
      beq_eq_false_iff_ne.mpr (by omega : first ≠ u),
      beq_eq_false_iff_ne.mpr (by omega : v ≠ u), Bool.false_and, Bool.or_false,
      Bool.not_false, Bool.and_true] using h.outside u hu

end ActiveSpan

/-- Appended queue entries belong to the cell currently being split.
The saved largest-fragment position therefore cannot erase another cell. -/
structure QueueSpan (first last base : Nat) (queue : Array Nat) : Prop where
  size : base ≤ queue.size
  entries : ∀ p, base ≤ p → p < queue.size → first < queue[p]! ∧ queue[p]! < last

namespace QueueSpan

theorem initial (queue : Array Nat) : QueueSpan first last queue.size queue :=
  ⟨Nat.le_refl _, fun _ _ _ => by omega⟩

theorem push (h : QueueSpan first last base queue) (hf : first < v) (hl : v < last) :
    QueueSpan first last base (queue.push v) := by
  refine ⟨by have := h.size; simp; omega, ?_⟩
  intro p hp hb
  by_cases he : p < queue.size
  · rw [getElem!_pos (queue.push v) p (by simp; omega)]
    simpa only [Array.getElem_push, he, ↓reduceDIte, getElem!_pos queue p he]
      using h.entries p hp he
  · have heq : p = queue.size := by simp only [Array.size_push] at hb; omega
    subst p
    simpa using And.intro hf hl

end QueueSpan

/-- Read the saved queue position using the bounds established by the
executed append operations. -/
theorem ActiveSpan.replace_get {n level first last base pos : Nat}
    {before active : VSet n} {ptn queue : Array Nat}
    (h : ActiveSpan level first last before active ptn)
    (hq : QueueSpan first last base queue) (hp : base ≤ pos) (hb : pos < queue.size)
    (hn : last ≤ n) (ha : active.mem first = false) :
    CellActive level first last before ((active.erase queue[pos]).insert first) ptn ∧
      ∀ u, u < first ∨ last ≤ u → ((active.erase queue[pos]).insert first).mem u = before.mem u := by
  have hv := hq.entries pos hp hb
  simpa only [getElem!_pos queue pos hb] using h.replace hv.1 hv.2 hn ha

end Hex.GraphIso.Nauty.Sparse
