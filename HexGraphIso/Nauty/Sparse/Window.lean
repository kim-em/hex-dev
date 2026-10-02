/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Rotate
public import HexGraphIso.Nauty.Sparse.SortSegments

public section

namespace Hex.GraphIso.Nauty.Sparse.Sort

/-- A permutation supported inside a half-open position interval. -/
structure Window (before after : Array Nat) (first last : Nat) : Prop where
  perm : after.toList.Perm before.toList
  outside : ∀ q, q < first ∨ last ≤ q → after[q]! = before[q]!

namespace Window

theorem refl (lab : Array Nat) (first last : Nat) : Window lab lab first last :=
  ⟨.refl _, fun _ _ => rfl⟩

theorem size (h : Window before after first last) : after.size = before.size := h.perm.length_eq

theorem exchange (h : Window before after first last)
    (hi : first ≤ i ∧ i < last) (hj : first ≤ j ∧ j < last) (hb : last ≤ after.size) :
    Window before ((after.setIfInBounds i after[j]!).setIfInBounds j after[i]!) first last := by
  change Window before ((after.set! i after[j]!).set! j after[i]!) first last
  refine ⟨(exchange_perm after i j (by omega) (by omega)).trans h.perm, ?_⟩
  intro q hq
  rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
    Array.getElem!_set!_ne _ _ _ _ (by omega)]
  exact h.outside q hq

theorem rotate (h : Window before after first last)
    (hk : first ≤ k) (hkj : k ≤ j) (hji : j ≤ i) (hi : i < last) (hb : last ≤ after.size) :
    Window before
      (((after.setIfInBounds i after[j]!).setIfInBounds j after[k]!).setIfInBounds k after[i]!)
      first last := by
  change Window before (((after.set! i after[j]!).set! j after[k]!).set! k after[i]!) first last
  refine ⟨(rotate_perm after i j k hkj hji (by omega)).trans h.perm, ?_⟩
  intro q hq
  rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
    Array.getElem!_set!_ne _ _ _ _ (by omega), Array.getElem!_set!_ne _ _ _ _ (by omega)]
  exact h.outside q hq

theorem indirect (h : Window before after first last)
    (hl : first ≤ start) (hh : start + len ≤ last) (hb : last ≤ after.size) :
    Window before (Sort.indirect after hits start len) first last := by
  refine ⟨(Sort.indirect_perm after hits start len (by omega)).trans h.perm, ?_⟩
  intro q hq
  rw [Sort.indirect_outside after hits start len q (by omega) (by omega)]
  exact h.outside q hq

theorem mem (h : Window before after first last) (hb : last ≤ after.size)
    (hq : first ≤ q ∧ q < last) :
    ∃ r, first ≤ r ∧ r < last ∧ after[q]! = before[r]! := by
  have hs := h.size
  exact segment_mem hb (segment_perm ⟨by omega, by omega⟩ h.perm h.outside) hq

end Window

end Hex.GraphIso.Nauty.Sparse.Sort

namespace Hex.GraphIso.Nauty.Sparse

variable {lab : Array Nat} {n i j : Nat}

theorem perm_bound (h : lab.toList.Perm (List.range n)) (hi : i < n) : lab[i]! < n := by
  have hs : lab.size = n := by simpa using h.length_eq
  have hm : lab[i]! ∈ lab.toList := by
    rw [getElem!_pos lab i (by omega), ← Array.getElem_toList (by simp; omega)]
    exact List.getElem_mem _
  exact List.mem_range.mp (h.mem_iff.mp hm)

theorem perm_injective (h : lab.toList.Perm (List.range n))
    (hi : i < n) (hj : j < n) (he : lab[i]! = lab[j]!) : i = j := by
  have hs : lab.size = n := by simpa using h.length_eq
  have hn : lab.toList.Nodup := h.nodup_iff.mpr List.nodup_range
  apply (hn.getElem_inj (hi := by simp; omega) (hj := by simp; omega)).mp
  simpa only [getElem!_pos lab i (by omega), getElem!_pos lab j (by omega),
    Array.getElem_toList] using he

end Hex.GraphIso.Nauty.Sparse
