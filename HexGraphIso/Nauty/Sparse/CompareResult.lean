/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CompareMarks

public section

namespace Hex.GraphIso.Nauty.Sparse

namespace RowOrder

@[simp] theorem mem_values (row : List (Fin n)) (v : Fin n) :
    v.val ∈ row.map Fin.val ↔ v ∈ row := by
  constructor
  · intro hv
    obtain ⟨w, hw, he⟩ := List.mem_map.mp hv
    exact (Fin.ext he) ▸ hw
  · intro hv
    exact List.mem_map.mpr ⟨v, hv, rfl⟩

theorem eq_of_subset {a b : List (Fin n)}
    (ha : a.Pairwise (· < ·)) (hb : b.Pairwise (· < ·))
    (hlen : a.length = b.length) (hsub : a ⊆ b) : a = b := by
  have han : a.Nodup := ha.imp fun h => Fin.ne_of_lt h
  have hbn : b.Nodup := hb.imp fun h => Fin.ne_of_lt h
  apply List.Perm.eq_of_pairwise (le := (· < ·))
    (fun x y _ _ hxy hyx => False.elim (by omega)) ha hb
  apply (List.perm_ext_iff_of_nodup han hbn).mpr
  intro v
  refine ⟨fun hv => hsub hv, fun hv => ?_⟩
  by_cases hn : v ∈ a
  · exact hn
  · have hle := (List.nodup_cons.mpr ⟨hn, han⟩).length_le_of_subset
      (l₂ := b) (fun w hw => by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hv
        · exact hsub hw)
    simp only [List.length_cons] at hle
    omega

end RowOrder

namespace Diff

variable {n stamp : Nat} {old seen : List Nat} {marks : Array Nat} {mina : Nat}

theorem congr_seen (h : Diff n stamp old seen marks mina) {other : List Nat}
    (he : ∀ v, v ∈ seen ↔ v ∈ other) : Diff n stamp old other marks mina := by
  refine ⟨h.marks.congr (fun v _ => by simp [he v]), ?_, h.min_le, ?_, ?_⟩
  · exact fun v hv => h.seen_lt v ((he v).mpr hv)
  · exact fun hm => ⟨(he mina).mp (h.witness hm).1, (h.witness hm).2⟩
  · exact fun v hv hn => h.least v ((he v).mpr hv) hn

variable {a b : List (Fin n)}

theorem equal (h : Diff n stamp (b.map Fin.val) (a.map Fin.val) marks mina)
    (ha : a.Pairwise (· < ·)) (hb : b.Pairwise (· < ·))
    (hlen : a.length = b.length) (hm : mina = n) : a = b := by
  apply RowOrder.eq_of_subset ha hb hlen
  intro v hv
  exact (RowOrder.mem_values b v).mp (h.sentinel hm ((RowOrder.mem_values a v).mpr hv))

/-- A surviving old mark below the candidate's least exclusive vertex
determines a strict loss for the candidate row. -/
theorem smaller (h : Diff n stamp (b.map Fin.val) (a.map Fin.val) marks mina)
    (ha : a.Pairwise (· < ·)) (hb : b.Pairwise (· < ·)) (hlen : a.length = b.length)
    {v : Fin n} (hmark : marks[v.val]! = stamp) (hlt : v.val < mina) :
    rowCmp a b = .lt := by
  obtain ⟨hvb, hva⟩ := (h.marks.marked v.val v.isLt).mp hmark
  apply RowOrder.row_lt ha hb hlen ((RowOrder.mem_values b v).mp hvb)
    (fun hv => hva ((RowOrder.mem_values a v).mpr hv))
  intro w hw hn
  have hle := h.least w.val ((RowOrder.mem_values a w).mpr hw)
    (fun h => hn ((RowOrder.mem_values b w).mp h))
  show v.val < w.val
  omega

/-- Exhausting the old row without a smaller surviving mark determines a
strict win whenever the candidate has an exclusive vertex. -/
theorem greater (h : Diff n stamp (b.map Fin.val) (a.map Fin.val) marks mina)
    (ha : a.Pairwise (· < ·)) (hb : b.Pairwise (· < ·)) (hlen : a.length = b.length)
    (hm : mina < n)
    (hscan : ∀ v ∈ b.map Fin.val, marks[v]! = stamp → mina ≤ v) :
    rowCmp a b = .gt := by
  obtain ⟨hva, hvb⟩ := h.witness hm
  apply RowOrder.row_gt (v := ⟨mina, hm⟩) ha hb hlen
    ((RowOrder.mem_values a ⟨mina, hm⟩).mp hva)
    (fun hv => hvb ((RowOrder.mem_values b ⟨mina, hm⟩).mpr hv))
  intro w hw hn
  have hw' := (RowOrder.mem_values b w).mpr hw
  have hmark := (h.marks.marked w.val w.isLt).mpr
    ⟨hw', fun h => hn ((RowOrder.mem_values a w).mp h)⟩
  have hle := hscan w.val hw' hmark
  have hne : mina ≠ w.val := fun he => hvb (he ▸ hw')
  show mina < w.val
  omega

end Diff

end Hex.GraphIso.Nauty.Sparse
