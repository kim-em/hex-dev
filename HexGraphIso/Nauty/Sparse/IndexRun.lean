/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Index
public import HexGraphIso.Nauty.Sparse.Inverse
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 800000

/-- The executed bounded cell walk fills every cell index. It needs only a
bounded injective labelling and a partition closed at its last position. -/
theorem indexCells_valid (lab ptn starts ends : Array Nat) (level : Nat)
    (hptn : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hbound : ∀ i, i < n → lab[i]! < n)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hs : starts.size = n) (he : ends.size = n) :
    Index.Valid n lab ptn level (indexCells n lab ptn level starts ends).1
      (indexCells n lab ptn level starts ends).2 := by
  have cell (first : Nat) (hi : first < n)
      (hc : first = 0 ∨ ptn[first - 1]! ≤ level) :=
    isCell_cellEnd (ptn := ptn) (level := level) (a := first)
      (by omega) hc (by simpa [hptn] using hend)
  have last_lt (first : Nat) (hi : first < n) : cellEnd ptn level first < n := by
    have := cellEnd_lt (ptn := ptn) (level := level) (i := first)
      (by omega) (by simpa [hptn] using hend)
    omega
  unfold indexCells
  apply Id.of_wp_run_eq rfl (fun r : Array Nat × Array Nat =>
    Index.Valid n lab ptn level r.1 r.2)
  mvcgen invariants
  | inv1 => ⇓⟨cursor, s⟩ => ⌜
      cursor.prefix.length ≤ s.2.2 ∧ s.2.2 ≤ n ∧
      (s.2.2 = 0 ∨ ptn[s.2.2 - 1]! ≤ level) ∧
      Index.Prefix n lab ptn level s.2.2 s.1 s.2.1⌝
  | inv2 pref it suff hr state starts' pair ends' first hguard last newends jp htrivial hout =>
      ⇓⟨cursor, out⟩ => ⌜
        Index.Scatter n lab starts' out first (first + cursor.prefix.length) first⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.add_sub_cancel, Nat.sub_zero,
      Nat.div_one, List.length_append, List.length_cons, List.length_nil,
      List.length_range'] at *
  case vc1.step.isTrue =>
    rename_i hguard hin hr
    exact ⟨hguard, hin.2⟩
  case vc2.step =>
    rename_i pref it suff s os pair oe first hg last ne jp ht hout pre j suf out ns hin hr he
    have hi := List.eq_of_range'_eq_append_cons he
    have hm := List.mem_of_range'_eq_append_cons he
    simp only [Nat.one_mul, List.mem_range'_1] at hi hm
    rw [← hi] at hin
    have hb := last_lt s.2.2 (by omega)
    simpa only [hi, Nat.add_assoc] using hin.step hbound hinj (by omega) (by omega)
  case vc3.step.isFalse.isTrue.pre =>
    rename_i hin hr
    simpa using Index.Scatter.initial hin.2.2.2.starts_size
  case vc4.step.isFalse.isTrue.post.success =>
    rename_i pref it suff s os pair oe first hg last ne jp ht hout out nf hr hin
    have hb := last_lt s.2.2 (by omega)
    have hge : s.2.2 ≤ cellEnd ptn level s.2.2 := cellEnd_ge
    have hc := cell s.2.2 (by omega) hout.2.2.1
    refine ⟨by omega, by omega, Or.inr ?_, ?_⟩
    · have heq : s.2.2 + (cellEnd ptn level s.2.2 + 1 - s.2.2) - 1 =
          cellEnd ptn level s.2.2 := by omega
      simpa only [heq] using hc.2.2.2
    · apply hout.2.2.2.extend hc hge hb hin.size
      intro i hi
      rw [hin.get i hi, ite_eq_left ht]
      have he : s.2.2 + (cellEnd ptn level s.2.2 + 1 - s.2.2) =
          cellEnd ptn level s.2.2 + 1 := by omega
      simp only [he, Nat.lt_add_one_iff]
  case vc5.step.isFalse.isFalse =>
    rename_i pref it suff s os pair oe first hg last ne jp ht ns nf hin hr
    have hb := last_lt s.2.2 (by omega)
    have hge : s.2.2 ≤ cellEnd ptn level s.2.2 := cellEnd_ge
    have hc := cell s.2.2 (by omega) hin.2.2.1
    have hl : cellEnd ptn level s.2.2 = s.2.2 := by omega
    refine ⟨by omega, by omega, Or.inr ?_, ?_⟩
    · have heq : s.2.2 + (cellEnd ptn level s.2.2 + 1 - s.2.2) - 1 =
          cellEnd ptn level s.2.2 := by omega
      simpa only [heq] using hc.2.2.2
    · apply hin.2.2.2.extend hc hge hb (by simpa using hin.2.2.2.starts_size)
      have hscan := (Index.Scatter.initial (lab := lab) (first := s.2.2) (value := n)
        hin.2.2.2.starts_size).step hbound hinj (Nat.le_refl _) (by omega)
      intro i hi
      rw [hscan.get i hi, ite_eq_right ht, hl]
      simp only [Nat.lt_add_one_iff]
  case vc6.pre => exact ⟨Nat.le_refl _, Nat.zero_le _, Or.inl trivial, .zero hs he⟩
  case vc7.post.success =>
    rename_i hin
    have heq : _ = n := Nat.le_antisymm hin.2.1 hin.1
    simpa only [heq] using hin.2.2.2

/-- A checked public label supplies the bounded, injective raw labelling. -/
theorem indexCells_label (lab ptn starts ends : Array Nat) (level : Nat)
    (l : Label n) (hl : Label.ofArray? n lab = some l)
    (hptn : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hs : starts.size = n) (he : ends.size = n) :
    Index.Valid n lab ptn level (indexCells n lab ptn level starts ends).1
      (indexCells n lab ptn level starts ends).2 := by
  apply indexCells_valid lab ptn starts ends level hptn hend _ _ hs he
  · intro i hi
    rw [← Label.ofArray?_get hl i hi]
    exact (l.get ⟨i, hi⟩).isLt
  · intro i j hi hj hij
    have heq : l.get ⟨i, hi⟩ = l.get ⟨j, hj⟩ := Fin.ext (by
      simpa only [Label.ofArray?_get hl] using hij)
    exact congrArg Fin.val (l.perm.get_inj heq)

end Hex.GraphIso.Nauty.Sparse
