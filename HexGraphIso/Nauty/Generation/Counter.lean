/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Invariant.Cursor
import all HexGraphIso.Nauty.Invariant.Cursor

public section

namespace Hex.GraphIso.Nauty.Generation

/-- The counter is the number of qualifying vertices passed by the
actual ascending cursor. The witness records all of them exactly once. -/
def Counter (P : Fin n → Prop) (cursor : Option Nat) (index : Nat) : Prop :=
  ∃ seen : List (Fin n), seen.Nodup ∧ seen.length = index ∧
    ∀ v, v ∈ seen ↔ P v ∧ ¬ After cursor v.val

namespace Counter

variable {P : Fin n → Prop} {cursor : Option Nat} {index : Nat}

theorem start (P : Fin n → Prop) : Counter P none 0 :=
  ⟨[], by simp, rfl, fun _ => by simp [After]⟩

/-- Advancing the real target cursor adds precisely its current vertex
when the executed mark test agrees with the qualifying property. -/
theorem advance (h : Counter P cursor index) {cell : VSet n} {tv : Fin n} {mark : Bool}
    (hwindow : ∀ v, P v → cell.mem v.val = true)
    (hnext : cell.nextElem cursor = some tv.val) (hmark : mark = true ↔ P tv) :
    Counter P (some tv.val) (if mark then index + 1 else index) := by
  obtain ⟨seen, hnd, hlen, hseen⟩ := h
  have ha := nextElem_after hnext
  have hn : tv ∉ seen := fun hm => (hseen tv).mp hm |>.2 ha
  have hsplit (v : Fin n) : P v ∧ ¬ After (some tv.val) v.val ↔
      (v = tv ∧ P tv) ∨ (P v ∧ ¬ After cursor v.val) := by
    constructor
    · rintro ⟨hp, hv⟩
      rcases after_or_not cursor v.val with hb | hb
      · have hle := nextElem_le hnext (hwindow v hp) hb
        have he : v = tv := Fin.ext (by change ¬ tv.val < v.val at hv; omega)
        exact Or.inl ⟨he, he ▸ hp⟩
      · exact Or.inr ⟨hp, hb⟩
    · rintro (⟨rfl, hp⟩ | ⟨hp, hb⟩)
      · exact ⟨hp, by simp [After]⟩
      · refine ⟨hp, ?_⟩
        cases cursor with
        | none => exact (hb trivial).elim
        | some c =>
          change ¬ c < v.val at hb
          change c < tv.val at ha
          change ¬ tv.val < v.val
          omega
  cases mark with
  | false =>
    have hp : ¬ P tv := fun hp => Bool.false_ne_true (hmark.mpr hp)
    refine ⟨seen, hnd, hlen, fun v => ?_⟩
    rw [hseen, hsplit]
    simp only [hp, and_false, false_or]
  | true =>
    have hp : P tv := hmark.mp rfl
    refine ⟨tv :: seen, List.nodup_cons.mpr ⟨hn, hnd⟩, by simpa using congrArg Nat.succ hlen,
      fun v => ?_⟩
    rw [List.mem_cons, hseen, hsplit]
    simp only [hp, and_true]

/-- Exhausting the actual target set identifies the accumulated index
with the cardinality of the qualifying vertices in the whole graph. -/
theorem finish (h : Counter P cursor index) {cell : VSet n}
    (hwindow : ∀ v, P v → cell.mem v.val = true) (hnext : cell.nextElem cursor = none)
    [DecidablePred P] : index = (List.finRange n).countP (fun v => decide (P v)) := by
  obtain ⟨seen, hnd, hlen, hseen⟩ := h
  have hm : ∀ v, v ∈ seen ↔ P v := fun v => ⟨fun hv => ((hseen v).mp hv).1,
    fun hp => (hseen v).mpr ⟨hp, no_child_after hnext v.val (hwindow v hp)⟩⟩
  have he : seen.Perm ((List.finRange n).filter (fun v => decide (P v))) :=
    (List.perm_ext_iff_of_nodup hnd ((List.nodup_finRange n).filter _)).mpr
      (fun v => by simp [hm, List.mem_finRange])
  exact hlen.symm.trans (he.length_eq.trans List.countP_eq_length_filter.symm)

end Counter
end Hex.GraphIso.Nauty.Generation
