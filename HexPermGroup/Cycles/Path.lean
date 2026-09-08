/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Cycles

public section

namespace Hex.Perm.Cycle

/-- The array follows the permutation, with `next` immediately after its last
entry. This is the invariant maintained by the executable visit loop. -/
@[expose] def Follows (p : Perm n) (c : Array (Fin n)) (next : Fin n) : Prop :=
  ∀ i (hi : i < c.size), p.get c[i] = if hj : i + 1 < c.size then c[i + 1] else next

theorem follows_empty (p : Perm n) (x : Fin n) : Follows p #[] x := by
  intro i hi
  simp at hi

theorem Follows.push {p : Perm n} {c : Array (Fin n)} {x : Fin n} (h : Follows p c x) :
    Follows p (c.push x) (p.get x) := by
  intro i hi
  by_cases hc : i < c.size
  · by_cases hj : i + 1 < c.size
    · have hk : i + 1 < c.size + 1 := by omega
      simpa [Array.getElem_push, hc, hj, hk] using h i hc
    · have he : i + 1 = c.size := by omega
      simpa [Array.getElem_push, hc, hj, he] using h i hc
  · have he : i = c.size := by simp only [Array.size_push] at hi; omega
    subst i
    simp [Array.getElem_push]

theorem nodup_size {c : Array (Fin n)} (h : c.toList.Nodup) : c.size ≤ n := by
  have hh := List.nodup_subset_length_le h (l₂ := List.finRange n) (fun x _ => List.mem_finRange x)
  simpa using hh

theorem get_injective {c : Array (Fin n)} (h : c.toList.Nodup) {i j : Nat}
    (hi : i < c.size) (hj : j < c.size) (he : c[i] = c[j]) : i = j := by
  have hv : c.toList[i]'(by simpa using hi) = c.toList[j]'(by simpa using hj) := by
    rw [Array.getElem_toList, Array.getElem_toList]
    exact he
  exact h.getElem_inj.mp hv

/-- A path without repeated entries can first return only to its first entry:
a return to a later entry would give its predecessor two equal images. -/
theorem Follows.return_first {p : Perm n} {c : Array (Fin n)} {x : Fin n}
    (h : Follows p c x) (hd : c.toList.Nodup) (hx : x ∈ c) :
    ∃ hc : 0 < c.size, x = c[0] := by
  obtain ⟨j, hj, he⟩ := Array.mem_iff_getElem.mp hx
  have hc : 0 < c.size := by omega
  refine ⟨hc, ?_⟩
  by_cases hz : j = 0
  · simpa [hz] using he.symm
  · have hp : j - 1 < c.size := by omega
    have hl : c.size - 1 < c.size := by omega
    have hprev := h (j - 1) hp
    have hlast := h (c.size - 1) hl
    have hje : j - 1 + 1 = j := by omega
    have hle : c.size - 1 + 1 = c.size := by omega
    simp only [hje, hj, dite_true, he] at hprev
    simp only [hle, Nat.lt_irrefl, dite_false] at hlast
    have hv := p.get_inj (hprev.trans hlast.symm)
    have hh : j - 1 = c.size - 1 := get_injective hd hp hl hv
    omega

/-- A nonempty, duplicate-free array records one complete directed cycle,
including the singleton cycle of a fixed point. -/
@[expose] def Valid (p : Perm n) (c : Array (Fin n)) : Prop :=
  c.toList.Nodup ∧ ∃ hc : 0 < c.size, Follows p c c[0]

theorem Follows.valid {p : Perm n} {c : Array (Fin n)} {x : Fin n}
    (h : Follows p c x) (hd : c.toList.Nodup) (hx : x ∈ c) : Valid p c := by
  obtain ⟨hc, he⟩ := h.return_first hd hx
  exact ⟨hd, hc, he ▸ h⟩

theorem Valid.nonempty {p : Perm n} {c : Array (Fin n)} (h : Valid p c) : 0 < c.size := h.2.choose

/-- The wrap-around successor equation gives a direct reconstruction rule. -/
theorem Valid.get {p : Perm n} {c : Array (Fin n)} (h : Valid p c) (i : Nat) (hi : i < c.size) :
    p.get c[i] = c[(i + 1) % c.size]'(Nat.mod_lt _ h.nonempty) := by
  obtain ⟨hd, hc, hf⟩ := h
  have he := hf i hi
  by_cases hj : i + 1 < c.size
  · simpa [hj, Nat.mod_eq_of_lt hj] using he
  · have hk : i + 1 = c.size := by omega
    simpa [hj, hk] using he

theorem Valid.closed {p : Perm n} {c : Array (Fin n)} (h : Valid p c) {x : Fin n} (hx : x ∈ c) :
    p.get x ∈ c := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
  rw [h.get i hi]
  exact Array.getElem_mem _

theorem Valid.mem_iff {p : Perm n} {c : Array (Fin n)} (h : Valid p c) (x : Fin n) :
    p.get x ∈ c ↔ x ∈ c := by
  refine ⟨?_, h.closed⟩
  intro hx
  obtain ⟨j, hj, he⟩ := Array.mem_iff_getElem.mp hx
  let i := if j = 0 then c.size - 1 else j - 1
  have hc := h.nonempty
  have hi : i < c.size := by dsimp only [i]; split <;> omega
  have hm : (i + 1) % c.size = j := by
    dsimp only [i]
    split
    · rename_i hz
      have hl : c.size - 1 + 1 = c.size := by omega
      simp [hl, hz]
    · rename_i hz
      have hl : j - 1 + 1 = j := by omega
      simp [hl, Nat.mod_eq_of_lt hj]
  have hp := h.get i hi
  have hp' : p.get c[i] = c[j] := by simpa only [hm] using hp
  have hv := p.get_inj (hp'.trans he)
  exact hv ▸ Array.getElem_mem hi

theorem Valid.pow_get {p : Perm n} {c : Array (Fin n)} (h : Valid p c) (k i : Nat) (hi : i < c.size) :
    (p.pow k).get c[i] = c[(i + k) % c.size]'(Nat.mod_lt _ h.nonempty) := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt hi]
  | succ k ih =>
    rw [Perm.pow_succ, Perm.get_comp, ih, h.get]
    simp only [Nat.mod_add_mod, Nat.add_assoc]

theorem Valid.period {p : Perm n} {c : Array (Fin n)} (h : Valid p c) (x : Fin n) (hx : x ∈ c) :
    (p.pow c.size).get x = x := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
  rw [h.pow_get c.size i hi]
  simp [Nat.mod_eq_of_lt hi]

/-- Returning the first point forces the exponent to be divisible by the
cycle length. In particular, no smaller positive period is possible. -/
theorem Valid.dvd_period {p : Perm n} {c : Array (Fin n)} (h : Valid p c) (k : Nat)
    (hk : (p.pow k).get (c[0]'h.nonempty) = c[0]'h.nonempty) : c.size ∣ k := by
  rw [h.pow_get k 0 h.nonempty] at hk
  simp only [Nat.zero_add] at hk
  exact Nat.dvd_of_mod_eq_zero (get_injective h.1 (Nat.mod_lt _ h.nonempty) h.nonempty hk)

end Hex.Perm.Cycle
