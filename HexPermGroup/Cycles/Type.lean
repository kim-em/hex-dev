/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Cycles.Scan

public section

namespace Hex.Perm.Cycle

theorem counts_size (cs : List (Array (Fin n))) (a : Array Nat) :
    (cs.foldl (fun counts c => counts.modify c.size (· + 1)) a).size = a.size := by
  induction cs generalizing a with
  | nil => rfl
  | cons c cs ih => simp only [List.foldl_cons, ih, Array.size_modify]

theorem counts_get (cs : List (Array (Fin n))) (a : Array Nat) (k : Nat) (hk : k < a.size) :
    (cs.foldl (fun counts c => counts.modify c.size (· + 1)) a)[k]! =
      a[k]! + (cs.map Array.size).count k := by
  induction cs generalizing a with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih _ (by simpa using hk)]
    have hk' : k < (a.modify c.size (· + 1)).size := by simpa using hk
    rw [getElem!_pos (a.modify c.size (· + 1)) k hk', Array.getElem_modify,
      getElem!_pos a k hk]
    by_cases he : c.size = k
    · simp [he, Nat.add_assoc, Nat.add_comm]
    · simp [he]

theorem expand_count (ks : List Nat) (f : Nat → Nat) (k : Nat) (hd : ks.Nodup) :
    (ks.flatMap (fun j => List.replicate (f j) j)).count k = if k ∈ ks then f k else 0 := by
  induction ks with
  | nil => simp
  | cons j js ih =>
    have ht := ih hd.of_cons
    by_cases he : j = k
    · subst j
      simp [ht, (List.nodup_cons.mp hd).1]
    · simp [List.count_replicate, ht, he, Ne.symm he]

theorem expand_sorted (ks : List Nat) (f : Nat → Nat) (hs : ks.Pairwise (· ≤ ·)) :
    (ks.flatMap (fun j => List.replicate (f j) j)).Pairwise (· ≤ ·) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro j _
    simp
  · apply hs.imp
    intro a b hab x hx y hy
    have hx' := (List.mem_replicate.mp hx).2
    have hy' := (List.mem_replicate.mp hy).2
    simpa [hx', hy'] using hab

end Hex.Perm.Cycle

namespace Hex.Perm

/-- The length histogram retains exactly the multiplicity of every emitted
cycle length, including singleton fixed points. -/
theorem cycleType_count (p : Perm n) (k : Nat) :
    p.cycleType.toList.count k = (p.allCycles.toList.map Array.size).count k := by
  simp only [cycleType, Array.toList_flatMap, Array.toList_replicate]
  rw [Cycle.expand_count _ _ _ List.nodup_range]
  by_cases hk : k < n + 1
  · rw [ite_eq_left (List.mem_range.mpr hk), ← Array.foldl_toList, Cycle.counts_get]
    · simp [getElem!_pos, hk]
    · simpa using hk
  · rw [ite_eq_right (by simpa using hk)]
    symm
    apply List.count_eq_zero.mpr
    intro hm
    obtain ⟨c, hc, he⟩ := List.mem_map.mp hm
    have hs := Cycle.nodup_size (p.allCycles_valid c (by simpa using hc)).1
    omega

theorem cycleType_perm (p : Perm n) :
    p.cycleType.toList.Perm (p.allCycles.toList.map Array.size) :=
  List.perm_iff_count.mpr p.cycleType_count

theorem cycleType_sorted (p : Perm n) : p.cycleType.toList.Pairwise (· ≤ ·) := by
  simp only [cycleType, Array.toList_flatMap, Array.toList_replicate]
  apply Cycle.expand_sorted
  exact List.pairwise_lt_range.imp Nat.le_of_lt

theorem cycleType_sum (p : Perm n) : p.cycleType.toList.sum = n :=
  p.cycleType_perm.sum_nat.trans p.allCycles_length

theorem cycleType_size (p : Perm n) : p.cycleType.size = p.allCycles.size := by
  simpa using p.cycleType_perm.length_eq

end Hex.Perm
