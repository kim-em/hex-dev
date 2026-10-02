/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SortStack
public import HexGraphIso.Nauty.Sparse.SortFinal

public section

namespace Hex.GraphIso.Nauty.Sparse.Sort

set_option maxHeartbeats 800000

/-- A whole-array permutation supported inside a segment induces a
permutation of that segment, cancelling the fixed exterior. -/
theorem segment_perm {a b : Array Nat} {lo hi : Nat}
    (hb : lo ≤ hi ∧ hi ≤ a.size) (hp : b.toList.Perm a.toList)
    (he : ∀ q, q < lo ∨ hi ≤ q → b[q]! = a[q]!) :
    (b.extract lo hi).toList.Perm (a.extract lo hi).toList := by
  have hs : b.size = a.size := hp.length_eq
  have hpre := extract_eq hs 0 lo (fun q _ hq => he q (.inl hq))
  have hpost := extract_eq hs hi a.size (fun q hq _ => he q (.inr hq))
  have hbs := congrArg Array.toList (split_three b lo hi a.size hb.1 hb.2 hs).symm
  have has := congrArg Array.toList (split_three a lo hi a.size hb.1 hb.2 rfl).symm
  simp only [Array.toList_append] at hbs has
  rw [hbs, has, hpre, hpost] at hp
  exact (List.perm_append_left_iff _).mp ((List.perm_append_right_iff _).mp hp)

theorem segment_mem {a b : Array Nat} {lo hi q : Nat}
    (hsize : hi ≤ b.size) (hp : (b.extract lo hi).toList.Perm (a.extract lo hi).toList)
    (hq : lo ≤ q ∧ q < hi) : ∃ r, lo ≤ r ∧ r < hi ∧ b[q]! = a[r]! := by
  have hm : b[q]! ∈ (b.extract lo hi).toList := by
    rw [Array.mem_toList_iff, Array.mem_extract_iff_getElem]
    refine ⟨q - lo, by omega, ?_⟩
    simp only [show lo + (q - lo) = q by omega, getElem!_pos b q (by omega)]
  have hm' := hp.mem_iff.mp hm
  rw [Array.mem_toList_iff, Array.mem_extract_iff_getElem] at hm'
  obtain ⟨r, hr, he⟩ := hm'
  exact ⟨lo + r, by omega, by omega,
    by simpa only [getElem!_pos a (lo + r) (by omega)] using he.symm⟩

/-- Two pending segments do not overlap. -/
@[expose] def Apart (p q : Nat × Nat) : Prop :=
  p.1 + p.2 ≤ q.1 ∨ q.1 + q.2 ≤ p.1

/-- All ordering obligations except pairs still in one pending segment. -/
@[expose] def Pending (x y : Array Nat) (lo hi : Nat) (stack : List (Nat × Nat)) : Prop :=
  ∀ i j, lo ≤ i → i < j → j < hi →
    y[x[i]!]! ≤ y[x[j]!]! ∨ ∃ p ∈ stack, p.1 ≤ i ∧ j < p.1 + p.2

/-- Replacing one segment by a permutation cannot disturb its ordering
against the disjoint pending segments or the already completed entries. -/
theorem Pending.replace {a b y : Array Nat} {lo hi start len : Nat}
    {rest parts : List (Nat × Nat)}
    (h : Pending a y lo hi ((start, len) :: rest))
    (hb : lo ≤ start ∧ start + len ≤ hi)
    (hd : ∀ p ∈ rest, Apart (start, len) p)
    (he : ∀ q, q < start ∨ start + len ≤ q → b[q]! = a[q]!)
    (hm : ∀ q, start ≤ q → q < start + len →
      ∃ r, start ≤ r ∧ r < start + len ∧ b[q]! = a[r]!)
    (hl : Pending b y start (start + len) parts) :
    Pending b y lo hi (parts ++ rest) := by
  intro i j hil hij hjh
  have hrest (p : Nat × Nat) (hp : p ∈ rest) (q : Nat)
      (hql : start ≤ q) (hqh : q < start + len) :
      ¬(p.1 ≤ q ∧ q < p.1 + p.2) := by
    have hdp := hd p hp
    dsimp [Apart] at hdp
    omega
  by_cases hi : start ≤ i ∧ i < start + len
  · by_cases hj : start ≤ j ∧ j < start + len
    · rcases hl i j hi.1 hij hj.2 with hkey | ⟨p, hp, hpi, hpj⟩
      · exact Or.inl hkey
      · exact Or.inr ⟨p, List.mem_append_left _ hp, hpi, hpj⟩
    · obtain ⟨r, hrl, hrh, her⟩ := hm i hi.1 hi.2
      have hjr : r < j := by omega
      rw [her, he j (by omega)]
      rcases h r j (by omega) hjr hjh with hkey | ⟨p, hp, hpr, hpj⟩
      · exact Or.inl hkey
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · omega
        · exact False.elim (hrest p hp r hrl hrh ⟨hpr, by omega⟩)
  · by_cases hj : start ≤ j ∧ j < start + len
    · obtain ⟨r, hrl, hrh, her⟩ := hm j hj.1 hj.2
      have hir : i < r := by omega
      rw [he i (by omega), her]
      rcases h i r hil hir (by omega) with hkey | ⟨p, hp, hpi, hpr⟩
      · exact Or.inl hkey
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · omega
        · exact False.elim (hrest p hp r hrl hrh ⟨by omega, hpr⟩)
    · rw [he i (by omega), he j (by omega)]
      rcases h i j hil hij hjh with hkey | ⟨p, hp, hpi, hpj⟩
      · exact Or.inl hkey
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · omega
        · exact Or.inr ⟨p, List.mem_append_right _ hp, hpi, hpj⟩

end Hex.GraphIso.Nauty.Sparse.Sort
