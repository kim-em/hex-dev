/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Partition

public section

namespace Hex.PermGroup.Partition

/-- The discrete partition, including the empty partition in degree zero. -/
@[expose] def discrete (n : Nat) : Partition n where
  labels := Hex.Vector.ofFn' id
  least _ := by simp
  idem _ := by simp

@[simp] theorem discrete_same (x y : Fin n) : (discrete n).Same x y ↔ x = y := by
  simp [Same, discrete]

/-- The single-block partition; in degree zero there are no blocks. -/
@[expose] def indiscrete (n : Nat) : Partition n where
  labels := Hex.Vector.ofFn' fun x : Fin n => ⟨0, Nat.zero_lt_of_lt x.isLt⟩
  least x := by
    simp only [Hex.Vector.getElem_ofFn']
    exact Nat.zero_le x.val
  idem _ := by simp

@[simp] theorem indiscrete_same (x y : Fin n) : (indiscrete n).Same x y := by
  simp [Same, indiscrete]

theorem equivalence (p : Partition n) : Equivalence p.Same :=
  ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- Every block of `p` lies in one equivalence class of `R`. -/
@[expose] def Refines (p : Partition n) (R : Fin n → Fin n → Prop) : Prop :=
  ∀ x y, p.Same x y → R x y

/-- Block representatives in increasing point order. -/
@[expose] def roots (p : Partition n) : List (Fin n) :=
  (List.finRange n).filter fun x => p.labels[x.val] = x

@[simp] theorem mem_roots (p : Partition n) (x : Fin n) :
    x ∈ p.roots ↔ p.labels[x.val] = x := by
  simp [roots]

theorem roots_nodup (p : Partition n) : p.roots.Nodup :=
  (List.nodup_finRange n).filter _

theorem roots_pos (p : Partition n) (hn : 0 < n) : 0 < p.roots.length := by
  apply List.length_pos_iff_exists_mem.mpr
  exact ⟨p.labels[0], (p.mem_roots _).mpr (p.idem ⟨0, hn⟩)⟩

/-- Quick-find union: redirect one root and all its points to a smaller root.
The direct label array keeps each find constant-time and each union linear. -/
@[expose] def mergeRoots (p : Partition n) (a b : Fin n)
    (ha : p.labels[a.val] = a) (_hb : p.labels[b.val] = b) (hab : a ≤ b) : Partition n where
  labels := Hex.Vector.ofFn' fun x => if p.labels[x.val] = b then a else p.labels[x.val]
  least x := by
    simp only [Hex.Vector.getElem_ofFn']
    split
    · rename_i hx
      exact Fin.le_trans hab (hx ▸ p.least x)
    · exact p.least x
  idem x := by
    simp only [Hex.Vector.getElem_ofFn']
    split
    · simp [ha]
    · rename_i hx
      simp [p.idem x, hx]

theorem mergeRoots_coarsens (p : Partition n) (a b : Fin n) (ha hb hab) :
    p.Refines (p.mergeRoots a b ha hb hab).Same := by
  intro x y h
  simp only [Same, mergeRoots, Hex.Vector.getElem_ofFn']
  rw [h]

theorem mergeRoots_pair (p : Partition n) (a b : Fin n) (ha hb hab) :
    (p.mergeRoots a b ha hb hab).Same a b := by
  simp [Same, mergeRoots, ha, hb]

theorem mergeRoots_least (p : Partition n) (a b : Fin n) (ha hb hab)
    {R : Fin n → Fin n → Prop} (hR : Equivalence R) (hp : p.Refines R) (h : R a b) :
    (p.mergeRoots a b ha hb hab).Refines R := by
  have hr (x : Fin n) : R x p.labels[x.val] := hp _ _ (p.idem x).symm
  have step (x : Fin n) : R x (if p.labels[x.val] = b then a else p.labels[x.val]) := by
    split
    · rename_i hx
      exact hR.trans (hx ▸ hr x) (hR.symm h)
    · exact hr x
  intro x y he
  simp only [Same, mergeRoots, Hex.Vector.getElem_ofFn'] at he
  exact hR.trans (he ▸ step x) (hR.symm (step y))

theorem mergeRoots_root (p : Partition n) (a b : Fin n) (ha hb hab) (hne : a ≠ b)
    (x : Fin n) :
    (p.mergeRoots a b ha hb hab).labels[x.val] = x ↔ p.labels[x.val] = x ∧ x ≠ b := by
  simp only [mergeRoots, Hex.Vector.getElem_ofFn']
  split
  · rename_i hx
    constructor
    · intro he
      subst x
      exact False.elim (hne (ha.symm.trans hx))
    · rintro ⟨hr, hn⟩
      exact False.elim (hn (hr.symm.trans hx))
  · rename_i hx
    constructor
    · intro he
      exact ⟨he, fun h => hx (he.trans h)⟩
    · exact And.left

theorem roots_mergeRoots (p : Partition n) (a b : Fin n) (ha hb hab) (hne : a ≠ b) :
    (p.mergeRoots a b ha hb hab).roots = p.roots.erase b := by
  rw [p.roots_nodup.erase_eq_filter]
  simp only [roots, List.filter_filter]
  apply List.filter_congr
  intro x _
  apply Bool.eq_iff_iff.mpr
  simp [p.mergeRoots_root a b ha hb hab hne x, and_comm]

/-- Merge the two blocks, preserving canonical least-point labels. -/
@[expose] def merge (p : Partition n) (x y : Fin n) : Partition n :=
  let a := p.labels[x.val]
  let b := p.labels[y.val]
  if h : a ≤ b then p.mergeRoots a b (p.idem x) (p.idem y) h
  else p.mergeRoots b a (p.idem y) (p.idem x) (by omega)

theorem merge_coarsens (p : Partition n) (x y : Fin n) : p.Refines (p.merge x y).Same := by
  simp only [merge]
  split <;> exact p.mergeRoots_coarsens _ _ _ _ _

theorem merge_pair (p : Partition n) (x y : Fin n) : (p.merge x y).Same x y := by
  have hx := p.merge_coarsens x y x p.labels[x.val] (p.idem x).symm
  have hy := p.merge_coarsens x y y p.labels[y.val] (p.idem y).symm
  apply Eq.trans hx
  apply Eq.trans _ hy.symm
  simp only [merge]
  split
  · exact p.mergeRoots_pair ..
  · exact (p.mergeRoots_pair ..).symm

/-- Union introduces exactly the equivalences forced by the old blocks and
the requested pair, for any target equivalence relation. -/
theorem merge_least (p : Partition n) (x y : Fin n)
    {R : Fin n → Fin n → Prop} (hR : Equivalence R) (hp : p.Refines R) (h : R x y) :
    (p.merge x y).Refines R := by
  have hr := hR.trans (hR.symm (hp _ _ (p.idem x).symm))
    (hR.trans h (hp _ _ (p.idem y).symm))
  simp only [merge]
  split
  · exact p.mergeRoots_least _ _ _ _ _ hR hp hr
  · exact p.mergeRoots_least _ _ _ _ _ hR hp (hR.symm hr)

/-- Each effective union removes exactly one block. -/
theorem roots_merge (p : Partition n) (x y : Fin n) (h : ¬p.Same x y) :
    (p.merge x y).roots.length + 1 = p.roots.length := by
  have hn : 0 < p.roots.length := p.roots_pos (Nat.zero_lt_of_lt x.isLt)
  simp only [merge]
  split
  · rw [p.roots_mergeRoots _ _ _ _ _ h, List.length_erase_of_mem (by simpa using p.idem y)]
    omega
  · rw [p.roots_mergeRoots _ _ _ _ _ (Ne.symm h),
      List.length_erase_of_mem (by simpa using p.idem x)]
    omega

end Hex.PermGroup.Partition
