/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Kernel.Sound
public import HexPermGroup.Perm.Images

public section

namespace Hex.PermGroup.Kernel

open Hex.Kernel

variable {n : Nat}

/-- Bitset check that `l` lists distinct values below `n`, none of them in `seen`. -/
@[expose] def imagesDistinct (n : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | x :: xs, seen =>
    Nat.blt x n && Nat.beq (Nat.land (Nat.shiftRight seen x) 1) 0 &&
      imagesDistinct n xs (Nat.lor seen (Nat.shiftLeft 1 x))

/-- `l` is the image list of a permutation of `Fin n`, checked in time linear in `n`. -/
@[expose] def imagesOk (n : Nat) (l : List Nat) : Bool :=
  Nat.beq l.length n && imagesDistinct n l 0

/-- The packing of an image list. -/
@[expose] def packList (n : Nat) (l : List Nat) : Nat :=
  packFn (width n) (fun i => l.getD i 0) n

theorem imagesDistinct_spec (n : Nat) : ∀ (l : List Nat) (seen : Nat),
    imagesDistinct n l seen = true →
      (∀ x ∈ l, x < n ∧ seen.testBit x = false) ∧ l.Nodup
  | [], _, _ => by simp
  | x :: xs, seen, h => by
    simp only [imagesDistinct, Bool.and_eq_true, blt_eq_decide, beq_eq_decide,
      decide_eq_true_eq] at h
    obtain ⟨⟨hx, hbit⟩, hrest⟩ := h
    have hxbit : seen.testBit x = false := by
      simp only [land_eq, shiftRight_eq, Nat.and_one_is_mod] at hbit
      simp [Nat.testBit, hbit]
    obtain ⟨ih₁, ih₂⟩ := imagesDistinct_spec n xs _ hrest
    have hne : ∀ y ∈ xs, y < n ∧ seen.testBit y = false ∧ y ≠ x := by
      intro y hy
      obtain ⟨hy₁, hy₂⟩ := ih₁ y hy
      simp only [lor_eq, shiftLeft_eq, Nat.one_shiftLeft, Nat.testBit_or,
        Nat.testBit_two_pow, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hy₂
      exact ⟨hy₁, hy₂.1, fun h => hy₂.2 h.symm⟩
    refine ⟨?_, List.nodup_cons.mpr ⟨fun hmem => (hne x hmem).2.2 rfl, ih₂⟩⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨hx, hxbit⟩
    · exact ⟨(hne y hy).1, (hne y hy).2.1⟩

theorem imagesOk_spec {n : Nat} {l : List Nat} (h : imagesOk n l = true) :
    l.length = n ∧ (∀ x ∈ l, x < n) ∧ l.Nodup := by
  simp only [imagesOk, Bool.and_eq_true, beq_eq_decide, decide_eq_true_eq] at h
  obtain ⟨hl, hd⟩ := imagesDistinct_spec n l 0 h.2
  exact ⟨h.1, fun x hx => (hl x hx).1, hd⟩

/-- Every value below `n` occurs in an accepted image list. -/
theorem mem_of_imagesOk {n : Nat} {l : List Nat} (h : imagesOk n l = true) {i : Nat}
    (hi : i < n) : i ∈ l := by
  obtain ⟨hlen, hlt, hnd⟩ := imagesOk_spec h
  apply Decidable.byContradiction
  intro hni
  have hnodup : (i :: l).Nodup := List.nodup_cons.mpr ⟨hni, hnd⟩
  have hsub : i :: l ⊆ List.range n := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_range.mpr hi
    · exact List.mem_range.mpr (hlt x hx)
  have hlen := hnodup.length_le_of_subset hsub
  simp only [List.length_cons, List.length_range] at hlen
  omega

theorem ofNatArray_permOfImages {n : Nat} {l : List Nat} (h : imagesOk n l = true) :
    ∃ p, Perm.ofNatArray? n l.toArray = some p := by
  obtain ⟨hlen, hlt, hnd⟩ := imagesOk_spec h
  have hc : l.toArray.size = n ∧ ∀ i, (hi : i < l.toArray.size) → l.toArray[i] < n :=
    ⟨by simpa using hlen, fun i hi => hlt _ (by simp)⟩
  rw [Perm.ofNatArray?]
  split
  case isFalse hn => exact absurd hc hn
  apply Option.isSome_iff_exists.mp
  rw [Perm.isSome_ofVector?]
  have hmap : ((Hex.Vector.ofFn' fun i : Fin n =>
      (⟨l.toArray[i.val]'(hc.1.symm ▸ i.isLt), hc.2 i.val (hc.1.symm ▸ i.isLt)⟩ : Fin n)).toList.map
        Fin.val) = l := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h₁ h₂
      simp [Hex.Vector.ofFn'_eq_ofFn]
  constructor
  · exact List.Pairwise.of_map Fin.val (fun a b (h : a.val ≠ b.val) he => h (congrArg Fin.val he)) (by rw [hmap]; exact hnd)
  · intro i
    have : i.val ∈ l := mem_of_imagesOk h i.isLt
    rw [← hmap] at this
    obtain ⟨j, hj, hji⟩ := List.mem_map.mp this
    rwa [Fin.ext hji] at hj

/-- The entries of a checked raw permutation array. -/
theorem val_get_of_ofNatArray? {a : Array Nat} {p : Perm n}
    (h : Perm.ofNatArray? n a = some p) (i : Fin n) :
    (p.get i).val = a[i.val]! := by
  rw [Perm.ofNatArray?] at h
  split at h
  · rename_i hc
    have hsz : i.val < a.size := hc.1.symm ▸ i.isLt
    rw [Perm.get, Perm.vec_of_ofVector? h]
    rw [getElem!_pos a i.val hsz]
    simp
  · simp at h

theorem pack_ofImages {n : Nat} {l : List Nat} (h : imagesOk n l = true) :
    pack (Perm.ofImages n l) = packList n l := by
  obtain ⟨p, hp⟩ := ofNatArray_permOfImages h
  have hperm : Perm.ofImages n l = p := by simp [Perm.ofImages, hp]
  rw [hperm]
  obtain ⟨hlen, hlt, -⟩ := imagesOk_spec h
  have hval : ∀ i : Fin n, (p.get i).val = l.getD i.val 0 := by
    intro i
    rw [val_get_of_ofNatArray? hp]
    simp [List.getD_eq_getElem?_getD]
  have hbound : ∀ i < n, l.getD i 0 < 2 ^ width n := fun i hi =>
    Nat.lt_trans (hlt _ (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact List.getElem_mem _))
      (lt_two_pow_width n)
  refine Canon.eq_of_rep (canon_pack p) (canon_packFn _ hbound) (rep_pack p) fun i => ?_
  rw [packList, field_packFn _ _ n hbound _ i.isLt, ← hval]


end Hex.PermGroup.Kernel
