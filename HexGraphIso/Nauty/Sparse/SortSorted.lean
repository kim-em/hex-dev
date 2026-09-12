/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SortSegments

public section

namespace Hex.GraphIso.Nauty.Sparse.Sort

set_option maxHeartbeats 800000

theorem children_append (start len left right : Nat) (rest : List (Nat × Nat)) :
    children start len left right rest = children start len left right [] ++ rest := by
  unfold children
  split <;> split <;> split <;> rfl

private theorem children_left (start len left right : Nat) (h : 1 < left) :
    (start, left) ∈ children start len left right [] := by
  unfold children
  split <;> split <;> (try split) <;> simp_all

private theorem children_right (start len left right : Nat) (h : 1 < right) :
    (start + len - right, right) ∈ children start len left right [] := by
  unfold children
  split <;> split <;> (try split) <;> simp_all

private theorem children_shape (lo hi start len left right : Nat) (rest : List (Nat × Nat))
    (hb : lo ≤ start ∧ start + len ≤ hi) (hl : left + right ≤ len)
    (hr : ∀ p ∈ rest, lo ≤ p.1 ∧ p.1 + p.2 ≤ hi)
    (hd : ((start, len) :: rest).Pairwise Apart) :
    (∀ p ∈ children start len left right rest, lo ≤ p.1 ∧ p.1 + p.2 ≤ hi) ∧
      (children start len left right rest).Pairwise Apart := by
  simp only [List.pairwise_cons] at hd
  have hleft (p : Nat × Nat) (hp : p ∈ rest) : Apart (start, left) p := by
    have h := hd.1 p hp
    dsimp [Apart] at *
    omega
  have hright (p : Nat × Nat) (hp : p ∈ rest) : Apart (start + len - right, right) p := by
    have h := hd.1 p hp
    dsimp [Apart] at *
    omega
  unfold children
  split <;> split <;> split
  all_goals simp_all only [List.mem_cons, forall_eq_or_imp, List.pairwise_cons]
  all_goals dsimp [Apart] at *
  all_goals grind

theorem Separated.pending {x y : Array Nat} {start len v left right : Nat}
    (h : Separated x y start (start + len) v (start + left) (start + len - right))
    (hr : right ≤ len) :
    Pending x y start (start + len) (children start len left right []) := by
  intro i j hil hij hjh
  have hb := h.bounds
  by_cases hjl : j < start + left
  · exact Or.inr ⟨(start, left), children_left _ _ _ _ (by omega), hil, hjl⟩
  · by_cases hir : start + len - right ≤ i
    · exact Or.inr ⟨(start + len - right, right), children_right _ _ _ _ (by omega),
        hir, by omega⟩
    · apply Or.inl
      by_cases hil' : i < start + left
      · have hi := h.lt i hil hil'
        by_cases hjr : j < start + len - right
        · have hj := h.eq j (by omega) hjr
          omega
        · have hj := h.gt j (by omega) hjh
          omega
      · have hi := h.eq i (by omega) (by omega)
        by_cases hjr : j < start + len - right
        · have hj := h.eq j (by omega) hjr
          omega
        · have hj := h.gt j (by omega) hjh
          omega

theorem Sorted.pending {x y : Array Nat} {start len : Nat} (h : Sorted x y start len) :
    Pending x y start (start + len) [] := by
  intro i j hil hij hjh
  apply Or.inl
  have hs := h (i - start) (j - start) (by omega) (by omega)
  simpa only [show start + (i - start) = i by omega,
    show start + (j - start) = j by omega] using hs

/-- The complete executed indirect sort orders its requested segment.
The proof uses the actual smaller-side-first stack, its established
exhaustion bound, and the exact partition and insertion operations. -/
theorem indirect_sorted (x y : Array Nat) (start len : Nat)
    (hb : start + len ≤ x.size) : Sorted (indirect x y start len) y start len := by
  let P := fun (a : Array Nat) (stack : List (Nat × Nat)) =>
    (∀ p ∈ stack, start ≤ p.1 ∧ p.1 + p.2 ≤ start + len) ∧
      stack.Pairwise Apart ∧ Pending a y start (start + len) stack
  have hout := indirect_induction x y start len hb P ?_ ?_ ?_
  · intro i j hij hj
    have h := hout.2.2 (start + i) (start + j) (by omega) (by omega) (by omega)
    simpa using h
  · dsimp [P]
    split
    · refine ⟨by simp, by simp, ?_⟩
      intro i j hil hij hjh
      exact Or.inr ⟨(start, len), by simp, hil, hjh⟩
    · refine ⟨by simp, by simp, ?_⟩
      intro i j hil hij hjh
      omega
  · intro a lo size rest has hbs hsmall hp
    have hseg := hp.1 (lo, size) (by simp)
    have hd := List.pairwise_cons.mp hp.2.1
    have he := insertion_outside a y lo size
    have hperm := segment_perm ⟨by omega, by omega⟩ (insertion_perm a y lo size (by omega)) he
    refine ⟨fun p hm => hp.1 p (by simp [hm]), hd.2, ?_⟩
    exact hp.2.2.replace hseg hd.1 he
      (fun q hql hqh => segment_mem (by rw [insertion_size]; omega) hperm ⟨hql, hqh⟩)
      (insertion_sorted a y lo size (by omega)).pending
  · intro a lo size rest has hbs hlarge hp
    have hseg := hp.1 (lo, size) (by simp)
    have hd := List.pairwise_cons.mp hp.2.1
    have hproper := partition_proper a y lo size (by omega) (by omega)
    have hshape := children_shape start (start + len) lo size _ _ rest hseg
      (Nat.le_of_lt hproper.1) (fun p hm => hp.1 p (by simp [hm])) hp.2.1
    have hperm := segment_perm ⟨by omega, by omega⟩ (partition_perm a y lo size) hproper.2
    refine ⟨hshape.1, hshape.2, ?_⟩
    rw [children_append]
    exact hp.2.2.replace hseg hd.1 hproper.2
      (fun q hql hqh => segment_mem (by rw [partition_size]; omega) hperm ⟨hql, hqh⟩)
      ((partition_order a y lo size (by omega) (by omega)).pending (by omega))

end Hex.GraphIso.Nauty.Sparse.Sort
