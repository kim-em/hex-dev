/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SpecTree
public import HexGraphIso.Nauty.Sparse.PrefixKey

public section

namespace Hex.GraphIso.Nauty.Sparse

theorem SpecLeaf.prepend_key (G : Hex.SparseGraph n) (c : Nat) (l : SpecLeaf n) :
    (l.prepend c).key G = prefixKey [c] (l.key G) := rfl

namespace Replay

/-- A successful replay bounds every leaf and records whether the claimed
key is attained. The label witness comes from an executed tree leaf. -/
structure Valid (G : Hex.SparseGraph n) (B : Key n) (leaves : List (SpecLeaf n))
    (attained : Bool) : Prop where
  bound : ∀ l ∈ leaves, Key.Le (l.key G) B
  attains : attained = true ↔ ∃ l ∈ leaves, l.key G = B

/-- Combine all child checks, propagating rejection and recording attainment.
The explicit recursion also reduces after importing the checker. -/
@[expose] def all (check : α → Option Bool) : List α → Option Bool
  | [] => some false
  | x :: xs => do
    let a ← check x
    let b ← all check xs
    pure (a || b)

theorem all_cons {check : α → Option Bool} {x : α} {xs : List α} {a : Bool} :
    all check (x :: xs) = some a ↔
      ∃ b c, check x = some b ∧ all check xs = some c ∧ (b || c) = a := by
  cases hx : check x <;> cases hs : all check xs <;> simp [all, hx, hs]

theorem valid_nil (G : Hex.SparseGraph n) (B : Key n) : Valid G B [] false := by
  constructor <;> simp

theorem Valid.append {G : Hex.SparseGraph n} {B : Key n}
    {xs ys : List (SpecLeaf n)} {a b : Bool}
    (hx : Valid G B xs a) (hy : Valid G B ys b) :
    Valid G B (xs ++ ys) (a || b) := by
  constructor
  · intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact hx.bound l hl
    · exact hy.bound l hl
  · simp only [Bool.or_eq_true, hx.attains, hy.attains, List.mem_append]
    constructor
    · rintro (⟨l, hl, he⟩ | ⟨l, hl, he⟩)
      · exact ⟨l, Or.inl hl, he⟩
      · exact ⟨l, Or.inr hl, he⟩
    · rintro ⟨l, hl | hl, he⟩
      · exact Or.inl ⟨l, hl, he⟩
      · exact Or.inr ⟨l, hl, he⟩

theorem all_valid {G : Hex.SparseGraph n} {B : Key n} {check : α → Option Bool}
    {leaves : α → List (SpecLeaf n)} {xs : List α} {a : Bool}
    (hcheck : ∀ x ∈ xs, ∀ b, check x = some b → Valid G B (leaves x) b)
    (h : all check xs = some a) : Valid G B (xs.flatMap leaves) a := by
  induction xs generalizing a with
  | nil =>
    have ha : a = false := by simpa [all] using h.symm
    subst a
    exact valid_nil G B
  | cons x xs ih =>
    obtain ⟨b, c, hb, hc, rfl⟩ := all_cons.mp h
    exact (hcheck x List.mem_cons_self b hb).append
      (ih (fun y hy => hcheck y (List.mem_cons_of_mem _ hy)) hc)

theorem all_exists {check : α → Option Bool} {xs : List α}
    (h : ∀ x ∈ xs, ∃ a, check x = some a) : ∃ a, all check xs = some a := by
  induction xs with
  | nil => exact ⟨false, rfl⟩
  | cons x xs ih =>
    obtain ⟨a, ha⟩ := h x List.mem_cons_self
    obtain ⟨b, hb⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    exact ⟨a || b, all_cons.mpr ⟨a, b, ha, hb, rfl⟩⟩

/-- Check one actual leaf against a claimed upper bound. -/
@[expose] def leaf (G : Hex.SparseGraph n) (B : Key n) (l : SpecLeaf n) : Option Bool :=
  match Key.cmp (l.key G) B with
  | .gt => none
  | .eq => some true
  | .lt => some false

theorem leaf_valid {G : Hex.SparseGraph n} {B : Key n} {l : SpecLeaf n} {a : Bool}
    (h : leaf G B l = some a) : Valid G B [l] a := by
  cases hc : Key.cmp (l.key G) B with
  | gt => simp [leaf, hc] at h
  | eq =>
    have ha : a = true := by simpa [leaf, hc] using h.symm
    subst a
    have he := Key.cmp_eq.mp hc
    constructor
    · intro q hq
      rw [List.mem_singleton.mp hq, he]
      exact Key.le_refl B
    · simp [he]
  | lt =>
    have ha : a = false := by simpa [leaf, hc] using h.symm
    subst a
    constructor
    · intro q hq
      rw [List.mem_singleton.mp hq]
      exact Ordering.isLE_of_eq_lt hc
    · have hn : l.key G ≠ B := by
        intro he
        have := Key.cmp_eq.mpr he
        rw [hc] at this
        contradiction
      simp [hn]

theorem leaf_exists {G : Hex.SparseGraph n} {B : Key n} {l : SpecLeaf n}
    (h : Key.Le (l.key G) B) : ∃ a, leaf G B l = some a := by
  cases hc : Key.cmp (l.key G) B with
  | gt => simp [Key.Le, hc] at h
  | eq => exact ⟨true, by simp [leaf, hc]⟩
  | lt => exact ⟨false, by simp [leaf, hc]⟩

theorem Valid.prepend {G : Hex.SparseGraph n} {B : Key n}
    {xs : List (SpecLeaf n)} {a : Bool} (h : Valid G B xs a) (c : Nat) :
    Valid G (prefixKey [c] B) (xs.map (SpecLeaf.prepend c)) a := by
  constructor
  · intro l hl
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
    rw [SpecLeaf.prepend_key]
    exact prefixKey_le [c] (h.bound q hq)
  · rw [h.attains]
    constructor
    · rintro ⟨l, hl, he⟩
      exact ⟨l.prepend c, List.mem_map.mpr ⟨l, hl, rfl⟩, by rw [SpecLeaf.prepend_key, he]⟩
    · rintro ⟨l, hl, he⟩
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
      refine ⟨q, hq, Key.cmp_eq.mp ?_⟩
      rw [SpecLeaf.prepend_key] at he
      simpa only [prefixKey_cmp] using Key.cmp_eq.mpr he

end Replay
end Hex.GraphIso.Nauty.Sparse
