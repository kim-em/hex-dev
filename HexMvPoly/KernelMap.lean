/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.Kernel

public section

/-! Coefficient embeddings commute with list arithmetic. No ring laws on the
encoding type are required: only the operations on the image must agree. -/

namespace Hex.MvPoly.Kernel.CoeffMap

universe u v w
variable {α : Type u} {β : Type v}

/-- Change the coefficient representation without changing support. -/
@[expose] def map (f : α → β) (p : PolyList α) : PolyList β :=
  p.map fun t => (t.1, f t.2)

@[simp] theorem map_nil (f : α → β) : map f [] = [] := rfl
@[simp] theorem map_cons (f : α → β) (t : Term α) (ts : PolyList α) :
    map f (t :: ts) = (t.1, f t.2) :: map f ts := rfl

@[simp] theorem map_map {γ : Type w} (g : β → γ) (f : α → β) (p : PolyList α) :
    map g (map f p) = map (fun a => g (f a)) p := by
  simp [map, List.map_map]

theorem map_injective (f : α → β) (hf : Function.Injective f) :
    Function.Injective (map f) := by
  intro p q h
  apply (List.map_inj_right (f := fun t : Term α => (t.1, f t.2)) (fun a b hab =>
    Prod.ext (Prod.mk.inj hab).1 (hf (Prod.mk.inj hab).2))).mp
  exact h

section Zero
variable [Zero α] [Zero β] (f : α → β)
variable (hz : ∀ a, f a = 0 ↔ a = 0)
include hz

theorem canonical_map {n : Nat} {p : PolyList α} :
    Canonical n (map f p) ↔ Canonical n p := by
  simp only [Canonical, map, List.forall_mem_map, List.pairwise_map, ne_eq, hz]

variable [DecidableEq α] [DecidableEq β]
variable [Add α] [Add β] (ha : ∀ a b, f (a + b) = f a + f b)
include ha

theorem map_insert (t : Term α) (p : PolyList α) :
    map f (insert t p) = insert (t.1, f t.2) (map f p) := by
  induction p with
  | nil => simp [insert, hz]; split <;> rfl
  | cons u us ih =>
    simp only [insert, map_cons]
    split <;> simp_all [← ha, apply_ite]

theorem map_insertSum (p q : PolyList α) :
    map f (insertSum p q) = insertSum (map f p) (map f q) := by
  induction p with
  | nil => rfl
  | cons t ts ih => simp [insertSum, map_insert f hz ha, ih]

theorem map_merge (fuel : Nat) (p q : PolyList α) :
    map f (merge fuel p q) = merge fuel (map f p) (map f q) := by
  induction fuel generalizing p q with
  | zero => cases p <;> cases q <;> simp [merge, map_insertSum f hz ha]
  | succ fuel ih =>
    cases p with
    | nil => rfl
    | cons t ts =>
      cases q with
      | nil => rfl
      | cons u us =>
        simp only [merge, map_cons]
        split <;> simp_all [← ha, apply_ite]

theorem map_add (p q : PolyList α) :
    map f (add p q) = add (map f p) (map f q) := by
  simpa [add, map, List.length_map] using map_merge f hz ha (p.length + q.length) p q

omit ha [Add α] [Add β] in
theorem map_mapCoeffs (g : α → α) (h : β → β)
    (hg : ∀ a, f (g a) = h (f a)) (p : PolyList α) :
    map f (mapCoeffs g p) = mapCoeffs h (map f p) := by
  induction p with
  | nil => rfl
  | cons t ts ih => simp [mapCoeffs, ← hg, hz]; split <;> simp_all

variable [Mul α] [Mul β] (hm : ∀ a b, f (a * b) = f a * f b)
include hm

theorem map_mulTerm (t : Term α) (p : PolyList α) :
    map f (mulTerm t p) = mulTerm (t.1, f t.2) (map f p) := by
  induction p with
  | nil => rfl
  | cons u us ih => simp [mulTerm, map_insert f hz ha, hm, ih]

omit hm [Mul α] [Mul β] in
theorem map_sumRows (ps : List (PolyList α)) :
    map f (sumRows ps) = sumRows (ps.map (map f)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [sumRows, map_add f hz ha, ih]

omit hm [Mul α] [Mul β] in
theorem map_mergeRound (ps : List (PolyList α)) :
    (mergeRound ps).map (map f) = mergeRound (ps.map (map f)) := by
  induction ps using mergeRound.induct with
  | case1 => rfl
  | case2 p => rfl
  | case3 p q ps ih => simp [mergeRound, map_add f hz ha, ih]

omit hm [Mul α] [Mul β] in
theorem map_mergeRows (fuel : Nat) (ps : List (PolyList α)) :
    map f (mergeRows fuel ps) = mergeRows fuel (ps.map (map f)) := by
  induction fuel generalizing ps with
  | zero =>
    cases ps with
    | nil => rfl
    | cons p ps => cases ps <;> simp [mergeRows, map_sumRows f hz ha]
  | succ fuel ih =>
    cases ps with
    | nil => rfl
    | cons p ps =>
      cases ps <;> simp [mergeRows, ih, map_mergeRound f hz ha]

theorem map_mul (p q : PolyList α) :
    map f (mul p q) = mul (map f p) (map f q) := by
  unfold mul
  rw [map_mergeRows f hz ha]
  simp only [map, List.length_map, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro t ht
  exact map_mulTerm f hz ha hm t q

end Zero
end Hex.MvPoly.Kernel.CoeffMap
