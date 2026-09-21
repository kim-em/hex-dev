/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.Kernel

public section

/-! Coefficient embeddings and predicates for list arithmetic. No ring laws
on the encoding type are required: operations must agree on the image, and
coefficient predicates must be closed under the relevant operations. -/

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
  | cons u us ih => simp [map_insert f hz ha, hm, ih]

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

namespace Hex.MvPoly.Kernel

universe u
variable {κ : Type u} [Zero κ] [DecidableEq κ]

/-- Mapping coefficients preserves any predicate satisfied by the map's image. -/
theorem coeffs_mapCoeffs (P : κ → Prop) (f : κ → κ)
    (hf : ∀ c, P (f c)) (a : PolyList κ) :
    ∀ t ∈ mapCoeffs f a, P t.2 := by
  induction a with
  | nil => simp [mapCoeffs]
  | cons t ts ih =>
    simp only [mapCoeffs]
    split
    · exact ih
    · exact List.forall_mem_cons.mpr ⟨hf _, ih⟩

variable [Add κ] (P : κ → Prop)
variable (hadd : ∀ a b, P a → P b → P (a + b))
include hadd

/-- Insertion preserves a coefficient predicate closed under addition. -/
theorem coeffs_insert (t : Term κ) (a : PolyList κ)
    (ht : P t.2) (ha : ∀ u ∈ a, P u.2) : ∀ u ∈ insert t a, P u.2 := by
  induction a with
  | nil => simp only [insert]; split <;> simp_all
  | cons u us ih =>
    have hu := ha u (by simp)
    have hus : ∀ v ∈ us, P v.2 := fun v hv => ha v (by simp [hv])
    have hi := ih hus
    simp only [insert]
    split
    · split
      · exact ha
      · exact List.forall_mem_cons.mpr ⟨ht, ha⟩
    · split
      · exact hus
      · exact List.forall_mem_cons.mpr ⟨hadd _ _ ht hu, hus⟩
    · exact List.forall_mem_cons.mpr ⟨hu, hi⟩

/-- Insertion summation preserves a coefficient predicate. -/
theorem coeffs_insertSum (a b : PolyList κ)
    (ha : ∀ t ∈ a, P t.2) (hb : ∀ t ∈ b, P t.2) :
    ∀ t ∈ insertSum a b, P t.2 := by
  induction a with
  | nil => exact hb
  | cons t ts ih =>
    exact coeffs_insert P hadd t _ (ha t (by simp)) (ih (fun u hu => ha u (by simp [hu])))

/-- Every budgeted merge preserves a coefficient predicate. -/
theorem coeffs_merge (fuel : Nat) (a b : PolyList κ)
    (ha : ∀ t ∈ a, P t.2) (hb : ∀ t ∈ b, P t.2) :
    ∀ t ∈ merge fuel a b, P t.2 := by
  induction fuel generalizing a b with
  | zero =>
    cases a with
    | nil => exact hb
    | cons t ts =>
      cases b with
      | nil => exact ha
      | cons u us => exact coeffs_insertSum P hadd _ _ ha hb
  | succ fuel ih =>
    cases a with
    | nil => exact hb
    | cons t ts =>
      cases b with
      | nil => exact ha
      | cons u us =>
        have hts : ∀ v ∈ ts, P v.2 := fun v hv => ha v (by simp [hv])
        have hus : ∀ v ∈ us, P v.2 := fun v hv => hb v (by simp [hv])
        simp only [merge]
        split
        · exact List.forall_mem_cons.mpr ⟨ha t (by simp), ih _ _ hts hb⟩
        · exact List.forall_mem_cons.mpr ⟨hb u (by simp), ih _ _ ha hus⟩
        · split
          · exact ih _ _ hts hus
          · exact List.forall_mem_cons.mpr
              ⟨hadd _ _ (ha t (by simp)) (hb u (by simp)), ih _ _ hts hus⟩

/-- Polynomial addition preserves a coefficient predicate. -/
theorem coeffs_add (a b : PolyList κ)
    (ha : ∀ t ∈ a, P t.2) (hb : ∀ t ∈ b, P t.2) :
    ∀ t ∈ add a b, P t.2 := coeffs_merge P hadd _ a b ha hb

/-- Summing rows preserves a coefficient predicate. -/
theorem coeffs_sumRows (as : List (PolyList κ))
    (ha : ∀ a ∈ as, ∀ t ∈ a, P t.2) : ∀ t ∈ sumRows as, P t.2 := by
  induction as with
  | nil => simp [sumRows]
  | cons a as ih =>
    exact coeffs_add P hadd a _ (ha a (by simp)) (ih (fun b hb => ha b (by simp [hb])))

/-- One round of pairwise row merging preserves a coefficient predicate. -/
theorem coeffs_mergeRound (as : List (PolyList κ))
    (ha : ∀ a ∈ as, ∀ t ∈ a, P t.2) :
    ∀ a ∈ mergeRound as, ∀ t ∈ a, P t.2 := by
  induction as using mergeRound.induct with
  | case1 => simp [mergeRound]
  | case2 a => simpa [mergeRound] using ha
  | case3 a b as ih =>
    simp only [mergeRound, List.forall_mem_cons]
    exact ⟨coeffs_add P hadd a b (ha a (by simp)) (ha b (by simp)),
      ih (fun c hc => ha c (by simp [hc]))⟩

/-- Balanced row merging preserves a coefficient predicate. -/
theorem coeffs_mergeRows (fuel : Nat) (as : List (PolyList κ))
    (ha : ∀ a ∈ as, ∀ t ∈ a, P t.2) : ∀ t ∈ mergeRows fuel as, P t.2 := by
  induction fuel generalizing as with
  | zero =>
    cases as with
    | nil => simp [mergeRows]
    | cons a as =>
      cases as with
      | nil => simpa [mergeRows] using ha
      | cons b bs => exact coeffs_sumRows P hadd _ ha
  | succ fuel ih =>
    cases as with
    | nil => simp [mergeRows]
    | cons a as =>
      cases as with
      | nil => simpa [mergeRows] using ha
      | cons b bs => exact ih _ (coeffs_mergeRound P hadd _ ha)

variable [Mul κ] (hmul : ∀ a b, P (a * b))
include hmul

/-- Translating a multiplication row preserves a predicate on products and sums. -/
theorem coeffs_mulTerm (t : Term κ) (a : PolyList κ) :
    ∀ u ∈ mulTerm t a, P u.2 := by
  induction a with
  | nil => simp [mulTerm]
  | cons u us ih => exact coeffs_insert P hadd _ _ (hmul _ _) ih

/-- Multiplication preserves a predicate on products and sums. -/
theorem coeffs_mul (a b : PolyList κ) : ∀ t ∈ mul a b, P t.2 := by
  apply coeffs_mergeRows P hadd
  simp only [List.forall_mem_map]
  exact fun t _ => coeffs_mulTerm P hadd hmul t b

end Hex.MvPoly.Kernel
