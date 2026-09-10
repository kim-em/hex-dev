/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic

public section

/-! Executable permutations of a fixed indexed set, with left-action composition. -/

namespace Hex

/-- A permutation of the vertex set `Fin n`, stored as the array of images:
vertex `i` maps to `vec[i]`. The two proof fields record that the array is
duplicate-free and contains every vertex; both are decidable, and carrying
both makes the inverse constructible directly. -/
structure Perm (n : Nat) where
  /-- The image array: vertex `i` maps to `vec[i]`. -/
  vec : Vector (Fin n) n
  /-- The image array has no duplicate entries. -/
  nodup : vec.toList.Nodup
  /-- Every vertex occurs in the image array. -/
  complete : ∀ i : Fin n, i ∈ vec.toList

namespace Perm

variable {n : Nat}

/-- Apply a permutation to a vertex. -/
@[inline, expose] def get (p : Perm n) (i : Fin n) : Fin n :=
  p.vec[i]

instance : CoeFun (Perm n) (fun _ => Fin n → Fin n) := ⟨get⟩

theorem get_toList (p : Perm n) (i : Fin n) : p.vec.toList[i.val] = p.get i := by
  simp [get]

/-- Distinct vertices have distinct images. -/
theorem get_ne (p : Perm n) {i j : Fin n} (h : i ≠ j) : p.get i ≠ p.get j := by
  have hp := List.pairwise_iff_getElem.mp p.nodup
  have hlen : p.vec.toList.length = n := by simp
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · have := hp i.val j.val (by omega) (by omega) hlt
    rwa [get_toList, get_toList] at this
  · exact absurd (Fin.ext heq) h
  · have := hp j.val i.val (by omega) (by omega) hgt
    rw [get_toList, get_toList] at this
    exact fun hne => this hne.symm

/-- A permutation is injective. -/
theorem get_inj (p : Perm n) {i j : Fin n} (h : p.get i = p.get j) : i = j := by
  rcases Decidable.em (i = j) with heq | hne
  · exact heq
  · exact absurd h (p.get_ne hne)

/-- A permutation is surjective. -/
theorem get_surj (p : Perm n) (i : Fin n) : ∃ j, p.get j = i := by
  rcases List.mem_iff_getElem.mp (p.complete i) with ⟨j, hj, hget⟩
  have hjn : j < n := by simpa using hj
  refine ⟨⟨j, hjn⟩, ?_⟩
  rw [← get_toList]
  exact hget

/-- Two permutations with the same image array are equal. -/
theorem ext_vec {p q : Perm n} (h : p.vec = q.vec) : p = q := by
  cases p; cases q; cases h; rfl

/-- Extensional equality of permutations. -/
@[ext] theorem ext {p q : Perm n} (h : ∀ i, p.get i = q.get i) : p = q := by
  refine ext_vec (Vector.ext fun i hi => ?_)
  exact h ⟨i, hi⟩

instance : DecidableEq (Perm n) := fun p q =>
  if h : p.vec = q.vec then
    .isTrue (ext_vec h)
  else
    .isFalse fun e => h (congrArg Perm.vec e)

/-! # Construction -/

/-- The image array of every vertex in order is duplicate-free and complete
whenever the entry function is injective and surjective. -/
theorem nodup_ofFn_toList {f : Fin n → Fin n}
    (hf : ∀ i j, f i = f j → i = j) : (Vector.ofFn f).toList.Nodup := by
  refine List.pairwise_iff_getElem.mpr fun i j hi hj hij => ?_
  have hi' : i < n := by simpa using hi
  have hj' : j < n := by simpa using hj
  simp only [Vector.getElem_toList, Vector.getElem_ofFn]
  intro he
  exact absurd (hf _ _ he) (by simp; omega)

theorem complete_ofFn_toList {f : Fin n → Fin n}
    (hf : ∀ i, ∃ j, f j = i) : ∀ i : Fin n, i ∈ (Vector.ofFn f).toList := by
  intro i
  rcases hf i with ⟨j, hj⟩
  refine List.mem_iff_getElem.mpr ⟨j.val, by simp, ?_⟩
  simpa using hj

/-- Build a permutation from an injective-and-surjective entry function. -/
@[expose] def ofFn (f : Fin n → Fin n) (hinj : ∀ i j, f i = f j → i = j)
    (hsurj : ∀ i, ∃ j, f j = i) : Perm n where
  vec := Hex.Vector.ofFn' f
  nodup := by rw [Hex.Vector.ofFn'_eq_ofFn]; exact nodup_ofFn_toList hinj
  complete := by rw [Hex.Vector.ofFn'_eq_ofFn]; exact complete_ofFn_toList hsurj

@[simp] theorem get_ofFn (f : Fin n → Fin n) (hinj) (hsurj) (i : Fin n) :
    (ofFn f hinj hsurj).get i = f i := by
  simp [ofFn, get]

/-- Checked construction: accepts exactly the duplicate-free complete vertex
arrays. -/
@[expose] def ofVector? (v : Vector (Fin n) n) : Option (Perm n) :=
  if h : v.toList.Nodup ∧ ∀ i : Fin n, i ∈ v.toList then
    some ⟨v, h.1, h.2⟩
  else
    none

theorem isSome_ofVector? (v : Vector (Fin n) n) :
    (ofVector? v).isSome = true ↔ v.toList.Nodup ∧ ∀ i : Fin n, i ∈ v.toList := by
  rw [ofVector?]
  split <;> simp_all

theorem vec_of_ofVector? {v : Vector (Fin n) n} {p : Perm n}
    (h : ofVector? v = some p) : p.vec = v := by
  rw [ofVector?] at h
  split at h
  · injection h with h
    exact congrArg Perm.vec h.symm
  · simp at h

/-- The identity permutation. -/
@[expose] protected def id (n : Nat) : Perm n :=
  ofFn (fun i => i) (fun _ _ h => h) (fun i => ⟨i, rfl⟩)

@[simp] theorem get_id (i : Fin n) : (Perm.id n).get i = i :=
  get_ofFn ..

/-- Composition: `(p.comp q).get i = p.get (q.get i)`. -/
@[expose] def comp (p q : Perm n) : Perm n :=
  ofFn (fun i => p.get (q.get i))
    (fun _ _ h => q.get_inj (p.get_inj h))
    (fun i => by
      rcases p.get_surj i with ⟨j, hj⟩
      rcases q.get_surj j with ⟨m, hm⟩
      exact ⟨m, by rw [hm, hj]⟩)

@[simp] theorem get_comp (p q : Perm n) (i : Fin n) :
    (p.comp q).get i = p.get (q.get i) :=
  get_ofFn ..

/-! # Inverse -/

/-- One scatter step: record `i` at position `p.get i`. -/
@[inline, expose] def scatterStep (p : Perm n) (v : Vector (Fin n) n)
    (i : Fin n) : Vector (Fin n) n :=
  v.set (p.get i).val i (p.get i).isLt

/-- The image array of the inverse, built by one scatter pass over the
vertices: each `i` is written at position `p.get i`. Every position is
written, because `p` is surjective. -/
@[expose] def invVec (p : Perm n) : Vector (Fin n) n :=
  (List.finRange n).foldl p.scatterStep (Hex.Vector.ofFn' fun i => i)

/-- A scatter pass leaves untouched every position that is not the image
of an element of the list. -/
theorem scatter_unchanged (p : Perm n) :
    ∀ (l : List (Fin n)) (v : Vector (Fin n) n) (q : Fin n),
      (∀ j ∈ l, p.get j ≠ q) →
        (l.foldl p.scatterStep v)[q.val] = v[q.val] := by
  intro l
  induction l with
  | nil => intro v q _; rfl
  | cons a l ih =>
    intro v q h
    rw [List.foldl_cons,
      ih (p.scatterStep v a) q (fun j hj => h j (List.mem_cons_of_mem a hj)),
      scatterStep,
      Vector.getElem_set_ne (p.get a).isLt q.isLt
        (fun he => h a List.mem_cons_self (Fin.eq_of_val_eq he))]

/-- A scatter pass writes `i` at position `p.get i` for every `i` in the
list. -/
theorem scatter_get (p : Perm n) :
    ∀ (l : List (Fin n)) (v : Vector (Fin n) n) {i : Fin n}, i ∈ l →
      (l.foldl p.scatterStep v)[(p.get i).val] = i := by
  intro l
  induction l with
  | nil => intro _ _ hi; cases hi
  | cons a l ih =>
    intro v i hi
    rcases Decidable.em (i ∈ l) with hin | hnin
    · rw [List.foldl_cons]
      exact ih _ hin
    · have hia : i = a := (List.mem_cons.mp hi).resolve_right hnin
      subst hia
      rw [List.foldl_cons,
        scatter_unchanged p l (p.scatterStep v i)
          (p.get i) (fun j hj => p.get_ne (fun hji => hnin (hji ▸ hj))),
        scatterStep, Vector.getElem_set_self (p.get i).isLt]

/-- The vertex mapping to `i`, read off the scattered inverse array. -/
@[expose] def preimage (p : Perm n) (i : Fin n) : Fin n :=
  p.invVec[i.val]

@[simp] theorem preimage_get (p : Perm n) (i : Fin n) :
    p.preimage (p.get i) = i :=
  scatter_get p (List.finRange n) _ (List.mem_finRange i)

@[simp] theorem get_preimage (p : Perm n) (i : Fin n) :
    p.get (p.preimage i) = i := by
  rcases p.get_surj i with ⟨j, hj⟩
  rw [← hj, preimage_get]

theorem preimage_inj (p : Perm n) {i j : Fin n}
    (h : p.preimage i = p.preimage j) : i = j := by
  have := congrArg p.get h
  rwa [get_preimage, get_preimage] at this

/-- The image array of a permutation is duplicate-free whenever its
entries are pairwise distinct. -/
theorem nodup_toList {v : Vector (Fin n) n}
    (hv : ∀ i j : Fin n, v[i.val] = v[j.val] → i = j) : v.toList.Nodup := by
  refine List.pairwise_iff_getElem.mpr fun i j hi hj hij => ?_
  have hi' : i < n := by simpa using hi
  have hj' : j < n := by simpa using hj
  simp only [Vector.getElem_toList]
  intro he
  exact absurd (hv ⟨i, hi'⟩ ⟨j, hj'⟩ he) (by simp; omega)

/-- The inverse permutation: the scattered inverse array. -/
@[expose] def inv (p : Perm n) : Perm n where
  vec := p.invVec
  nodup := nodup_toList fun _ _ h => p.preimage_inj h
  complete := fun i => List.mem_iff_getElem.mpr
    ⟨(p.get i).val, by simp, by
      rw [Vector.getElem_toList]
      exact p.preimage_get i⟩

theorem get_inv (p : Perm n) (i : Fin n) : p.inv.get i = p.preimage i :=
  rfl

@[simp] theorem get_inv_get (p : Perm n) (i : Fin n) : p.get (p.inv.get i) = i := by
  rw [get_inv, get_preimage]

@[simp] theorem inv_get_get (p : Perm n) (i : Fin n) : p.inv.get (p.get i) = i := by
  rw [get_inv, preimage_get]

/-! # Algebra -/

@[simp] theorem comp_id (p : Perm n) : p.comp (Perm.id n) = p := by
  ext i; simp

@[simp] theorem id_comp (p : Perm n) : (Perm.id n).comp p = p := by
  ext i; simp

theorem comp_assoc (p q r : Perm n) : (p.comp q).comp r = p.comp (q.comp r) := by
  ext i; simp

@[simp] theorem comp_inv_self (p : Perm n) : p.comp p.inv = Perm.id n := by
  ext i; simp

@[simp] theorem inv_comp_self (p : Perm n) : p.inv.comp p = Perm.id n := by
  ext i; simp

@[simp] theorem inv_inv (p : Perm n) : p.inv.inv = p := by
  refine Perm.ext fun i => p.inv.get_inj ?_
  simp

@[simp] theorem inv_id : (Perm.id n).inv = Perm.id n := by
  refine Perm.ext fun i => (Perm.id n).get_inj ?_
  simp

theorem inv_comp (p q : Perm n) : (p.comp q).inv = q.inv.comp p.inv := by
  refine Perm.ext fun i => (p.comp q).get_inj ?_
  simp

end Perm

/-- Checked permutation construction from raw entries, for literal data
emitted by tactics: entries must be in range, duplicate-free, and
complete. -/
@[expose] def Perm.ofNatArray? (n : Nat) (a : Array Nat) : Option (Perm n) :=
  if h : a.size = n ∧ ∀ i, (hi : i < a.size) → a[i] < n then
    Perm.ofVector? (Hex.Vector.ofFn' fun i : Fin n =>
      ⟨a[i.val]'(h.1.symm ▸ i.isLt), h.2 i.val (h.1.symm ▸ i.isLt)⟩)
  else
    none

end Hex
