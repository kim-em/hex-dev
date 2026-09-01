/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraph.Basic

public section

/-!
Executable permutations of `Fin n` for graph canonical labelling.

The executable permutation data is an array of all vertices: a vector of
`Fin n` values carrying a no-duplicates proof and an every-vertex-occurs
proof. Carrying both decidable facts makes the two-sided inverse
constructible without a pigeonhole argument, and checked construction
(`ofVector?`) decides both.

Two wrappers make the direction visible at use sites:

- `Perm n` maps an old vertex to its image. An isomorphism from `G` to `H`
  uses this direction.
- `Label n` stores the old vertex at each new position (nauty's `canonlab`
  convention).

Equality of either wrapper is extensional: it compares only the underlying
vertex array (`Perm.ext`), with proof irrelevance handling the two proof
fields, so `DecidableEq` is kernel-reducible.
-/

namespace Hex.GraphIso

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

/-- The vertex mapping to `i`: the executable preimage search. -/
@[expose] def preimage (p : Perm n) (i : Fin n) : Fin n :=
  (((List.finRange n).find? fun j => p.get j == i).getD i)

@[simp] theorem get_preimage (p : Perm n) (i : Fin n) :
    p.get (p.preimage i) = i := by
  rw [preimage]
  rcases hfind : (List.finRange n).find? (fun j => p.get j == i) with _ | j
  · rcases p.get_surj i with ⟨j, hj⟩
    have := List.find?_eq_none.mp hfind j (List.mem_finRange j)
    simp [hj] at this
  · have := List.find?_some hfind
    simpa using this

@[simp] theorem preimage_get (p : Perm n) (i : Fin n) :
    p.preimage (p.get i) = i :=
  p.get_inj (p.get_preimage (p.get i))

/-- The inverse permutation. -/
@[expose] def inv (p : Perm n) : Perm n :=
  ofFn p.preimage
    (fun i j h => by
      have : p.get (p.preimage i) = p.get (p.preimage j) := congrArg p.get h
      rwa [get_preimage, get_preimage] at this)
    (fun i => ⟨p.get i, p.preimage_get i⟩)

theorem get_inv (p : Perm n) (i : Fin n) : p.inv.get i = p.preimage i :=
  get_ofFn ..

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
@[expose] def permOfNatArray? (n : Nat) (a : Array Nat) : Option (Perm n) :=
  if h : a.size = n ∧ ∀ i, (hi : i < a.size) → a[i] < n then
    Perm.ofVector? (Hex.Vector.ofFn' fun i : Fin n =>
      ⟨a[i.val]'(h.1.symm ▸ i.isLt), h.2 i.val (h.1.symm ▸ i.isLt)⟩)
  else
    none

/-- A canonical-labelling result array in nauty's `canonlab` convention:
`l[i]` is the old vertex placed at new position `i`. The underlying data is
the same duplicate-free complete vertex array as `Perm`; the wrapper marks
the direction. -/
structure Label (n : Nat) where
  /-- The underlying bijection sending each new position to the old vertex
  placed there. -/
  perm : Perm n

namespace Label

variable {n : Nat}

instance : DecidableEq (Label n) := fun l m =>
  if h : l.perm = m.perm then
    .isTrue (by cases l; cases m; cases h; rfl)
  else
    .isFalse fun e => h (congrArg Label.perm e)

/-- The old vertex at new position `i`. -/
@[inline, expose] def get (l : Label n) (i : Fin n) : Fin n :=
  l.perm.get i

instance : GetElem (Label n) (Fin n) (Fin n) (fun _ _ => True) where
  getElem l i _ := l.get i

@[simp] theorem getElem_eq_get (l : Label n) (i : Fin n) : l[i] = l.get i := rfl

@[ext] theorem ext {l m : Label n} (h : ∀ i, l.get i = m.get i) : l = m := by
  cases l; cases m
  exact congrArg Label.mk (Perm.ext h)

/-- Checked construction from a vertex array. -/
@[expose] def ofVector? (v : Vector (Fin n) n) : Option (Label n) :=
  (Perm.ofVector? v).map Label.mk

/-- The identity labelling. -/
@[expose] protected def id (n : Nat) : Label n :=
  ⟨Perm.id n⟩

@[simp] theorem get_id (i : Fin n) : (Label.id n).get i = i :=
  Perm.get_id i

/-- Sequential composition: relabelling by `l` and then by `m` is
relabelling by `l.comp m`, with `(l.comp m).get i = l.get (m.get i)`. -/
@[expose] def comp (l m : Label n) : Label n :=
  ⟨l.perm.comp m.perm⟩

@[simp] theorem get_comp (l m : Label n) (i : Fin n) :
    (l.comp m).get i = l.get (m.get i) :=
  Perm.get_comp ..

/-- The forward permutation of a labelling: old vertex `v` moves to the new
position where `l` placed it. -/
@[expose] def toPerm (l : Label n) : Perm n :=
  l.perm.inv

@[simp] theorem get_toPerm_get (l : Label n) (i : Fin n) :
    l.get (l.toPerm.get i) = i :=
  Perm.get_inv_get ..

@[simp] theorem toPerm_get_get (l : Label n) (i : Fin n) :
    l.toPerm.get (l.get i) = i :=
  Perm.inv_get_get ..

end Label

namespace Perm

/-- The labelling of a forward permutation: new position `i` holds the old
vertex mapped to `i`. -/
@[expose] def toLabel (p : Perm n) : Label n :=
  ⟨p.inv⟩

@[simp] theorem get_toLabel (p : Perm n) (i : Fin n) :
    p.toLabel.get i = p.inv.get i := rfl

@[simp] theorem toLabel_toPerm (p : Perm n) : p.toLabel.toPerm = p := by
  rw [toLabel, Label.toPerm, inv_inv]

@[simp] theorem toPerm_toLabel (l : Label n) : l.toPerm.toLabel = l := by
  cases l
  rw [Label.toPerm, toLabel, inv_inv]

end Perm

end Hex.GraphIso
