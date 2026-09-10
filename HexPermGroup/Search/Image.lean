/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Node

public section

namespace Hex.PermGroup.Search.Node

variable {G : Group n}

theorem symmetric (t : Node G) (p : Perm n) (hp : p ∈ t.suffix.generators) :
    p.inv ∈ t.suffix.generators := by
  have h := t.checked
  cases hs : t.suffix with
  | leaf S words =>
    rw [hs] at h
    simp only [hs, Chain.generators] at hp ⊢
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hp
    have he := (of_decide_eq_true h).2.2 ⟨i, hi⟩
    simpa only [he, Perm.inv_id] using (Array.getElem_mem (xs := S) hi)
  | cons level tail =>
    rw [hs] at h
    simp only [hs, Chain.generators] at hp ⊢
    unfold Chain.checkFrom at h
    split at h
    · split at h
      · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hp
        exact ((of_decide_eq_true h).1.2.2 ⟨i, hi⟩).2
      · cases h
    · cases h

/-- A remaining point orbit is computed directly from the suffix generators;
there is no need to rebuild a group or enumerate its elements. -/
@[expose] def orbit (t : Node G) (x : Fin n) : Array (Fin n) :=
  (Orbit.ofSymmetric t.suffix.generators x t.symmetric).val.points

theorem mem_orbit (t : Node G) (x y : Fin n) :
    y ∈ t.orbit x ↔ ∃ p : Perm n, Generated t.suffix.generators p ∧ p.get x = y := by
  exact (Orbit.ofSymmetric _ x t.symmetric).property.mem_iff y

/-- A forced image is feasible exactly when it belongs to the prefix image of
the relevant suffix orbit. -/
@[expose] def imagePossible (t : Node G) (x y : Fin n) : Bool :=
  decide (t.rep.val.inv.get y ∈ t.orbit x)

theorem imagePossible_iff (t : Node G) (x y : Fin n) :
    t.imagePossible x y = true ↔ ∃ p : Perm n, t.Contains p ∧ p.get x = y := by
  rw [imagePossible, decide_eq_true_eq, mem_orbit]
  constructor
  · rintro ⟨q, hq, he⟩
    refine ⟨t.rep.val.comp q, ?_, ?_⟩
    · simpa only [Contains, ← Perm.comp_assoc, Perm.inv_comp_self, Perm.id_comp] using hq
    · simp [he]
  · rintro ⟨p, hp, he⟩
    exact ⟨t.rep.val.inv.comp p, hp, by simp [he]⟩

theorem imagePossible_of_contains (t : Node G) {p : Perm n} (hp : t.Contains p) (x : Fin n) :
    t.imagePossible x (p.get x) = true :=
  (t.imagePossible_iff x _).mpr ⟨p, hp, rfl⟩

theorem orbit_invariant (t : Node G) {q : Perm n} (hq : Generated t.suffix.generators q)
    (x y : Fin n) : y ∈ t.orbit x ↔ q.get y ∈ t.orbit x := by
  rw [t.mem_orbit, t.mem_orbit]
  constructor
  · rintro ⟨r, hr, he⟩
    exact ⟨q.comp r, hq.comp hr, by simp [he]⟩
  · rintro ⟨r, hr, he⟩
    exact ⟨q.inv.comp r, hq.inv.comp hr, by simp [he]⟩

/-- Suffix elements permute each remaining point orbit, so any membership
count on such an orbit is preserved by reindexing along a completion. -/
theorem orbit_perm (t : Node G) {q : Perm n} (hq : Generated t.suffix.generators q) (x : Fin n) :
    ((t.orbit x).toList.map q.get).Perm (t.orbit x).toList := by
  have hn : (t.orbit x).toList.Nodup :=
    (Orbit.ofSymmetric _ x t.symmetric).property.1
  have hm : ((t.orbit x).toList.map q.get).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    apply hn.imp
    intro a b hab he
    exact hab (q.get_inj he)
  apply (List.perm_ext_iff_of_nodup hm hn).mpr
  intro y
  simp only [List.mem_map, Array.mem_toList_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (t.orbit_invariant hq x z).mp hz
  · intro hy
    refine ⟨q.inv.get y, ?_, by simp⟩
    apply (t.orbit_invariant hq x _).mpr
    simpa only [Perm.get_inv_get] using hy

end Hex.PermGroup.Search.Node
