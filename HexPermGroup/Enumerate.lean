/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Rank
public import HexPermGroup.Normalize

public section

namespace Hex.PermGroup

/-- A requested complete output exceeds the caller's allocation bound. -/
structure SizeLimit where
  required : Nat
  capacity : Nat
  deriving DecidableEq, Repr

namespace Element

/-- Image-array comparison for deterministic public enumeration. -/
@[expose] def le (G : Group n) (p q : Element G) : Bool :=
  (compare (Generator.images p.val) (Generator.images q.val)).isLE

theorem le_trans (G : Group n) (p q r : Element G) (hpq : le G p q) (hqr : le G q r) : le G p r :=
  Std.TransOrd.isLE_trans hpq hqr

theorem le_total (G : Group n) (p q : Element G) : le G p q || le G q p := by
  unfold le
  rw [Std.OrientedOrd.eq_swap (a := Generator.images q.val)]
  cases compare (Generator.images p.val) (Generator.images q.val) <;> rfl

theorem before_of_le (G : Group n) (p q : Element G) (hle : le G p q) (hne : p ≠ q) :
    Chain.before p.val q.val := by
  change compare (Generator.images p.val) (Generator.images q.val) = .lt
  cases h : compare (Generator.images p.val) (Generator.images q.val) with
  | lt => rfl
  | eq => exact False.elim (hne (Subtype.ext (Generator.images_injective (Std.LawfulEqOrd.eq_of_compare h))))
  | gt => simp [le, h] at hle

end Element

namespace Group

/-- Enumerate by the orbit-choice bijection, then sort by image arrays. This
uncapped helper is used only after the public allocation check. -/
@[expose] def enumerate (G : Group n) : Array (Element G) :=
  (((List.finRange G.order).map G.unrank).mergeSort (Element.le G)).toArray

theorem enumerate_size (G : Group n) : G.enumerate.size = G.order := by simp [enumerate]

theorem mem_enumerate (G : Group n) (p : Element G) : p ∈ G.enumerate := by
  simp only [enumerate, List.mem_toArray, List.mem_mergeSort, List.mem_map]
  exact ⟨G.rank p, List.mem_finRange _, G.unrank_rank p⟩

theorem enumerate_nodup (G : Group n) : G.enumerate.toList.Nodup := by
  simp only [enumerate, List.toList_toArray]
  apply (List.mergeSort_perm _ _).nodup_iff.mpr
  apply List.pairwise_map.mpr
  apply (List.nodup_finRange G.order).imp
  intro i j hne he
  apply hne
  have h := congrArg G.rank he
  simpa only [G.rank_unrank] using h

theorem enumerate_sorted (G : Group n) :
    G.enumerate.toList.Pairwise (fun p q => Chain.before p.val q.val) := by
  have hle : G.enumerate.toList.Pairwise (fun p q => Element.le G p q = true) := by
    simpa only [enumerate, List.toList_toArray] using
      List.pairwise_mergeSort (Element.le_trans G) (Element.le_total G) ((List.finRange G.order).map G.unrank)
  have hne := G.enumerate_nodup
  have hand := List.pairwise_and_iff.mpr ⟨hle, hne⟩
  exact hand.imp fun h => Element.before_of_le G _ _ h.1 h.2

/-- Test the exact group order before allocating any enumeration. A size-limit
result reports the required output size and is distinct from an empty result. -/
@[expose] def elementsWith (cap : Nat) (G : Group n) : Except SizeLimit (Array (Element G)) :=
  if G.order ≤ cap then .ok G.enumerate else .error ⟨G.order, cap⟩

theorem elementsWith_ok (cap : Nat) (G : Group n) :
    G.elementsWith cap = .ok G.enumerate ↔ G.order ≤ cap := by
  unfold elementsWith
  split <;> simp_all

theorem elementsWith_error (cap : Nat) (G : Group n) :
    G.elementsWith cap = .error ⟨G.order, cap⟩ ↔ cap < G.order := by
  unfold elementsWith
  split <;> simp_all

theorem elementsWith_spec (cap : Nat) (G : Group n) (values : Array (Element G))
    (h : G.elementsWith cap = .ok values) :
    values.size = G.order ∧ values.size ≤ cap ∧
      (∀ p : Element G, p ∈ values) ∧ values.toList.Nodup ∧
      values.toList.Pairwise (fun p q => Chain.before p.val q.val) := by
  unfold elementsWith at h
  split at h
  · rename_i hc
    have he := Except.ok.inj h
    subst values
    exact ⟨G.enumerate_size, by simpa [G.enumerate_size] using hc,
      G.mem_enumerate, G.enumerate_nodup, G.enumerate_sorted⟩
  · cases h

end Group

end Hex.PermGroup
