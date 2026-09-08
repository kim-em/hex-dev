/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Product.WreathFactors
public import HexPermGroup.Build

public section

namespace Hex.PermGroup.Group

open Perm.Wreath

/-- One copy of every original generator in every block, followed by the
original top generators. All blocks are included even for intransitive `H`. -/
@[expose] def wreathProduct (G : Group n) (H : Group m) (hn : 0 < n) : Group (n * m) :=
  ofGenerators (((List.finRange m).flatMap fun i => G.generators.toList.map (copy hn i)).toArray ++
    H.generators.map (lift hn))

theorem wreath_generators_size (G : Group n) (H : Group m) (hn : 0 < n) :
    (G.wreathProduct H hn).generators.size = m * G.generators.size + H.generators.size := by
  simp [wreathProduct, List.length_flatMap, List.map_const', List.sum_replicate_nat]

theorem wreath_copy_mem (G : Group n) (H : Group m) (hn : 0 < n) (i : Fin m)
    (p : Perm n) (hp : Generated G.generators p) : Generated (G.wreathProduct H hn).generators (copy hn i p) := by
  apply hp.lift
  · simpa only [copy_id] using (Generated.id (S := (G.wreathProduct H hn).generators))
  · intro p hp
    apply Generated.generator
    apply Array.mem_append.mpr
    apply Or.inl
    apply List.mem_toArray.mpr
    exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨p, by simpa using hp, rfl⟩⟩
  · intro p q hp hq
    simpa only [copy_comp] using hp.comp hq
  · intro p hp
    simpa only [copy_inv] using hp.inv

theorem wreath_lift_mem (G : Group n) (H : Group m) (hn : 0 < n)
    (h : Perm m) (hh : Generated H.generators h) : Generated (G.wreathProduct H hn).generators (lift hn h) := by
  apply hh.lift
  · simpa only [lift_id] using (Generated.id (S := (G.wreathProduct H hn).generators))
  · intro h hh
    exact .generator (Array.mem_append.mpr (Or.inr (Array.mem_map.mpr ⟨h, hh, rfl⟩)))
  · intro h k hh hk
    simpa only [lift_comp] using hh.comp hk
  · intro h hh
    simpa only [lift_inv] using hh.inv

theorem wreath_base_mem (G : Group n) (H : Group m) (hn : 0 < n)
    (f : Fin m → Perm n) (hf : ∀ j, Generated G.generators (f j)) :
    Generated (G.wreathProduct H hn).generators (perm hn f (Perm.id m)) := by
  have hi (k : Nat) (hk : k ≤ m) :
      Generated (G.wreathProduct H hn).generators (perm hn (initial f k) (Perm.id m)) := by
    induction k with
    | zero => simpa only [initial_zero, perm_id] using (Generated.id (S := (G.wreathProduct H hn).generators))
    | succ k ih =>
      have hl : k < m := by omega
      rw [initial_succ hn f k hl]
      exact (ih (by omega)).comp (G.wreath_copy_mem H hn ⟨k, hl⟩ _ (hf _))
  simpa only [initial_full] using hi m (Nat.le_refl _)

theorem wreath_perm_mem (G : Group n) (H : Group m) (hn : 0 < n)
    (f : Fin m → Perm n) (h : Perm m) (hf : ∀ j, Generated G.generators (f j)) (hh : Generated H.generators h) :
    Generated (G.wreathProduct H hn).generators (perm hn f h) := by
  rw [factor]
  exact (G.wreath_base_mem H hn f hf).comp (G.wreath_lift_mem H hn h hh)

/-- Generated elements are exactly the base functions together with a top
element. This also proves that the listed copies and lifts generate the result. -/
theorem mem_wreathProduct (G : Group n) (H : Group m) (hn : 0 < n) (r : Perm (n * m)) :
    Generated (G.wreathProduct H hn).generators r ↔
      ∃ (f : Fin m → Perm n) (h : Perm m),
        (∀ j, Generated G.generators (f j)) ∧ Generated H.generators h ∧ r = perm hn f h := by
  constructor
  · intro hr
    apply hr.lift
    · exact ⟨fun _ => Perm.id n, Perm.id m, fun _ => .id, .id, (perm_id hn).symm⟩
    · intro r hr
      simp only [wreathProduct, generators_ofGenerators, Array.mem_append] at hr
      rcases hr with hr | hr
      · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp (List.mem_toArray.mp hr)
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
        refine ⟨single i p, Perm.id m, ?_, .id, rfl⟩
        intro j
        by_cases hj : j = i
        · simpa [single, hj] using (Generated.generator (by simpa using hp) : Generated G.generators p)
        · simpa [single, hj] using (Generated.id (S := G.generators))
      · obtain ⟨h, hh, rfl⟩ := Array.mem_map.mp hr
        exact ⟨fun _ => Perm.id n, h, fun _ => .id, .generator hh, rfl⟩
    · rintro r s ⟨f, h, hf, hh, rfl⟩ ⟨g, k, hg, hk, rfl⟩
      exact ⟨fun j => (f j).comp (g (h.inv.get j)), h.comp k,
        fun j => (hf j).comp (hg _), hh.comp hk, perm_comp hn f g h k⟩
    · rintro r ⟨f, h, hf, hh, rfl⟩
      exact ⟨inverse f h, h.inv, fun j => (hf (h.get j)).inv, hh.inv, perm_inv hn f h⟩
  · rintro ⟨f, h, hf, hh, rfl⟩
    exact G.wreath_perm_mem H hn f h hf hh

end Hex.PermGroup.Group

namespace Hex.PermGroup.WreathProduct

inductive Error where
  | emptyBlocks
  deriving DecidableEq, Repr

end Hex.PermGroup.WreathProduct

namespace Hex.PermGroup.Group

/-- Raw requests with empty blocks are rejected: their point action would
lose the top group. Zero blocks with a positive block size are permitted. -/
@[expose] def wreathProduct? (G : Group n) (H : Group m) : Except WreathProduct.Error (Group (n * m)) :=
  if hn : 0 < n then .ok (G.wreathProduct H hn) else .error .emptyBlocks

theorem wreathProduct_error (G : Group n) (H : Group m) : G.wreathProduct? H = .error .emptyBlocks ↔ n = 0 := by
  unfold wreathProduct?
  split <;> simp_all <;> omega

end Hex.PermGroup.Group
