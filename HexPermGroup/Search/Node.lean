/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Membership

public section

namespace Hex.PermGroup.Search

/-- A search node describes the coset `prefix * <suffix.generators>`. The
checked suffix fixes every point preceding the current base position. -/
structure Node (G : Group n) where
  base : Nat
  suffix : Chain n
  checked : suffix.checkFrom base = true
  inside : ∀ p : Perm n, Generated suffix.generators p → Generated G.generators p
  rep : Element G

namespace Node

variable {G : Group n}

@[expose] def root (G : Group n) : Node G where
  base := 0
  suffix := G.chain
  checked := G.checked
  inside := fun _ hp => checkWords_sound (of_decide_eq_true G.valid).2.1 hp
  rep := Element.id G

/-- Membership in the node's entire remaining search region. -/
@[expose] def Contains (t : Node G) (p : Perm n) : Prop :=
  Generated t.suffix.generators (t.rep.val.inv.comp p)

@[expose] def contains (t : Node G) (p : Perm n) : Bool :=
  t.suffix.accepts t.base (t.rep.val.inv.comp p)

theorem contains_iff (t : Node G) (p : Perm n) : t.contains p = true ↔ t.Contains p :=
  Chain.checkFrom_sound t.checked _

theorem root_contains (G : Group n) (p : Perm n) : (root G).Contains p ↔ Generated G.generators p := by
  rw [← contains_iff]
  simpa [contains, root, Group.contains] using G.contains_iff p

theorem contains_rep (t : Node G) : t.Contains t.rep.val := by
  simp only [Contains, Perm.inv_comp_self]
  exact .id

theorem generated (t : Node G) {p : Perm n} (hp : t.Contains p) : Generated G.generators p := by
  have h := t.rep.property.comp (t.inside _ hp)
  simpa [← Perm.comp_assoc] using h

/-- Every completion agrees with the stored prefix on assigned source points. -/
theorem agrees (t : Node G) {p : Perm n} (hp : t.Contains p) (x : Fin n) (hx : x.val < t.base) :
    p.get x = t.rep.val.get x := by
  have he := Chain.fixed_generated (Chain.checkFrom_fixed t.checked) hp x hx
  have hh := congrArg t.rep.val.get he
  simpa using hh

theorem level_checked (t : Node G) {level : Level n} {tail : Chain n}
    (hs : t.suffix = .cons level tail) : (Chain.cons level tail).checkFrom t.base = true :=
  hs ▸ t.checked

theorem tail_inside (t : Node G) {level : Level n} {tail : Chain n}
    (hs : t.suffix = .cons level tail) {p : Perm n} (hp : Generated tail.generators p) :
    Generated G.generators p := by
  apply t.inside
  rw [hs]
  exact checkWords_sound (Chain.suffix_words (t.level_checked hs)) hp

theorem rep_inside (t : Node G) {level : Level n} {tail : Chain n}
    (hs : t.suffix = .cons level tail) (i : Fin level.orbit.points.size) :
    Generated G.generators level.orbit.reps[i.val] := by
  apply t.inside
  rw [hs]
  exact Orbit.rep_generated (Chain.orbit_valid (t.level_checked hs)) i

/-- Extend by one stored orbit representative in its discovery order. -/
@[expose] def child (t : Node G) {level : Level n} {tail : Chain n}
    (hs : t.suffix = .cons level tail) (i : Fin level.orbit.points.size) : Node G where
  base := t.base + 1
  suffix := tail
  checked := Chain.suffix_checked (t.level_checked hs)
  inside := fun _ hp => t.tail_inside hs hp
  rep := t.rep.comp ⟨level.orbit.reps[i.val], t.rep_inside hs i⟩

theorem child_contains (t : Node G) {level : Level n} {tail : Chain n}
    (hs : t.suffix = .cons level tail) (i : Fin level.orbit.points.size) (p : Perm n) :
    (t.child hs i).Contains p ↔
      Generated tail.generators (level.orbit.reps[i.val].inv.comp (t.rep.val.inv.comp p)) := by
  simp [Contains, child, Perm.inv_comp, Perm.comp_assoc]

/-- Every parent completion belongs to a child, and every child stays in its
parent. The children are reconstructed from the checked chain. -/
theorem contains_children (t : Node G) {level : Level n} {tail : Chain n}
    (hs : t.suffix = .cons level tail) (p : Perm n) :
    t.Contains p ↔ ∃ i : Fin level.orbit.points.size, (t.child hs i).Contains p := by
  constructor
  · intro hp
    have hr : Generated (Chain.cons level tail).generators (t.rep.val.inv.comp p) := by
      simpa only [Contains, hs] using hp
    obtain ⟨digits, hd⟩ := Chain.value_surjective (t.level_checked hs) hr
    refine ⟨digits.1, ?_⟩
    rw [child_contains, ← hd]
    simpa [Chain.value, ← Perm.comp_assoc] using
      Chain.value_generated (Chain.suffix_checked (t.level_checked hs)) digits.2
  · rintro ⟨i, hi⟩
    rw [child_contains] at hi
    have hr := (Orbit.rep_generated (Chain.orbit_valid (t.level_checked hs)) i).comp
      (checkWords_sound (Chain.suffix_words (t.level_checked hs)) hi)
    simpa only [Contains, hs, Chain.generators, ← Perm.comp_assoc, Perm.comp_inv_self, Perm.id_comp] using hr

/-- Distinct children are disjoint, detected at the next assigned base point. -/
theorem child_disjoint (t : Node G) {level : Level n} {tail : Chain n}
    (hs : t.suffix = .cons level tail) {i j : Fin level.orbit.points.size} {p : Perm n}
    (hi : (t.child hs i).Contains p) (hj : (t.child hs j).Contains p) : i = j := by
  let x : Fin n := ⟨t.base, Chain.base_lt (t.level_checked hs)⟩
  have hpi := (t.child hs i).agrees hi x (Nat.lt_succ_self _)
  have hpj := (t.child hs j).agrees hj x (Nat.lt_succ_self _)
  have he : level.orbit.reps[i.val].get x = level.orbit.reps[j.val].get x :=
    t.rep.val.get_inj (by simpa [child] using hpi.symm.trans hpj)
  apply Orbit.point_injective (Chain.orbit_valid (t.level_checked hs))
  simpa [x, Orbit.rep_apply (Chain.orbit_valid (t.level_checked hs))] using he

/-- At a checked terminal suffix the only completion is the prefix itself. -/
theorem leaf_contains (t : Node G) {S : Array (Perm n)} {words : Vector Program S.size}
    (hs : t.suffix = .leaf S words) (p : Perm n) : t.Contains p ↔ p = t.rep.val := by
  rw [← contains_iff]
  simp only [contains, hs, Chain.accepts_leaf, decide_eq_true_eq]
  constructor
  · intro he
    have hh := congrArg (fun q => t.rep.val.comp q) he
    simpa [← Perm.comp_assoc] using hh
  · rintro rfl
    simp

end Node

end Hex.PermGroup.Search
