/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Primitivity
public import HexPermGroupMathlib.Blocks
public import HexPermGroupMathlib.Subgroup
public import Mathlib.GroupTheory.GroupAction.Primitive

public section

namespace Hex.PermGroup

namespace Partition

/-- Canonical representatives of an arbitrary mathematical equivalence relation.
This proof-side construction does not enter the executable block algorithm. -/
noncomputable def ofSetoid (r : Setoid (Fin n)) : Partition n := by
  classical
  exact ofValues (Hex.Vector.ofFn' fun x => Quotient.mk r x)

theorem ofSetoid_same (r : Setoid (Fin n)) (x y : Fin n) :
    (ofSetoid r).Same x y ↔ r x y := by
  classical
  simp [ofSetoid, ofValues_same, Quotient.eq]

end Partition

namespace Blocks

open scoped Pointwise

variable {M X : Type*} [_root_.Group M] [MulAction M X]

/-- An invariant equivalence class is a block in Mathlib's translate-or-disjoint
sense, without assuming that the action is transitive. -/
theorem class_isBlock (r : Setoid X)
    (hr : ∀ g : M, ∀ x y, r x y ↔ r (g • x) (g • y)) (a : X) :
    MulAction.IsBlock M {x | r a x} := by
  have image (g : M) : g • {x | r a x} = {x | r (g • a) x} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hr g a y).mp hy
    · intro hx
      refine ⟨g⁻¹ • x, ?_, by simp⟩
      simpa using (hr g⁻¹ (g • a) x).mp hx
  apply MulAction.isBlock_iff_smul_eq_or_disjoint.mpr
  intro g
  rw [image g]
  by_cases h : r (g • a) a
  · left
    ext x
    exact ⟨fun hx => r.trans (r.symm h) hx, fun hx => r.trans h hx⟩
  · right
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact h (r.trans hx (r.symm hy))

/-- Indistinguishability by all translates of a subset is an invariant
equivalence relation. For a block, all its points are indistinguishable. -/
def translateSetoid (B : Set X) : Setoid X where
  r x y := ∀ g : M, g • x ∈ B ↔ g • y ∈ B
  iseqv := ⟨fun _ _ => Iff.rfl, fun h g => (h g).symm,
    fun h k g => (h g).trans (k g)⟩

theorem translate_invariant (B : Set X) (g : M) (x y : X) :
    translateSetoid (M := M) B x y ↔ translateSetoid (M := M) B (g • x) (g • y) := by
  constructor
  · intro h k
    simpa only [mul_smul] using h (k * g)
  · intro h k
    simpa only [mul_smul, inv_smul_smul] using h (k * g⁻¹)

theorem related_of_mem {B : Set X} (hB : MulAction.IsBlock M B) {x y : X}
    (hx : x ∈ B) (hy : y ∈ B) : translateSetoid (M := M) B x y := by
  intro g
  have step {x y : X} (hx : x ∈ B) (hy : y ∈ B) (h : g • x ∈ B) : g • y ∈ B := by
    have he := hB.smul_eq_of_mem hx h
    rw [← he]
    exact Set.smul_mem_smul_set hy
  exact ⟨step hx hy, step hy hx⟩

end Blocks

/-- Classes of an invariant partition form a Mathlib block system, also for
intransitive actions and unequal class sizes. -/
theorem Partition.blockSystem (p : Partition n) {G : Group n} (hp : p.IsInvariant G) :
    MulAction.IsBlockSystem (closure G.generators) p.toSetoid.classes := by
  refine ⟨Setoid.isPartition_classes p.toSetoid, ?_⟩
  rintro B ⟨a, rfl⟩
  have he : ({x | p.toSetoid x a} : Set (Fin n)) = {x | p.toSetoid a x} := by
    ext x
    exact p.toSetoid.comm
  rw [he]
  apply Blocks.class_isBlock
  intro g x y
  exact (p.invariant_spec G).mp hp g.val g.property x y

namespace Group

/-- Mathlib's preprimitivity admits degenerate degrees; the executable
primitive convention retains the explicit degree-at-least-two condition. -/
theorem primitive_spec (G : Group n) : G.IsPrimitive ↔
    2 ≤ n ∧ MulAction.IsPreprimitive (closure G.generators) (Fin n) := by
  classical
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    refine { exists_smul_eq := ?_, isTrivialBlock_of_isBlock := ?_ }
    · intro x y
      exact (G.isTransitive_spec.mp h.2.1).2 x y
    · intro B hB
      let r := Blocks.translateSetoid (M := closure G.generators) B
      let p := Partition.ofSetoid r
      have hp : p.IsInvariant G := by
        intro g hg x y
        rw [Partition.ofSetoid_same, Partition.ofSetoid_same]
        exact Blocks.translate_invariant B
          (⟨g.toEquiv, generated_iff_mem.mp hg⟩ : closure G.generators) x y
      rcases h.2.2 p hp with hd | hi
      · left
        intro x hx y hy
        have hr := Blocks.related_of_mem hB hx hy
        have he : p.Same x y := (Partition.ofSetoid_same r x y).mpr hr
        rw [hd, Partition.discrete_same] at he
        exact he
      · rcases B.eq_empty_or_nonempty with he | ⟨x, hx⟩
        · left
          simp [he]
        · right
          apply Set.eq_univ_of_forall
          intro y
          have he : p.Same x y := by rw [hi]; exact Partition.indiscrete_same x y
          have hr := (Partition.ofSetoid_same r x y).mp he
          have hmem := (hr 1).mp (by simpa using hx)
          simpa using hmem
  · rintro ⟨hn, h⟩
    let _ := h
    have ht : G.isTransitive = true := by
      apply G.isTransitive_spec.mpr
      exact ⟨by omega, fun x y => MulAction.exists_smul_eq (closure G.generators) x y⟩
    refine ⟨hn, ht, ?_⟩
    intro p hp
    by_cases hd : p = Partition.discrete n
    · exact Or.inl hd
    · let a : Fin n := ⟨0, by omega⟩
      obtain ⟨b, hb, hab⟩ := hp.nonsingleton ht hd a
      have hr : ∀ g : closure G.generators, ∀ x y,
          p.toSetoid x y ↔ p.toSetoid (g • x) (g • y) := by
        intro g x y
        exact (p.invariant_spec G).mp hp g.val g.property x y
      have hB := Blocks.class_isBlock p.toSetoid hr a
      rcases hB.subsingleton_or_eq_univ with hs | hu
      · exact False.elim (hb (hs hab (show p.toSetoid a a from rfl)))
      · apply Or.inr
        apply p.eq_indiscrete.mpr
        have hall (x : Fin n) : p.Same a x := by
          have hx : x ∈ ({x | p.toSetoid a x} : Set (Fin n)) := by rw [hu]; trivial
          exact hx
        intro x y
        exact (hall x).symm.trans (hall y)

theorem isPrimitive_spec (G : Group n) : G.isPrimitive = true ↔
    2 ≤ n ∧ MulAction.IsPreprimitive (closure G.generators) (Fin n) :=
  G.isPrimitive_iff.trans G.primitive_spec

end Group

end Hex.PermGroup
