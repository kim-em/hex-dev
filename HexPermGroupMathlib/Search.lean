/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Centralizer
public import HexPermGroup.Search.Intersection
public import HexPermGroup.Search.Normalizer
public import HexPermGroup.Search.Sets
public import HexPermGroup.Search.SetTransporter
public import HexPermGroupMathlib.Subgroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.GroupAction.Basic

public section

namespace Hex.PermGroup

open scoped Pointwise

/-- Accepted completeness certificates identify the mathematical subgroup by
the same executable predicate used by the search. -/
theorem Search.checkSearch_mathlib {G : Group n} {P : Search.Predicate n}
    (C : Search.Constraint G P) (K : Group n) (certificate : Search.Certificate C.Reason)
    (h : Search.checkSearch C K certificate = true) (e : Equiv.Perm (Fin n)) :
    e ∈ closure K.generators ↔ e ∈ closure G.generators ∧ P.test (Perm.ofEquiv e) = true := by
  simpa only [generated_iff_mem, Perm.toEquiv_ofEquiv] using
    Search.checkSearch_spec C K certificate h (Perm.ofEquiv e)

theorem Search.Predicate.centralizer_spec (H : Group n) (p : Perm n) :
    (centralizer H).test p = true ↔ p.toEquiv ∈ Subgroup.centralizer (closure H.generators : Set _) := by
  rw [centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h q hq
    change q ∈ closure H.generators at hq
    have he := h (Perm.ofEquiv q) (generated_iff_mem.mpr (by simpa only [Perm.toEquiv_ofEquiv] using hq))
    simpa only [Perm.toEquiv_comp, Perm.toEquiv_ofEquiv] using congrArg Perm.toEquiv he.symm
  · intro h q hq
    apply Perm.equiv.injective
    change (p.comp q).toEquiv = (q.comp p).toEquiv
    simpa only [Perm.toEquiv_comp] using (h q.toEquiv (generated_iff_mem.mp hq)).symm

theorem Group.centralizer_spec (G H : Group n) :
    closure (G.centralizer H).generators =
      closure G.generators ⊓ Subgroup.centralizer (closure H.generators : Set _) := by
  ext e
  simpa only [Group.centralizer, Search.Predicate.centralizer_spec, Perm.toEquiv_ofEquiv,
    Subgroup.mem_inf] using Search.checkSearch_mathlib (Search.Centralizer.constraint G H)
      (G.centralizerSearch H).group (G.centralizerSearch H).certificate (G.centralizerSearch H).checked e

theorem Group.center_spec (G : Group n) :
    closure G.center.generators =
      closure G.generators ⊓ Subgroup.centralizer (closure G.generators : Set _) :=
  G.centralizer_spec G

theorem Group.centralizerPerm_spec (G : Group n) (q : Perm n) :
    closure (G.centralizerPerm q).generators =
      closure G.generators ⊓ Subgroup.centralizer ({q.toEquiv} : Set _) := by
  ext e
  have h := G.mem_centralizerPerm q (Perm.ofEquiv e)
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  simp only [generated_iff_mem, Perm.toEquiv_ofEquiv] at h
  rw [h]
  apply and_congr_right
  intro _
  constructor
  · intro he
    simpa only [Perm.toEquiv_comp, Perm.toEquiv_ofEquiv] using congrArg Perm.toEquiv he
  · intro he
    apply Perm.equiv.injective
    change ((Perm.ofEquiv e).comp q).toEquiv = (q.comp (Perm.ofEquiv e)).toEquiv
    simpa only [Perm.toEquiv_comp, Perm.toEquiv_ofEquiv] using he

theorem Group.intersection_spec (G H : Group n) :
    closure (G.intersection H).generators = closure G.generators ⊓ closure H.generators := by
  ext e
  simpa only [generated_iff_mem, Perm.toEquiv_ofEquiv, Subgroup.mem_inf] using
    G.mem_intersection H (Perm.ofEquiv e)

theorem Search.Predicate.normalizer_spec (H : Group n) (p : Perm n) :
    (normalizer H).test p = true ↔ p.toEquiv ∈ Subgroup.normalizer (closure H.generators : Set _) := by
  rw [normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h e
    simpa only [generated_iff_mem, Perm.conj, Perm.toEquiv_comp, Perm.toEquiv_inv,
      Perm.toEquiv_ofEquiv, mul_assoc] using h (Perm.ofEquiv e)
  · intro h q
    simpa only [generated_iff_mem, Perm.conj, Perm.toEquiv_comp, Perm.toEquiv_inv, mul_assoc] using h q.toEquiv

theorem Group.normalizer_spec (G H : Group n) :
    closure (G.normalizer H).generators =
      closure G.generators ⊓ Subgroup.normalizer (closure H.generators : Set _) := by
  ext e
  simpa only [Group.normalizer, Search.Predicate.normalizer_spec, Perm.toEquiv_ofEquiv,
    Subgroup.mem_inf] using Search.checkSearch_mathlib (Search.Normalizer.constraint G H)
      (G.normalizerSearch H).group (G.normalizerSearch H).certificate (G.normalizerSearch H).checked e

theorem Search.Predicate.setStabilizer_spec (A : Vector Bool n) (p : Perm n) :
    (setStabilizer A).test p = true ↔
      p.toEquiv ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) {x | A.get x = true} := by
  rw [MulAction.mem_stabilizer_iff, Set.ext_iff]
  simp only [Set.mem_smul_set_iff_inv_smul_mem, Equiv.Perm.smul_def, Set.mem_ofPred_eq,
    ← Perm.toEquiv_inv, Perm.toEquiv_apply]
  constructor
  · intro h x
    apply Bool.eq_iff_iff.mp
    simpa only [Perm.get_inv_get] using (of_decide_eq_true h) (p.inv.get x)
  · intro h
    apply decide_eq_true
    intro x
    apply Bool.eq_iff_iff.mpr
    simpa only [Perm.inv_get_get] using h (p.get x)

theorem Group.setStabilizer_spec (G : Group n) (A : Vector Bool n) :
    closure (G.setStabilizer A).generators = closure G.generators ⊓
      MulAction.stabilizer (Equiv.Perm (Fin n)) {x | A.get x = true} := by
  ext e
  simpa only [Group.setStabilizer, Search.Predicate.setStabilizer_spec, Perm.toEquiv_ofEquiv,
    Subgroup.mem_inf] using Search.checkSearch_mathlib (Search.Sets.constraint G A)
      (G.setStabilizerSearch A).group (G.setStabilizerSearch A).certificate (G.setStabilizerSearch A).checked e

theorem Search.Sets.test_image (A B : Vector Bool n) (p : Perm n) :
    test A B p = true ↔ p.toEquiv '' {x | A.get x = true} = {x | B.get x = true} := by
  constructor
  · intro h
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change B.get (p.get x) = true
      rw [← (of_decide_eq_true h) x]
      exact hx
    · intro hy
      refine ⟨p.inv.get y, ?_, by simp⟩
      change A.get (p.inv.get y) = true
      rw [(of_decide_eq_true h) (p.inv.get y), Perm.get_inv_get]
      exact hy
  · intro h
    apply decide_eq_true
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      have hy : p.toEquiv x ∈ p.toEquiv '' {x | A.get x = true} := ⟨x, hx, rfl⟩
      rw [h] at hy
      exact hy
    · intro hx
      have hy : p.toEquiv x ∈ p.toEquiv '' {x | A.get x = true} := by rw [h]; exact hx
      obtain ⟨y, hy, he⟩ := hy
      have hxy := p.toEquiv.injective he
      change A.get y = true at hy
      simpa only [hxy] using hy

theorem Group.setTransporter_spec (G : Group n) (A B : Vector Bool n) (p : Element G)
    (h : G.setTransporter? A B = some p) :
    p.val.toEquiv '' {x | A.get x = true} = {x | B.get x = true} :=
  (Search.Sets.test_image A B p.val).mp
    ((Search.Sets.test_action G A B p).mpr (G.setTransporter_image A B p h))

theorem Group.setTransporter_none_spec (G : Group n) (A B : Vector Bool n) :
    G.setTransporter? A B = none ↔ ¬ ∃ e : Equiv.Perm (Fin n), e ∈ closure G.generators ∧
      e '' {x | A.get x = true} = {x | B.get x = true} := by
  rw [Group.setTransporter_none]
  apply not_congr
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.val.toEquiv, generated_iff_mem.mp p.property,
      (Search.Sets.test_image A B p.val).mp ((Search.Sets.test_action G A B p).mpr hp)⟩
  · rintro ⟨e, he, hi⟩
    let p : Element G := ⟨Perm.ofEquiv e, generated_iff_mem.mpr (by simpa only [Perm.toEquiv_ofEquiv] using he)⟩
    refine ⟨p, (Search.Sets.test_action G A B p).mp ?_⟩
    apply (Search.Sets.test_image A B p.val).mpr
    simpa only [p, Perm.toEquiv_ofEquiv] using hi

theorem Group.transporter_coset_spec (G : Group n) (A B : Vector Bool n) (t : Element G)
    (ht : (Action.subsets G).act t A = B) (e : Equiv.Perm (Fin n)) :
    t.val.toEquiv⁻¹ * e ∈ closure (G.setStabilizer A).generators ↔ e ∈ closure G.generators ∧
      e '' {x | A.get x = true} = {x | B.get x = true} := by
  simpa only [generated_iff_mem, Perm.toEquiv_comp, Perm.toEquiv_inv, Perm.toEquiv_ofEquiv,
    Search.Sets.test_image] using G.mem_transporter_coset A B t ht (Perm.ofEquiv e)

end Hex.PermGroup
