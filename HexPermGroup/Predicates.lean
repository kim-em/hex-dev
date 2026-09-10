/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Conjugate

public section

namespace Hex.PermGroup

/-- Commutation with generators extends through products and inverses. -/
theorem Generated.commutes {S : Array (Perm n)} {p q : Perm n}
    (hq : Generated S q) (h : ∀ s ∈ S, p.comp s = s.comp p) : p.comp q = q.comp p := by
  induction hq with
  | id => simp
  | generator hs => exact h _ hs
  | @comp q r _ _ hq hr =>
    calc
      p.comp (q.comp r) = (p.comp q).comp r := (Perm.comp_assoc ..).symm
      _ = (q.comp p).comp r := congrArg (fun t => t.comp r) hq
      _ = q.comp (p.comp r) := Perm.comp_assoc ..
      _ = q.comp (r.comp p) := congrArg q.comp hr
      _ = (q.comp r).comp p := (Perm.comp_assoc ..).symm
  | @inv q _ hq =>
    apply Perm.ext
    intro x
    apply q.get_inj
    have he := congrArg (fun t : Perm n => t.get (q.inv.get x)) hq
    simpa using he.symm

namespace Group

/-- Test conjugates of original subgroup generators by symmetric ambient
generators. Containment is supplied separately, as required for normality. -/
@[expose] def isNormal (H G : Group n) (_h : H.IsSubgroup G) : Bool :=
  let symmetric := G.working.generators
  decide (∀ i : Fin symmetric.size, ∀ j : Fin H.generators.size,
    H.contains (symmetric[i.val].conj H.generators[j.val]) = true)

theorem isNormal_iff (H G : Group n) (h : H.IsSubgroup G) : H.isNormal G h = true ↔
    ∀ p q : Perm n, Generated G.generators p → Generated H.generators q →
      Generated H.generators (p.conj q) := by
  constructor
  · intro hc
    have step (p : Perm n) (hp : p ∈ G.working.generators) (q : Perm n)
        (hq : Generated H.generators q) : Generated H.generators (p.conj q) := by
      apply hq.lift (P := fun q => Generated H.generators (p.conj q))
      · simpa using (Generated.id : Generated H.generators (Perm.id n))
      · intro r hr
        obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hp
        obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hr
        exact (H.contains_iff _).mp ((of_decide_eq_true hc) ⟨i, hi⟩ ⟨j, hj⟩)
      · intro r s hr hs
        simpa only [Perm.conj_comp] using Generated.comp hr hs
      · intro r hr
        simpa only [Perm.conj_inv] using Generated.inv hr
    have invariant {p : Perm n} (hp : Generated G.working.generators p) (q : Perm n) :
        Generated H.generators q ↔ Generated H.generators (p.conj q) := by
      induction hp generalizing q with
      | id => simp
      | @generator p hp =>
        refine ⟨step p hp q, ?_⟩
        intro hq
        simpa using step p.inv (G.working.symmetric p hp) (p.conj q) hq
      | @comp p r _ _ hp hr =>
        simpa only [Perm.comp_conj] using (hr q).trans (hp (r.conj q))
      | @inv p _ hp =>
        simpa using (hp (p.inv.conj q)).symm
    intro p q hp hq
    exact (invariant ((G.working.generated_iff p).mpr hp) q).mp hq
  · intro hc
    apply decide_eq_true
    intro i j
    apply (H.contains_iff _).mpr
    exact hc _ _ ((G.working.generated_iff _).mp (.generator (Array.getElem_mem i.isLt)))
      (.generator (Array.getElem_mem j.isLt))

/-- Check commutation of the original generator pairs, without enumerating the group. -/
@[expose] def isAbelian (G : Group n) : Bool :=
  decide (∀ i j : Fin G.generators.size,
    G.generators[i.val].comp G.generators[j.val] = G.generators[j.val].comp G.generators[i.val])

/-- A noncommuting original generator pair, in deterministic index order. -/
@[expose] def abelianFailure? (G : Group n) : Option (Fin G.generators.size × Fin G.generators.size) :=
  ((List.finRange G.generators.size).flatMap fun i =>
    (List.finRange G.generators.size).map fun j => (i, j)).find? fun (i, j) =>
      decide (G.generators[i.val].comp G.generators[j.val] ≠ G.generators[j.val].comp G.generators[i.val])

theorem abelianFailure_none (G : Group n) : G.abelianFailure? = none ↔ G.isAbelian = true := by
  simp [abelianFailure?, isAbelian]

theorem abelianFailure_sound (G : Group n) (i j : Fin G.generators.size)
    (h : G.abelianFailure? = some (i, j)) :
    G.generators[i.val].comp G.generators[j.val] ≠ G.generators[j.val].comp G.generators[i.val] := by
  have hf := List.find?_some h
  exact of_decide_eq_true hf

/-- A symmetric ambient generator and original subgroup generator whose
conjugate has a failed complete sift in the subgroup. -/
@[expose] def normalFailure? (H G : Group n) :
    Option (Fin G.working.generators.size × Fin H.generators.size) :=
  ((List.finRange G.working.generators.size).flatMap fun i =>
    (List.finRange H.generators.size).map fun j => (i, j)).find? fun (i, j) =>
      !H.contains (G.working.generators[i.val].conj H.generators[j.val])

theorem normalFailure_none (H G : Group n) (h : H.IsSubgroup G) :
    H.normalFailure? G = none ↔ H.isNormal G h = true := by
  simp [normalFailure?, isNormal]

theorem normalFailure_sound (H G : Group n)
    (i : Fin G.working.generators.size) (j : Fin H.generators.size)
    (h : H.normalFailure? G = some (i, j)) :
    ¬ Generated H.generators (G.working.generators[i.val].conj H.generators[j.val]) := by
  have hf := List.find?_some h
  intro hp
  simp [(H.contains_iff _).mpr hp] at hf

theorem isAbelian_iff (G : Group n) : G.isAbelian = true ↔
    ∀ p q : Perm n, Generated G.generators p → Generated G.generators q → p.comp q = q.comp p := by
  constructor
  · intro h p q hp hq
    apply hq.commutes
    intro s hs
    apply Eq.symm
    apply hp.commutes
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hs
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp ht
    exact (of_decide_eq_true h) ⟨i, hi⟩ ⟨j, hj⟩
  · intro h
    apply decide_eq_true
    intro i j
    exact h _ _ (.generator (Array.getElem_mem i.isLt)) (.generator (Array.getElem_mem j.isLt))

/-- Transitivity requires a nonempty action. A singleton is transitive, including
when its generator array is empty. -/
@[expose] def isTransitive (G : Group n) : Bool :=
  if hn : 0 < n then
    let points := G.orbit ⟨0, hn⟩
    decide (∀ b : Fin n, b ∈ points)
  else false

theorem isTransitive_iff (G : Group n) : G.isTransitive = true ↔
    0 < n ∧ ∀ a b : Fin n, ∃ p : Perm n, Generated G.generators p ∧ p.get a = b := by
  unfold isTransitive
  split
  · rename_i hn
    constructor
    · intro h
      refine ⟨hn, ?_⟩
      intro a b
      obtain ⟨p, hp, ha⟩ := (G.mem_orbit ⟨0, hn⟩ a).mp ((of_decide_eq_true h) a)
      obtain ⟨q, hq, hb⟩ := (G.mem_orbit ⟨0, hn⟩ b).mp ((of_decide_eq_true h) b)
      refine ⟨q.comp p.inv, .comp hq (.inv hp), ?_⟩
      have he := congrArg p.inv.get ha
      simp only [Perm.inv_get_get] at he
      simp [← he, hb]
    · intro h
      apply decide_eq_true
      intro b
      exact (G.mem_orbit ⟨0, hn⟩ b).mpr (h.2 ⟨0, hn⟩ b)
  · rename_i hn
    simp [hn]

end Group

end Hex.PermGroup
