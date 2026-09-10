/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Orbit

public section

namespace Hex.PermGroup.Orbit

variable {S : Array (Perm n)} {a : Fin n} {c : Orbit n}

/-- Read the orbit index of a point known to belong to the checked orbit. -/
@[expose] def index (h : c.Valid S a) (x : Fin n) (hx : x ∈ c.points) :
    Fin c.points.size :=
  c.lookup[x.val].get (Option.isSome_iff_ne_none.mpr fun he =>
    (h.2.2.2.1 x).1.mp he hx)

@[simp] theorem point_index (h : c.Valid S a) (x : Fin n) (hx : x ∈ c.points) :
    c.points[(index h x hx).val] = x :=
  (h.2.2.2.1 x).2 _ (Option.some_get _).symm

theorem point_injective (h : c.Valid S a) {i j : Fin c.points.size}
    (he : c.points[i.val] = c.points[j.val]) : i = j := by
  have hh := congrArg (fun x : Fin n => c.lookup[x.val]) he
  simp only [h.2.2.1 i, h.2.2.1 j] at hh
  exact Option.some.inj hh

/-- The action of a generated permutation on the stored orbit indices. -/
@[expose] def act (h : c.Valid S a) (p : Perm n) (hp : Generated S p)
    (x : Fin c.points.size) : Fin c.points.size :=
  index h (p.get c.points[x.val])
    ((h.invariant hp _).mp (Array.getElem_mem x.isLt))

@[simp] theorem point_act (h : c.Valid S a) (p : Perm n) (hp : Generated S p)
    (x : Fin c.points.size) :
    c.points[(act h p hp x).val] = p.get c.points[x.val] :=
  point_index ..

@[simp] theorem act_id (h : c.Valid S a) (x : Fin c.points.size) :
    act h (Perm.id n) .id x = x := by
  apply point_injective h
  simp

theorem act_comp (h : c.Valid S a) {p q : Perm n}
    (hp : Generated S p) (hq : Generated S q) (x : Fin c.points.size) :
    act h (p.comp q) (.comp hp hq) x = act h p hp (act h q hq x) := by
  apply point_injective h
  simp

@[simp] theorem act_inv (h : c.Valid S a) {p : Perm n}
    (hp : Generated S p) (x : Fin c.points.size) :
    act h p hp (act h p.inv (.inv hp) x) = x := by
  apply point_injective h
  simp

@[simp] theorem rep_apply (h : c.Valid S a) (x : Fin c.points.size) :
    c.reps[x.val].get a = c.points[x.val] :=
  (h.2.2.2.2.1 x).2.1

theorem rep_generated (h : c.Valid S a) (x : Fin c.points.size) :
    Generated S c.reps[x.val] :=
  checkWord_sound (h.2.2.2.2.1 x).1

/-- The Schreier element `t_(p(x))⁻¹ * p * t_x`, in left-action order. -/
@[expose] def schreier (h : c.Valid S a) (p : Perm n) (hp : Generated S p)
    (x : Fin c.points.size) : Perm n :=
  c.reps[(act h p hp x).val].inv.comp (p.comp c.reps[x.val])

@[simp] theorem schreier_id (h : c.Valid S a) (x : Fin c.points.size) :
    schreier h (Perm.id n) .id x = Perm.id n := by
  simp [schreier]

/-- Multiplication of Schreier elements follows the successive point images. -/
theorem schreier_comp (h : c.Valid S a) {p q : Perm n}
    (hp : Generated S p) (hq : Generated S q) (x : Fin c.points.size) :
    schreier h (p.comp q) (.comp hp hq) x =
      (schreier h p hp (act h q hq x)).comp (schreier h q hq x) := by
  apply Perm.ext
  intro i
  simp [schreier, act_comp h hp hq x]

theorem schreier_inv (h : c.Valid S a) {p : Perm n}
    (hp : Generated S p) (x : Fin c.points.size) :
    schreier h p.inv (.inv hp) x =
      (schreier h p hp (act h p.inv (.inv hp) x)).inv := by
  simp [schreier, Perm.inv_comp, Perm.comp_assoc]

theorem schreier_generated (h : c.Valid S a) {p : Perm n}
    (hp : Generated S p) (x : Fin c.points.size) :
    Generated S (schreier h p hp x) :=
  .comp (.inv (rep_generated h _)) (.comp hp (rep_generated h _))

@[simp] theorem schreier_fixes (h : c.Valid S a) {p : Perm n}
    (hp : Generated S p) (x : Fin c.points.size) :
    (schreier h p hp x).get a = a := by
  apply c.reps[(act h p hp x).val].get_inj
  simp [schreier, rep_apply h]

/-- If a subgroup contains the Schreier elements for all input generators,
it contains those for every generated permutation. -/
theorem schreier_mem {T : Array (Perm n)} (h : c.Valid S a)
    (hs : ∀ (i : Fin S.size) (x : Fin c.points.size),
      Generated T (schreier h S[i.val] (.generator (Array.getElem_mem i.isLt)) x))
    {p : Perm n} (hp : Generated S p) (x : Fin c.points.size) :
    Generated T (schreier h p hp x) := by
  induction hp generalizing x with
  | id => simpa using (Generated.id (S := T))
  | generator hp =>
    rcases Array.mem_iff_getElem.mp hp with ⟨i, hi, rfl⟩
    exact hs ⟨i, hi⟩ x
  | comp hp hq ihp ihq =>
    rw [schreier_comp h hp hq]
    exact .comp (ihp _) (ihq x)
  | inv hp ih =>
    rw [schreier_inv h hp]
    exact .inv (ih _)

/-- The complete Schreier family for the supplied generators and checked orbit.
The chain builder supplies its normalized symmetric array here. -/
@[expose] def stabilizerGens (h : c.Valid S a) : Array (Perm n) :=
  ((List.finRange S.size).flatMap fun i =>
    (List.finRange c.points.size).map fun x =>
      schreier h S[i.val] (.generator (Array.getElem_mem i.isLt)) x).toArray

/-- Schreier's lemma: these generators give the entire point stabilizer. -/
theorem stabilizerGens_spec (h : c.Valid S a) (p : Perm n) :
    Generated (stabilizerGens h) p ↔ Generated S p ∧ p.get a = a := by
  constructor
  · intro hp
    apply hp.lift
    · exact ⟨.id, Perm.get_id a⟩
    · intro q hq
      simp only [stabilizerGens, List.mem_toArray, List.mem_flatMap,
        List.mem_map, List.mem_finRange, true_and] at hq
      rcases hq with ⟨i, x, rfl⟩
      exact ⟨schreier_generated h _ _, schreier_fixes h _ _⟩
    · intro q r hq hr
      exact ⟨.comp hq.1 hr.1, by simp [hq.2, hr.2]⟩
    · intro q hq
      refine ⟨.inv hq.1, ?_⟩
      apply q.get_inj
      simp [hq.2]
  · rintro ⟨hp, hfix⟩
    have hs : ∀ (i : Fin S.size) (x : Fin c.points.size),
        Generated (stabilizerGens h)
          (schreier h S[i.val] (.generator (Array.getElem_mem i.isLt)) x) := by
      intro i x
      apply Generated.generator
      simp only [stabilizerGens, List.mem_toArray, List.mem_flatMap,
        List.mem_map, List.mem_finRange, true_and]
      exact ⟨i, x, rfl⟩
    let b := index h a h.2.1
    have hb : c.reps[b.val] = Perm.id n :=
      (h.2.2.2.2.1 b).2.2 (point_index h a h.2.1)
    have hab : act h p hp b = b := by
      apply point_injective h
      simp [b, hfix]
    have hh := schreier_mem h hs hp b
    simpa [schreier, hab, hb] using hh

end Hex.PermGroup.Orbit
