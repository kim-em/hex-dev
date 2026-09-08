/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Action.Orbit
public import HexPermGroup.Word.Compose

public section

namespace Hex.PermGroup.Action.Orbit

variable {G : Group n} {α : Type u} [DecidableEq α] {a : Action G α} {x : α}
  {c : Orbit G α} (h : c.Valid a x)

/-- Schreier elements stay in the original permutation group. The action on
objects is used only to select the representative at the new orbit index. -/
@[expose] def schreier (p : Element G) (i : Fin c.objects.size) : Element G :=
  c.reps[(h.1.act p i).val].inv.comp (p.comp c.reps[i.val])

@[simp] theorem schreier_id (i : Fin c.objects.size) :
    schreier h (Element.id G) i = Element.id G := by
  simp [schreier]

theorem schreier_comp (p q : Element G) (i : Fin c.objects.size) :
    schreier h (p.comp q) i = (schreier h p (h.1.act q i)).comp (schreier h q i) := by
  apply Subtype.ext
  apply Perm.ext
  intro j
  simp [schreier, Domain.act_comp]

theorem schreier_inv (p : Element G) (i : Fin c.objects.size) :
    schreier h p.inv i = (schreier h p (h.1.act p.inv i)).inv := by
  apply Subtype.ext
  simp [schreier, Perm.inv_comp, Perm.comp_assoc]

@[simp] theorem schreier_fixes (p : Element G) (i : Fin c.objects.size) :
    a.act (schreier h p i) x = x := by
  apply a.act_injective c.reps[(h.1.act p i).val]
  simp only [schreier, Action.act_comp, Action.act_inv, rep_apply h]
  exact (h.1.object_act p i).symm

/-- Generator Schreier elements suffice for all elements, by the multiplication
and inverse identities above. This proof does not assume a faithful action. -/
theorem schreier_mem {T : Array (Perm n)}
    (hs : ∀ (j : Fin G.generators.size) (i : Fin c.objects.size),
      Generated T (schreier h ⟨G.generators[j.val], .generator (Array.getElem_mem j.isLt)⟩ i).val)
    (p : Element G) (i : Fin c.objects.size) : Generated T (schreier h p i).val := by
  obtain ⟨p, hp⟩ := p
  induction hp generalizing i with
  | id =>
    change Generated T (schreier h (Element.id G) i).val
    simp only [schreier_id, Element.val_id]
    exact .id
  | generator hp =>
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hp
    exact hs ⟨j, hj⟩ i
  | @comp p q hp hq ihp ihq =>
    change Generated T (schreier h (Element.comp ⟨p, hp⟩ ⟨q, hq⟩) i).val
    rw [schreier_comp, Element.val_comp]
    exact .comp (ihp _) (ihq i)
  | @inv p hp ih =>
    change Generated T (schreier h (Element.inv ⟨p, hp⟩) i).val
    rw [schreier_inv, Element.val_inv]
    exact .inv (ih _)

/-- Full Schreier family, in original-generator then orbit-discovery order. -/
@[expose] def stabilizerGens : Array (Perm n) :=
  ((List.finRange G.generators.size).flatMap fun j =>
    (List.finRange c.objects.size).map fun i =>
      (schreier h ⟨G.generators[j.val], .generator (Array.getElem_mem j.isLt)⟩ i).val).toArray

/-- The Schreier family generates exactly the object stabilizer in the
original group, including every element in the action kernel. -/
theorem stabilizerGens_spec (p : Perm n) : Generated (stabilizerGens h) p ↔
    ∃ hp : Generated G.generators p, a.act ⟨p, hp⟩ x = x := by
  constructor
  · intro hp
    apply hp.lift
    · exact ⟨.id, a.act_id x⟩
    · intro q hq
      simp only [stabilizerGens, List.mem_toArray, List.mem_flatMap, List.mem_map,
        List.mem_finRange, true_and] at hq
      obtain ⟨j, i, rfl⟩ := hq
      exact ⟨(schreier h _ i).property, schreier_fixes h _ i⟩
    · rintro q r ⟨hq, hqfix⟩ ⟨hr, hrfix⟩
      refine ⟨.comp hq hr, ?_⟩
      change a.act (Element.comp ⟨q, hq⟩ ⟨r, hr⟩) x = x
      rw [Action.act_comp, hrfix, hqfix]
    · rintro q ⟨hq, hfix⟩
      refine ⟨.inv hq, ?_⟩
      change a.act (Element.inv ⟨q, hq⟩) x = x
      apply a.act_injective ⟨q, hq⟩
      rw [Action.act_inv, hfix]
  · rintro ⟨hp, hfix⟩
    have hs : ∀ (j : Fin G.generators.size) (i : Fin c.objects.size),
        Generated (stabilizerGens h)
          (schreier h ⟨G.generators[j.val], .generator (Array.getElem_mem j.isLt)⟩ i).val := by
      intro j i
      apply Generated.generator
      simp only [stabilizerGens, List.mem_toArray, List.mem_flatMap, List.mem_map,
        List.mem_finRange, true_and]
      exact ⟨j, i, rfl⟩
    let b := Domain.index x h.2.1
    have hb : c.reps[b.val] = Element.id G :=
      (h.2.2 b).2.2 (Domain.object_index x h.2.1)
    have hab : h.1.act ⟨p, hp⟩ b = b := by
      apply h.1.object_injective
      simp [b, hfix]
    have hh := schreier_mem h hs ⟨p, hp⟩ b
    simpa [schreier, hab, hb] using hh

/-- Rebuild a checked chain for the complete object stabilizer. -/
@[expose] def stabilizer : Group n := Group.ofGenerators (stabilizerGens h)

theorem mem_stabilizer (p : Perm n) : Generated (stabilizer h).generators p ↔
    ∃ hp : Generated G.generators p, a.act ⟨p, hp⟩ x = x := stabilizerGens_spec h p

theorem stabilizer_subgroup : (stabilizer h).IsSubgroup G := fun p hp =>
  ((mem_stabilizer h p).mp hp).choose

/-- A Schreier generator has a checked program in the original inputs. -/
@[expose] def schreierWord (j : Fin G.generators.size) (i : Fin c.objects.size) : Program :=
  let p : Element G := ⟨G.generators[j.val], .generator (Array.getElem_mem j.isLt)⟩
  c.words[(h.1.act p i).val].inv.comp ((⟨#[.generator j.val], 0⟩ : Program).comp c.words[i.val])

theorem check_schreierWord (j : Fin G.generators.size) (i : Fin c.objects.size) :
    checkWord G.generators
      (schreier h ⟨G.generators[j.val], .generator (Array.getElem_mem j.isLt)⟩ i).val
      (schreierWord h j i) = true := by
  apply decide_eq_true
  apply Program.eval_comp
  · exact Program.eval_inv (of_decide_eq_true (h.2.2 _).1)
  · apply Program.eval_comp
    · simp [Program.eval, Program.evalCertified, Program.evalNodes, Program.evalNode, j.isLt]
    · exact of_decide_eq_true (h.2.2 i).1

end Hex.PermGroup.Action.Orbit
