/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Subgroup

public section

namespace Hex.Perm

/-- Conjugation in left-action order. -/
@[expose] def conj (p q : Perm n) : Perm n := p.comp (q.comp p.inv)

@[simp] theorem conj_id (p : Perm n) : p.conj (Perm.id n) = Perm.id n := by simp [conj]

@[simp] theorem id_conj (p : Perm n) : (Perm.id n).conj p = p := by simp [conj]

theorem conj_comp (p q r : Perm n) : p.conj (q.comp r) = (p.conj q).comp (p.conj r) := by
  apply Perm.ext
  intro x
  simp [conj]

theorem conj_inv (p q : Perm n) : p.conj q.inv = (p.conj q).inv := by
  simp [conj, inv_comp, comp_assoc]

theorem comp_conj (p q r : Perm n) : (p.comp q).conj r = p.conj (q.conj r) := by
  simp [conj, inv_comp, comp_assoc]

@[simp] theorem inv_conj_conj (p q : Perm n) : p.inv.conj (p.conj q) = q := by
  rw [← comp_conj]
  simp

@[simp] theorem conj_inv_conj (p q : Perm n) : p.conj (p.inv.conj q) = q := by
  rw [← comp_conj]
  simp

end Hex.Perm

namespace Hex.PermGroup

theorem Generated.conj {S : Array (Perm n)} {q : Perm n} (hq : Generated S q) (p : Perm n) :
    Generated (S.map p.conj) (p.conj q) := by
  induction hq with
  | id => simpa using (Generated.id : Generated (S.map p.conj) (Perm.id n))
  | generator h => exact .generator (Array.mem_map.mpr ⟨_, h, rfl⟩)
  | comp _ _ ih ij => simpa only [Perm.conj_comp] using Generated.comp ih ij
  | inv _ ih => simpa only [Perm.conj_inv] using Generated.inv ih

namespace Group

/-- Conjugate every original generator and construct the resulting group. -/
@[expose] def conjugate (p : Perm n) (G : Group n) : Group n :=
  ofGenerators (G.generators.map p.conj)

theorem mem_conjugate (p : Perm n) (G : Group n) (q : Perm n) :
    Generated (conjugate p G).generators q ↔ Generated G.generators (p.inv.conj q) := by
  constructor
  · intro h
    apply h.lift (P := fun q => Generated G.generators (p.inv.conj q))
    · simpa using (Generated.id : Generated G.generators (Perm.id n))
    · intro r hr
      obtain ⟨s, hs, rfl⟩ := Array.mem_map.mp hr
      simpa using (Generated.generator hs : Generated G.generators s)
    · intro r s hr hs
      simpa only [Perm.conj_comp] using Generated.comp hr hs
    · intro r hr
      simpa only [Perm.conj_inv] using Generated.inv hr
  · intro h
    simpa only [conjugate, generators_ofGenerators, Perm.conj_inv_conj] using h.conj p

end Group

end Hex.PermGroup
