/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Action.Finite

public section

namespace Hex.PermGroup

namespace LeftCoset

/-- Left cosets satisfy `pH = qH` exactly when `q⁻¹p` lies in `H`. -/
@[expose, instance_reducible] def setoid (H : Group n) : Setoid (Perm n) where
  r p q := Generated H.generators (q.inv.comp p)
  iseqv := ⟨fun p => by simpa using (Generated.id (S := H.generators)),
    fun {p q} h => by simpa [Perm.inv_comp] using h.inv,
    fun {p q r} hpq hqr => by
      have he : (r.inv.comp q).comp (q.inv.comp p) = r.inv.comp p := by
        apply Perm.ext
        intro i
        simp
      simpa only [he] using hqr.comp hpq⟩

end LeftCoset

/-- Cosets retain representatives internally, with equality determined by a
checked subgroup membership test. No normality assumption is made. -/
abbrev LeftCoset (H : Group n) := Quotient (LeftCoset.setoid H)

namespace LeftCoset

instance (H : Group n) : DecidableEq (LeftCoset H) :=
  @Quotient.decidableEq _ (setoid H) (fun p q =>
    decidable_of_iff (H.contains (q.inv.comp p) = true) (H.contains_iff _))

@[expose] def mk (H : Group n) (p : Perm n) : LeftCoset H := Quotient.mk _ p

theorem eq_iff (H : Group n) (p q : Perm n) : mk H p = mk H q ↔
    Generated H.generators (q.inv.comp p) :=
  ⟨Quotient.exact, fun h => Quotient.sound (s := setoid H) h⟩

@[simp] theorem eq_id (H : Group n) (p : Perm n) : mk H p = mk H (Perm.id n) ↔
    Generated H.generators p := by simp [eq_iff]

variable {H : Group n}

/-- Left multiplication is well-defined on left cosets for every subgroup. -/
@[expose] def act (p : Perm n) (q : LeftCoset H) : LeftCoset H :=
  Quotient.liftOn q (fun r => mk H (p.comp r)) (by
    intro r s hrs
    apply Quotient.sound
    have he : (p.comp s).inv.comp (p.comp r) = s.inv.comp r := by
      apply Perm.ext
      intro i
      simp [Perm.inv_comp]
    change Generated H.generators ((p.comp s).inv.comp (p.comp r))
    rw [he]
    exact hrs)

@[simp] theorem act_mk (H : Group n) (p q : Perm n) : act p (mk H q) = mk H (p.comp q) := rfl

@[simp] theorem act_id (q : LeftCoset H) : act (Perm.id n) q = q := by
  induction q using Quotient.inductionOn with
  | h q =>
    change act (Perm.id n) (mk H q) = mk H q
    rw [act_mk, Perm.id_comp]

theorem act_comp (p q : Perm n) (r : LeftCoset H) : act (p.comp q) r = act p (act q r) := by
  induction r using Quotient.inductionOn with
  | h r =>
    change act (p.comp q) (mk H r) = act p (act q (mk H r))
    simp only [act_mk, Perm.comp_assoc]

end LeftCoset

namespace Action

/-- The left action used for transversal discovery, including nonnormal subgroups. -/
@[expose] def leftCosets (G H : Group n) : Action G (LeftCoset H) where
  act p q := LeftCoset.act p.val q
  id_act := LeftCoset.act_id
  comp_act p q r := LeftCoset.act_comp p.val q.val r

end Action

end Hex.PermGroup
