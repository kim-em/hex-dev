/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Word

public section

namespace Hex.PermGroup.Kernel

/-- Generation by a predicate, for packed generators that have not yet been
reified as an array of permutations. Words use left-action composition. -/
inductive Span (S : Perm n → Prop) : Perm n → Prop
  | id : Span S (Perm.id n)
  | mul_left {a b} : S a → Span S b → Span S (a.comp b)
  | inv_mul_left {a b} : S a → Span S b → Span S (a.inv.comp b)

namespace Span

variable {S : Perm n → Prop}

theorem generator {p} (hp : S p) : Span S p := by
  simpa using mul_left hp id

theorem comp {p q} (hp : Span S p) (hq : Span S q) : Span S (p.comp q) := by
  induction hp with
  | id => simpa using hq
  | mul_left ha _ ih => simpa only [Perm.comp_assoc] using mul_left ha ih
  | inv_mul_left ha _ ih => simpa only [Perm.comp_assoc] using inv_mul_left ha ih

theorem inv {p} (hp : Span S p) : Span S p.inv := by
  induction hp with
  | id => simpa using (id (S := S))
  | mul_left ha _ ih =>
    simpa only [Perm.inv_comp, Perm.comp_id] using comp ih (inv_mul_left ha id)
  | inv_mul_left ha _ ih =>
    simpa only [Perm.inv_comp, Perm.inv_inv, Perm.comp_id] using comp ih (generator ha)

theorem lift {P : Perm n → Prop} (hi : P (Perm.id n)) (hs : ∀ p, S p → P p)
    (hc : ∀ p q, P p → P q → P (p.comp q)) (hv : ∀ p, P p → P p.inv)
    {p} (hp : Span S p) : P p := by
  induction hp with
  | id => exact hi
  | mul_left ha _ ih => exact hc _ _ (hs _ ha) ih
  | inv_mul_left ha _ ih => exact hc _ _ (hv _ (hs _ ha)) ih

theorem empty {p : Perm n} : Span (fun _ => False) p ↔ p = Perm.id n := by
  constructor
  · intro hp
    cases hp with
    | id => rfl
    | mul_left ha _ => cases ha
    | inv_mul_left ha _ => cases ha
  · rintro rfl
    exact id

end Span

end Hex.PermGroup.Kernel
