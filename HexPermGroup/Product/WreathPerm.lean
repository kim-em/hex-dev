/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Product.Block

public section

namespace Hex.Perm.Wreath

/-- The imprimitive action uses the base factor at the destination block:
`(f,h)(i,j) = (f(h(j))(i), h(j))`. -/
@[expose] def act (hn : 0 < n) (f : Fin m → Perm n) (h : Perm m) (x : Fin (n * m)) : Fin (n * m) :=
  index ((f (h.get (block hn x))).get (point hn x)) (h.get (block hn x))

@[simp] theorem act_index (hn : 0 < n) (f : Fin m → Perm n) (h : Perm m) (i : Fin n) (j : Fin m) :
    act hn f h (index i j) = index ((f (h.get j)).get i) (h.get j) := by simp [act]

@[expose] def inverse (f : Fin m → Perm n) (h : Perm m) : Fin m → Perm n := fun j => (f (h.get j)).inv

@[simp] theorem inv_act (hn : 0 < n) (f : Fin m → Perm n) (h : Perm m) (x : Fin (n * m)) :
    act hn (inverse f h) h.inv (act hn f h x) = x := by
  simp [act, inverse]

@[simp] theorem act_inv (hn : 0 < n) (f : Fin m → Perm n) (h : Perm m) (x : Fin (n * m)) :
    act hn f h (act hn (inverse f h) h.inv x) = x := by
  simp [act, inverse]

@[expose] def perm (hn : 0 < n) (f : Fin m → Perm n) (h : Perm m) : Perm (n * m) :=
  Perm.ofFn (act hn f h)
    (fun i j he => by simpa using congrArg (act hn (inverse f h) h.inv) he)
    (fun i => ⟨act hn (inverse f h) h.inv i, act_inv hn f h i⟩)

@[simp] theorem perm_index (hn : 0 < n) (f : Fin m → Perm n) (h : Perm m) (i : Fin n) (j : Fin m) :
    (perm hn f h).get (index i j) = index ((f (h.get j)).get i) (h.get j) := by simp [perm]

@[simp] theorem perm_id (hn : 0 < n) : perm (m := m) hn (fun _ => Perm.id n) (Perm.id m) = Perm.id (n * m) := by
  apply Perm.ext
  intro x
  simp [perm, act]

/-- Multiplication is `(f,h)(g,k) = (j ↦ f(j)*g(h⁻¹(j)), h*k)`. -/
theorem perm_comp (hn : 0 < n) (f g : Fin m → Perm n) (h k : Perm m) :
    (perm hn f h).comp (perm hn g k) =
      perm hn (fun j => (f j).comp (g (h.inv.get j))) (h.comp k) := by
  apply Perm.ext
  intro x
  rw [← index_point_block hn x]
  simp only [Perm.get_comp, perm_index, Perm.inv_get_get]

theorem perm_inv (hn : 0 < n) (f : Fin m → Perm n) (h : Perm m) :
    (perm hn f h).inv = perm hn (inverse f h) h.inv := by
  apply Perm.ext
  intro x
  apply (perm hn f h).get_inj
  simpa only [perm, Perm.get_ofFn, Perm.get_inv_get] using (act_inv hn f h x).symm

/-- Nonempty blocks are necessary for the top permutation to be recoverable.
The base factors are then uniquely recoverable from the point action too. -/
theorem perm_injective (hn : 0 < n) {f g : Fin m → Perm n} {h k : Perm m}
    (he : perm hn f h = perm hn g k) : (∀ j, f j = g j) ∧ h = k := by
  have ht : h = k := by
    apply Perm.ext
    intro j
    have hh := congrArg (fun p : Perm (n * m) => block hn (p.get (index ⟨0, hn⟩ j))) he
    simpa using hh
  subst k
  refine ⟨?_, rfl⟩
  intro j
  apply Perm.ext
  intro i
  have hh := congrArg (fun p : Perm (n * m) => point hn (p.get (index i (h.inv.get j)))) he
  simpa using hh

end Hex.Perm.Wreath
