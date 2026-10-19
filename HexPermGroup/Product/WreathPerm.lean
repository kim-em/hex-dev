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
@[expose] def act (f : Fin m → Perm n) (h : Perm m) (x : Fin (n * m)) : Fin (n * m) :=
  index ((f (h.get (block x))).get (point x)) (h.get (block x))

@[simp] theorem act_index (f : Fin m → Perm n) (h : Perm m) (i : Fin n) (j : Fin m) :
    act f h (index i j) = index ((f (h.get j)).get i) (h.get j) := by simp [act]

@[expose] def inverse (f : Fin m → Perm n) (h : Perm m) : Fin m → Perm n := fun j => (f (h.get j)).inv

@[simp] theorem inv_act (f : Fin m → Perm n) (h : Perm m) (x : Fin (n * m)) :
    act (inverse f h) h.inv (act f h x) = x := by
  simp [act, inverse]

@[simp] theorem act_inv (f : Fin m → Perm n) (h : Perm m) (x : Fin (n * m)) :
    act f h (act (inverse f h) h.inv x) = x := by
  simp [act, inverse]

@[expose] def perm (f : Fin m → Perm n) (h : Perm m) : Perm (n * m) :=
  Perm.ofFn (act f h)
    (fun i j he => by simpa using congrArg (act (inverse f h) h.inv) he)
    (fun i => ⟨act (inverse f h) h.inv i, act_inv f h i⟩)

/-- Cache each base permutation once before materializing the point action.
In particular, identity base factors in copies and lifts are not rebuilt at
every point of their block. -/
@[expose] def permImpl (f : Fin m → Perm n) (h : Perm m) : Perm (n * m) :=
  let factors := Hex.Vector.ofFn' f
  let action := act (fun j => factors[j.val]) h
  have agrees (x : Fin (n * m)) : action x = (perm f h).get x := by
    simp [action, factors, act, perm]
  Perm.ofFn action
    (fun i j he => (perm f h).get_inj (by simpa only [agrees] using he))
    (fun i => by
      obtain ⟨j, hj⟩ := (perm f h).get_surj i
      exact ⟨j, (agrees j).trans hj⟩)

/-- Native materialization caches the supplied base functions; kernel reduction
retains the original point-action definition. -/
@[csimp] theorem perm_eq : @perm = @permImpl := by
  funext n m f h
  apply Perm.ext
  intro x
  simp [perm, permImpl, act]

@[simp] theorem perm_index (f : Fin m → Perm n) (h : Perm m) (i : Fin n) (j : Fin m) :
    (perm f h).get (index i j) = index ((f (h.get j)).get i) (h.get j) := by simp [perm]

@[simp] theorem perm_id : perm (m := m) (fun _ => Perm.id n) (Perm.id m) = Perm.id (n * m) := by
  apply Perm.ext
  intro x
  simp [perm, act]

/-- Multiplication is `(f,h)(g,k) = (j ↦ f(j)*g(h⁻¹(j)), h*k)`. -/
theorem perm_comp (f g : Fin m → Perm n) (h k : Perm m) :
    (perm f h).comp (perm g k) =
      perm (fun j => (f j).comp (g (h.inv.get j))) (h.comp k) := by
  apply Perm.ext
  intro x
  rw [← index_point_block x]
  simp only [Perm.get_comp, perm_index, Perm.inv_get_get]

theorem perm_inv (f : Fin m → Perm n) (h : Perm m) :
    (perm f h).inv = perm (inverse f h) h.inv := by
  apply Perm.ext
  intro x
  apply (perm f h).get_inj
  simpa only [perm, Perm.get_ofFn, Perm.get_inv_get] using (act_inv f h x).symm

/-- Nonempty blocks are necessary for the top permutation to be recoverable.
The base factors are then uniquely recoverable from the point action too. -/
theorem perm_injective (hn : 0 < n) {f g : Fin m → Perm n} {h k : Perm m}
    (he : perm f h = perm g k) : (∀ j, f j = g j) ∧ h = k := by
  have ht : h = k := by
    apply Perm.ext
    intro j
    have hh := congrArg (fun p : Perm (n * m) => block (p.get (index ⟨0, hn⟩ j))) he
    simpa using hh
  subst k
  refine ⟨?_, rfl⟩
  intro j
  apply Perm.ext
  intro i
  have hh := congrArg (fun p : Perm (n * m) => point (p.get (index i (h.inv.get j)))) he
  simpa using hh

end Hex.Perm.Wreath
