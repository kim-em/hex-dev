/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Product.WreathOrder
public import HexPermGroupMathlib.Group
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Algebra.Group.Pi.Basic

public section

namespace Hex.PermGroup.WreathProduct

/-- The top group acts on the base functions by inverse reindexing. -/
@[expose] def shift (G : Group n) (H : Group m) : Element H →* MulAut (Fin m → Element G) where
  toFun h :=
    { toFun := fun f j => f (h.val.inv.get j)
      invFun := fun f j => f (h.val.get j)
      left_inv := by intro f; funext j; simp
      right_inv := by intro f; funext j; simp
      map_mul' := by intro f g; rfl }
  map_one' := by
    apply MulEquiv.ext
    intro f
    funext j
    change f ((Perm.id m).inv.get j) = f j
    simp
  map_mul' h k := by
    apply MulEquiv.ext
    intro f
    funext j
    change f ((h.val.comp k.val).inv.get j) = f (k.val.inv.get (h.val.inv.get j))
    simp [Perm.inv_comp]

/-- The imprimitive permutation group is the semidirect product `G^m ⋊ H`,
with the executable base and top projections as the equivalence. -/
@[expose] def equiv (G : Group n) (H : Group m) (hn : 0 < n) :
    Element (G.wreathProduct H hn) ≃* SemidirectProduct (Fin m → Element G) (Element H) (shift G H) where
  toFun r := ⟨base hn r, top hn r⟩
  invFun x := pair hn x.left x.right
  left_inv := pair_factors hn
  right_inv x := by
    apply SemidirectProduct.ext
    · funext j
      exact base_pair hn x.left x.right j
    · exact top_pair hn x.left x.right
  map_mul' r s := by
    apply SemidirectProduct.ext
    · funext j
      exact base_comp hn r s j
    · exact top_comp hn r s

@[simp] theorem equiv_pair (G : Group n) (H : Group m) (hn : 0 < n)
    (f : Fin m → Element G) (h : Element H) : equiv G H hn (pair hn f h) = ⟨f, h⟩ := by
  apply SemidirectProduct.ext
  · funext j
    exact base_pair hn f h j
  · exact top_pair hn f h

@[expose] def inlHom (G : Group n) (H : Group m) (hn : 0 < n) :
    (Fin m → Element G) →* Element (G.wreathProduct H hn) where
  toFun := inl H hn
  map_one' := pair_id hn
  map_mul' f g := (inl_comp hn f g).symm

@[expose] def inrHom (G : Group n) (H : Group m) (hn : 0 < n) : Element H →* Element (G.wreathProduct H hn) where
  toFun := inr G hn
  map_one' := pair_id hn
  map_mul' h k := (inr_comp hn h k).symm

@[expose] def topHom (G : Group n) (H : Group m) (hn : 0 < n) : Element (G.wreathProduct H hn) →* Element H :=
  SemidirectProduct.rightHom.comp (equiv G H hn).toMonoidHom

theorem range_inl (G : Group n) (H : Group m) (hn : 0 < n) :
    (inlHom G H hn).range = (topHom G H hn).ker := by
  ext r
  exact (top_eq_id hn r).symm

theorem equiv_inl (G : Group n) (H : Group m) (hn : 0 < n) (f : Fin m → Element G) :
    equiv G H hn (inl H hn f) = SemidirectProduct.inl f := equiv_pair G H hn f (Element.id H)

theorem equiv_inr (G : Group n) (H : Group m) (hn : 0 < n) (h : Element H) :
    equiv G H hn (inr G hn h) = SemidirectProduct.inr h := equiv_pair G H hn (fun _ => Element.id G) h

/-- Inverse reindexing stated entirely in the generated Mathlib subgroups. -/
@[expose] def subgroupShift (G : Group n) (H : Group m) :
    closure H.generators →* MulAut (Fin m → closure G.generators) where
  toFun h :=
    { toFun := fun f j => f (h.val⁻¹ j)
      invFun := fun f j => f (h.val j)
      left_inv := by intro f; funext j; simp
      right_inv := by intro f; funext j; simp
      map_mul' := by intro f g; rfl }
  map_one' := by
    apply MulEquiv.ext
    intro f
    funext j
    simp
  map_mul' h k := by
    apply MulEquiv.ext
    intro f
    funext j
    simp

/-- The checked permutation subgroup is multiplicatively equivalent to the
Mathlib semidirect product of its mathematical factors. -/
@[expose] def groupEquiv (G : Group n) (H : Group m) (hn : 0 < n) :
    closure (G.wreathProduct H hn).generators ≃*
      SemidirectProduct (Fin m → closure G.generators) (closure H.generators) (subgroupShift G H) :=
  (Element.equiv (G.wreathProduct H hn)).symm.trans ((equiv G H hn).trans
    (SemidirectProduct.congr (φ₁ := shift G H) (φ₂ := subgroupShift G H)
      (MulEquiv.piCongrRight fun _ : Fin m => Element.equiv G) (Element.equiv H)
      (by intro h; apply MulEquiv.ext; intro f; funext j; rfl)))

theorem groupEquiv_pair (G : Group n) (H : Group m) (hn : 0 < n)
    (f : Fin m → Element G) (h : Element H) :
    groupEquiv G H hn (Element.equiv (G.wreathProduct H hn) (pair hn f h)) =
      ⟨fun j => Element.equiv G (f j), Element.equiv H h⟩ := by
  simp only [groupEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, equiv_pair]
  rfl

end Hex.PermGroup.WreathProduct
