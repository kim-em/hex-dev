/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Product.Order
public import HexPermGroupMathlib.Group
public import Mathlib.Algebra.Group.Prod

public section

namespace Hex.PermGroup.DirectProduct

/-- The executable factor projections identify the checked group with the
mathematical direct product, preserving multiplication. -/
@[expose] def equiv (G : Group n) (H : Group m) : Element (G.directProduct H) ≃* Element G × Element H where
  toFun r := (fst r, snd r)
  invFun pq := pair pq.1 pq.2
  left_inv := pair_factors
  right_inv pq := Prod.ext (fst_pair pq.1 pq.2) (snd_pair pq.1 pq.2)
  map_mul' r s := Prod.ext (fst_comp r s) (snd_comp r s)

@[simp] theorem equiv_pair (G : Group n) (H : Group m) (p : Element G) (q : Element H) :
    equiv G H (pair p q) = (p, q) := Prod.ext (fst_pair p q) (snd_pair p q)

@[expose] def inlHom (G : Group n) (H : Group m) : Element G →* Element (G.directProduct H) where
  toFun := inl H
  map_one' := pair_id
  map_mul' := inl_comp

@[expose] def inrHom (G : Group n) (H : Group m) : Element H →* Element (G.directProduct H) where
  toFun := inr G
  map_one' := pair_id
  map_mul' := inr_comp

@[expose] def fstHom (G : Group n) (H : Group m) : Element (G.directProduct H) →* Element G :=
  (MonoidHom.fst (Element G) (Element H)).comp (equiv G H).toMonoidHom

@[expose] def sndHom (G : Group n) (H : Group m) : Element (G.directProduct H) →* Element H :=
  (MonoidHom.snd (Element G) (Element H)).comp (equiv G H).toMonoidHom

/-- The same multiplicative equivalence stated entirely in Mathlib subgroups. -/
@[expose] def groupEquiv (G : Group n) (H : Group m) :
    closure (G.directProduct H).generators ≃* closure G.generators × closure H.generators :=
  (Element.equiv (G.directProduct H)).symm.trans
    ((equiv G H).trans (MulEquiv.prodCongr (Element.equiv G) (Element.equiv H)))

theorem groupEquiv_pair (G : Group n) (H : Group m) (p : Element G) (q : Element H) :
    groupEquiv G H (Element.equiv (G.directProduct H) (pair p q)) =
      (Element.equiv G p, Element.equiv H q) := by
  simp [groupEquiv]
  rfl

/-- The Mathlib equivalence uses exactly the executable coordinate projections. -/
theorem groupEquiv_apply (G : Group n) (H : Group m) (r : Element (G.directProduct H)) :
    groupEquiv G H (Element.equiv (G.directProduct H) r) =
      (Element.equiv G (fst r), Element.equiv H (snd r)) := by
  simpa only [pair_factors] using groupEquiv_pair G H (fst r) (snd r)

end Hex.PermGroup.DirectProduct
