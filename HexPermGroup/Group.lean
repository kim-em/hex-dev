/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Chain.Order

public section

namespace Hex.PermGroup

/-- A finite permutation group with an independently checked complete chain.
The original ordered generator array is retained for membership programs. -/
structure Group (n : Nat) where
  generators : Array (Perm n)
  chain : Chain n
  valid : checkChain generators chain = true

namespace Group

/-- Validate raw chain data before exposing any group decision or exact order. -/
@[expose] def ofChain? (S : Array (Perm n)) (c : Chain n) : Option (Group n) :=
  if h : checkChain S c = true then some ⟨S, c, h⟩ else none

@[simp] theorem isSome_ofChain? (S : Array (Perm n)) (c : Chain n) :
    (ofChain? S c).isSome = checkChain S c := by
  unfold ofChain?
  split <;> simp_all

/-- Exact membership, including replayable negative sifts. -/
@[expose] def contains (G : Group n) (p : Perm n) : Bool :=
  G.chain.accepts 0 p

theorem contains_iff (G : Group n) (p : Perm n) :
    G.contains p = true ↔ Generated G.generators p :=
  sift_iff G.valid p

/-- Exact order from the complete chain, using arbitrary-precision naturals. -/
@[expose] def order (G : Group n) : Nat := G.chain.orbitProduct

theorem order_pos (G : Group n) : 0 < G.order :=
  Chain.orbitProduct_pos (of_decide_eq_true G.valid).2.2

end Group

/-- Mathematical equality of represented subgroups, independent of their
ordered generators, certificates, or Lean record equality. -/
@[expose] def SameGroup (G H : Group n) : Prop :=
  ∀ p : Perm n, Generated G.generators p ↔ Generated H.generators p

/-- An element's identity is its permutation value. A membership word is separate
certificate data and does not enter equality. -/
abbrev Element (G : Group n) := {p : Perm n // Generated G.generators p}

namespace Element

variable {G : Group n}

/-- Construct an element from a raw permutation exactly when it belongs to the group. -/
@[expose] def ofPerm? (G : Group n) (p : Perm n) : Option (Element G) :=
  if h : G.contains p = true then some ⟨p, (G.contains_iff p).mp h⟩ else none

@[simp] theorem isSome_ofPerm? (G : Group n) (p : Perm n) :
    (ofPerm? G p).isSome = G.contains p := by
  unfold ofPerm?
  split <;> simp_all

@[expose] protected def id (G : Group n) : Element G := ⟨Perm.id n, .id⟩

@[expose] def comp (p q : Element G) : Element G :=
  ⟨p.val.comp q.val, .comp p.property q.property⟩

@[expose] def inv (p : Element G) : Element G := ⟨p.val.inv, .inv p.property⟩

instance : Mul (Element G) := ⟨comp⟩
instance : Inv (Element G) := ⟨inv⟩
instance : OfNat (Element G) 1 := ⟨Element.id G⟩

@[simp] theorem val_id : (Element.id G).val = Perm.id n := rfl
@[simp] theorem val_comp (p q : Element G) : (p.comp q).val = p.val.comp q.val := rfl
@[simp] theorem val_inv (p : Element G) : p.inv.val = p.val.inv := rfl

@[simp] theorem comp_id (p : Element G) : p.comp (Element.id G) = p := by
  apply Subtype.ext
  simp

@[simp] theorem id_comp (p : Element G) : (Element.id G).comp p = p := by
  apply Subtype.ext
  simp

theorem comp_assoc (p q r : Element G) : (p.comp q).comp r = p.comp (q.comp r) := by
  apply Subtype.ext
  simp [Perm.comp_assoc]

@[simp] theorem comp_inv_self (p : Element G) : p.comp p.inv = Element.id G := by
  apply Subtype.ext
  simp

@[simp] theorem inv_comp_self (p : Element G) : p.inv.comp p = Element.id G := by
  apply Subtype.ext
  simp

end Element

end Hex.PermGroup
