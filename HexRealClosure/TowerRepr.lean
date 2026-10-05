/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ReprFormat
import all HexRealClosure.TowerBytes

public section

namespace Hex.RealClosure.Tower
open SignDet
variable {registry : BaseContext.Registry}

/-- Checked reconstruction code using caller bindings `catalog` and `limits`. -/
def Root.reprText {parent : Context registry} (root : Root parent) : String :=
  ReprFormat.write "restoreRootText" (root.writeText)

/-- Accept only this object's canonical checked reconstruction expression. -/
def Catalog.readRootRepr (catalog : Catalog registry) (input : String)
    (limits : Codec.Limits := {}) : Except String (PackedRoot registry) :=
  match ReprFormat.read "restoreRootText" input limits with
  | .error message => .error message
  | .ok text => catalog.restoreRootText text limits

instance {parent : Context registry} : Repr (Root parent) where
  reprPrec root _ := .text root.reprText

/-- The standard formatter receives exactly the proved total string printer. -/
theorem Root.reprPrec_eq {parent : Context registry} (root : Root parent) (precedence : Nat) :
    reprPrec root precedence = Std.Format.text root.reprText := rfl

/-- Re-reading the emitted expression reconstructs the exact native object
from its validated origin base, without installing an algebraic suffix.
All three bounds are lexical policy, rather than successful parse premises. -/
theorem Root.repr_roundtrip (catalog : BaseContext.Catalog registry)
    (parent : Context registry)
    (root : Root parent)
    (available : catalog.read (parent).origin.base.signature = some (parent).origin.base)
    (limits : Codec.Limits)
    (sourceBound : root.reprText.toUTF8.size ≤ limits.bytes)
    (literalBound : Codec.checkBytes limits (ReprFormat.quote (root.writeText)).toUTF8 = .ok ())
    (packetBound : Codec.checkBytes limits (root.writeBytes) = .ok ()) :
    (Catalog.ofBase catalog).readRootRepr root.reprText limits = .ok ⟨parent, root⟩ := by
  unfold Catalog.readRootRepr Root.reprText
  rw [ReprFormat.read_write _ _ limits sourceBound literalBound]
  exact Catalog.restoreRootText_origin catalog parent available root limits packetBound

/-- Checked reconstruction code using caller bindings `catalog` and `limits`. -/
def RootSet.reprText {parent : Context registry} (roots : RootSet parent) : String :=
  ReprFormat.write "restoreRootSetText" (roots.writeText)

/-- Accept only this object's canonical checked reconstruction expression. -/
def Catalog.readRootSetRepr (catalog : Catalog registry) (input : String)
    (limits : Codec.Limits := {}) : Except String (PackedRootSet registry) :=
  match ReprFormat.read "restoreRootSetText" input limits with
  | .error message => .error message
  | .ok text => catalog.restoreRootSetText text limits

instance {parent : Context registry} : Repr (RootSet parent) where
  reprPrec roots _ := .text roots.reprText

/-- The standard formatter receives exactly the proved total string printer. -/
theorem RootSet.reprPrec_eq {parent : Context registry} (roots : RootSet parent) (precedence : Nat) :
    reprPrec roots precedence = Std.Format.text roots.reprText := rfl

/-- Re-reading the emitted expression reconstructs the exact native object
from its validated origin base, without installing an algebraic suffix.
All three bounds are lexical policy, rather than successful parse premises. -/
theorem RootSet.repr_roundtrip (catalog : BaseContext.Catalog registry)
    (parent : Context registry)
    (roots : RootSet parent)
    (available : catalog.read (parent).origin.base.signature = some (parent).origin.base)
    (limits : Codec.Limits)
    (sourceBound : roots.reprText.toUTF8.size ≤ limits.bytes)
    (literalBound : Codec.checkBytes limits (ReprFormat.quote (roots.writeText)).toUTF8 = .ok ())
    (packetBound : Codec.checkBytes limits (roots.writeBytes) = .ok ()) :
    (Catalog.ofBase catalog).readRootSetRepr roots.reprText limits = .ok ⟨parent, roots⟩ := by
  unfold Catalog.readRootSetRepr RootSet.reprText
  rw [ReprFormat.read_write _ _ limits sourceBound literalBound]
  exact Catalog.restoreRootSetText_origin catalog parent available roots limits packetBound

/-- Checked reconstruction code using caller bindings `catalog` and `limits`. -/
def PackedElement.reprText (a : PackedElement registry) : String :=
  ReprFormat.write "restoreElementText" (a.writeText)

/-- Accept only this object's canonical checked reconstruction expression. -/
def Catalog.readElementRepr (catalog : Catalog registry) (input : String)
    (limits : Codec.Limits := {}) : Except String (PackedElement registry) :=
  match ReprFormat.read "restoreElementText" input limits with
  | .error message => .error message
  | .ok text => catalog.restoreElementText text limits

instance : Repr (PackedElement registry) where
  reprPrec a _ := .text a.reprText

/-- The standard formatter receives exactly the proved total string printer. -/
theorem PackedElement.reprPrec_eq (a : PackedElement registry) (precedence : Nat) :
    reprPrec a precedence = Std.Format.text a.reprText := rfl

/-- Re-reading the emitted expression reconstructs the exact native object
from its validated origin base, without installing an algebraic suffix.
All three bounds are lexical policy, rather than successful parse premises. -/
theorem PackedElement.repr_roundtrip (catalog : BaseContext.Catalog registry)
    (a : PackedElement registry)
    (available : catalog.read (a.context).origin.base.signature = some (a.context).origin.base)
    (limits : Codec.Limits)
    (sourceBound : a.reprText.toUTF8.size ≤ limits.bytes)
    (literalBound : Codec.checkBytes limits (ReprFormat.quote (a.writeText)).toUTF8 = .ok ())
    (packetBound : Codec.checkBytes limits (a.context.writeBytes a.value) = .ok ()) :
    (Catalog.ofBase catalog).readElementRepr a.reprText limits = .ok ⟨a.context, a.value⟩ := by
  unfold Catalog.readElementRepr PackedElement.reprText
  rw [ReprFormat.read_write _ _ limits sourceBound literalBound]
  exact Catalog.restoreElementText_origin catalog a.context available a.value limits packetBound

/-- Checked reconstruction code using caller bindings `catalog` and `limits`. -/
def PackedPolynomial.reprText (p : PackedPolynomial registry) : String :=
  ReprFormat.write "restorePolynomialText" (p.writeText)

/-- Accept only this object's canonical checked reconstruction expression. -/
def Catalog.readPolynomialRepr (catalog : Catalog registry) (input : String)
    (limits : Codec.Limits := {}) : Except String (PackedPolynomial registry) :=
  match ReprFormat.read "restorePolynomialText" input limits with
  | .error message => .error message
  | .ok text => catalog.restorePolynomialText text limits

instance : Repr (PackedPolynomial registry) where
  reprPrec p _ := .text p.reprText

/-- The standard formatter receives exactly the proved total string printer. -/
theorem PackedPolynomial.reprPrec_eq (p : PackedPolynomial registry) (precedence : Nat) :
    reprPrec p precedence = Std.Format.text p.reprText := rfl

/-- Re-reading the emitted expression reconstructs the exact native object
from its validated origin base, without installing an algebraic suffix.
All three bounds are lexical policy, rather than successful parse premises. -/
theorem PackedPolynomial.repr_roundtrip (catalog : BaseContext.Catalog registry)
    (p : PackedPolynomial registry)
    (available : catalog.read (p.context).origin.base.signature = some (p.context).origin.base)
    (limits : Codec.Limits)
    (sourceBound : p.reprText.toUTF8.size ≤ limits.bytes)
    (literalBound : Codec.checkBytes limits (ReprFormat.quote (p.writeText)).toUTF8 = .ok ())
    (packetBound : Codec.checkBytes limits (p.context.writePolyBytes p.value) = .ok ()) :
    (Catalog.ofBase catalog).readPolynomialRepr p.reprText limits = .ok ⟨p.context, p.value⟩ := by
  unfold Catalog.readPolynomialRepr PackedPolynomial.reprText
  rw [ReprFormat.read_write _ _ limits sourceBound literalBound]
  exact Catalog.restorePolynomialText_origin catalog p.context available p.value limits packetBound

def PackedRoot.reprText (root : PackedRoot registry) : String := root.root.reprText

def PackedRootSet.reprText (roots : PackedRootSet registry) : String := roots.roots.reprText

instance : Repr (PackedRoot registry) where
  reprPrec root _ := .text root.reprText

instance : Repr (PackedRootSet registry) where
  reprPrec roots _ := .text roots.reprText

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Root.reprPrec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Root.reprPrec_eq

/-- info: 'Hex.RealClosure.Tower.Root.repr_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Root.repr_roundtrip

/-- info: 'Hex.RealClosure.Tower.RootSet.reprPrec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.RootSet.reprPrec_eq

/-- info: 'Hex.RealClosure.Tower.RootSet.repr_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.RootSet.repr_roundtrip

/-- info: 'Hex.RealClosure.Tower.PackedElement.reprPrec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.PackedElement.reprPrec_eq

/-- info: 'Hex.RealClosure.Tower.PackedElement.repr_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.PackedElement.repr_roundtrip

/-- info: 'Hex.RealClosure.Tower.PackedPolynomial.reprPrec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.PackedPolynomial.reprPrec_eq

/-- info: 'Hex.RealClosure.Tower.PackedPolynomial.repr_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.PackedPolynomial.repr_roundtrip
