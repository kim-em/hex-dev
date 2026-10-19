/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ReprFormat
import all HexRealClosure.TowerBytes
import all HexRealClosure.RootBytes

public section

namespace Hex.RealClosure.Tower
open SignDet
variable {registry : BaseContext.Registry}

/-- Unwrap a generated reconstruction expression. Arbitrary untrusted input
should use the corresponding `Except` reader instead. -/
@[expose] def ReprFormat.unwrap {α : Type u} (fallback : α) : Except String α → α
  | .ok value => value
  | .error message => Hex.panicWith fallback ("tower Repr: " ++ message)

/-- Restore a printed packed element using the caller's validated catalog. -/
@[expose] def Catalog.restoreElementText! (catalog : Catalog registry) (text : String) :
    PackedElement registry :=
  ReprFormat.unwrap ⟨Context.base (BaseContext.rational registry), 0⟩
    (match ReprFormat.readPacket text with
      | .error message => .error message
      | .ok data => catalog.restoreElement data)

/-- Restore a printed packed polynomial using the caller's validated catalog. -/
@[expose] def Catalog.restorePolynomialText! (catalog : Catalog registry) (text : String) :
    PackedPolynomial registry :=
  ReprFormat.unwrap ⟨Context.base (BaseContext.rational registry), 0⟩
    (match ReprFormat.readPacket text with
      | .error message => .error message
      | .ok data => catalog.restorePolynomial data)

/-- Restore a printed packed root using the caller's validated catalog. -/
@[expose] def Catalog.restoreRootText! (catalog : Catalog registry) (text : String) :
    PackedRoot registry :=
  ReprFormat.unwrap ⟨Context.base (BaseContext.rational registry), .point 0⟩
    (match ReprFormat.readPacket text with
      | .error message => .error message
      | .ok data => catalog.restoreRoot data)

/-- Restore a printed packed rootset using the caller's validated catalog. -/
@[expose] def Catalog.restoreRootSetText! (catalog : Catalog registry) (text : String) :
    PackedRootSet registry :=
  ReprFormat.unwrap ⟨Context.base (BaseContext.rational registry), .all⟩
    (match ReprFormat.readPacket text with
      | .error message => .error message
      | .ok data => catalog.restoreRootSet data)

/-- Restore the printed root in its original indexed predecessor. -/
@[expose] def Context.readRootText! (parent : Context registry) (text : String) : Root parent :=
  ReprFormat.unwrap (.point 0)
    (match ReprFormat.readPacket text with
      | .error message => .error message
      | .ok data => parent.readRootPacket data)

/-- The printed reader returns a value of the original indexed type. -/
def Root.reprText {parent : Context registry} (root : Root parent) : String :=
  ReprFormat.write "Context.readRootText!" "parent" root.writeText

instance {parent : Context registry} : Repr (Root parent) where
  reprPrec root _ := .text root.reprText

theorem Root.reprPrec_eq {parent : Context registry} (root : Root parent) (precedence : Nat) :
    reprPrec root precedence = Std.Format.text root.reprText := rfl

/-- The reconstruction expression returns the exact indexed object. Its only
requirement is the original indexed predecessor. -/
theorem Root.repr_roundtrip (parent : Context registry) (root : Root parent) :
    parent.readRootText! root.writeText = root := by
  unfold Context.readRootText! Root.writeText
  rw [ReprFormat.readPacket_write]
  simp only [bind, Except.bind]
  rw [Context.readRoot_write]
  rfl

/-- Restore the printed rootset in its original indexed predecessor. -/
@[expose] def Context.readRootSetText! (parent : Context registry) (text : String) : RootSet parent :=
  ReprFormat.unwrap (.all)
    (match ReprFormat.readPacket text with
      | .error message => .error message
      | .ok data => parent.readRootSetPacket data)

/-- The printed reader returns a value of the original indexed type. -/
def RootSet.reprText {parent : Context registry} (roots : RootSet parent) : String :=
  ReprFormat.write "Context.readRootSetText!" "parent" roots.writeText

instance {parent : Context registry} : Repr (RootSet parent) where
  reprPrec roots _ := .text roots.reprText

theorem RootSet.reprPrec_eq {parent : Context registry} (roots : RootSet parent) (precedence : Nat) :
    reprPrec roots precedence = Std.Format.text roots.reprText := rfl

/-- The reconstruction expression returns the exact indexed object. Its only
requirement is the original indexed predecessor. -/
theorem RootSet.repr_roundtrip (parent : Context registry) (roots : RootSet parent) :
    parent.readRootSetText! roots.writeText = roots := by
  unfold Context.readRootSetText! RootSet.writeText
  rw [ReprFormat.readPacket_write]
  simp only [bind, Except.bind]
  rw [Context.readRootSet_write]
  rfl

/-- Reconstruct the full immutable context from the caller's base catalog. -/
def PackedElement.reprText (a : PackedElement registry) : String :=
  ReprFormat.write "Catalog.restoreElementText!" "catalog" a.writeText

instance : Repr (PackedElement registry) where
  reprPrec a _ := .text a.reprText

theorem PackedElement.reprPrec_eq (a : PackedElement registry) (precedence : Nat) :
    reprPrec a precedence = Std.Format.text a.reprText := rfl

/-- The printed reader reconstructs the exact packed object from a base-only
catalog; no algebraic suffix or parser-success premise is supplied. -/
theorem PackedElement.repr_roundtrip (catalog : BaseContext.Catalog registry)
    (a : PackedElement registry)
    (available : catalog.read a.context.origin.base.signature = some a.context.origin.base) :
    (Catalog.ofBase catalog).restoreElementText! a.writeText = a := by
  unfold Catalog.restoreElementText! PackedElement.writeText Context.writeText
  rw [ReprFormat.readPacket_write]
  simp only [bind, Except.bind]
  rw [Catalog.restoreElement_origin catalog a.context available a.value]
  rfl

/-- Reconstruct the full immutable context from the caller's base catalog. -/
def PackedPolynomial.reprText (p : PackedPolynomial registry) : String :=
  ReprFormat.write "Catalog.restorePolynomialText!" "catalog" p.writeText

instance : Repr (PackedPolynomial registry) where
  reprPrec p _ := .text p.reprText

theorem PackedPolynomial.reprPrec_eq (p : PackedPolynomial registry) (precedence : Nat) :
    reprPrec p precedence = Std.Format.text p.reprText := rfl

/-- The printed reader reconstructs the exact packed object from a base-only
catalog; no algebraic suffix or parser-success premise is supplied. -/
theorem PackedPolynomial.repr_roundtrip (catalog : BaseContext.Catalog registry)
    (p : PackedPolynomial registry)
    (available : catalog.read p.context.origin.base.signature = some p.context.origin.base) :
    (Catalog.ofBase catalog).restorePolynomialText! p.writeText = p := by
  unfold Catalog.restorePolynomialText! PackedPolynomial.writeText Context.writePolyText
  rw [ReprFormat.readPacket_write]
  simp only [bind, Except.bind]
  rw [Catalog.restorePolynomial_origin catalog p.context available p.value]
  rfl

/-- Reconstruct the full immutable context from the caller's base catalog. -/
def PackedRoot.reprText (root : PackedRoot registry) : String :=
  ReprFormat.write "Catalog.restoreRootText!" "catalog" root.writeText

instance : Repr (PackedRoot registry) where
  reprPrec root _ := .text root.reprText

theorem PackedRoot.reprPrec_eq (root : PackedRoot registry) (precedence : Nat) :
    reprPrec root precedence = Std.Format.text root.reprText := rfl

/-- The printed reader reconstructs the exact packed object from a base-only
catalog; no algebraic suffix or parser-success premise is supplied. -/
theorem PackedRoot.repr_roundtrip (catalog : BaseContext.Catalog registry)
    (root : PackedRoot registry)
    (available : catalog.read root.parent.origin.base.signature = some root.parent.origin.base) :
    (Catalog.ofBase catalog).restoreRootText! root.writeText = root := by
  unfold Catalog.restoreRootText! PackedRoot.writeText Root.writeText
  rw [ReprFormat.readPacket_write]
  simp only [bind, Except.bind]
  rw [Catalog.restoreRoot_origin catalog root.parent available root.root]
  rfl

/-- Reconstruct the full immutable context from the caller's base catalog. -/
def PackedRootSet.reprText (roots : PackedRootSet registry) : String :=
  ReprFormat.write "Catalog.restoreRootSetText!" "catalog" roots.writeText

instance : Repr (PackedRootSet registry) where
  reprPrec roots _ := .text roots.reprText

theorem PackedRootSet.reprPrec_eq (roots : PackedRootSet registry) (precedence : Nat) :
    reprPrec roots precedence = Std.Format.text roots.reprText := rfl

/-- The printed reader reconstructs the exact packed object from a base-only
catalog; no algebraic suffix or parser-success premise is supplied. -/
theorem PackedRootSet.repr_roundtrip (catalog : BaseContext.Catalog registry)
    (roots : PackedRootSet registry)
    (available : catalog.read roots.parent.origin.base.signature = some roots.parent.origin.base) :
    (Catalog.ofBase catalog).restoreRootSetText! roots.writeText = roots := by
  unfold Catalog.restoreRootSetText! PackedRootSet.writeText RootSet.writeText
  rw [ReprFormat.readPacket_write]
  simp only [bind, Except.bind]
  rw [Catalog.restoreRootSet_origin catalog roots.parent available roots.roots]
  rfl

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

/-- info: 'Hex.RealClosure.Tower.PackedRoot.reprPrec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.PackedRoot.reprPrec_eq

/-- info: 'Hex.RealClosure.Tower.PackedRoot.repr_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.PackedRoot.repr_roundtrip

/-- info: 'Hex.RealClosure.Tower.PackedRootSet.reprPrec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.PackedRootSet.reprPrec_eq

/-- info: 'Hex.RealClosure.Tower.PackedRootSet.repr_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.PackedRootSet.repr_roundtrip
