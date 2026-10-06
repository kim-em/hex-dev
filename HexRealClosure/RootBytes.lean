/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootFormat
public import HexRealClosure.TowerBytes
import all HexRealClosure.TowerBytes

public section

namespace Hex.RealClosure.Tower

open SignDet
variable {registry : BaseContext.Registry}

/-- Print the root kind and complete descriptor under its original predecessor. -/
def Root.writeBytes {parent : Context registry} (root : Root parent) : ByteArray :=
  root.write.writeBytes

def Root.writeText {parent : Context registry} (root : Root parent) : String :=
  root.write.writeText

/-- Parse the shared format before checking the original predecessor and root. -/
def Context.readRootBytes (parent : Context registry) (input : ByteArray)
    (limits : Codec.Limits := {}) : Except String (Root parent) :=
  match Serialized.readBytes input limits with
  | .error message => .error message
  | .ok data => parent.readRootPacket data

def Context.readRootText (parent : Context registry) (input : String)
    (limits : Codec.Limits := {}) : Except String (Root parent) :=
  parent.readRootBytes input.toUTF8 limits

/-- Print complete finite or universal results, retaining order and multiplicities. -/
def RootSet.writeBytes {parent : Context registry} (roots : RootSet parent) : ByteArray :=
  roots.write.writeBytes

def RootSet.writeText {parent : Context registry} (roots : RootSet parent) : String :=
  roots.write.writeText

def Context.readRootSetBytes (parent : Context registry) (input : ByteArray)
    (limits : Codec.Limits := {}) : Except String (RootSet parent) :=
  match Serialized.readBytes input limits with
  | .error message => .error message
  | .ok data => parent.readRootSetPacket data

def Context.readRootSetText (parent : Context registry) (input : String)
    (limits : Codec.Limits := {}) : Except String (RootSet parent) :=
  parent.readRootSetBytes input.toUTF8 limits

/-- Reconstruct the actual predecessor from its validated base before reading the root. -/
def Catalog.restoreRootBytes (catalog : Catalog registry) (input : ByteArray)
    (limits : Codec.Limits := {}) : Except String (PackedRoot registry) :=
  match Serialized.readBytes input limits with
  | .error message => .error message
  | .ok data => catalog.restoreRoot data

def Catalog.restoreRootText (catalog : Catalog registry) (input : String)
    (limits : Codec.Limits := {}) : Except String (PackedRoot registry) :=
  catalog.restoreRootBytes input.toUTF8 limits

def Catalog.restoreRootSetBytes (catalog : Catalog registry) (input : ByteArray)
    (limits : Codec.Limits := {}) : Except String (PackedRootSet registry) :=
  match Serialized.readBytes input limits with
  | .error message => .error message
  | .ok data => catalog.restoreRootSet data

def Catalog.restoreRootSetText (catalog : Catalog registry) (input : String)
    (limits : Codec.Limits := {}) : Except String (PackedRootSet registry) :=
  catalog.restoreRootSetBytes input.toUTF8 limits

def PackedRoot.writeText (root : PackedRoot registry) : String := root.root.writeText

def PackedRootSet.writeText (roots : PackedRootSet registry) : String := roots.roots.writeText

theorem Context.readRootBytes_write (parent : Context registry) (root : Root parent)
    (limits : Codec.Limits) (bound : Codec.checkBytes limits root.writeBytes = .ok ()) :
    parent.readRootBytes root.writeBytes limits = .ok root := by
  unfold Context.readRootBytes Root.writeBytes
  rw [Serialized.readBytes_write _ limits bound]
  exact parent.readRoot_write root

theorem Context.readRootText_write (parent : Context registry) (root : Root parent)
    (limits : Codec.Limits) (bound : Codec.checkBytes limits root.writeBytes = .ok ()) :
    parent.readRootText root.writeText limits = .ok root := by
  unfold Context.readRootText Root.writeText
  rw [Serialized.writeText_utf8]
  exact parent.readRootBytes_write root limits bound

theorem Context.readRootSetBytes_write (parent : Context registry) (roots : RootSet parent)
    (limits : Codec.Limits) (bound : Codec.checkBytes limits roots.writeBytes = .ok ()) :
    parent.readRootSetBytes roots.writeBytes limits = .ok roots := by
  unfold Context.readRootSetBytes RootSet.writeBytes
  rw [Serialized.readBytes_write _ limits bound]
  exact parent.readRootSet_write roots

theorem Context.readRootSetText_write (parent : Context registry) (roots : RootSet parent)
    (limits : Codec.Limits) (bound : Codec.checkBytes limits roots.writeBytes = .ok ()) :
    parent.readRootSetText roots.writeText limits = .ok roots := by
  unfold Context.readRootSetText RootSet.writeText
  rw [Serialized.writeText_utf8]
  exact parent.readRootSetBytes_write roots limits bound

/-- A stale predecessor is rejected after successful shared byte parsing. -/
theorem Context.readRootBytes_stale (parent : Context registry) (data : Serialized)
    (different : data.binding ≠ parent.signature) (limits : Codec.Limits)
    (bound : Codec.checkBytes limits data.writeBytes = .ok ()) :
    parent.readRootBytes data.writeBytes limits = .error "root predecessor mismatch" := by
  unfold Context.readRootBytes
  rw [Serialized.readBytes_write _ limits bound]
  exact parent.readRoot_stale data different

theorem Context.readRootSetBytes_stale (parent : Context registry) (data : Serialized)
    (different : data.binding ≠ parent.signature) (limits : Codec.Limits)
    (bound : Codec.checkBytes limits data.writeBytes = .ok ()) :
    parent.readRootSetBytes data.writeBytes limits = .error "root-set predecessor mismatch" := by
  unfold Context.readRootSetBytes
  rw [Serialized.readBytes_write _ limits bound]
  exact parent.readRootSet_stale data different

/-- Fresh reconstruction needs the original validated base, with no installed
algebraic suffix or assumed parser success. The result is the exact native root. -/
theorem Catalog.restoreRootBytes_origin (catalog : BaseContext.Catalog registry)
    (parent : Context registry)
    (available : catalog.read parent.origin.base.signature = some parent.origin.base)
    (root : Root parent) (limits : Codec.Limits)
    (bound : Codec.checkBytes limits root.writeBytes = .ok ()) :
    (Catalog.ofBase catalog).restoreRootBytes root.writeBytes limits = .ok ⟨parent, root⟩ := by
  unfold Catalog.restoreRootBytes Root.writeBytes
  rw [Serialized.readBytes_write _ limits bound]
  exact Catalog.restoreRoot_origin catalog parent available root

theorem Catalog.restoreRootText_origin (catalog : BaseContext.Catalog registry)
    (parent : Context registry)
    (available : catalog.read parent.origin.base.signature = some parent.origin.base)
    (root : Root parent) (limits : Codec.Limits)
    (bound : Codec.checkBytes limits root.writeBytes = .ok ()) :
    (Catalog.ofBase catalog).restoreRootText root.writeText limits = .ok ⟨parent, root⟩ := by
  unfold Catalog.restoreRootText Root.writeText
  rw [Serialized.writeText_utf8]
  exact Catalog.restoreRootBytes_origin catalog parent available root limits bound

theorem Catalog.restoreRootSetBytes_origin (catalog : BaseContext.Catalog registry)
    (parent : Context registry)
    (available : catalog.read parent.origin.base.signature = some parent.origin.base)
    (roots : RootSet parent) (limits : Codec.Limits)
    (bound : Codec.checkBytes limits roots.writeBytes = .ok ()) :
    (Catalog.ofBase catalog).restoreRootSetBytes roots.writeBytes limits = .ok ⟨parent, roots⟩ := by
  unfold Catalog.restoreRootSetBytes RootSet.writeBytes
  rw [Serialized.readBytes_write _ limits bound]
  exact Catalog.restoreRootSet_origin catalog parent available roots

theorem Catalog.restoreRootSetText_origin (catalog : BaseContext.Catalog registry)
    (parent : Context registry)
    (available : catalog.read parent.origin.base.signature = some parent.origin.base)
    (roots : RootSet parent) (limits : Codec.Limits)
    (bound : Codec.checkBytes limits roots.writeBytes = .ok ()) :
    (Catalog.ofBase catalog).restoreRootSetText roots.writeText limits = .ok ⟨parent, roots⟩ := by
  unfold Catalog.restoreRootSetText RootSet.writeText
  rw [Serialized.writeText_utf8]
  exact Catalog.restoreRootSetBytes_origin catalog parent available roots limits bound

/-- A native scalar's complete printed context reconstructs from its validated
base even when none of its algebraic suffix has been installed. -/
theorem Catalog.restoreElementBytes_origin (catalog : BaseContext.Catalog registry)
    (context : Context registry)
    (available : catalog.read context.origin.base.signature = some context.origin.base)
    (a : context.Value) (limits : Codec.Limits)
    (bound : Codec.checkBytes limits (context.writeBytes a) = .ok ()) :
    (Catalog.ofBase catalog).restoreElementBytes (context.writeBytes a) limits = .ok ⟨context, a⟩ := by
  unfold Catalog.restoreElementBytes Context.writeBytes
  rw [Serialized.readBytes_write _ limits bound]
  exact Catalog.restoreElement_origin catalog context available a

theorem Catalog.restorePolynomialBytes_origin (catalog : BaseContext.Catalog registry)
    (context : Context registry)
    (available : catalog.read context.origin.base.signature = some context.origin.base)
    (p : context.Poly) (limits : Codec.Limits)
    (bound : Codec.checkBytes limits (context.writePolyBytes p) = .ok ()) :
    (Catalog.ofBase catalog).restorePolynomialBytes (context.writePolyBytes p) limits = .ok ⟨context, p⟩ := by
  unfold Catalog.restorePolynomialBytes Context.writePolyBytes
  rw [Serialized.readBytes_write _ limits bound]
  exact Catalog.restorePolynomial_origin catalog context available p

theorem Catalog.restoreElementText_origin (catalog : BaseContext.Catalog registry)
    (context : Context registry)
    (available : catalog.read context.origin.base.signature = some context.origin.base)
    (a : context.Value) (limits : Codec.Limits)
    (bound : Codec.checkBytes limits (context.writeBytes a) = .ok ()) :
    (Catalog.ofBase catalog).restoreElementText (context.writeText a) limits = .ok ⟨context, a⟩ := by
  unfold Catalog.restoreElementText Context.writeText
  rw [Serialized.writeText_utf8]
  exact Catalog.restoreElementBytes_origin catalog context available a limits bound

theorem Catalog.restorePolynomialText_origin (catalog : BaseContext.Catalog registry)
    (context : Context registry)
    (available : catalog.read context.origin.base.signature = some context.origin.base)
    (p : context.Poly) (limits : Codec.Limits)
    (bound : Codec.checkBytes limits (context.writePolyBytes p) = .ok ()) :
    (Catalog.ofBase catalog).restorePolynomialText (context.writePolyText p) limits = .ok ⟨context, p⟩ := by
  unfold Catalog.restorePolynomialText Context.writePolyText
  rw [Serialized.writeText_utf8]
  exact Catalog.restorePolynomialBytes_origin catalog context available p limits bound

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Context.readRootBytes_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readRootBytes_write

/-- info: 'Hex.RealClosure.Tower.Context.readRootText_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readRootText_write

/-- info: 'Hex.RealClosure.Tower.Context.readRootSetBytes_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readRootSetBytes_write

/-- info: 'Hex.RealClosure.Tower.Context.readRootSetText_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readRootSetText_write

/-- info: 'Hex.RealClosure.Tower.Catalog.restoreRootBytes_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.restoreRootBytes_origin

/-- info: 'Hex.RealClosure.Tower.Catalog.restoreRootText_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.restoreRootText_origin

/-- info: 'Hex.RealClosure.Tower.Catalog.restoreRootSetBytes_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.restoreRootSetBytes_origin

/-- info: 'Hex.RealClosure.Tower.Catalog.restoreRootSetText_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.restoreRootSetText_origin

/-- info: 'Hex.RealClosure.Tower.Catalog.restoreElementBytes_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.restoreElementBytes_origin

/-- info: 'Hex.RealClosure.Tower.Catalog.restoreElementText_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.restoreElementText_origin

/-- info: 'Hex.RealClosure.Tower.Catalog.restorePolynomialBytes_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.restorePolynomialBytes_origin

/-- info: 'Hex.RealClosure.Tower.Catalog.restorePolynomialText_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.restorePolynomialText_origin

/-- info: 'Hex.RealClosure.Tower.Context.readRootBytes_stale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readRootBytes_stale

/-- info: 'Hex.RealClosure.Tower.Context.readRootSetBytes_stale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readRootSetBytes_stale
