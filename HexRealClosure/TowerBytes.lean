/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootFrame
public import HexRealClosure.TowerRoots
public import HexSignDet.Codec.Bytes
import all HexSignDet.Codec.Bytes

public section

namespace Hex.RealClosure.Tower

open SignDet
open SignDet.Codec (Json)
variable {registry : BaseContext.Registry}

/-- A complete context binding and value payload in the shared JSON format. -/
@[expose] def Serialized.codec : ValueCodec Serialized where
  encode raw := .array (.cons (Signature.codec.encode raw.binding) (.cons raw.value .nil))
  decode
    | .array (.cons binding (.cons value .nil)) => do
      let binding ← Signature.codec.decode binding
      return ⟨binding, value⟩
    | _ => .error "expected a context and payload pair"

theorem Serialized.codec_lawful : Serialized.codec.Lawful := by
  intro raw
  simp only [codec]
  rw [Signature.codec_lawful raw.binding]
  rfl

/-- Print the whole binding and payload, retaining provider versions and root frames. -/
def Serialized.writeBytes (raw : Serialized) : ByteArray := Serialized.codec.encodeBytes raw

/-- The same shared JSON printer as text, including its token-separating whitespace. -/
@[expose] def Serialized.writeText (raw : Serialized) : String :=
  String.ofList (Codec.Token.writeTokens (Serialized.codec.encode raw).tokensLoop)

theorem Serialized.writeText_utf8 (raw : Serialized) : raw.writeText.toUTF8 = raw.writeBytes := by
  unfold Serialized.writeText Serialized.writeBytes ValueCodec.encodeBytes
    Json.Value.writeBytes Codec.Token.writeBytes
  rfl

/-- The actual shared printer and total UTF-8/JSON parser retain every field,
independently of a caller's optional lexical resource policy. -/
theorem Serialized.parse_write (raw : Serialized) :
    Json.readBytes raw.writeBytes = some (Serialized.codec.encode raw) := by
  unfold Serialized.writeBytes ValueCodec.encodeBytes
  exact Json.readBytes_write _

/-- Shared UTF-8/JSON parsing and lexical limits precede context or value validation. -/
def Serialized.readBytes (input : ByteArray) (limits : Codec.Limits := {}) : Except String Serialized :=
  Serialized.codec.decodeBytes input limits

/-- Exact byte roundtrip, under the caller's lexical resource policy. -/
theorem Serialized.readBytes_write (raw : Serialized) (limits : Codec.Limits)
    (bound : Codec.checkBytes limits raw.writeBytes = .ok ()) :
    Serialized.readBytes raw.writeBytes limits = .ok raw :=
  Serialized.codec.decode_encode Serialized.codec_lawful raw limits bound

/-- Print a native value with its complete immutable context. -/
def Context.writeBytes (context : Context registry) (a : context.Value) : ByteArray :=
  (context.write a).writeBytes

/-- Parse printed data, then require the supplied context's exact binding. -/
def Context.readBytes (context : Context registry) (input : ByteArray)
    (limits : Codec.Limits := {}) : Except String context.Value := do
  context.read (← Serialized.readBytes input limits)

/-- Print the actual complete context/value packet using the shared text format. -/
def Context.writeText (context : Context registry) (a : context.Value) : String :=
  (context.write a).writeText

def Context.readText (context : Context registry) (input : String)
    (limits : Codec.Limits := {}) : Except String context.Value :=
  context.readBytes input.toUTF8 limits

theorem Context.readBytes_write (context : Context registry) (a : context.Value)
    (limits : Codec.Limits) (bound : Codec.checkBytes limits (context.writeBytes a) = .ok ()) :
    context.readBytes (context.writeBytes a) limits = .ok a := by
  unfold Context.readBytes Context.writeBytes
  rw [Serialized.readBytes_write _ limits bound]
  exact context.read_write a

/-- A different full context binding is rejected after successful byte parsing. -/
theorem Context.readBytes_stale (context : Context registry) (raw : Serialized)
    (different : raw.binding ≠ context.signature) (limits : Codec.Limits)
    (bound : Codec.checkBytes limits raw.writeBytes = .ok ()) :
    context.readBytes raw.writeBytes limits = .error "context binding mismatch" := by
  unfold Context.readBytes
  rw [Serialized.readBytes_write _ limits bound]
  exact context.read_stale raw different

/-- Actual text printing and parsing return the exact original native value. -/
theorem Context.readText_write (context : Context registry) (a : context.Value)
    (limits : Codec.Limits) (bound : Codec.checkBytes limits (context.writeBytes a) = .ok ()) :
    context.readText (context.writeText a) limits = .ok a := by
  unfold Context.readText Context.writeText
  rw [Serialized.writeText_utf8]
  exact context.readBytes_write a limits bound

/-- Print every stored coefficient under the same whole-context binding. -/
def Context.writePolyBytes (context : Context registry) (p : context.Poly) : ByteArray :=
  (context.writePoly p).writeBytes

/-- Parse printed coefficients through the context's checked polynomial reader. -/
def Context.readPolyBytes (context : Context registry) (input : ByteArray)
    (limits : Codec.Limits := {}) : Except String context.Poly := do
  context.readPoly (← Serialized.readBytes input limits)

def Context.writePolyText (context : Context registry) (p : context.Poly) : String :=
  (context.writePoly p).writeText

def Context.readPolyText (context : Context registry) (input : String)
    (limits : Codec.Limits := {}) : Except String context.Poly :=
  context.readPolyBytes input.toUTF8 limits

theorem Context.readPolyBytes_write (context : Context registry) (p : context.Poly)
    (limits : Codec.Limits) (bound : Codec.checkBytes limits (context.writePolyBytes p) = .ok ()) :
    context.readPolyBytes (context.writePolyBytes p) limits = .ok p := by
  unfold Context.readPolyBytes Context.writePolyBytes
  rw [Serialized.readBytes_write _ limits bound]
  exact context.readPoly_write p

theorem Context.readPolyText_write (context : Context registry) (p : context.Poly)
    (limits : Codec.Limits) (bound : Codec.checkBytes limits (context.writePolyBytes p) = .ok ()) :
    context.readPolyText (context.writePolyText p) limits = .ok p := by
  unfold Context.readPolyText Context.writePolyText
  rw [Serialized.writeText_utf8]
  exact context.readPolyBytes_write p limits bound

/-- Read the full printed context through its registry-bound validated-prefix catalog. -/
def Catalog.restoreElementBytes (catalog : Catalog registry) (input : ByteArray)
    (limits : Codec.Limits := {}) : Except String (PackedElement registry) :=
  match Serialized.readBytes input limits with
  | .error message => .error message
  | .ok raw => catalog.restoreElement raw

/-- Read printed polynomial data in the actual reconstructed context. -/
def Catalog.restorePolynomialBytes (catalog : Catalog registry) (input : ByteArray)
    (limits : Codec.Limits := {}) : Except String (PackedPolynomial registry) :=
  match Serialized.readBytes input limits with
  | .error message => .error message
  | .ok raw => catalog.restorePolynomial raw

def Catalog.restoreElementText (catalog : Catalog registry) (input : String)
    (limits : Codec.Limits := {}) : Except String (PackedElement registry) :=
  catalog.restoreElementBytes input.toUTF8 limits

def Catalog.restorePolynomialText (catalog : Catalog registry) (input : String)
    (limits : Codec.Limits := {}) : Except String (PackedPolynomial registry) :=
  catalog.restorePolynomialBytes input.toUTF8 limits

def PackedElement.writeText (a : PackedElement registry) : String :=
  a.context.writeText a.value

def PackedPolynomial.writeText (p : PackedPolynomial registry) : String :=
  p.context.writePolyText p.value

theorem Catalog.restoreElementBytes_write (catalog : Catalog registry) (context : Context registry)
    (a : context.Value) (installed : catalog.lookup context.signature = some context)
    (limits : Codec.Limits) (bound : Codec.checkBytes limits (context.writeBytes a) = .ok ()) :
    catalog.restoreElementBytes (context.writeBytes a) limits = .ok ⟨context,a⟩ := by
  unfold Catalog.restoreElementBytes Context.writeBytes
  rw [Serialized.readBytes_write _ limits bound]
  exact catalog.restoreElement_write context a installed

theorem Catalog.restorePolynomialBytes_write (catalog : Catalog registry) (context : Context registry)
    (p : context.Poly) (installed : catalog.lookup context.signature = some context)
    (limits : Codec.Limits) (bound : Codec.checkBytes limits (context.writePolyBytes p) = .ok ()) :
    catalog.restorePolynomialBytes (context.writePolyBytes p) limits = .ok ⟨context,p⟩ := by
  unfold Catalog.restorePolynomialBytes Context.writePolyBytes
  rw [Serialized.readBytes_write _ limits bound]
  exact catalog.restorePolynomial_write context p installed

theorem Catalog.restoreElementText_write (catalog : Catalog registry) (context : Context registry)
    (a : context.Value) (installed : catalog.lookup context.signature = some context)
    (limits : Codec.Limits) (bound : Codec.checkBytes limits (context.writeBytes a) = .ok ()) :
    catalog.restoreElementText (context.writeText a) limits = .ok ⟨context,a⟩ := by
  unfold Catalog.restoreElementText Context.writeText
  rw [Serialized.writeText_utf8]
  exact catalog.restoreElementBytes_write context a installed limits bound

theorem Catalog.restorePolynomialText_write (catalog : Catalog registry) (context : Context registry)
    (p : context.Poly) (installed : catalog.lookup context.signature = some context)
    (limits : Codec.Limits) (bound : Codec.checkBytes limits (context.writePolyBytes p) = .ok ()) :
    catalog.restorePolynomialText (context.writePolyText p) limits = .ok ⟨context,p⟩ := by
  unfold Catalog.restorePolynomialText Context.writePolyText
  rw [Serialized.writeText_utf8]
  exact catalog.restorePolynomialBytes_write context p installed limits bound

/-- A printed root retains its actual owner and native value. Selected-root
heads, endpoints, Thom words and replay graphs are in the owner's full binding. -/
def Root.writeValueBytes {parent : Context registry} (root : Root parent) : ByteArray :=
  root.context.writeBytes root.value

def Root.writeValueText {parent : Context registry} (root : Root parent) : String :=
  root.context.writeText root.value

/-- Read a value packet using the root's original owner. -/
def Root.readValueBytes {parent : Context registry} (root : Root parent) (input : ByteArray)
    (limits : Codec.Limits := {}) : Except String root.context.Value :=
  root.context.readBytes input limits

def Root.readValueText {parent : Context registry} (root : Root parent) (input : String)
    (limits : Codec.Limits := {}) : Except String root.context.Value :=
  root.context.readText input limits

/-- A printed root is read as its exact native value in its original owner. -/
theorem Root.readValueBytes_write {parent : Context registry} (root : Root parent)
    (limits : Codec.Limits) (bound : Codec.checkBytes limits root.writeValueBytes = .ok ()) :
    root.readValueBytes root.writeValueBytes limits = .ok root.value :=
  root.context.readBytes_write root.value limits bound

theorem Root.readValueText_write {parent : Context registry} (root : Root parent)
    (limits : Codec.Limits) (bound : Codec.checkBytes limits root.writeValueBytes = .ok ()) :
    root.readValueText root.writeValueText limits = .ok root.value :=
  root.context.readText_write root.value limits bound

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Serialized.readBytes_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Serialized.readBytes_write

/-- info: 'Hex.RealClosure.Tower.Context.readBytes_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readBytes_write

/-- info: 'Hex.RealClosure.Tower.Context.readPolyBytes_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readPolyBytes_write

/-- info: 'Hex.RealClosure.Tower.Catalog.restoreElementBytes_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.restoreElementBytes_write

/-- info: 'Hex.RealClosure.Tower.Catalog.restorePolynomialBytes_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.restorePolynomialBytes_write

/-- info: 'Hex.RealClosure.Tower.Context.readText_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readText_write

/-- info: 'Hex.RealClosure.Tower.Context.readPolyText_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readPolyText_write

/-- info: 'Hex.RealClosure.Tower.Catalog.restoreElementText_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.restoreElementText_write

/-- info: 'Hex.RealClosure.Tower.Root.readValueText_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Root.readValueText_write

/-- info: 'Hex.RealClosure.Tower.Serialized.parse_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Serialized.parse_write

/-- info: 'Hex.RealClosure.Tower.Context.readBytes_stale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readBytes_stale

/-- info: 'Hex.RealClosure.Tower.Catalog.restorePolynomialText_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.restorePolynomialText_write

/-- info: 'Hex.RealClosure.Tower.Root.readValueBytes_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Root.readValueBytes_write
