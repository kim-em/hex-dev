/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerCatalog

public section

namespace Hex.RealClosure.Tower
open Lean SignDet
variable {registry : BaseContext.Registry}

/-- Read the descriptor fields and independently replay the supplied graph
over the exact native predecessor. All mathematical acceptance comes from
the shared descriptor checker, including its derived formal derivatives. -/
def Context.readDescriptor (parent : Context registry) (j : Json) :
    Except String (Descriptor parent.Value Signature parent.sign parent.signature) := do
  let fields ← Codec.tuple 7 j
  let binding ← (contextCodec parent.signature).decode fields[0]
  if binding ≠ parent.signature then throw "root predecessor mismatch"
  let head ← Codec.readPoly parent.codec fields[1]
  let lower ← Codec.readEndpoint parent.codec fields[2]
  let upper ← Codec.readEndpoint parent.codec fields[3]
  let indices ← fromJson? (α := List Nat) fields[4]
  let signs ← fromJson? (α := List Int) fields[5]
  let raw : RawDescriptor parent.Value Signature :=
    ⟨binding, head, lower, upper, indices, signs⟩
  let graph ← Codec.readGraph parent.codec (contextCodec parent.signature)
    parent.signature head lower upper fields[6]
  match graph.descriptor? parent.sign parent.signature raw with
  | none => throw "root descriptor replay rejected"
  | some descriptor => return descriptor

/-- A reconstructed root owns both the checked descriptor and the actual
native extension. Exact frame equality retains the requested full identity,
including replay sharing and every coefficient representation. -/
structure RestoredRoot (parent : Context registry) (frame : Literal) : Type 1 where
  private mk ::
  descriptor : Descriptor parent.Value Signature parent.sign parent.signature
  extension : Extension parent descriptor
  accepted : parent.readDescriptor frame.toJson = .ok descriptor
  constructed : parent.adjoin? descriptor = some extension
  frame_eq : extension.frame = frame

/-- Reconstruct one new native algebraic level from supplied structured data.
An accepted but differently encoded replay is rejected as a different binding;
the reader never silently replaces a full requested context identity. -/
def Context.readFrame (parent : Context registry) (frame : Literal) :
    Except String (RestoredRoot parent frame) :=
  match hd : parent.readDescriptor frame.toJson with
  | .error message => .error message
  | .ok descriptor => match he : parent.adjoin? descriptor with
    | none => .error "unsupported native root frame"
    | some extension => if hf : extension.frame = frame then
        .ok ⟨descriptor, extension, hd, he, hf⟩
      else .error "noncanonical root frame"

theorem RestoredRoot.binding (result : RestoredRoot parent frame) :
    result.extension.context.signature = parent.signature.extend frame := by
  rw [result.extension.binding, result.frame_eq]

/-- The retained descriptor re-encodes to the exact input frame, including its
complete replay graph. This is a property of every successful reconstruction. -/
theorem RestoredRoot.frame_data (result : RestoredRoot parent frame) :
    frame.toJson = rootData parent.codec result.descriptor := by
  exact (congrArg Literal.toJson result.frame_eq).symm.trans
    (Literal.toJson_ofJson _ _ result.extension.encoded)

@[expose] def Signature.append (signature : Signature) (frames : List Literal) : Signature :=
  { signature with roots := signature.roots ++ frames }

theorem Signature.append_nil (signature : Signature) : signature.append [] = signature := by
  cases signature
  simp [Signature.append]

theorem Signature.append_cons (signature : Signature) (frame : Literal) (frames : List Literal) :
    (signature.extend frame).append frames = signature.append (frame :: frames) := by
  simp [Signature.extend, Signature.append, List.append_assoc]

/-- Reconstruct successive levels in predecessor order. A validated cached
prefix is reused; every missing prefix goes through the actual frame reader.
The returned context's full binding is proved, rather than a hash assertion. -/
def Catalog.readFrames (catalog : Catalog registry) (parent : Context registry) :
    (frames : List Literal) →
      Except String { context : Context registry // context.signature = parent.signature.append frames }
  | [] => .ok ⟨parent, (Signature.append_nil parent.signature).symm⟩
  | frame :: frames =>
    let next : Except String { context : Context registry //
        context.signature = parent.signature.extend frame } :=
      match hl : catalog.lookup (parent.signature.extend frame) with
      | some context => .ok ⟨context, catalog.lookup_signature _ context hl⟩
      | none => match parent.readFrame frame with
        | .error message => .error message
        | .ok root => .ok ⟨root.extension.context, root.binding⟩
    match next with
    | .error message => .error message
    | .ok child => match catalog.readFrames child.val frames with
      | .error message => .error message
      | .ok result => .ok ⟨result.val, by
          rw [result.property, child.property, Signature.append_cons]⟩

/-- Recover a native tower from a supplied whole-context identity. The catalog
supplies the exact validated real base and its erased search progress. Unknown
algebraic levels are independently reconstructed from their replay frames. -/
def Catalog.reconstruct (catalog : Catalog registry) (binding : Signature) :
    Except String { context : Context registry // context.signature = binding } :=
  match hl : catalog.lookup binding with
  | some context => .ok ⟨context, catalog.lookup_signature _ context hl⟩
  | none => match hb : catalog.lookup ⟨binding.base, []⟩ with
    | none => .error "unknown validated base"
    | some base => match catalog.readFrames base binding.roots with
      | .error message => .error message
      | .ok result => .ok ⟨result.val, by
          rw [result.property, catalog.lookup_signature _ base hb]
          cases binding
          rfl⟩

theorem Catalog.reconstruct_lookup (catalog : Catalog registry) (binding : Signature)
    (context : Context registry) (h : catalog.lookup binding = some context) :
    catalog.reconstruct binding = .ok ⟨context, catalog.lookup_signature _ context h⟩ := by
  unfold Catalog.reconstruct
  split
  · rename_i found hf
    have he : found = context := Option.some.inj (hf.symm.trans h)
    subst found
    rfl
  · rename_i hn
    rw [hn] at h
    contradiction

/-- Reconstruct the full native context before checking the scalar payload.
The catalog is immutable; the returned value owns the newly reconstructed
context whether or not the caller chooses to install it for subsequent reads. -/
def Catalog.restoreElement (catalog : Catalog registry) (raw : Serialized) :
    Except String (PackedElement registry) :=
  match catalog.reconstruct raw.binding with
  | .error message => .error message
  | .ok context => match context.val.read raw with
    | .error message => .error message
    | .ok value => .ok ⟨context.val, value⟩

def Catalog.restorePolynomial (catalog : Catalog registry) (raw : Serialized) :
    Except String (PackedPolynomial registry) :=
  match catalog.reconstruct raw.binding with
  | .error message => .error message
  | .ok context => match context.val.readPoly raw with
    | .error message => .error message
    | .ok value => .ok ⟨context.val, value⟩

theorem Catalog.restoreElement_signature (catalog : Catalog registry) (raw : Serialized)
    (result : PackedElement registry) (h : catalog.restoreElement raw = .ok result) :
    result.context.signature = raw.binding := by
  simp only [Catalog.restoreElement] at h
  cases hc : catalog.reconstruct raw.binding with
  | error message => simp [hc] at h
  | ok context =>
    simp only [hc] at h
    cases hr : context.val.read raw with
    | error message => simp [hr] at h
    | ok value =>
      simp only [hr, Except.ok.injEq] at h
      subst result
      exact context.property

theorem Catalog.restorePolynomial_signature (catalog : Catalog registry) (raw : Serialized)
    (result : PackedPolynomial registry) (h : catalog.restorePolynomial raw = .ok result) :
    result.context.signature = raw.binding := by
  simp only [Catalog.restorePolynomial] at h
  cases hc : catalog.reconstruct raw.binding with
  | error message => simp [hc] at h
  | ok context =>
    simp only [hc] at h
    cases hr : context.val.readPoly raw with
    | error message => simp [hr] at h
    | ok value =>
      simp only [hr, Except.ok.injEq] at h
      subst result
      exact context.property

theorem Catalog.restoreElement_write (catalog : Catalog registry) (context : Context registry)
    (a : context.Value) (h : catalog.lookup context.signature = some context) :
    catalog.restoreElement (context.write a) = .ok ⟨context, a⟩ := by
  simp only [Catalog.restoreElement, Context.write]
  rw [catalog.reconstruct_lookup _ context h]
  simp [Context.read, context.codec_lawful a]

theorem Catalog.restorePolynomial_write (catalog : Catalog registry) (context : Context registry)
    (p : context.Poly) (h : catalog.lookup context.signature = some context) :
    catalog.restorePolynomial (context.writePoly p) = .ok ⟨context, p⟩ := by
  simp only [Catalog.restorePolynomial, Context.writePoly]
  rw [catalog.reconstruct_lookup _ context h]
  simp [Context.readPoly, Codec.read_poly context.codec context.codec_lawful p]

end Hex.RealClosure.Tower
