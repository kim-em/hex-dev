/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerContext

public section

namespace Hex.RealClosure.Tower
open SignDet
open SignDet.Codec (Json)
variable {registry : BaseContext.Registry}

/-- The exact whole-context binding is checked before decoding the payload. -/
structure Serialized where
  binding : Signature
  value : Json

@[expose] def Context.write (context : Context registry) (a : context.Value) : Serialized :=
  ⟨context.signature, context.codec.encode a⟩

@[expose] def Context.read (context : Context registry) (raw : Serialized) :
    Except String context.Value :=
  if raw.binding = context.signature then context.codec.decode raw.value
  else .error "context binding mismatch"

theorem Context.read_write (context : Context registry) (a : context.Value) :
    context.read (context.write a) = .ok a := by
  simp [Context.read, Context.write, context.codec_lawful a]

theorem Context.read_stale (context : Context registry) (raw : Serialized)
    (h : raw.binding ≠ context.signature) :
    context.read raw = .error "context binding mismatch" := by simp [Context.read, h]

@[expose, reducible] def Context.Poly (context : Context registry) : Type := DensePoly context.Value

@[expose] def Context.writePoly (context : Context registry) (p : context.Poly) : Serialized :=
  ⟨context.signature, Codec.poly context.codec p⟩

@[expose] def Context.readPoly (context : Context registry) (raw : Serialized) :
    Except String context.Poly :=
  if raw.binding = context.signature then Codec.readPoly context.codec raw.value
  else .error "context binding mismatch"

theorem Context.readPoly_write (context : Context registry) (p : context.Poly) :
    context.readPoly (context.writePoly p) = .ok p := by
  simp only [Context.readPoly, Context.writePoly, ↓reduceIte]
  exact Codec.read_poly context.codec context.codec_lawful p

/-- A reconstructed scalar retains the entire returned context. -/
structure PackedElement (registry : BaseContext.Registry) : Type 1 where
  context : Context registry
  value : context.Value

@[expose] def PackedElement.write (a : PackedElement registry) : Serialized :=
  a.context.write a.value

@[expose] def PackedElement.sign (a : PackedElement registry) : Int := a.context.sign a.value

structure PackedPolynomial (registry : BaseContext.Registry) : Type 1 where
  context : Context registry
  value : context.Poly

@[expose] def PackedPolynomial.write (p : PackedPolynomial registry) : Serialized :=
  p.context.writePoly p.value

@[expose] def Context.ofBase (entry : BaseContext.PackedContext registry) : Context registry := by
  cases entry with
  | pack context => exact Context.base context

theorem Context.ofBase_signature (entry : BaseContext.PackedContext registry) :
    (Context.ofBase entry).signature = ⟨entry.signature, []⟩ := by
  cases entry
  rfl

private structure CatalogItem (registry : BaseContext.Registry) : Type 1 where
  digest : UInt64
  context : Context registry

/-- Immutable catalog of native validated prefixes. Entries retain exact real
search progress and every checked algebraic descriptor. A binding can never be
rebound; the separate base catalog reconstructs uninstalled base stages. -/
structure Catalog (registry : BaseContext.Registry) : Type 1 where
  private mk ::
  private base : BaseContext.Catalog registry
  private entries : List (CatalogItem registry)

namespace Catalog

def ofBase (base : BaseContext.Catalog registry) : Catalog registry := ⟨base, []⟩
def empty (registry : BaseContext.Registry) : Catalog registry := ofBase (.empty registry)

private def find (binding : Signature) (digest : UInt64) :
    List (CatalogItem registry) → Option (Context registry)
  | [] => none
  | entry :: rest =>
    if entry.digest = digest then
      if entry.context.signature = binding then some entry.context else find binding digest rest
    else find binding digest rest

/-- Compare the full ordered literal binding. Unknown algebraic signatures
are rejected; a reader does not manufacture new progress proofs or roots. -/
def lookup (catalog : Catalog registry) (binding : Signature) : Option (Context registry) :=
  match find binding (hash binding.literal) catalog.entries with
  | some context => some context
  | none => if binding.roots = [] then (catalog.base.read binding.base).map Context.ofBase
    else none

/-- Install an already constructed prefix, retaining the exact native handle. -/
def insert (catalog : Catalog registry) (entry : Context registry) : Option (Catalog registry) :=
  match catalog.lookup entry.signature with
  | none => some ⟨catalog.base, ⟨hash entry.signature.literal, entry⟩ :: catalog.entries⟩
  | some _ => none

/-- Resolve the context first, then check every recursively stored coefficient. -/
@[expose] def readElement (catalog : Catalog registry) (raw : Serialized) :
    Except String (PackedElement registry) :=
  match catalog.lookup raw.binding with
  | none => .error "unknown context"
  | some context => match context.codec.decode raw.value with
    | .error message => .error message
    | .ok value => .ok ⟨context, value⟩

@[expose] def readPolynomial (catalog : Catalog registry) (raw : Serialized) :
    Except String (PackedPolynomial registry) :=
  match catalog.lookup raw.binding with
  | none => .error "unknown context"
  | some context => match Codec.readPoly context.codec raw.value with
    | .error message => .error message
    | .ok value => .ok ⟨context, value⟩

private theorem find_signature (binding : Signature) (digest : UInt64)
    (entries : List (CatalogItem registry))
    (context : Context registry) (h : find binding digest entries = some context) :
    context.signature = binding := by
  induction entries with
  | nil => simp [find] at h
  | cons first rest ih =>
    simp only [find] at h
    split at h
    · split at h
      · cases h; assumption
      · exact ih h
    · exact ih h

theorem lookup_signature (catalog : Catalog registry) (binding : Signature)
    (context : Context registry) (h : catalog.lookup binding = some context) :
    context.signature = binding := by
  simp only [lookup] at h
  cases he : find binding (hash binding.literal) catalog.entries with
  | some entry =>
    simp only [he, Option.some.injEq] at h
    subst context
    exact find_signature binding _ _ entry he
  | none =>
    simp only [he] at h
    split at h
    · rename_i hr
      cases hb : catalog.base.read binding.base with
      | none => simp [hb] at h
      | some entry =>
        simp only [hb, Option.map] at h
        cases h
        rw [Context.ofBase_signature, catalog.base.read_signature binding.base entry hb]
        cases binding
        simp_all
    · contradiction

/-- A successful scalar reader returns exactly the requested full binding. -/
theorem readElement_signature (catalog : Catalog registry) (raw : Serialized)
    (result : PackedElement registry) (h : catalog.readElement raw = .ok result) :
    result.context.signature = raw.binding := by
  simp only [readElement] at h
  cases hl : catalog.lookup raw.binding with
  | none => simp [hl] at h
  | some context =>
    simp only [hl] at h
    cases hr : context.codec.decode raw.value with
    | error message => simp [hr] at h
    | ok value =>
      simp only [hr, Except.ok.injEq] at h
      subst result
      exact catalog.lookup_signature _ context hl

theorem readPolynomial_signature (catalog : Catalog registry) (raw : Serialized)
    (result : PackedPolynomial registry) (h : catalog.readPolynomial raw = .ok result) :
    result.context.signature = raw.binding := by
  simp only [readPolynomial] at h
  cases hl : catalog.lookup raw.binding with
  | none => simp [hl] at h
  | some context =>
    simp only [hl] at h
    cases hr : Codec.readPoly context.codec raw.value with
    | error message => simp [hr] at h
    | ok value =>
      simp only [hr, Except.ok.injEq] at h
      subst result
      exact catalog.lookup_signature _ context hl

theorem readElement_missing (catalog : Catalog registry) (raw : Serialized)
    (h : catalog.lookup raw.binding = none) :
    catalog.readElement raw = .error "unknown context" := by simp [readElement, h]

theorem readPolynomial_missing (catalog : Catalog registry) (raw : Serialized)
    (h : catalog.lookup raw.binding = none) :
    catalog.readPolynomial raw = .error "unknown context" := by simp [readPolynomial, h]

theorem lookup_insert (catalog : Catalog registry) (entry : Context registry)
    (h : catalog.lookup entry.signature = none) :
    (catalog.insert entry).bind (fun next => next.lookup entry.signature) = some entry := by
  simp only [insert, h, Option.bind]
  simp [lookup, find]

theorem insert_existing (catalog : Catalog registry) (entry found : Context registry)
    (h : catalog.lookup entry.signature = some found) : catalog.insert entry = none := by
  simp [insert, h]

theorem lookup_insert_other (catalog : Catalog registry) (entry : Context registry)
    (binding : Signature) (h : catalog.lookup entry.signature = none)
    (hne : entry.signature ≠ binding) :
    (catalog.insert entry).bind (fun next => next.lookup binding) = catalog.lookup binding := by
  simp only [insert, h, Option.bind]
  simp [lookup, find, hne]

theorem read_write (catalog : Catalog registry) (context : Context registry) (a : context.Value)
    (h : catalog.lookup context.signature = some context) :
    catalog.readElement (context.write a) = .ok ⟨context, a⟩ := by
  simp [readElement, Context.write, h, context.codec_lawful a]

theorem readPolynomial_write (catalog : Catalog registry) (context : Context registry)
    (p : context.Poly) (h : catalog.lookup context.signature = some context) :
    catalog.readPolynomial (context.writePoly p) = .ok ⟨context, p⟩ := by
  simp [readPolynomial, Context.writePoly, h,
    Codec.read_poly context.codec context.codec_lawful p]

end Catalog
end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Catalog.read_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Catalog.read_write
