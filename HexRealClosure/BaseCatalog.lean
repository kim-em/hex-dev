/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BasePolynomial

public section

namespace Hex.RealClosure.BaseContext

/-- An existing real prefix, including the progress proofs already supplied
when its providers were registered. Packing does not construct a new field. -/
inductive RealPrefix (registry : Registry) : Type 1
  | pack {K : Type} [Lean.Grind.Field K] [DecidableEq K]
      {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
      (context : RealContext registry K approx sign)

/-- An existing staged base context with its native carrier hidden. -/
inductive PackedContext (registry : Registry) : Type 1
  | pack {K : Type} [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
      (context : Context registry K sign)

namespace RealPrefix

@[expose] def keys {registry : Registry} (entry : RealPrefix registry) : List ConstantKey := by
  cases entry with
  | pack context => exact context.keys

@[expose] def finish {registry : Registry} (entry : RealPrefix registry) : PackedContext registry := by
  cases entry with
  | pack context => exact .pack (.real context)

theorem keys_rational (registry : Registry) :
    (pack (.rational registry)).keys = [] := RealContext.keys_rational registry

end RealPrefix

namespace PackedContext

@[expose] def signature {registry : Registry} (entry : PackedContext registry) : Signature := by
  cases entry with
  | pack context => exact context.signature

@[expose] def infinitesimal {registry : Registry} (entry : PackedContext registry) : PackedContext registry := by
  cases entry with
  | pack context => exact .pack context.infinitesimal

/-- Reconstruct finitely many infinitesimal stages using the native constructor. -/
@[expose] def extend {registry : Registry} (context : PackedContext registry) :
    Nat → PackedContext registry
  | 0 => context
  | n + 1 => (context.extend n).infinitesimal

theorem infinitesimal_signature {registry : Registry} (context : PackedContext registry) :
    context.infinitesimal.signature =
      { context.signature with infinitesimals := context.signature.infinitesimals + 1 } := by
  cases context with
  | pack context => exact Context.signature_infinitesimal context

theorem extend_signature {registry : Registry} (context : PackedContext registry) (n : Nat) :
    (context.extend n).signature =
      { context.signature with infinitesimals := context.signature.infinitesimals + n } := by
  induction n with
  | zero => simp [extend]
  | succ n ih => simp [extend, infinitesimal_signature, ih, Nat.add_assoc]

@[expose] def Value {registry : Registry} (entry : PackedContext registry) : Type := by
  cases entry with
  | pack context => exact Element context

@[expose] def write {registry : Registry} (context : PackedContext registry) :
    context.Value → Syntax := by
  cases context with
  | pack context => exact fun a => context.write a.stored

@[expose] def read {registry : Registry} (context : PackedContext registry) :
    Syntax → Option context.Value := by
  cases context with
  | pack context => exact fun raw => (context.read raw).map Element.mk

@[expose] def sign {registry : Registry} (context : PackedContext registry) :
    context.Value → Int := by
  cases context with
  | pack context => exact Element.sign

theorem read_write {registry : Registry} (context : PackedContext registry)
    (a : context.Value) : context.read (context.write a) = some a := by
  cases context with
  | pack context =>
    simp only [read, write, Context.read_write]
    rfl

@[expose] def Poly {registry : Registry} (entry : PackedContext registry) : Type := by
  cases entry with
  | pack context => exact Polynomial context

@[expose] def writePoly {registry : Registry} (context : PackedContext registry) :
    context.Poly → Polynomial.Serialized := by
  cases context with
  | pack context => exact Polynomial.write

@[expose] def readPoly {registry : Registry} (context : PackedContext registry) :
    Polynomial.Serialized → Option context.Poly := by
  cases context with
  | pack context => exact Polynomial.read context

theorem writePoly_binding {registry : Registry} (context : PackedContext registry)
    (p : context.Poly) : (context.writePoly p).binding = context.signature := by
  cases context
  rfl

theorem readPoly_write {registry : Registry} (context : PackedContext registry)
    (p : context.Poly) : context.readPoly (context.writePoly p) = some p := by
  cases context with
  | pack context => exact Polynomial.read_write p

end PackedContext

theorem RealPrefix.finish_signature {registry : Registry} (entry : RealPrefix registry) :
    entry.finish.signature = ⟨entry.keys, 0⟩ := by
  cases entry with
  | pack context => exact Context.signature_real context

/-- A reconstructed value retains the entire context returned by the reader. -/
structure PackedElement (registry : Registry) : Type 1 where
  context : PackedContext registry
  value : context.Value

@[expose] def PackedElement.write {registry : Registry} (a : PackedElement registry) :
    Serialized := ⟨a.context.signature, a.context.write a.value⟩

@[expose] def PackedElement.sign {registry : Registry} (a : PackedElement registry) : Int :=
  a.context.sign a.value

/-- A polynomial whose coefficients belong to the reconstructed context. -/
structure PackedPolynomial (registry : Registry) : Type 1 where
  context : PackedContext registry
  value : context.Poly

@[expose] def PackedPolynomial.write {registry : Registry} (p : PackedPolynomial registry) :
    Polynomial.Serialized := p.context.writePoly p.value

/-- Immutable catalog of caller-constructed real prefixes. Insertion rejects
an already installed path; the rational prefix is always available. -/
structure Catalog (registry : Registry) : Type 1 where
  private mk ::
  private entries : List (RealPrefix registry)

namespace Catalog

def empty (registry : Registry) : Catalog registry := ⟨[]⟩

private def findPrefix {registry : Registry} (keys : List ConstantKey) :
    List (RealPrefix registry) → Option (RealPrefix registry)
  | [] => none
  | entry :: rest => if entry.keys = keys then some entry else findPrefix keys rest

/-- Resolve the complete predecessor path in one fixed immutable registry. -/
def lookup {registry : Registry} (catalog : Catalog registry)
    (keys : List ConstantKey) : Option (RealPrefix registry) :=
  if keys = [] then some (.pack (.rational registry)) else findPrefix keys catalog.entries

/-- Install an existing prefix without rebinding another entry. Its native
constructor has already stored progress for every exact predecessor. -/
def insert {registry : Registry} (catalog : Catalog registry)
    (entry : RealPrefix registry) : Option (Catalog registry) :=
  match catalog.lookup entry.keys with
  | none => some ⟨entry :: catalog.entries⟩
  | some _ => none

/-- Resolve the real prefix, then reconstruct the declared infinitesimal order.
No convergence or relative-transcendence proposition is decided by this reader. -/
@[expose] def read {registry : Registry} (catalog : Catalog registry) (raw : Signature) :
    Option (PackedContext registry) := do
  let entry ← catalog.lookup raw.constants
  return entry.finish.extend raw.infinitesimals

/-- Read the full context before checking recursive scalar data. -/
@[expose] def readElement {registry : Registry} (catalog : Catalog registry)
    (raw : Serialized) : Option (PackedElement registry) := do
  let context ← catalog.read raw.binding
  match context.read raw.value with
  | none => none
  | some value => some ⟨context, value⟩

/-- Resolve the complete context before invoking its checked polynomial reader. -/
@[expose] def readPolynomial {registry : Registry} (catalog : Catalog registry)
    (raw : Polynomial.Serialized) : Option (PackedPolynomial registry) := do
  let context ← catalog.read raw.binding
  match context.readPoly raw with
  | none => none
  | some value => some ⟨context, value⟩

private theorem findPrefix_keys {registry : Registry} (keys : List ConstantKey)
    (entries : List (RealPrefix registry)) (entry : RealPrefix registry)
    (h : findPrefix keys entries = some entry) : entry.keys = keys := by
  induction entries with
  | nil => simp [findPrefix] at h
  | cons first rest ih =>
    simp only [findPrefix] at h
    split at h
    · cases h; assumption
    · exact ih h

theorem lookup_keys {registry : Registry} (catalog : Catalog registry)
    (keys : List ConstantKey) (entry : RealPrefix registry)
    (h : catalog.lookup keys = some entry) : entry.keys = keys := by
  simp only [lookup] at h
  split at h
  · cases h
    simpa [RealPrefix.keys, RealContext.keys, RealContext.keys_rational] using ‹keys = []›.symm
  · exact findPrefix_keys keys catalog.entries entry h

theorem lookup_rational {registry : Registry} (catalog : Catalog registry) :
    catalog.lookup [] = some (.pack (.rational registry)) := by simp [lookup]

theorem lookup_empty (registry : Registry) (keys : List ConstantKey) (h : keys ≠ []) :
    (empty registry).lookup keys = none := by simp [lookup, empty, h, findPrefix]

/-- A successful insertion returns the exact installed prefix, not an entry
identified by a shortened name or a hash. -/
theorem lookup_insert {registry : Registry} (catalog : Catalog registry)
    (entry : RealPrefix registry) (h : catalog.lookup entry.keys = none) :
    (catalog.insert entry).bind (fun next => next.lookup entry.keys) = some entry := by
  have hk : entry.keys ≠ [] := by
    intro he
    simp [lookup, he] at h
  simp only [insert, h, Option.bind]
  simp [lookup, hk, findPrefix]

theorem insert_existing {registry : Registry} (catalog : Catalog registry)
    (entry found : RealPrefix registry) (h : catalog.lookup entry.keys = some found) :
    catalog.insert entry = none := by simp [insert, h]

/-- Inserting another path preserves every previously installed lookup. -/
theorem lookup_insert_other {registry : Registry} (catalog : Catalog registry)
    (entry : RealPrefix registry) (keys : List ConstantKey)
    (h : catalog.lookup entry.keys = none) (hne : entry.keys ≠ keys) :
    (catalog.insert entry).bind (fun next => next.lookup keys) = catalog.lookup keys := by
  simp only [insert, h, Option.bind]
  simp [lookup, findPrefix, hne]

/-- Reconstruction reuses the exact registered prefix and native stages. -/
theorem read_prefix {registry : Registry} (catalog : Catalog registry)
    (entry : RealPrefix registry) (n : Nat) (h : catalog.lookup entry.keys = some entry) :
    catalog.read ⟨entry.keys, n⟩ = some (entry.finish.extend n) := by
  simp [read, h]

theorem read_extend {registry : Registry} (catalog : Catalog registry)
    (entry : RealPrefix registry) (n : Nat) (h : catalog.lookup entry.keys = some entry) :
    catalog.read (entry.finish.extend n).signature = some (entry.finish.extend n) := by
  rw [PackedContext.extend_signature, RealPrefix.finish_signature]
  simpa only [Nat.zero_add] using read_prefix catalog entry n h

theorem read_signature {registry : Registry} (catalog : Catalog registry)
    (raw : Signature) (context : PackedContext registry)
    (h : catalog.read raw = some context) : context.signature = raw := by
  simp only [read] at h
  cases he : catalog.lookup raw.constants with
  | none => simp [he] at h
  | some entry =>
    simp only [he, bind, Option.bind, pure, Pure.pure] at h
    cases h
    simp [PackedContext.extend_signature, RealPrefix.finish_signature,
      lookup_keys catalog raw.constants entry he]

theorem read_missing {registry : Registry} (catalog : Catalog registry)
    (raw : Signature) (h : catalog.lookup raw.constants = none) :
    catalog.read raw = none := by simp [read, h]

theorem readElement_missing {registry : Registry} (catalog : Catalog registry)
    (raw : Serialized) (h : catalog.read raw.binding = none) :
    catalog.readElement raw = none := by simp [readElement, h]

theorem readElement_signature {registry : Registry} (catalog : Catalog registry)
    (raw : Serialized) (a : PackedElement registry)
    (h : catalog.readElement raw = some a) : a.context.signature = raw.binding := by
  cases hc : catalog.read raw.binding with
  | none => simp [readElement, hc] at h
  | some context =>
    simp only [readElement, hc, bind, Option.bind] at h
    cases hv : context.read raw.value with
    | none => simp [hv] at h
    | some value =>
      simp only [hv] at h
      cases h
      exact read_signature catalog raw.binding context hc

/-- The same catalog reconstructs the same context before any coefficient is
read. Canonical scalar readers then return the original value. -/
theorem read_write {registry : Registry} (catalog : Catalog registry)
    (a : PackedElement registry)
    (h : catalog.read a.context.signature = some a.context) :
    catalog.readElement a.write = some a := by
  cases a with
  | mk context value =>
    simp only [readElement, PackedElement.write, h, bind, Option.bind,
      PackedContext.read_write]

theorem readPolynomial_write {registry : Registry} (catalog : Catalog registry)
    (p : PackedPolynomial registry)
    (h : catalog.read p.context.signature = some p.context) :
    catalog.readPolynomial p.write = some p := by
  cases p with
  | mk context value =>
    simp only [readPolynomial, PackedPolynomial.write, PackedContext.writePoly_binding,
      h, bind, Option.bind, PackedContext.readPoly_write]

end Catalog
end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.Catalog.read_signature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.Catalog.read_signature
/-- info: 'Hex.RealClosure.BaseContext.Catalog.read_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.Catalog.read_write
/-- info: 'Hex.RealClosure.BaseContext.Catalog.readPolynomial_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Catalog.readPolynomial_write
