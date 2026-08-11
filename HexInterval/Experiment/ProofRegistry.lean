/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.ProofEmitter

@[expose] public section

/-!
# Joint semantic and proof-emitter package assembly

An executable propagator package, its semantic replay schemas, and its tactic
emission handles are three views of one extension point.  This module keeps
the latter two views in one descriptor and checks them against the executable
registry in the same package order.

The full replay key includes the rule, event role, and payload schema.  Joint
assembly requires exact package-local equality of those keys: an emitter may
neither omit a semantic schema nor borrow one from another package.  The
frontend therefore remains function-agnostic without maintaining a second,
potentially divergent registry by hand.
-/

namespace Hex.Interval.Experiment.ProofRegistry

open Propagator PayloadArena SemanticReplay ProofEmitter

/-- The proof-facing declarations contributed by one executable package.

`semantic` contains the package-owned checkers and the corresponding `emit`
fragment contains exactly the handles a tactic may use to apply them. -/
structure Package (semantics : Semantics Fact) (Handle : Type) where
  semantic : SemanticReplay.Package semantics
  emit : EmitPackage Handle

/-- A semantic registry and emitter table assembled from the same packages. -/
structure Registry (semantics : Semantics Fact) (Handle : Type) where
  semantic : SemanticReplay.Registry semantics
  emit : SchemaTable Handle

/-- Failures specific to joint proof-package assembly.

Semantic failures retain the executable/semantic registry diagnostic.  The
remaining cases say which package failed exact emitter coverage. -/
inductive BuildError where
  | semantic (error : SemanticReplay.BuildError)
  | duplicateEmit (key : ReplayKey)
  | missingEmit (package : Nat) (key : ReplayKey)
  | extraEmit (package : Nat) (key : ReplayKey)
  | invalidEmit
  deriving DecidableEq, Repr

namespace Package

/-- Exact semantic replay addresses owned by this package. -/
def semanticKeys (package : Package semantics Handle) : List ReplayKey :=
  package.semantic.factSchemas.toList.map PackedFactSchema.key ++
    package.semantic.instanceSchemas.toList.map PackedInstanceSchema.key ++
      package.semantic.equalitySchemas.toList.map PackedEqualitySchema.key

/-- Exact tactic-emission addresses claimed by this package. -/
def emitKeys (package : Package semantics Handle) : List ReplayKey :=
  package.emit.schemas.map (fun schema => schema.key)

end Package

def firstDuplicate (seen : List ReplayKey) :
    List (SchemaRef Handle) -> Option ReplayKey
  | [] => none
  | schema :: rest =>
      if seen.contains schema.key then some schema.key
      else firstDuplicate (schema.key :: seen) rest

def checkMissing (package : Nat) (emit : List ReplayKey) :
    List ReplayKey -> Except BuildError Unit
  | [] => pure ()
  | key :: rest =>
      if emit.contains key then checkMissing package emit rest
      else throw (.missingEmit package key)

def checkExtra (package : Nat) (semantic : List ReplayKey) :
    List ReplayKey -> Except BuildError Unit
  | [] => pure ()
  | key :: rest =>
      if semantic.contains key then checkExtra package semantic rest
      else throw (.extraEmit package key)

def checkPackages (index : Nat) :
    List (Package semantics Handle) -> Except BuildError Unit
  | [] => pure ()
  | package :: rest => do
      let semantic := package.semanticKeys
      let emit := package.emitKeys
      checkMissing index emit semantic
      checkExtra index semantic emit
      checkPackages (index + 1) rest

/-- Build the semantic checker and tactic schema table from one package list.

The existing semantic builder first checks exact executable ownership and
coverage.  This layer additionally checks exact package-local correspondence
between semantic schemas and emitter handles, plus global emitter uniqueness.
The resulting table is selection data only: emitted theorem applications are
still checked by Lean and by the transparent replay transitions. -/
def build (executable : Propagator.Registry Fact)
    (packages : Array (Package semantics Handle)) :
    Except BuildError (Registry semantics Handle) := do
  let semanticPackages := packages.map (fun package => package.semantic)
  let semantic ←
    match SemanticReplay.Registry.build executable semanticPackages with
    | .ok registry => pure registry
    | .error error => throw (BuildError.semantic error)
  let emitPackages := packages.toList.map (fun package => package.emit)
  let entries := emitPackages.flatMap (fun package => package.schemas)
  if let some key := firstDuplicate [] entries then
    throw (BuildError.duplicateEmit key)
  match checkPackages 0 packages.toList with
  | .error error => throw error
  | .ok _ =>
      match SchemaTable.build emitPackages with
      | none => throw BuildError.invalidEmit
      | some emit => pure { semantic, emit }

end Hex.Interval.Experiment.ProofRegistry
