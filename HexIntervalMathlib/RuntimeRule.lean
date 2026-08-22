/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.RuntimeProof
public import HexIntervalMathlib.Rule

@[expose] public section

/-!
# Executable built-in arithmetic rules

This module owns the executable half of `Rule`'s arithmetic package. Each
handler recomputes one checked public interval operation from its exact
`RuleRequest`, returns one typed `Runtime.fact` event, and declares the same
one-cell replay format as the corresponding theorem schema. `buildWithWithin`
then seals bidirectional executable/proof coverage through
`RuntimeProof.Registry.buildWithin`.

The built-in handlers schedule only version-zero result nodes whose current
fact is `Interval.whole`. This is the state produced for computed nodes by the
supported frontend. It makes the callback's installed fact exactly its
proposal without exposing the previous branch fact to the callback. The
runtime predecessor check rejects a direct repeated invocation. A refused
checked arithmetic operation returns an empty batch, which the sealed runtime
rejects transactionally; callback failure never becomes theorem evidence.

Additional opaque operations remain caller-owned. `buildWithWithin` accepts
paired executable and proof packages for the configured `extraMeanings`, then
checks exact registration and format/schema coverage across the complete
registry. No raw assembly or proof-registry splice is exposed by the combined
builder.
-/

namespace Hex.Interval.Rule.Runtime

open Hex.Interval.Executable

/-- Inert package-owned provenance retained in the fact history. RuntimeProof
derives scope, schema, and body from the sealed tree and executable quote, not
from this value. -/
structure Cause where
  rule : RuleKey
  body : List Nat
  deriving DecidableEq, Repr

/-- The private executable cache records committed callback count. Its logical
measure makes retained callback history independently resource-bounded. -/
structure Cache where
  calls : Nat := 0
  deriving DecidableEq, Repr

abbrev Assembly := RuntimeProof.Assembly Hex.Interval Cause

abbrev Registry (config : Rule.Config) (Plan : Type := List Nat) :=
  RuntimeProof.Registry Hex.Interval (Rule.semantics config) Cause Plan

inductive Error where
  | executable (error : Executable.Error)
  | proof (error : Rule.BuildError)
  | registry (error : RuntimeProof.Error)
  deriving Repr

private def buildValue? : BuildResult → Option Hex.Interval := Rule.ready?

private def arithmeticValue? : Arithmetic.Result → Option Hex.Interval :=
  Rule.arithmeticReady?

private def proposal? (config : Rule.Config) (rule : RuleKey)
    (inputs : List (FactView Hex.Interval)) : Option Hex.Interval :=
  match rule, inputs with
  | key, [] =>
      if key == Rule.constantKey then
        buildValue? (singletonWithin config.endpoint config.constant)
      else none
  | key, [input] =>
      if key == Rule.negKey then
        buildValue? (negWithin config.endpoint input.fact)
      else if key == Rule.powKey then
        arithmeticValue? (powWithin config.endpoint config.powerWork input.fact config.exponent)
      else if key == Rule.absKey then
        buildValue? (absWithin config.endpoint input.fact)
      else if key == Rule.invKey then
        arithmeticValue? (invWithin config.precisionLimits config.precision input.fact)
      else if key == Rule.regularizeKey then
        arithmeticValue?
          (regularizeWithin config.precisionLimits config.precision input.fact)
      else none
  | key, [left, right] =>
      if key == Rule.addKey then
        buildValue? (addWithin config.endpoint left.fact right.fact)
      else if key == Rule.subKey then
        buildValue? (subWithin config.endpoint left.fact right.fact)
      else if key == Rule.mulKey then
        arithmeticValue? (mulWithin config.endpoint left.fact right.fact)
      else if key == Rule.minKey then
        buildValue? (minWithin config.endpoint left.fact right.fact)
      else if key == Rule.maxKey then
        buildValue? (maxWithin config.endpoint left.fact right.fact)
      else if key == Rule.divKey then
        arithmeticValue?
          (divWithin config.precisionLimits config.precision left.fact right.fact)
      else none
  | _, _ => none

private def quote (tag : Nat) : Executable.Quote :=
  { role := .fact, schema := 1, body := [tag] }

private def batch? (config : Rule.Config) (rule : RuleKey) (tag : Nat)
    (request : RuleRequest Hex.Interval) : Option (Runtime.Batch Hex.Interval Cause) := do
  let proposed ← proposal? config rule request.inputs
  let output ← request.writes.getLast?
  if request.writes != [output] || output != request.action.node then none
  let replay := quote tag
  pure
    { events := #[.fact
        { action := request.action
          update :=
            { programVersion := request.action.programVersion
              node := output
              previous := { node := output, version := 0 }
              fact := proposed
              version := 1
              cause := { rule, body := replay.body } }
          proposed
          quote := replay }] }

private def offered (config : Rule.Config) (rule : RuleKey) (tag : Nat)
    (snapshot : Snapshot Hex.Interval) (request : RuleRequest Hex.Interval) : Bool :=
  !snapshot.contradictory &&
    snapshot.version? request.action.node == some 0 &&
    snapshot.fact? request.action.node == some Hex.Interval.whole &&
    (batch? config rule tag request).isSome

private def format (tag : Nat) : ReplayFormat :=
  { role := .fact, schema := 1, validateBody := fun body => body == [tag] }

private def handler (config : Rule.Config) (registration : Registration) (tag : Nat) :
    Handler Hex.Interval (Runtime.Batch Hex.Interval Cause) Cache :=
  { registration
    offers := offered config registration.key tag
    invoke := fun cache request =>
      match batch? config registration.key tag request with
      | none => ({ result := { events := #[] } }, cache)
      | some batch =>
          ({ result := batch, quotes := #[quote tag] }, { calls := cache.calls + 1 })
    formats := #[format tag] }

/-- Executable arithmetic package in exactly the public registration order.
Source nodes have no handler: their version-zero facts remain caller-owned. -/
opaque package (config : Rule.Config) :
    Executable.Package Hex.Interval (Runtime.Batch Hex.Interval Cause) :=
  { Cache := Cache
    cache := {}
    operations := Rule.operations
    handlers :=
      #[handler config (Rule.unaryRegistration Rule.negKey Rule.negOp) 1,
        handler config (Rule.binaryRegistration Rule.addKey Rule.addOp) 2,
        handler config (Rule.binaryRegistration Rule.subKey Rule.subOp) 3,
        handler config (Rule.binaryRegistration Rule.mulKey Rule.mulOp) 4,
        handler config (Rule.unaryRegistration Rule.powKey Rule.powOp) 5,
        handler config (Rule.unaryRegistration Rule.absKey Rule.absOp) 6,
        handler config (Rule.binaryRegistration Rule.minKey Rule.minOp) 7,
        handler config (Rule.binaryRegistration Rule.maxKey Rule.maxOp) 8,
        handler config
          { key := Rule.constantKey, head := Rule.constantOp.key, kind := .forward,
            watches := [], writes := [.result] } 9,
        handler config (Rule.unaryRegistration Rule.invKey Rule.invOp) 10,
        handler config (Rule.binaryRegistration Rule.divKey Rule.divOp) 11,
        handler config (Rule.unaryRegistration Rule.regularizeKey Rule.regularizeOp) 12]
    measure :=
      { metadata := { bytes := 12, work := 12 }
        application := fun _ => { bytes := 1, work := 1 }
        cache := fun cache => { bytes := cache.calls, work := cache.calls }
        result := fun batch => { bytes := batch.events.size, work := batch.events.size } } }

/-- Assemble the exact executable arithmetic package together with paired
caller-owned packages for configured opaque operations. -/
def assemblyWithWithin (limits : Executable.Limits) (config : Rule.Config)
    (program : Program)
    (extra : Array (Executable.Package Hex.Interval
      (Runtime.Batch Hex.Interval Cause))) : Except Error Assembly :=
  Executable.buildWithin limits (#[package config] ++ extra) program
    |>.mapError Error.executable

/-- Convenience executable assembly for the built-in arithmetic registry. -/
def assemblyWithin (limits : Executable.Limits) (config : Rule.Config)
    (program : Program) : Except Error Assembly :=
  assemblyWithWithin limits config program #[]

/-- Build and seal exact executable-format/theorem-schema ownership for the
built-in arithmetic rules and paired caller-owned opaque-operation packages. -/
def buildWithWithin (executableLimits : Executable.Limits)
    (proofLimits : Proof.Limits) (key : RuntimeProof.Key) (config : Rule.Config)
    (program : Program)
    (extraExecutable : Array (Executable.Package Hex.Interval
      (Runtime.Batch Hex.Interval Cause)))
    (extraProof : Array (Proof.Package (Rule.semantics config))) :
    Except Error (Registry config) := do
  let assembly ← assemblyWithWithin executableLimits config program extraExecutable
  let proof ← Rule.buildWithWithin proofLimits config program extraProof
    |>.mapError Error.proof
  RuntimeProof.Registry.buildWithin executableLimits key assembly proof
    |>.mapError Error.registry

/-- Convenience sealed registry for the built-in arithmetic package. -/
def buildWithin (executableLimits : Executable.Limits)
    (proofLimits : Proof.Limits) (key : RuntimeProof.Key) (config : Rule.Config)
    (program : Program) : Except Error (Registry config) :=
  buildWithWithin executableLimits proofLimits key config program #[] #[]

end Hex.Interval.Rule.Runtime
