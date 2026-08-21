/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Fact

@[expose] public section

/-!
# Function-agnostic action contracts

This module defines stable identities, scoped registrations, immutable actions,
and exact package-request projections. It contains no package callback,
outcome, proposal, scheduler, search policy, real semantics, or theorem
evidence.

Compact identifiers are meaningful only in the exact validated snapshot named
by an action. Stable operation and rule keys carry explicit compatibility
epochs. Passing these structural checks authorizes neither state mutation nor
theorem evidence.
-/

namespace Hex.Interval

/-- Stable rule name and compatibility epoch. Payload schema versions remain
separate recipe variants within this exact rule epoch. -/
structure RuleKey where
  name : String
  schema : Nat := 1
  deriving DecidableEq, Repr

/-- Compact index into one registry snapshot. -/
structure RuleId where
  index : Nat
  deriving DecidableEq, Repr

/-- Compact index of a rule application in one controller snapshot. -/
structure ApplicationId where
  index : Nat
  deriving DecidableEq, Repr

/-- Compact index of one admitted structural equality. -/
structure EqualityId where
  index : Nat
  deriving DecidableEq, Repr

/-- Stable structural evidence inspected by a matcher. -/
inductive StructuralKey where
  | node (node : NodeId)
  | equality (equality : EqualityId)
  | application (application : ApplicationId)
  deriving DecidableEq, Repr

/-- One controller-enumerated structural input with its immutable creation
generation. -/
structure StructuralInput where
  key : StructuralKey
  generation : Nat
  deriving DecidableEq, Repr

/-- Rule roles are controller policy data, not operation semantics. -/
inductive ActionKind where
  | forward
  | backward
  | improve
  | shave
  | instantiate
  | rewrite
  | regularize
  | split
  deriving DecidableEq, Repr

/-- A registration names its result or an argument without depending on
snapshot-local node identifiers. -/
inductive Slot where
  | result
  | argument (index : Nat)
  deriving DecidableEq, Repr

/-- How a registration is bound to a validated program. -/
inductive BindingKind where
  | local
  | scoped
  | global
  deriving DecidableEq, Repr

/-- Structural enumeration requested by one registration. The supported
contract currently exposes the reference whole-network watch only; alternate
matcher indexes remain controller implementation choices. -/
inductive MatchWatch where
  | none
  | network
  deriving DecidableEq, Repr

/-- One explicit propagator registration. The callback and all proof recipes
remain outside this structural record. -/
structure Registration where
  key : RuleKey
  head : OpKey
  kind : ActionKind
  watches : List Slot
  writes : List Slot
  binding : BindingKind := .local
  watchesProgram : Bool := false
  matchWatch : MatchWatch := .none
  initialEffort : Nat := 0
  deriving Repr

namespace Registration

/-- Exact equality of immutable registration metadata. -/
def same (left right : Registration) : Bool :=
  left.key == right.key && left.head == right.head && left.kind == right.kind &&
    left.watches == right.watches && left.writes == right.writes &&
      left.binding == right.binding && left.watchesProgram == right.watchesProgram &&
        left.matchWatch == right.matchWatch && left.initialEffort == right.initialEffort

/-- Resolve a stable rule key in one exact registry snapshot. -/
def find? (rules : Array Registration) (key : RuleKey) :
    Option (RuleId × Registration) := do
  for index in [0:rules.size] do
    let rule <- rules[index]?
    if rule.key == key then return ({ index }, rule)
  none

end Registration

/-- Whether a finite ordered contract projection contains no duplicate item. -/
def allDistinct [DecidableEq α] : List α → Bool
  | [] => true
  | item :: items => !(items.contains item) && allDistinct items

namespace Slot

/-- Whether this result/argument slot belongs to the exact operation
signature named by a registration. -/
def validFor (operation : Operation) : Slot → Bool
  | .result => true
  | .argument index => operation.inputs[index]?.isSome

/-- Resolve a checked local slot at one concrete instruction. -/
def resolve? (output : NodeId) (node : Node) : Slot → Option NodeId
  | .result => some output
  | .argument index => node.args[index]?

/-- Resolve an ordered local slot projection. -/
def resolveAll? (output : NodeId) (node : Node)
    (slots : List Slot) : Option (List NodeId) :=
  slots.mapM (resolve? output node)

end Slot

namespace Registration

/-- Validate a complete registration snapshot against a checked program.
Keys are unique, heads exist with exact stable versions, local slots are
unique and in range, and global matcher registrations have the one supported
network-watch shape. -/
def check (program : Program) (rules : Array Registration) : Bool :=
  allDistinct (rules.toList.map (·.key)) && rules.all fun rule =>
    match program.operationWithKey? rule.head with
    | none => false
    | some operation =>
        let matchValid :=
          match rule.matchWatch with
          | .none => rule.binding != .global
          | .network =>
              rule.binding == .global && rule.kind == .instantiate &&
                rule.watchesProgram && rule.watches.isEmpty && rule.writes.isEmpty
        matchValid && match rule.binding with
          | .local =>
              allDistinct rule.watches && allDistinct rule.writes &&
                rule.watches.all (Slot.validFor operation) &&
                  rule.writes.all (Slot.validFor operation)
          | .scoped => rule.watches.isEmpty && rule.writes.isEmpty
          | .global => rule.watches.isEmpty && rule.writes.isEmpty

end Registration

/-- One concrete scoped registration application. Exact ordered watches and
writes are part of its identity and later action authority. -/
structure ScopeBinding where
  rule : RuleKey
  anchor : NodeId
  watches : List NodeId
  writes : List NodeId
  deriving DecidableEq, Repr

namespace ScopeBinding

/-- Exact identity of one ordered scope binding. -/
def same (left right : ScopeBinding) : Bool :=
  left.rule == right.rule && left.anchor == right.anchor &&
    left.watches == right.watches && left.writes == right.writes

/-- Every node named by the binding, retaining watcher/write order. -/
def nodes (binding : ScopeBinding) : List NodeId :=
  binding.anchor :: binding.watches ++ binding.writes

/-- Validate one explicit scope against the exact checked program and
registration snapshot. Package code remains responsible for its semantic
shape. -/
def check (program : Program) (rules : Array Registration)
    (binding : ScopeBinding) : Bool :=
  match Registration.find? rules binding.rule, program.node? binding.anchor with
  | some (_, rule), some anchor =>
      rule.binding == .scoped &&
        (program.operation? anchor.op).any (fun operation => operation.key == rule.head) &&
        allDistinct binding.watches && allDistinct binding.writes &&
        binding.watches.all (fun node => (program.node? node).isSome) &&
        binding.writes.all (fun node => (program.node? node).isSome)
  | _, _ => false

/-- Validate a complete, duplicate-free explicit scope snapshot. -/
def checkAll (program : Program) (rules : Array Registration)
    (bindings : Array ScopeBinding) : Bool :=
  allDistinct bindings.toList && bindings.all (check program rules)

end ScopeBinding

/-- One scheduler request. Serial and program version prevent a delayed reply
from being confused with another invocation; `writes` is exact authority. -/
structure Action where
  serial : Nat
  programVersion : Nat
  application : ApplicationId
  rule : RuleId
  key : RuleKey
  node : NodeId
  kind : ActionKind
  effort : Nat
  generation : Nat := 0
  inputs : List SeenVersion
  writes : List NodeId := []
  structuralInputs : List StructuralInput := []
  matcherEpoch : Option Nat := none
  deriving DecidableEq, Repr

/-- Immutable decoded structural snapshot supplied with an action. Consumers
validate it with `ProgramView.check`; it grants no mutation or proof
authority. -/
structure ProgramView where
  programVersion : Nat
  operations : Array Operation
  nodes : Array Node
  generations : Array Nat
  depths : Array Nat

namespace ProgramView

def operation? (view : ProgramView) (operation : OpId) : Option Operation :=
  view.operations[operation.index]?

/-- Resolve a stable key to its snapshot-local identifier and exact signature. -/
def findOp? (view : ProgramView) (key : OpKey) : Option (OpId × Operation) := do
  for index in [0:view.operations.size] do
    let operation <- view.operations[index]?
    if operation.key == key then return ({ index }, operation)
  none

def node? (view : ProgramView) (node : NodeId) : Option Node :=
  view.nodes[node.index]?

def generation? (view : ProgramView) (node : NodeId) : Option Nat :=
  view.generations[node.index]?

def depth? (view : ProgramView) (node : NodeId) : Option Nat :=
  view.depths[node.index]?

def operationKey? (view : ProgramView) (node : NodeId) : Option OpKey := do
  let instruction <- view.node? node
  let operation <- view.operation? instruction.op
  pure operation.key

/-- Validate the decoded program plus the exact generation/depth side tables.
This does not authenticate `programVersion`; the controller owns that
snapshot identity. -/
def check (view : ProgramView) : Bool :=
  let program : Program := { operations := view.operations, nodes := view.nodes }
  program.check && view.generations.size == view.nodes.size &&
    program.depths? == some view.depths

end ProgramView

/-- Function-package request with exactly the action's declared fact inputs
and immutable structural snapshot. -/
structure RuleRequest (Fact : Type) where
  action : Action
  program : ProgramView
  inputs : List (FactView Fact)
  writes : List NodeId

namespace RuleRequest

/-- Lookup is restricted to declared inputs. -/
def fact? (request : RuleRequest Fact) (node : NodeId) : Option Fact :=
  (request.inputs.find? fun input => input.node == node).map (fun input => input.fact)

/-- Check that a request is the exact structural projection declared by a
registration. This validates keys, versions, ordered reads/writes, and the
immutable program view. The controller must separately authenticate compact
rule/application identifiers, serials, fact values, and pending ownership. -/
def accepts (registration : Registration) (request : RuleRequest Fact) : Bool :=
  if !request.program.check ||
      request.program.programVersion != request.action.programVersion then
    false
  else
    match request.program.node? request.action.node with
    | none => false
    | some anchor =>
        let inputNodes := request.inputs.map (fun input => input.node)
        let seen := request.inputs.map fun input =>
          { node := input.node, version := input.version : SeenVersion }
        let common := registration.key == request.action.key &&
          registration.kind == request.action.kind &&
          request.program.operationKey? request.action.node == some registration.head &&
          request.action.inputs == seen && request.action.writes == request.writes &&
          match registration.matchWatch with
          | .none =>
              request.action.structuralInputs.isEmpty && request.action.matcherEpoch.isNone
          | .network =>
              !request.action.structuralInputs.isEmpty && request.action.matcherEpoch.isSome
        common && match registration.binding with
          | .local =>
              Slot.resolveAll? request.action.node anchor registration.watches ==
                  some inputNodes &&
                Slot.resolveAll? request.action.node anchor registration.writes ==
                  some request.writes
          | .scoped =>
              registration.watches.isEmpty && registration.writes.isEmpty &&
                allDistinct inputNodes && allDistinct request.writes &&
                inputNodes.all (fun node => (request.program.node? node).isSome) &&
                request.writes.all (fun node => (request.program.node? node).isSome)
          | .global =>
              registration.watches.isEmpty && registration.writes.isEmpty &&
                inputNodes.isEmpty && request.writes.isEmpty

end RuleRequest

end Hex.Interval
