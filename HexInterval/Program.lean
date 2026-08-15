/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Basic

@[expose] public section

/-!
# Function-agnostic expression programs

This module is the supported structural boundary between a frontend and an
interval controller. Operations are opaque stable keys; the Mathlib-free
program layer knows only their typed signatures. `Program.check` validates
operation-key uniqueness, exact arities and domains, and strict SSA topology.

`Program` is intentionally plain decoded data. Constructing a value does not
assert that it is valid, and no mathematical evidence follows from it. A
controller must run `Program.check` before building dependency state or
invoking a package. This keeps certificate decoding inspectable without
giving untrusted runtime data proof authority.
-/

namespace Hex.Interval

/-- Compact domain identifier. The controller does not interpret domains. -/
structure DomainId where
  index : Nat
  deriving DecidableEq, Repr

/-- Stable, versioned semantic operation name. Compact operation identifiers
are snapshot-local; this key is the identity retained across snapshots. -/
structure OpKey where
  name : String
  version : Nat := 1
  deriving DecidableEq, Repr

/-- Compact index into one program's operation table. -/
structure OpId where
  index : Nat
  deriving DecidableEq, Repr

/-- Compact index into one program's node table. -/
structure NodeId where
  index : Nat
  deriving DecidableEq, Repr

/-- An opaque operation signature known to the typed frontend. -/
structure Operation where
  key : OpKey
  inputs : List DomainId
  output : DomainId
  deriving DecidableEq, Repr

/-- One instruction in a typed single-assignment expression DAG. -/
structure Node where
  domain : DomainId
  op : OpId
  args : List NodeId
  deriving DecidableEq, Repr

/-- Immutable decoded expression program. Validated consumers require
`Program.check program = true`. -/
structure Program where
  operations : Array Operation
  nodes : Array Node
  deriving DecidableEq, Repr

namespace Program

/-- Exact optional operation lookup. -/
def operation? (program : Program) (operation : OpId) : Option Operation :=
  program.operations[operation.index]?

/-- Exact optional node lookup. -/
def node? (program : Program) (node : NodeId) : Option Node :=
  program.nodes[node.index]?

/-- Resolve a stable operation key in this exact program snapshot. -/
def operationWithKey? (program : Program) (key : OpKey) : Option Operation :=
  program.operations.toList.find? fun operation => operation.key == key

/-- Resolve a stable operation key together with its snapshot-local compact
identifier. -/
def operationEntry? (program : Program) (key : OpKey) : Option (OpId × Operation) := do
  for index in [0:program.operations.size] do
    let operation <- program.operations[index]?
    if operation.key == key then return ({ index }, operation)
  none

def uniqueOpKeys : List Operation -> Bool
  | [] => true
  | operation :: operations =>
      !(operations.any fun other => other.key == operation.key) &&
        uniqueOpKeys operations

def argsCheck (program : Program) (outputIndex : Nat) :
    List NodeId -> List DomainId -> Bool
  | [], [] => true
  | argument :: arguments, domain :: domains =>
      argument.index < outputIndex &&
        (program.node? argument).any (fun node => node.domain == domain) &&
        argsCheck program outputIndex arguments domains
  | _, _ => false

def nodeCheck (program : Program) (outputIndex : Nat) (node : Node) : Bool :=
  match program.operation? node.op with
  | none => false
  | some operation =>
      node.domain == operation.output &&
        argsCheck program outputIndex node.args operation.inputs

def nodesCheckFrom (program : Program) : Nat -> List Node -> Bool
  | _, [] => true
  | outputIndex, node :: nodes =>
      nodeCheck program outputIndex node && nodesCheckFrom program (outputIndex + 1) nodes

/-- Validate operation-key uniqueness, operation references, arities, domains,
and strict SSA topology. In particular, every argument precedes its consumer,
so a checked program is acyclic. -/
def check (program : Program) : Bool :=
  uniqueOpKeys program.operations.toList && nodesCheckFrom program 0 program.nodes.toList

/-- Structural expression depth, with nullary nodes at depth zero. -/
def nodeDepth? (depths : Array Nat) (arguments : List NodeId) : Option Nat := do
  if arguments.isEmpty then
    pure 0
  else
    let mut greatest := 0
    for argument in arguments do
      let depth <- depths[argument.index]?
      greatest := Nat.max greatest depth
    pure (greatest + 1)

/-- Reconstruct the structural depth of every node in a validated SSA
program. This measure is independent of theorem-instantiation generation. -/
def depths? (program : Program) : Option (Array Nat) := do
  let mut depths := #[]
  for index in [0:program.nodes.size] do
    let node <- program.nodes[index]?
    let depth <- nodeDepth? depths node.args
    depths := depths.push depth
  pure depths

end Program
end Hex.Interval
