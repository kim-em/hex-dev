/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Lean
public import HexInterval.Experiment.SemanticReplay

@[expose] public section

/-!
# Extensible goal reification

This experiment derives a typed expression program and checker input from Lean
expressions without a central case split over mathematical functions.  Each
package owns one operation signature and a recognizer for that operation.
Reification tries all packages with the requested output domain, rejects
ambiguous matches, recursively reifies arguments in signature order, and
performs exact-expression common-subexpression elimination.

Fact parsing is a separate adapter.  It maps caller propositions to a term,
domain, and fact.  Unrecognized hypotheses are ignored, while the target must
be recognized exactly.  This division lets interval domains choose their own
open/closed fact language without putting it in the expression-DAG builder.
-/

namespace Hex.Interval.Experiment.GoalFrontend

open Lean Meta
open Propagator SemanticReplay

/-- Deterministic bounds for package discovery and recursive graph building. -/
structure Limits where
  maxPackages : Nat
  maxNodes : Nat
  maxDepth : Nat
  deriving DecidableEq, Repr

/-- One package-owned Lean-syntax view of an opaque engine operation.

Nullary packages represent caller variables or constants.  A recognizer must
return arguments in the exact order declared by `operation.inputs`. -/
structure Package where
  operation : Operation
  recognize : Expr → MetaM (Option (List Expr))

/-- A validated operation/recognizer registry. -/
structure Registry where
  private mk ::
  limits : Limits
  packages : Array Package
  operations : Array Operation

private def makeRegistry (limits : Limits) (packages : Array Package)
    (operations : Array Operation) : Registry :=
  { limits, packages, operations }

namespace Registry

private def uniqueKeys : List Operation → Bool
  | [] => true
  | operation :: rest =>
      !(rest.any fun other => other.key == operation.key) && uniqueKeys rest

/-- Validate finite package assembly before inspecting a goal. -/
opaque build (limits : Limits) (packages : Array Package) :
    Except String Registry := do
  if packages.size > limits.maxPackages then
    throw "too many goal-reification packages"
  let operations := packages.map (fun package => package.operation)
  if !uniqueKeys operations.toList then
    throw "duplicate goal-reification operation key"
  pure (makeRegistry limits packages operations)

end Registry

/-- One exact Lean expression already assigned to a graph node and domain. -/
structure TermRef where
  expression : Expr
  domain : DomainId
  node : NodeId

/-- Mutable-by-return graph construction state. -/
structure State where
  nodes : Array Node := #[]
  terms : Array TermRef := #[]

/-- A proposition parsed into one fact about one Lean term. -/
structure Claim (Fact : Type) where
  expression : Expr
  domain : DomainId
  fact : Fact

/-- Domain-specific recognition of hypotheses and the requested target. -/
structure Parser (Fact : Type) where
  parse : Expr → MetaM (Option (Claim Fact))

/-- One caller proposition contributing to a version-zero meet. -/
structure Assumption (Fact : Type) where
  fact : Fact
  proof : Expr

/-- Complete provenance for one caller-owned version-zero fact.

The empty list denotes domain top.  Each later entry must be combined in order
through the fact-domain meet theorem, so several hypotheses about the same
expression cannot overwrite one another's proof dependency. -/
structure Seed (Fact : Type) where
  assumptions : List (Assumption Fact) := []

/-- Exact frontend result, including the syntax-to-node map needed to connect
kernel expressions to the opaque program. -/
structure Result (Fact : Type) where
  input : CheckerInput Fact
  baseFacts : List (NodeFact Fact)
  seeds : Array (Seed Fact)
  terms : Array TermRef

def State.find? (state : State) (expression : Expr) (domain : DomainId) :
    Option NodeId := do
  let found ← state.terms.toList.find? fun term =>
    term.domain == domain && term.expression == expression
  pure found.node

/-- Select exactly one package for an expression and expected output domain. -/
def select (registry : Registry) (expression : Expr) (domain : DomainId) :
    MetaM (Nat × Package × List Expr) := do
  let mut selected : Option (Nat × Package × List Expr) := none
  for index in [0:registry.packages.size] do
    let some package := registry.packages[index]?
      | throwError "interval goal frontend: package index escaped its registry"
    if package.operation.output == domain then
      let match? ← package.recognize expression
      match match? with
      | none => pure ()
      | some arguments =>
          if arguments.length != package.operation.inputs.length then
            throwError
              "interval goal frontend: package returned the wrong argument count"
          if selected.isSome then
            throwError "interval goal frontend: ambiguous expression package"
          selected := some (index, package, arguments)
  let some result := selected
    | throwError "interval goal frontend: no package recognized expression"
  pure result

/-- Recursively append one expression and its dependencies to the SSA graph. -/
partial def reifyTerm (registry : Registry) (expression : Expr)
    (domain : DomainId) (depth : Nat) (state : State) :
    MetaM (NodeId × State) := do
  if registry.limits.maxDepth < depth then
    throwError "interval goal frontend: expression depth limit exceeded"
  if let some node := state.find? expression domain then
    return (node, state)
  let (operationIndex, package, arguments) ←
    select registry expression domain
  let mut state := state
  let mut nodes := []
  for (argument, argumentDomain) in arguments.zip package.operation.inputs do
    let (node, next) ←
      reifyTerm registry argument argumentDomain (depth + 1) state
    state := next
    nodes := nodes.concat node
  if registry.limits.maxNodes ≤ state.nodes.size then
    throwError "interval goal frontend: expression node limit exceeded"
  let node : NodeId := { index := state.nodes.size }
  let instruction : Node :=
    { domain
      op := { index := operationIndex }
      args := nodes }
  pure
    (node,
      { nodes := state.nodes.push instruction
        terms := state.terms.push { expression, domain, node } })

private def installedFact (domain : FactDomain Fact) (nodeDomain : DomainId)
    (current proposed : Fact) : Except String Fact :=
  match domain.narrow nodeDomain current proposed with
  | .noChange => pure current
  | .improved installed | .contradiction installed => pure installed
  | .malformed _ => throw "malformed caller interval fact"
  | .resourceLimit _ => throw "caller interval fact exceeded its resource bound"

/-- Reify a target and all recognized local hypotheses into one checker input.

The target is traversed first, so its node and dependencies have stable early
identifiers.  Later hypotheses reuse those nodes by exact-expression CSE and
may append additional expressions needed only by their facts. -/
opaque reify (registry : Registry) (factDomain : FactDomain Fact)
    (parser : Parser Fact) (hypotheses : List (Expr × Expr)) (target : Expr) :
    MetaM (Result Fact) := do
  let some targetClaim ← parser.parse target
    | throwError "interval goal frontend: target is not an interval claim"
  let (targetNode, initial) ←
    reifyTerm registry targetClaim.expression targetClaim.domain 0 {}
  let mut state := initial
  let mut assumed : List (NodeFact Fact × Expr) := []
  for (proposition, proof) in hypotheses do
    let parsed ← parser.parse proposition
    match parsed with
    | none => pure ()
    | some claim =>
        let (node, next) ←
          reifyTerm registry claim.expression claim.domain 0 state
        state := next
        assumed := assumed.concat ({ node, fact := claim.fact }, proof)
  let program : Program :=
    { operations := registry.operations
      nodes := state.nodes }
  unless program.check do
    throwError "interval goal frontend: reified program failed structural validation"
  let mut facts := #[]
  let mut seeds := #[]
  for index in [0:state.nodes.size] do
    let some instruction := state.nodes[index]?
      | throwError "interval goal frontend: node index escaped the graph"
    facts := facts.push (factDomain.top instruction.domain)
    seeds := seeds.push {}
  for (fact, proof) in assumed do
    let some instruction := state.nodes[fact.node.index]?
      | throwError "interval goal frontend: assumption node escaped the graph"
    let some current := facts[fact.node.index]?
      | throwError "interval goal frontend: assumption fact escaped the graph"
    let some seed := seeds[fact.node.index]?
      | throwError "interval goal frontend: assumption seed escaped the graph"
    let installed ←
      match installedFact factDomain instruction.domain current fact.fact with
      | .ok installed => pure installed
      | .error message => throwError "interval goal frontend: {message}"
    facts := facts.set! fact.node.index installed
    seeds := seeds.set! fact.node.index
      { assumptions := seed.assumptions.concat { fact := fact.fact, proof } }
  let targetFact : NodeFact Fact :=
    { node := targetNode, fact := targetClaim.fact }
  pure
    { input :=
        { baseProgram := program
          initialFacts := facts
          target := targetFact }
      baseFacts :=
        List.ofFn fun index : Fin facts.size =>
          { node := { index := index.val }, fact := facts[index] }
      seeds
      terms := state.terms }

end Hex.Interval.Experiment.GoalFrontend
