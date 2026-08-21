/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Rule

@[expose] public section

/-!
# Programmatic arithmetic frontend

This module is the supported, tactic-independent frontend boundary. It
recursively reifies a small arithmetic term language into the exact supported
SSA `Program`, resolves operations by stable key, constructs version-zero
source facts, invokes the supported Rule/Proof replay, and closes interval
membership to ordinary bounds, conjunctions, or singleton equality.

It intentionally contains no syntax elaborator. Turning arbitrary Lean
expressions and local hypotheses into this programmatic input additionally
requires a supported quotation bridge for `Program`, `Interval`, replay events,
and caller proof terms. The existing bridge is experimental and uses different
certificate types, so importing or aliasing it here would reverse the intended
production boundary. This module accepts one flat event chronology; it does not
derive proof recipes from retained search or split trees.
-/

namespace Hex.Interval.Frontend

open Proof

/-- Function-generic arithmetic syntax. One package-configured constant,
natural exponent, and precision keep semantic identity in `Rule.Config`, not
in an untrusted term payload. -/
inductive Term where
  | source (index : Nat)
  | constant
  | neg (input : Term)
  | add (left right : Term)
  | sub (left right : Term)
  | mul (left right : Term)
  | pow (input : Term)
  | abs (input : Term)
  | min (left right : Term)
  | max (left right : Term)
  | inv (input : Term)
  | div (left right : Term)
  | regularize (input : Term)
  deriving DecidableEq, Repr

/-- Reification caps are independent of interval arithmetic and proof replay
caps. `maxSources` also bounds caller fact-array traversal. `maxOperations`
admits the already-constructed configured meaning array before stable-key
lookup; it does not preempt construction of `Rule.Config` or structural
equality on caller `Term` values. -/
structure Limits where
  maxSources : Nat
  maxOperations : Nat
  maxNodes : Nat
  maxDepth : Nat
  deriving DecidableEq, Repr

/-- Every resource envelope needed by this frontend is explicit. -/
structure Config where
  rule : Rule.Config
  reify : Limits
  proof : Proof.Limits

structure Entry where
  term : Term
  node : NodeId
  deriving DecidableEq, Repr

structure State where
  nodes : Array Node := #[]
  entries : Array Entry := #[]
  deriving DecidableEq, Repr

structure Result where
  program : Program
  target : NodeId
  entries : Array Entry
  sourceCount : Nat
  deriving DecidableEq, Repr

inductive Error where
  | sourceLimit
  | operationLimit
  | sourceIndex (index : Nat)
  | depthLimit
  | nodeLimit
  | missingOperation (key : OpKey)
  | malformedProgram
  | malformedResult
  | wrongSourceCount
  | missingSource (index : Nat)
  | rule (error : Rule.BuildError)
  | replay (error : Proof.Error)
  deriving Repr

def State.find? (state : State) (term : Term) : Option NodeId :=
  (state.entries.toList.find? fun entry => entry.term == term).map (·.node)

def operationKey : Term → OpKey
  | .source _ => Rule.sourceOp.key
  | .constant => Rule.constantOp.key
  | .neg _ => Rule.negOp.key
  | .add _ _ => Rule.addOp.key
  | .sub _ _ => Rule.subOp.key
  | .mul _ _ => Rule.mulOp.key
  | .pow _ => Rule.powOp.key
  | .abs _ => Rule.absOp.key
  | .min _ _ => Rule.minOp.key
  | .max _ _ => Rule.maxOp.key
  | .inv _ => Rule.invOp.key
  | .div _ _ => Rule.divOp.key
  | .regularize _ => Rule.regularizeOp.key

def install (config : Config) (term : Term) (reified : List NodeId)
    (state : State) : Except Error (NodeId × State) := do
  if config.reify.maxNodes ≤ state.nodes.size then throw .nodeLimit
  let key := operationKey term
  let emptyProgram : Program :=
    { operations := (Rule.meanings config.rule).map (Program.Meaning.operation)
      nodes := #[] }
  let some (operation, signature) :=
      emptyProgram.operationEntry? key
    | throw (.missingOperation key)
  if signature.inputs.length != reified.length then throw .malformedProgram
  let node : NodeId := { index := state.nodes.size }
  let instruction : Node :=
    { domain := Rule.realDomain, op := operation, args := reified }
  pure (node,
    { nodes := state.nodes.push instruction
      entries := state.entries.push { term, node } })

def reifyTerm (config : Config) (sourceCount depth : Nat)
    (term : Term) (state : State) : Except Error (NodeId × State) := do
  if config.reify.maxDepth < depth then throw .depthLimit
  if let some node := state.find? term then return (node, state)
  match term with
  | .source index =>
      if sourceCount ≤ index then throw (.sourceIndex index)
      install config term [] state
  | .constant => install config term [] state
  | .neg input | .pow input | .abs input | .inv input | .regularize input =>
      let (node, state) ← reifyTerm config sourceCount (depth + 1) input state
      install config term [node] state
  | .add left right | .sub left right | .mul left right | .div left right |
      .min left right | .max left right =>
      let (leftNode, state) ← reifyTerm config sourceCount (depth + 1) left state
      let (rightNode, state) ← reifyTerm config sourceCount (depth + 1) right state
      install config term [leftNode, rightNode] state

/-- Recursively construct a checked SSA program. Failure returns no partial
result. Exact-expression CSE is structural equality on `Term`. -/
def reifyWithin (config : Config) (sourceCount : Nat) (target : Term) :
    Except Error Result := do
  if config.reify.maxSources < sourceCount then throw .sourceLimit
  if config.reify.maxOperations < (Rule.meanings config.rule).size then
    throw .operationLimit
  let (targetNode, state) ← reifyTerm config sourceCount 0 target {}
  let program : Program :=
    { operations := (Rule.meanings config.rule).map (Program.Meaning.operation)
      nodes := state.nodes }
  if !program.check then throw .malformedProgram
  pure { program, target := targetNode, entries := state.entries, sourceCount }

def Result.sourceNode? (result : Result) (index : Nat) : Option NodeId :=
  (result.entries.toList.find? fun entry => entry.term == .source index).map (·.node)

protected def Term.inputs : Term → List Term
  | .source _ | .constant => []
  | .neg input | .pow input | .abs input | .inv input | .regularize input => [input]
  | .add left right | .sub left right | .mul left right | .div left right |
      .min left right | .max left right => [left, right]

protected def Result.inputsMatch (entries : Array Entry) : List Term → List NodeId → Bool
  | [], [] => true
  | term :: terms, node :: nodes =>
      (entries[node.index]?).any (fun entry => entry.term == term) &&
        Result.inputsMatch entries terms nodes
  | _, _ => false

protected def Result.uniqueTerms : List Entry → Bool
  | [] => true
  | entry :: entries =>
      !(entries.any fun other => other.term == entry.term) && Result.uniqueTerms entries

/-- Authenticate the transparent reification record against its exact program.
This pins one entry to every SSA node, structural CSE, operation keys and
ordered child edges. The caller-facing resource checks run before this bounded
scan; structural equality of the already-constructed `Term` values remains a
programmatic-caller cost. -/
def Result.check (result : Result) : Bool :=
  result.entries.size == result.program.nodes.size &&
    Result.uniqueTerms result.entries.toList &&
    (List.range result.entries.size).all fun index =>
      match result.entries[index]?, result.program.nodes[index]? with
      | some entry, some node =>
          entry.node.index == index &&
            (result.program.operation? node.op).any
              (fun operation => operation.key == operationKey entry.term) &&
            (match entry.term with
              | .source source => source < result.sourceCount
              | _ => true) &&
            Result.inputsMatch result.entries entry.term.inputs node.args
      | _, _ => false

/-- Revalidate the bounded reification result, including its exact node/term
correspondence, bind every selected source exactly once, and seed all computed
nodes with domain top. Constants are proved by the constant rule rather than
trusted as assumptions. -/
def inputWithin (config : Config) (scope : Policy.ScopeId) (result : Result)
    (sources : Array Hex.Interval) (target : Hex.Interval) :
    Except Error (Proof.Input Hex.Interval) := do
  if config.reify.maxSources < result.sourceCount then throw .sourceLimit
  let meanings := Rule.meanings config.rule
  if config.reify.maxOperations < meanings.size ||
      config.reify.maxOperations < result.program.operations.size then
    throw .operationLimit
  if config.reify.maxNodes < result.program.nodes.size ||
      config.reify.maxNodes < result.entries.size then throw .nodeLimit
  if result.target.index ≥ result.program.nodes.size || !result.program.check then
    throw .malformedProgram
  if result.program.operations != meanings.map (Program.Meaning.operation) then
    throw .malformedProgram
  if !result.check then throw .malformedResult
  if sources.size != result.sourceCount then throw .wrongSourceCount
  let mut facts := Array.replicate result.program.nodes.size Hex.Interval.whole
  for index in [0:result.sourceCount] do
    let some node := result.sourceNode? index | throw (.missingSource index)
    let some fact := sources[index]? | throw .wrongSourceCount
    facts := facts.set! node.index fact
  let input : Proof.Input Hex.Interval :=
    { scope
      program := result.program
      facts
      target := { node := result.target, fact := target } }
  pure input

/-- Bounded supported registry assembly followed by exact chronological replay.
Neither the reifier nor the caller-supplied event list has proof authority. The
proof layer reauthenticates every event; retained search-tree recipe extraction
is a separate boundary. -/
def replay (config : Config) (input : Proof.Input Hex.Interval)
    (events : List (Proof.Event Hex.Interval)) (finalVersion : Nat)
    (finalProgram : Program) (result : SeenVersion) :
    Except Error (Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target)) := do
  match Rule.buildWithin config.proof config.rule input.program with
  | .error error => throw (.rule error)
  | .ok registry =>
      match Proof.replay config.proof registry (Rule.domain config.rule)
          (Rule.laws config.rule) input events finalVersion finalProgram result with
      | .ok evidence => pure evidence
      | .error error => throw (.replay error)

/-- Eliminate replay evidence at one exact valuation and caller context. -/
theorem close (config : Config) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (valuation : NodeId → ℝ)
    (model : Program.Models (Rule.meanings config.rule) input.program valuation)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (valuation fact.node)) :
    input.target.fact.Contains (valuation input.target.node) := by
  exact evidence.proof valuation model (by
    intro fact member
    simpa [Rule.semantics, Proof.Semantics.ofMeanings] using assumptions fact member)

/-- Close both endpoint predicates. This is the conjunction frontend used for
two-sided inequality goals. -/
theorem closeBounds (config : Config) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (valuation : NodeId → ℝ)
    (model : Program.Models (Rule.meanings config.rule) input.program valuation)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (valuation fact.node))
    (lower : Lower) (upper : Upper)
    (shape : input.target.fact.view = .bounds lower upper) :
    lower.Contains (valuation input.target.node) ∧
      upper.Contains (valuation input.target.node) := by
  have member := close config input evidence valuation model assumptions
  change input.target.fact.view.Contains (valuation input.target.node) at member
  simpa [shape, Raw.Contains] using member

theorem closeLower (config : Config) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (valuation : NodeId → ℝ)
    (model : Program.Models (Rule.meanings config.rule) input.program valuation)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (valuation fact.node))
    (value : Dyadic) (strict : Bool) (upper : Upper)
    (shape : input.target.fact.view = .bounds (.finite value strict) upper) :
    (Lower.finite value strict).Contains (valuation input.target.node) :=
  (closeBounds config input evidence valuation model assumptions _ _ shape).1

theorem closeUpper (config : Config) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (valuation : NodeId → ℝ)
    (model : Program.Models (Rule.meanings config.rule) input.program valuation)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (valuation fact.node))
    (lower : Lower) (value : Dyadic) (strict : Bool)
    (shape : input.target.fact.view = .bounds lower (.finite value strict)) :
    (Upper.finite value strict).Contains (valuation input.target.node) :=
  (closeBounds config input evidence valuation model assumptions _ _ shape).2

/-- A closed singleton interval closes an equality goal. -/
theorem closeSingleton (config : Config) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (valuation : NodeId → ℝ)
    (model : Program.Models (Rule.meanings config.rule) input.program valuation)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (valuation fact.node))
    (value : Dyadic)
    (shape : input.target.fact.view =
      .bounds (.finite value false) (.finite value false)) :
    valuation input.target.node = toReal value := by
  rcases closeBounds config input evidence valuation model assumptions _ _ shape with
    ⟨lower, upper⟩
  exact le_antisymm upper lower

end Hex.Interval.Frontend
