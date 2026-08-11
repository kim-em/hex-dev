/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.FrontendEncoder
public import HexInterval.Experiment.GenericInstanceReconstruction

@[expose] public section

/-!
# Generic direct-proof frontend

This module folds an arbitrary quoted interval chronology into an ordinary
Lean proof term.  It carries the current expression program, independently
checked program version, conservative-extension evidence, and an exact table
of proofs indexed by `(node, version)`.

The fold has no operation or mathematical-function cases.  A semantics adapter
supplies its domain laws and prefix-stability theorem, while each propagator
package is selected through the joint proof registry.  A small encoder turns
plain runtime data into Lean expressions; those expressions remain untrusted
until the emitted replay applications typecheck.
-/

namespace Hex.Interval.Experiment.ProofFrontend

open Lean Meta
open Propagator PayloadArena SemanticReplay ChronologicalReplay ProofEmitter
open GenericInstanceReconstruction ProofRegistry Frontend
open FrontendEncoder

/-- Kernel constants and runtime values needed by the generic fold.

Every `Expr` field is checked again at its use site.  In particular,
`finalPrefix` and `sameOperations` must have types referring to the reified
final program; a caller cannot attach them to a different expression graph. -/
structure Context (Fact Handle : Type) where
  encoder : Encoder Fact
  resolveSchema : Handle → MetaM Name
  semantics : Expr
  domain : Expr
  laws : Expr
  stableLaw : Expr
  input : Expr
  assumed : Name
  baseFacts : List (NodeFact Fact)
  baseFactsTerm : Expr
  baseProgram : Program
  baseProgramTerm : Expr
  basePrefix : Expr
  baseWithin : Expr
  initialExtension : Expr
  finalPrefix : Expr
  sameOperations : Expr
  top : DomainId → Fact

/-- One kernel proof already available at an exact engine fact version. -/
structure FactProof (Fact : Type) where
  seen : SeenVersion
  fact : Fact
  within : Expr
  proof : Expr

/-- Dependent proof state carried through the quoted chronology. -/
structure State (Fact : Type) where
  version : Nat
  programValue : Program
  program : Expr
  snapshot : Expr
  basePrefix : Expr
  baseWithin : Expr
  extension : Expr
  known : List (FactProof Fact)

/-- Preserve an already checked program proposition while giving the emitter a
stable declaration to apply to reified programs. -/
theorem keepCheck (program : Program) (checked : program.check = true) :
    program.check = true :=
  checked

/-- Project an accepted transparent replay result.  The supplied equality is
ordinary kernel reduction, never `native_decide`. -/
def replayGet {α : Type} (result : Option α) (success : result.isSome = true) : α :=
  result.get success

/-- Resolve one exact package-owned schema handle to a declaration. -/
def schemaName (context : Context Fact Handle) (table : SchemaTable Handle)
    (label : String) (entry : Entry) : MetaM Name := do
  let some handle := table.find? entry.replayKey
    | throwError "interval frontend: no proof schema for {label}"
  let declaration ← context.resolveSchema handle
  discard <| getConstInfo declaration
  pure declaration

/-- Find one previously established fact without substituting a newer value. -/
def findFact? [BEq Fact] (known : List (FactProof Fact)) (seen : SeenVersion)
    (fact : Fact) : Option (FactProof Fact) := do
  let item ← known.find? fun item => item.seen == seen
  if item.fact == fact then some item else none

/-- Find the proof term for one exact fact version. -/
def findProof? [BEq Fact] (known : List (FactProof Fact))
    (seen : SeenVersion) (fact : Fact) : Option Expr :=
  (findFact? known seen fact).map (fun item => item.proof)

/-- Insert a newly proved version, rejecting duplicate provenance. -/
def insertProof (known : List (FactProof Fact)) (item : FactProof Fact) :
    MetaM (List (FactProof Fact)) := do
  if known.any fun old => old.seen == item.seen then
    throwError "interval frontend: duplicate proof for a fact version"
  pure (item :: known)

/-- Assemble dependency evidence in the action's exact input order. -/
def inputProofs [BEq Fact] (context : Context Fact Handle) (program : Expr)
    (known : List (FactProof Fact)) :
    List SeenVersion → List (NodeFact Fact) → MetaM Expr
  | [], [] =>
      mkAppM ``EntailsList.empty
        #[context.semantics, program, context.baseFactsTerm]
  | seen :: seenTail, fact :: factTail => do
      unless seen.node == fact.node do
        throwError "interval frontend: input node does not match resolved fact"
      let some head := findProof? known seen fact.fact
        | throwError "interval frontend: input fact has not been proved yet"
      let tail ← inputProofs context program known seenTail factTail
      mkAppM ``EntailsList.cons #[head, tail]
  | _, _ =>
      throwError "interval frontend: input versions and facts differ in length"

/-- Package ordered dependency terms as the proposition consumed by replay. -/
def soundInputs [BEq Fact] (context : Context Fact Handle) (program : Expr)
    (known : List (FactProof Fact)) (seen : List SeenVersion)
    (facts : List (NodeFact Fact)) : MetaM Expr := do
  let proofs ← inputProofs context program known seen facts
  mkAppM ``EntailsList.sound #[proofs]

def replayResult (result : Expr) : MetaM Expr := do
  let success ← mkAppM ``Eq.refl #[mkConst ``Bool.true]
  mkAppM ``replayGet #[result, success]

/-- Emit a kernel-checked subsumption step from one exact retained fact version
to the caller's requested fact. -/
def closeTarget [BEq Fact] (context : Context Fact Handle)
    (state : State Fact) (seen : SeenVersion) (actual : Fact)
    (target : NodeFact Fact) : MetaM Expr := do
  unless seen.node == target.node do
    throwError "interval frontend: retained result is for the wrong target node"
  let some established := findFact? state.known seen actual
    | throwError "interval frontend: retained target version has not been proved"
  let nodeTerm ← context.encoder.nodeId target.node
  let actualTerm ← context.encoder.fact actual
  let requestedTerm ← context.encoder.fact target.fact
  let result ←
    mkAppM ``ProofEmitter.closeFact
      #[context.domain, state.program, context.baseFactsTerm, nodeTerm,
        actualTerm, requestedTerm, established.proof]
  replayResult result

/-- Seed caller-owned version-zero facts by exact positions in the base list. -/
def seedBase (context : Context Fact Handle) (program : Expr) (basePrefix : Expr) :
    MetaM (List (FactProof Fact)) := do
  let mut known := []
  let baseWithinProgram ←
    mkAppM ``ProofEmitter.liftFacts #[basePrefix, context.baseWithin]
  for (fact, index) in context.baseFacts.zipIdx do
    let factTerm ← context.encoder.nodeFact fact
    let someFact ← mkAppM ``Option.some #[factTerm]
    let found ← mkAppM ``Eq.refl #[someFact]
    let proof ←
      mkAppM context.assumed
        #[program, context.baseFactsTerm, mkNatLit index, factTerm, found]
    let within ←
      mkAppM ``ProofEmitter.factWithinAt
        #[program, context.baseFactsTerm, baseWithinProgram,
          mkNatLit index, factTerm, found]
    known ← insertProof known
      { seen := { node := fact.node, version := 0 }
        fact := fact.fact
        within
        proof }
  pure known

/-- Seed domain-top evidence for exactly one instance's fresh-node suffix. -/
def seedNew [BEq Fact] (context : Context Fact Handle) (programValue : Program)
    (program : Expr) (newNodes : List NodeId) (known : List (FactProof Fact)) :
    MetaM (List (FactProof Fact)) := do
  let mut known := known
  for node in newNodes do
    let some instruction := programValue.node? node
      | throwError "interval frontend: fresh node is absent from the program"
    let nodeTerm ← context.encoder.nodeId node
    let instructionTerm ← context.encoder.node instruction
    let factValue := context.top instruction.domain
    let someInstruction ← mkAppM ``Option.some #[instructionTerm]
    let found ← mkAppM ``Eq.refl #[someInstruction]
    let proof ←
      mkAppM ``ProofEmitter.topFact
        #[context.domain, program, context.baseFactsTerm,
          nodeTerm, instructionTerm, found]
    let within ←
      mkAppM ``ProofEmitter.nodeWithin
        #[program, nodeTerm, instructionTerm, found]
    known ← insertProof known
      { seen := { node, version := 0 }
        fact := factValue
        within
        proof }
  pure known

/-- Lift every established fact across one stable program extension. -/
def liftKnown (stable stepPrefix baseWithin : Expr)
    (known : List (FactProof Fact)) : MetaM (List (FactProof Fact)) :=
  known.mapM fun item => do
    let proof ←
      mkAppM ``ProofEmitter.liftFact
        #[stable, baseWithin, item.proof, item.within]
    let within ← mkAppM ``ProofEmitter.liftNode #[stepPrefix, item.within]
    pure { item with within, proof }

/-- Construct the initial generic reconstruction snapshot. -/
def initialSnapshot (context : Context Fact Handle) (finalProgram : Expr) : MetaM Expr := do
  let checked ← mkAppM ``Eq.refl #[mkConst ``Bool.true]
  let finalChecked ← mkAppM ``keepCheck #[finalProgram, checked]
  let baseChecked ← mkAppM ``keepCheck #[context.baseProgramTerm, checked]
  mkAppM ``GenericInstanceReconstruction.Snapshot.mk
    #[finalChecked, baseChecked, context.finalPrefix, context.sameOperations]

/-- Replay one arbitrary package-owned instantiation. -/
def emitInstance (context : Context Fact Handle) (version : Nat)
    (before after : Expr) (basePrefix stepPrefix sameOperations : Expr)
    (quote : InstanceQuote) (quoteTerm : Expr) (previous : Expr)
    (table : SchemaTable Handle) : MetaM Expr := do
  let schema ← schemaName context table "instantiation" quote.entry
  let result ←
    mkAppM ``ProofEmitter.replayInstance
      #[mkConst schema, context.input, mkNatLit version, before, after,
        basePrefix, stepPrefix, sameOperations, quoteTerm, previous]
  replayResult result

/-- Replay and install one instantiation event. -/
def emitInstantiation [BEq Fact] (context : Context Fact Handle)
    (finalValue : Program) (finalProgram : Expr) (table : SchemaTable Handle)
    (state : State Fact) (quote : InstanceQuote) : MetaM (State Fact) := do
  let eventTerm ← context.encoder.instanceQuote quote
  let reconstruction ←
    mkAppM ``GenericInstanceReconstruction.reconstruct?
      #[context.stableLaw, finalProgram, state.program, state.snapshot,
        ← mkAppM ``InstanceQuote.event #[eventTerm]]
  let step ← replayResult reconstruction
  let after ← mkAppM ``GenericInstanceReconstruction.Step.after #[step]
  let stepPrefix ←
    mkAppM ``GenericInstanceReconstruction.Step.stepPrefix #[step]
  let stable ← mkAppM ``GenericInstanceReconstruction.Step.stable #[step]
  let sameOperations ←
    mkAppM ``GenericInstanceReconstruction.Step.sameOperations #[step]
  let nextSnapshot ← mkAppM ``GenericInstanceReconstruction.Step.next #[step]
  let extension ←
    emitInstance context state.version state.program after state.basePrefix
      stepPrefix sameOperations quote eventTerm state.extension table
  let known ← liftKnown stable stepPrefix state.baseWithin state.known
  let baseWithin ←
    mkAppM ``ProofEmitter.liftFacts #[stepPrefix, state.baseWithin]
  let basePrefix ←
    mkAppM ``ChronologicalReplay.prefixTrans #[state.basePrefix, stepPrefix]
  let nextSize := state.programValue.nodes.size + quote.event.newNodes.length
  let afterValue := GenericInstanceReconstruction.programPrefix finalValue nextSize
  let known ← seedNew context afterValue after quote.event.newNodes known
  pure
    { version := quote.event.programVersion
      programValue := afterValue
      program := after
      snapshot := nextSnapshot
      basePrefix
      baseWithin
      extension
      known }

/-- Replay one arbitrary fact propagator. -/
def emitRule [BEq Fact] (context : Context Fact Handle) (state : State Fact)
    (table : SchemaTable Handle) (step : RuleStep Fact) : MetaM (State Fact) := do
  unless step.event.programVersion == state.version do
    throwError "interval frontend: rule event has the wrong program version"
  let .rule action _ _ := step.event.cause
    | throwError "interval frontend: rule quote has a transport cause"
  let some previous := findFact? state.known step.event.previous step.previous
    | throwError "interval frontend: rule previous fact has not been proved"
  let inputs ← soundInputs context state.program state.known
    action.inputs step.assumptions
  let schema ← schemaName context table "fact rule" step.entry
  let stepTerm ← context.encoder.ruleStep step
  let result ←
    mkAppM ``ProofEmitter.replayRule
      #[mkConst schema, context.domain, context.input, state.program,
        state.basePrefix, context.baseFactsTerm, stepTerm, previous.proof, inputs]
  let proof ← replayResult result
  let known ← insertProof state.known
    { seen := { node := step.event.node, version := step.event.version }
      fact := step.event.fact
      within := previous.within
      proof }
  pure { state with known }

/-- Replay one generic equality transport. -/
def emitTransport [BEq Fact] (context : Context Fact Handle) (state : State Fact)
    (table : SchemaTable Handle) (step : TransportStep Fact) :
    MetaM (State Fact) := do
  unless step.event.programVersion == state.version do
    throwError "interval frontend: transport event has the wrong program version"
  let .transport _ source := step.event.cause
    | throwError "interval frontend: transport quote has a rule cause"
  let some previous := findFact? state.known step.event.previous step.previous
    | throwError "interval frontend: transport previous fact is unavailable"
  let some sourceProof := findProof? state.known source step.sourceFact
    | throwError "interval frontend: equality source fact is unavailable"
  let inputs ← soundInputs context state.program state.known
    step.edge.origin.inputs step.assumptions
  let schema ← schemaName context table "equality transport" step.entry
  let stepTerm ← context.encoder.transportStep step
  let result ←
    mkAppM ``ProofEmitter.replayTransport
      #[mkConst schema, context.domain, context.laws, context.input,
        mkNatLit state.version, state.program, state.basePrefix,
        context.baseFactsTerm, stepTerm, previous.proof, sourceProof, inputs]
  let proof ← replayResult result
  let known ← insertProof state.known
    { seen := { node := step.event.node, version := step.event.version }
      fact := step.event.fact
      within := previous.within
      proof }
  pure { state with known }

/-- Fold arbitrary proof events in their supplied chronology. -/
def emitEvents [BEq Fact] (context : Context Fact Handle) (finalValue : Program)
    (finalProgram : Expr) (table : SchemaTable Handle) :
    List (Frontend.Event Fact) → State Fact → MetaM (State Fact)
  | [], state => pure state
  | .instantiation quote :: rest, state => do
      let state ← emitInstantiation context finalValue finalProgram table state quote
      emitEvents context finalValue finalProgram table rest state
  | .rule step :: rest, state => do
      let state ← emitRule context state table step
      emitEvents context finalValue finalProgram table rest state
  | .transport step :: rest, state => do
      let state ← emitTransport context state table step
      emitEvents context finalValue finalProgram table rest state

/-- Emit the complete generic state for one final program and chronology. -/
def emitTrace [BEq Fact] (context : Context Fact Handle) (programValue : Program)
    (events : List (Frontend.Event Fact)) (table : SchemaTable Handle) :
    MetaM (State Fact) := do
  unless programValue.check do
    throwError "interval frontend: final expression program is not checked"
  let finalProgram ← context.encoder.program programValue
  let snapshot ← initialSnapshot context finalProgram
  let known ← seedBase context context.baseProgramTerm context.basePrefix
  let initial : State Fact :=
    { version := 0
      programValue := context.baseProgram
      program := context.baseProgramTerm
      snapshot
      basePrefix := context.basePrefix
      baseWithin := context.baseWithin
      extension := context.initialExtension
      known }
  let state ← emitEvents context programValue finalProgram table events initial
  unless state.programValue == programValue do
    throwError "interval frontend: trace did not consume the complete final program"
  pure state

end Hex.Interval.Experiment.ProofFrontend
