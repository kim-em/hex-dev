/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Lean
public import HexInterval.Experiment.Frontend

@[expose] public section

/-!
# Shared Lean encoder for interval proof frontends

The search engine returns ordinary data.  A tactic must quote that data as
Lean expressions before applying transparent replay theorems.  This module
encodes every function-independent program and trace structure once; a fact
domain contributes only its fact type expression and fact-value encoder.
-/

namespace Hex.Interval.Experiment.FrontendEncoder

open Lean Meta
open Propagator PayloadArena SemanticReplay ProofEmitter

/-- Reification boundary for a frontend's concrete fact representation. -/
structure Encoder (Fact : Type) where
  program : Program → MetaM Expr
  input : CheckerInput Fact → MetaM Expr
  nodeId : NodeId → MetaM Expr
  node : Node → MetaM Expr
  fact : Fact → MetaM Expr
  nodeFact : NodeFact Fact → MetaM Expr
  instanceQuote : InstanceQuote → MetaM Expr
  ruleStep : RuleStep Fact → MetaM Expr
  transportStep : TransportStep Fact → MetaM Expr

def listExpr (type : Expr) (items : List Expr) : Expr :=
  items.foldr
    (fun item tail => mkApp3 (mkConst ``List.cons [Level.zero]) type item tail)
    (mkApp (mkConst ``List.nil [Level.zero]) type)

def natOptionExpr : Option Nat → Expr
  | none => mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Nat)
  | some value =>
      mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Nat)
        (mkNatLit value)

def nodeIdExpr (node : NodeId) : MetaM Expr :=
  mkAppM ``NodeId.mk #[mkNatLit node.index]

def domainExpr (domain : DomainId) : MetaM Expr :=
  mkAppM ``DomainId.mk #[mkNatLit domain.index]

def opExpr (operation : OpId) : MetaM Expr :=
  mkAppM ``OpId.mk #[mkNatLit operation.index]

def opKeyExpr (key : OpKey) : MetaM Expr :=
  mkAppM ``OpKey.mk #[toExpr key.name, mkNatLit key.version]

def operationExpr (operation : Operation) : MetaM Expr := do
  mkAppM ``Operation.mk
    #[← opKeyExpr operation.key,
      listExpr (mkConst ``DomainId) (← operation.inputs.mapM domainExpr),
      ← domainExpr operation.output]

def nodeExpr (instruction : Node) : MetaM Expr := do
  mkAppM ``Node.mk
    #[← domainExpr instruction.domain,
      ← opExpr instruction.op,
      listExpr (mkConst ``NodeId) (← instruction.args.mapM nodeIdExpr)]

def arrayExpr (type : Expr) (items : List Expr) : MetaM Expr :=
  mkAppM ``Array.mk #[listExpr type items]

def programExpr (program : Program) : MetaM Expr := do
  mkAppM ``Program.mk
    #[← arrayExpr (mkConst ``Operation)
        (← program.operations.toList.mapM operationExpr),
      ← arrayExpr (mkConst ``Node) (← program.nodes.toList.mapM nodeExpr)]

def ruleKeyExpr (key : RuleKey) : MetaM Expr :=
  mkAppM ``RuleKey.mk #[toExpr key.name, mkNatLit key.schema]

def ruleIdExpr (rule : RuleId) : MetaM Expr :=
  mkAppM ``RuleId.mk #[mkNatLit rule.index]

def applicationExpr (application : ApplicationId) : MetaM Expr :=
  mkAppM ``ApplicationId.mk #[mkNatLit application.index]

def equalityExpr (equality : EqualityId) : MetaM Expr :=
  mkAppM ``EqualityId.mk #[mkNatLit equality.index]

def payloadExpr (payload : PayloadId) : MetaM Expr :=
  mkAppM ``PayloadId.mk #[mkNatLit payload.index]

def actionKindExpr : ActionKind → Expr
  | .forward => mkConst ``ActionKind.forward
  | .backward => mkConst ``ActionKind.backward
  | .improve => mkConst ``ActionKind.improve
  | .shave => mkConst ``ActionKind.shave
  | .instantiate => mkConst ``ActionKind.instantiate
  | .rewrite => mkConst ``ActionKind.rewrite
  | .regularize => mkConst ``ActionKind.regularize
  | .split => mkConst ``ActionKind.split

def seenExpr (seen : SeenVersion) : MetaM Expr :=
  do mkAppM ``SeenVersion.mk #[← nodeIdExpr seen.node, mkNatLit seen.version]

def structuralKeyExpr : StructuralKey → MetaM Expr
  | .node node => do mkAppM ``StructuralKey.node #[← nodeIdExpr node]
  | .equality equality => do
      mkAppM ``StructuralKey.equality #[← equalityExpr equality]
  | .application application => do
      mkAppM ``StructuralKey.application #[← applicationExpr application]

def structuralInputExpr (input : StructuralInput) : MetaM Expr :=
  do
    mkAppM ``StructuralInput.mk
      #[← structuralKeyExpr input.key, mkNatLit input.generation]

def scopeExpr (binding : ScopeBinding) : MetaM Expr :=
  do
    mkAppM ``ScopeBinding.mk
      #[← ruleKeyExpr binding.rule,
        ← nodeIdExpr binding.anchor,
        listExpr (mkConst ``NodeId) (← binding.watches.mapM nodeIdExpr),
        listExpr (mkConst ``NodeId) (← binding.writes.mapM nodeIdExpr)]

def actionExpr (action : Action) : MetaM Expr := do
  mkAppM ``Action.mk
    #[mkNatLit action.serial,
      mkNatLit action.programVersion,
      ← applicationExpr action.application,
      ← ruleIdExpr action.rule,
      ← ruleKeyExpr action.key,
      ← nodeIdExpr action.node,
      actionKindExpr action.kind,
      mkNatLit action.effort,
      mkNatLit action.generation,
      listExpr (mkConst ``SeenVersion) (← action.inputs.mapM seenExpr),
      listExpr (mkConst ``NodeId) (← action.writes.mapM nodeIdExpr),
      listExpr (mkConst ``StructuralInput)
        (← action.structuralInputs.mapM structuralInputExpr),
      natOptionExpr action.matcherEpoch]

def roleExpr : Role → Expr
  | .fact => mkConst ``Role.fact
  | .instance => mkConst ``Role.instance
  | .equality => mkConst ``Role.equality

def entryExpr (entry : Entry) : MetaM Expr := do
  mkAppM ``Entry.mk
    #[← actionExpr entry.origin,
      roleExpr entry.role,
      mkNatLit entry.schema,
      listExpr (mkConst ``Nat) (entry.body.map mkNatLit)]

def factCauseExpr (factType : Expr) (factExpr : Fact → MetaM Expr) :
    FactCause Fact → MetaM Expr
  | .rule action proposed payload =>
      do
        mkAppM ``FactCause.rule
          #[← actionExpr action, ← factExpr proposed, ← payloadExpr payload]
  | .transport equality source => do
      pure <| mkApp3 (mkConst ``FactCause.transport) factType
        (← equalityExpr equality) (← seenExpr source)

def factEventExpr (factType : Expr) (factExpr : Fact → MetaM Expr)
    (event : FactEvent Fact) : MetaM Expr := do
  mkAppM ``FactEvent.mk
    #[mkNatLit event.programVersion,
      ← nodeIdExpr event.node,
      ← seenExpr event.previous,
      ← factExpr event.fact,
      mkNatLit event.version,
      ← factCauseExpr factType factExpr event.cause]

def nodeFactExpr (factExpr : Fact → MetaM Expr) (fact : NodeFact Fact) :
    MetaM Expr :=
  do mkAppM ``NodeFact.mk #[← nodeIdExpr fact.node, ← factExpr fact.fact]

def checkerInputExpr (factType : Expr) (factExpr : Fact → MetaM Expr)
    (input : CheckerInput Fact) : MetaM Expr := do
  mkAppM ``CheckerInput.mk
    #[← programExpr input.baseProgram,
      ← arrayExpr factType (← input.initialFacts.toList.mapM factExpr),
      ← nodeFactExpr factExpr input.target]

def edgeExpr (edge : EqualityEdge) : MetaM Expr := do
  mkAppM ``EqualityEdge.mk
    #[← nodeIdExpr edge.left,
      ← nodeIdExpr edge.right,
      mkNatLit edge.generation,
      ← actionExpr edge.origin,
      ← payloadExpr edge.payload]

def instanceEventExpr (event : InstanceEvent) : MetaM Expr := do
  mkAppM ``InstanceEvent.mk
    #[mkNatLit event.programVersion,
      ← actionExpr event.origin,
      mkNatLit event.family,
      listExpr (mkConst ``NodeId) (← event.substitution.mapM nodeIdExpr),
      listExpr (mkConst ``NodeId) (← event.products.mapM nodeIdExpr),
      listExpr (mkConst ``NodeId) (← event.newNodes.mapM nodeIdExpr),
      listExpr (mkConst ``ScopeBinding) (← event.bindings.mapM scopeExpr),
      listExpr (mkConst ``ScopeBinding) (← event.newBindings.mapM scopeExpr),
      listExpr (mkConst ``ApplicationId)
        (← event.applications.mapM applicationExpr),
      listExpr (mkConst ``ApplicationId)
        (← event.newApplications.mapM applicationExpr),
      mkNatLit event.generation,
      listExpr (mkConst ``EqualityId) (← event.equalities.mapM equalityExpr),
      listExpr (mkConst ``EqualityId)
        (← event.newEqualities.mapM equalityExpr),
      ← payloadExpr event.payload]

def instanceQuoteExpr (quote : InstanceQuote) : MetaM Expr :=
  do
    mkAppM ``InstanceQuote.mk
      #[← instanceEventExpr quote.event,
        ← payloadExpr quote.payload,
        ← entryExpr quote.entry]

def ruleStepExpr (factType : Expr) (factExpr : Fact → MetaM Expr)
    (step : RuleStep Fact) : MetaM Expr := do
  let nodeFactType ← mkAppM ``NodeFact #[factType]
  mkAppM ``RuleStep.mk
    #[← factEventExpr factType factExpr step.event,
      ← payloadExpr step.payload,
      ← entryExpr step.entry,
      listExpr nodeFactType (← step.assumptions.mapM (nodeFactExpr factExpr)),
      ← factExpr step.previous]

def transportStepExpr (factType : Expr) (factExpr : Fact → MetaM Expr)
    (step : TransportStep Fact) : MetaM Expr := do
  let nodeFactType ← mkAppM ``NodeFact #[factType]
  mkAppM ``TransportStep.mk
    #[← factEventExpr factType factExpr step.event,
      ← equalityExpr step.equality,
      ← edgeExpr step.edge,
      ← payloadExpr step.payload,
      ← entryExpr step.entry,
      listExpr nodeFactType (← step.assumptions.mapM (nodeFactExpr factExpr)),
      ← factExpr step.previous,
      ← factExpr step.sourceFact]

/-- Build the complete generic encoder from one fact-value encoder. -/
def make (factType : Expr) (factExpr : Fact → MetaM Expr) : Encoder Fact :=
  { program := programExpr
    input := checkerInputExpr factType factExpr
    nodeId := nodeIdExpr
    node := nodeExpr
    fact := factExpr
    nodeFact := nodeFactExpr factExpr
    instanceQuote := instanceQuoteExpr
    ruleStep := ruleStepExpr factType factExpr
    transportStep := transportStepExpr factType factExpr }

end Hex.Interval.Experiment.FrontendEncoder
