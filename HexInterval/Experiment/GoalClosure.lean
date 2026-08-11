/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.FrontendEncoder
public import HexInterval.Experiment.GoalFrontend
public import HexInterval.Experiment.OperationSemantics
public import HexInterval.Experiment.TraceReplay

@[expose] public section

/-!
# Kernel links for reified expression graphs

Goal recognizers are untrusted elaborator code.  This module turns their plain
graph result into a kernel-checked operation model by asking each aligned
package for a proof of its own relation at every node.  The assembler has no
case split on mathematical functions.
-/

namespace Hex.Interval.Experiment.GoalClosure

open Lean Meta
open Propagator SemanticReplay ChronologicalReplay
open GoalFrontend FrontendEncoder OperationSemantics

/-- Interpret a finite list of reified values as a total node valuation. -/
def valuationOf (fallback : Value) (values : List Value) (node : NodeId) : Value :=
  values[node.index]?.getD fallback

/-- The proof-producing half of one syntax package.

`model` is an expression denoting the package's `OperationSemantics.Model`;
`aligned` proves that model names the same opaque operation. `prove` must
return a term proving the model's relation for the supplied argument
expressions and result expression. All are checked by the kernel when the
assembled `Models` term is elaborated. -/
structure Package where
  operation : Operation
  model : Expr
  aligned : Expr
  prove : List Expr → Expr → MetaM Expr

/-- A reified valuation together with the kernel proof that it models the
exact expression program. -/
structure ModelProof where
  valuation : Expr
  proof : Expr

/-- Reified kernel terms for the caller's exact base graph and canonical
version-zero fact list. -/
structure BaseProof where
  input : Expr
  program : Expr
  facts : Expr
  basePrefix : Expr
  within : Expr
  extension : Expr
  sameOperations : Expr

/-- Domain-specific proof hooks for caller assumptions.  The callback receives
the graph expression, valuation, node, proposed fact, corresponding Lean term,
and the original local proof.  Its result must typecheck as the semantic fact
at that node. -/
structure FactBridge (Fact : Type) where
  runtime : FactDomain Fact
  schema : Expr
  proveAssumption : Expr → Expr → NodeId → Fact → Expr → Expr → MetaM Expr

/-- Resolve the exact Lean expression assigned to a reified node. -/
def termAt? (terms : Array TermRef) (node : NodeId) : Option Expr := do
  let term ← terms.toList.find? fun term => term.node == node
  pure term.expression

/-- Package one checked model lookup and relation theorem as a node meaning. -/
theorem meaningOf (models : Array (OperationSemantics.Model Value))
    (valuation : NodeId → Value) (node : NodeId) (instruction : Node)
    (model : OperationSemantics.Model Value)
    (found : models[instruction.op.index]? = some model)
    (related : model.relation (instruction.args.map valuation) (valuation node)) :
    OperationSemantics.NodeMeaning models valuation node instruction :=
  ⟨model, found, related⟩

/-- Exact semantic facts in list order, used to emit the universal base-fact
premise without generating a function by cases on node identifiers. -/
def FactMeanings (semantics : Semantics Fact) (program : Program)
    (valuation : NodeId → semantics.Value) : List (NodeFact Fact) → Prop
  | [] => True
  | fact :: rest =>
      semantics.holds program valuation fact ∧
        FactMeanings semantics program valuation rest

theorem FactMeanings.all {semantics : Semantics Fact} {program : Program}
    {valuation : NodeId → semantics.Value} (facts : List (NodeFact Fact))
    (meanings : FactMeanings semantics program valuation facts) :
    ∀ fact, fact ∈ facts → semantics.holds program valuation fact := by
  intro fact member
  induction facts with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact meanings.1
      · exact ih meanings.2 member

/-- Project a successful transparent domain check by ordinary reduction. -/
def checkedGet {α : Type} (result : Option α) (success : result.isSome = true) : α :=
  result.get success

/-- Combine the previous and proposed semantic facts through the domain's
checked meet theorem. -/
theorem holdsMeet {semantics : Semantics Fact} {program : Program}
    {valuation : NodeId → semantics.Value} {node : NodeId}
    {previous proposed installed : Fact}
    (meet : Evidence
      (∀ value, semantics.models program value →
        (semantics.holds program value { node, fact := installed } ↔
          semantics.holds program value { node, fact := previous } ∧
            semantics.holds program value { node, fact := proposed })))
    (model : semantics.models program valuation)
    (previousProof : semantics.holds program valuation { node, fact := previous })
    (proposedProof : semantics.holds program valuation { node, fact := proposed }) :
    semantics.holds program valuation { node, fact := installed } :=
  (meet.proof valuation model).mpr ⟨previousProof, proposedProof⟩

def installFact (domain : FactDomain Fact) (nodeDomain : DomainId)
    (current proposed : Fact) : Except String Fact :=
  match domain.narrow nodeDomain current proposed with
  | .noChange => pure current
  | .improved installed | .contradiction installed => pure installed
  | .malformed _ => throw "malformed caller interval fact"
  | .resourceLimit _ => throw "caller interval fact exceeded its resource bound"

/-- Prove the complete canonical base-fact premise from domain top and each
caller's ordered seed recipe. -/
def proveFacts [BEq Fact] (bridge : FactBridge Fact)
    (encoder : FrontendEncoder.Encoder Fact) (result : GoalFrontend.Result Fact)
    (base : BaseProof) (model : ModelProof) : MetaM Expr := do
  unless result.seeds.size == result.input.baseProgram.nodes.size &&
      result.baseFacts.length == result.input.baseProgram.nodes.size do
    throwError "interval goal closure: seed table does not cover the base graph"
  let mut proofs := []
  for index in [0:result.input.baseProgram.nodes.size] do
    let node : NodeId := { index }
    let some instruction := result.input.baseProgram.nodes[index]?
      | throwError "interval goal closure: fact node escaped its program"
    let some expression := termAt? result.terms node
      | throwError "interval goal closure: fact node has no Lean expression"
    let some seed := result.seeds[index]?
      | throwError "interval goal closure: fact node has no seed recipe"
    let some finalFact := result.baseFacts[index]?
      | throwError "interval goal closure: fact node has no canonical base fact"
    unless finalFact.node == node do
      throwError "interval goal closure: canonical base facts are out of order"
    let nodeTerm ← encoder.nodeId node
    let instructionTerm ← encoder.node instruction
    let someInstruction ← mkAppM ``Option.some #[instructionTerm]
    let found ← mkAppM ``Eq.refl #[someInstruction]
    let mut current := bridge.runtime.top instruction.domain
    let mut proof ←
      mkAppM ``FactDomainSchema.topSound
        #[bridge.schema, base.program, model.valuation, nodeTerm,
          instructionTerm, found, model.proof]
    for assumption in seed.assumptions do
      let proposedProof ← bridge.proveAssumption base.program model.valuation
        node assumption.fact expression assumption.proof
      let installed ←
        match installFact bridge.runtime instruction.domain current assumption.fact with
        | .ok installed => pure installed
        | .error message => throwError "interval goal closure: {message}"
      let meetResult ←
        mkAppM ``FactDomainSchema.proveMeet
          #[bridge.schema, base.program, nodeTerm,
            ← encoder.fact current, ← encoder.fact assumption.fact,
            ← encoder.fact installed]
      let success ← mkAppM ``Eq.refl #[mkConst ``Bool.true]
      let meet ← mkAppM ``checkedGet #[meetResult, success]
      proof ← mkAppM ``holdsMeet #[meet, model.proof, proof, proposedProof]
      current := installed
    unless current == finalFact.fact do
      throwError "interval goal closure: seed recipe does not produce its base fact"
    proofs := proofs.concat proof
  let mut meanings := mkConst ``True.intro
  for proof in proofs.reverse do
    meanings ← mkAppM ``And.intro #[proof, meanings]
  mkAppM ``FactMeanings.all #[base.facts, meanings]

/-- Quote a checker input with the same fact encoder used for proof events. -/
def inputExpr (factType : Expr) (encoder : FrontendEncoder.Encoder Fact)
    (input : CheckerInput Fact) : MetaM Expr := do
  let facts ← input.initialFacts.toList.mapM encoder.fact
  mkAppM ``CheckerInput.mk
    #[← encoder.program input.baseProgram,
      ← arrayExpr factType facts,
      ← encoder.nodeFact input.target]

/-- Construct the generic reflexive proof context for a reified base graph. -/
def proveBase (factType semantics : Expr)
    (encoder : FrontendEncoder.Encoder Fact) (input : CheckerInput Fact) :
    MetaM BaseProof := do
  unless input.initialFacts.size == input.baseProgram.nodes.size do
    throwError "interval goal closure: initial facts do not cover the base graph"
  let inputTerm ← inputExpr factType encoder input
  let program ← encoder.program input.baseProgram
  let facts ← mkAppM ``TraceReplay.initialBase #[inputTerm]
  let sizeEq ← mkAppM ``Eq.refl #[mkNatLit input.initialFacts.size]
  let within ← mkAppM ``TraceReplay.initialBaseWithin #[inputTerm, sizeEq]
  let basePrefix ← mkAppM ``ProgramPrefix.refl #[program]
  let extension ← mkAppM ``ChronologicalReplay.extendRefl #[semantics, program]
  let operations ← mkAppM ``Program.operations #[program]
  let sameOperations ← mkAppM ``Eq.refl #[operations]
  pure
    { input := inputTerm
      program
      facts
      basePrefix
      within
      extension
      sameOperations }

def relationProof (models valuation : Expr) (packages : Array Package)
    (terms : Array TermRef) (node : NodeId) (instruction : Node) : MetaM Expr := do
  let some package := packages[instruction.op.index]?
    | throwError "interval goal closure: node operation has no meaning package"
  let some output := termAt? terms node
    | throwError "interval goal closure: reified node has no Lean expression"
  let mut arguments := []
  for argument in instruction.args do
    let some expression := termAt? terms argument
      | throwError "interval goal closure: instruction argument has no Lean expression"
    arguments := arguments.concat expression
  let relation ← package.prove arguments output
  let someModel ← mkAppM ``Option.some #[package.model]
  let found ← mkAppM ``Eq.refl #[someModel]
  mkAppM ``meaningOf
    #[models, valuation, ← nodeIdExpr node, ← nodeExpr instruction,
      package.model, found, relation]

/-- Construct a kernel proof for the semantic meaning of every reified node.

Runtime equality first pins the meaning packages to the program's operation
array.  The emitted equality and node-relation terms must then reduce and
typecheck; a recognizer cannot establish either fact by returning `true`. -/
def proveModel (valueType fallback : Expr) (packages : Array Package)
    (encoder : FrontendEncoder.Encoder Fact) (result : GoalFrontend.Result Fact) :
    MetaM ModelProof := do
  unless result.input.baseProgram.check do
    throwError "interval goal closure: reified program is not structurally valid"
  unless packages.map (fun package => package.operation) ==
      result.input.baseProgram.operations do
    throwError "interval goal closure: syntax and meaning operations are not aligned"
  unless result.terms.size == result.input.baseProgram.nodes.size do
    throwError "interval goal closure: term table does not cover every graph node"
  for index in [0:result.terms.size] do
    let some term := result.terms[index]?
      | throwError "interval goal closure: term index escaped its table"
    unless term.node.index == index do
      throwError "interval goal closure: term table is not in node order"
    let some instruction := result.input.baseProgram.nodes[index]?
      | throwError "interval goal closure: term index escaped its program"
    unless term.domain == instruction.domain do
      throwError "interval goal closure: term domain differs from its instruction"
  let values := result.terms.toList.map (fun term => term.expression)
  let valuesTerm := listExpr valueType values
  let valuation ← mkAppM ``valuationOf #[fallback, valuesTerm]
  let modelType ← mkAppM ``OperationSemantics.Model #[valueType]
  let models ← arrayExpr modelType (packages.toList.map (fun package => package.model))
  let program ← encoder.program result.input.baseProgram
  let programOperations ← mkAppM ``Program.operations #[program]
  let mut aligned := mkConst ``True.intro
  for package in packages.toList.reverse do
    aligned ← mkAppM ``And.intro #[package.aligned, aligned]
  let operations ←
    mkAppM ``OperationSemantics.operationsOfAligned
      #[models, programOperations, aligned]
  let mut meanings := mkConst ``True.intro
  for offset in [0:result.input.baseProgram.nodes.size] do
    let index := result.input.baseProgram.nodes.size - 1 - offset
    let some instruction := result.input.baseProgram.nodes[index]?
      | throwError "interval goal closure: node index escaped its program"
    let nodeProof ← relationProof models valuation packages result.terms
      { index } instruction
    meanings ← mkAppM ``And.intro #[nodeProof, meanings]
  let proof ←
    mkAppM ``OperationSemantics.modelsOfMeanings
      #[models, program, valuation, operations, meanings]
  pure { valuation, proof }

end Hex.Interval.Experiment.GoalClosure
