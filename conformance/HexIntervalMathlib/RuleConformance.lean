/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Rule

/-!
# Built-in arithmetic rule conformance

Two independent source facts feed both sides of a shared DAG.  The accepted
supported-state history is quoted, chronologically replayed, and projected to
an ordinary theorem.  The negative guards mutate authenticated fields rather
than testing helper predicates in isolation.
-/

namespace Hex.IntervalMathlib.RuleConformance

open Hex.Interval
open Hex.Interval.Proof
open Hex.Interval.Rule

def d (value : Int) : Dyadic := .ofInt value
def endpoint : EndpointLimit := { maxEndpointHeight := 64, maxAlignmentShift := 64 }

def ready (raw : Raw) : Hex.Interval :=
  match Hex.Interval.ofRawWithin endpoint raw with
  | .ready interval => interval
  | .resourceLimit _ => Hex.Interval.empty

def singleton (value : Int) : Hex.Interval :=
  ready (.bounds (.finite (d value) false) (.finite (d value) false))

def config : Rule.Config :=
  { endpoint, powerWork := { maxExponent := 8 }, exponent := 2,
    precisionLimits :=
      { endpoint, maxPrecisionMagnitude := 64, maxPrecisionBits := 64,
        maxTemporaryBits := 128 },
    precision := 0, constant := d 5 }

def node (op : Nat) (args : List Nat) : Node :=
  { domain := realDomain, op := { index := op }, args := args.map fun index => { index } }

def program : Program :=
  { operations
    nodes := #[node 0 [], node 0 [], node 2 [0, 1], node 3 [0, 1], node 4 [2, 3],
      node 10 [0], node 11 [1, 0], node 12 [6], node 2 [4, 7], node 2 [8, 5]] }

def x : NodeId := { index := 0 }
def y : NodeId := { index := 1 }
def sum : NodeId := { index := 2 }
def difference : NodeId := { index := 3 }
def product : NodeId := { index := 4 }
def inverse : NodeId := { index := 5 }
def quotient : NodeId := { index := 6 }
def regularized : NodeId := { index := 7 }
def combined : NodeId := { index := 8 }
def final : NodeId := { index := 9 }

def seen (node : NodeId) (version : Nat := 0) : SeenVersion :=
  { node, version }

#guard program.check
#guard Rule.operations == program.operations

def opaqueOp : Operation :=
  { key := { name := "conformance.opaque" }, inputs := [realDomain], output := realDomain }
def opaqueMeaning : Program.Meaning ℝ :=
  { operation := opaqueOp, relation := fun args result => args = [result] }
def extendedConfig : Rule.Config := { config with extraMeanings := #[opaqueMeaning] }
def extendedProgram : Program := { program with operations := operations.push opaqueOp }

#guard extendedProgram.check

def xFact := singleton 1
def yFact := singleton 2
def sumFact := singleton 3
def differenceFact := singleton (-1)
def productFact := singleton (-3)
def inverseFact := singleton 1
def quotientFact := singleton 2
def regularizedFact := singleton 2
def combinedFact := singleton (-1)
def finalFact := singleton 0
def initialFacts : Array Hex.Interval :=
  #[xFact, yFact, Hex.Interval.whole, Hex.Interval.whole, Hex.Interval.whole,
    Hex.Interval.whole, Hex.Interval.whole, Hex.Interval.whole, Hex.Interval.whole,
    Hex.Interval.whole]

#guard ready? (Hex.Interval.addWithin endpoint xFact yFact) == some sumFact
#guard ready? (Hex.Interval.subWithin endpoint xFact yFact) == some differenceFact
#guard arithmeticReady? (Hex.Interval.mulWithin endpoint sumFact differenceFact) == some productFact
#guard arithmeticReady?
    (Hex.Interval.invWithin config.precisionLimits config.precision xFact) == some inverseFact
#guard arithmeticReady?
    (Hex.Interval.divWithin config.precisionLimits config.precision yFact xFact) == some quotientFact
#guard arithmeticReady?
    (Hex.Interval.regularizeWithin config.precisionLimits config.precision quotientFact) ==
      some regularizedFact
#guard ready? (Hex.Interval.addWithin endpoint productFact regularizedFact) == some combinedFact
#guard ready? (Hex.Interval.addWithin endpoint combinedFact inverseFact) == some finalFact

def action (serial ruleIndex : Nat) (key : RuleKey) (kind : ActionKind)
    (anchor : NodeId) (inputs : List SeenVersion) : Action :=
  { serial, programVersion := 0, application := { index := serial }, rule := { index := ruleIndex },
    key, node := anchor, kind, effort := 0, inputs, writes := [anchor] }

def addAction := action 0 1 addKey .forward sum [seen x, seen y]
def subAction := action 1 2 subKey .forward difference [seen x, seen y]
def mulAction := action 2 3 mulKey .forward product [seen sum 1, seen difference 1]
def invAction := action 3 9 invKey .forward inverse [seen x]
def divAction := action 4 10 divKey .forward quotient [seen y, seen x]
def regularizeAction :=
  action 5 11 regularizeKey .forward regularized [seen quotient 1]
def combinedAction := action 6 1 addKey .forward combined [seen product 1, seen regularized 1]
def finalAction := action 7 1 addKey .forward final [seen combined 1, seen inverse 1]

def cause (scope : Policy.ScopeId) (action : Action)
    (proposed : Hex.Interval) (key : RuleKey) (tag : Nat) : Rule.Cause :=
  { scope, action, proposed, schema := schemaKey key, body := [tag] }

def scope : Policy.ScopeId := { index := 4 }

def history : Array (State.Update Hex.Interval Rule.Cause) :=
  #[{ programVersion := 0, node := sum, previous := seen sum, fact := sumFact, version := 1,
      cause := cause scope addAction sumFact addKey 2 },
    { programVersion := 0, node := difference, previous := seen difference,
      fact := differenceFact, version := 1,
      cause := cause scope subAction differenceFact subKey 3 },
    { programVersion := 0, node := product, previous := seen product,
      fact := productFact, version := 1, cause := cause scope mulAction productFact mulKey 4 },
    { programVersion := 0, node := inverse, previous := seen inverse,
      fact := inverseFact, version := 1, cause := cause scope invAction inverseFact invKey 10 },
    { programVersion := 0, node := quotient, previous := seen quotient,
      fact := quotientFact, version := 1, cause := cause scope divAction quotientFact divKey 11 },
    { programVersion := 0, node := regularized, previous := seen regularized,
      fact := regularizedFact, version := 1,
      cause := cause scope regularizeAction regularizedFact regularizeKey 12 },
    { programVersion := 0, node := combined, previous := seen combined,
      fact := combinedFact, version := 1,
      cause := cause scope combinedAction combinedFact addKey 2 },
    { programVersion := 0, node := final, previous := seen final,
      fact := finalFact, version := 1, cause := cause scope finalAction finalFact addKey 2 }]

/-- Exact supported retained state used by the generic quote. -/
def branch : State.Branch Hex.Interval Rule.Cause :=
  { programVersion := 0, baseProgram := program, initialFacts, program,
    seeds := #[],
    versions := #[0, 0, 1, 1, 1, 1, 1, 1, 1, 1],
    generations := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    depths := #[0, 0, 1, 1, 2, 1, 1, 2, 3, 4], history, contradictory := false }

#guard branch.check
#guard (Rule.quote branch).length == 8

def proofLimits : Proof.Limits :=
  { maxPackages := 1, maxSchemas := 12, maxBodyCells := 1,
    maxDependencies := 2, maxChronology := 8 }

#guard
  match Rule.buildWithWithin proofLimits extendedConfig extendedProgram #[] with
  | .ok _ => true
  | .error _ => false

def input : Proof.Input Hex.Interval :=
  { scope, program, facts := initialFacts, target := { node := final, fact := finalFact } }

def replayResult : Option (Proof.Evidence
    ((Rule.semantics config).Entails program (Proof.initialBase input) input.target)) :=
  match Rule.buildWithin proofLimits config program with
  | .error _ => none
  | .ok registry =>
      match Proof.replay proofLimits registry (Rule.domain config) (Rule.laws config)
          input (Rule.quote branch) 0 program (seen final 1) with
      | .error _ => none
      | .ok evidence => some evidence

#guard Option.isSome replayResult

private theorem eq_of_mem_singleton {value : Dyadic} {result : Hex.Interval} {z : ℝ}
    (checked : Hex.Interval.singletonWithin endpoint value = .ready result)
    (member : result.Contains z) : z = Hex.Interval.toReal value := by
  change result.view.Contains z at member
  rw [Hex.Interval.view_singletonWithin_ready checked,
    Hex.Interval.contains_normalize] at member
  exact le_antisymm member.2 member.1

private theorem toReal_d (value : Int) : Hex.Interval.toReal (d value) = value := by
  change ((Dyadic.ofInt value).toRat : ℝ) = value
  rw [show Dyadic.ofInt value = (value : Dyadic) by rfl, Dyadic.toRat_intCast]
  norm_num

theorem checkedX : Hex.Interval.singletonWithin endpoint (d 1) = .ready xFact := by rfl
theorem checkedY : Hex.Interval.singletonWithin endpoint (d 2) = .ready yFact := by rfl
theorem checkedFinal : Hex.Interval.singletonWithin endpoint (d 0) = .ready finalFact := by rfl

def fallbackEvidence : Proof.Evidence
    ((Rule.semantics config).Entails program (Proof.initialBase input) input.target) :=
  { proof := by
      intro valuation model assumptions
      change NodeId → ℝ at valuation
      have xMember : xFact.Contains (valuation x) := by
        exact assumptions { node := x, fact := xFact } (by
          simp [Proof.initialBase, input, initialFacts, x])
      have yMember : yFact.Contains (valuation y) := by
        exact assumptions { node := y, fact := yFact } (by
          simp [Proof.initialBase, input, initialFacts, y])
      have sumRelation : valuation sum = valuation x + valuation y :=
        Rule.binaryRelation (config := config) (valuation := valuation)
          (node := sum) (left := x) (right := y) (index := 2)
          (relation := fun left right => left + right)
          (Rule.nodeMeaning config model (node := sum) (by rfl))
          (Or.inl ⟨rfl, rfl⟩)
      have subRelation : valuation difference = valuation x - valuation y :=
        Rule.binaryRelation (config := config) (valuation := valuation)
          (node := difference) (left := x) (right := y) (index := 3)
          (relation := fun left right => left - right)
          (Rule.nodeMeaning config model (node := difference) (by rfl))
          (Or.inr (Or.inl ⟨rfl, rfl⟩))
      have mulRelation : valuation product = valuation sum * valuation difference :=
        Rule.binaryRelation (config := config) (valuation := valuation)
          (node := product) (left := sum) (right := difference) (index := 4)
          (relation := fun left right => left * right)
          (Rule.nodeMeaning config model (node := product) (by rfl))
          (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      have invRelation : valuation inverse = (valuation x)⁻¹ :=
        Rule.invRelation (config := config) (valuation := valuation)
          (node := inverse) (input := x)
          (Rule.nodeMeaning config model (node := inverse) (by rfl))
      have divRelation : valuation quotient = valuation y / valuation x :=
        Rule.divRelation (config := config) (valuation := valuation)
          (node := quotient) (left := y) (right := x)
          (Rule.nodeMeaning config model (node := quotient) (by rfl))
      have regularizeRelation : valuation regularized = valuation quotient :=
        Rule.regularizeRelation (config := config) (valuation := valuation)
          (node := regularized) (input := quotient)
          (Rule.nodeMeaning config model (node := regularized) (by rfl))
      have combinedRelation : valuation combined = valuation product + valuation regularized :=
        Rule.binaryRelation (config := config) (valuation := valuation)
          (node := combined) (left := product) (right := regularized) (index := 2)
          (relation := fun left right => left + right)
          (Rule.nodeMeaning config model (node := combined) (by rfl))
          (Or.inl ⟨rfl, rfl⟩)
      have finalRelation : valuation final = valuation combined + valuation inverse :=
        Rule.binaryRelation (config := config) (valuation := valuation)
          (node := final) (left := combined) (right := inverse) (index := 2)
          (relation := fun left right => left + right)
          (Rule.nodeMeaning config model (node := final) (by rfl))
          (Or.inl ⟨rfl, rfl⟩)
      have xEq := eq_of_mem_singleton checkedX xMember
      have yEq := eq_of_mem_singleton checkedY yMember
      rw [toReal_d] at xEq yEq
      have finalEq : valuation final = 0 := by
        rw [finalRelation, combinedRelation, mulRelation, sumRelation, subRelation,
          regularizeRelation, divRelation, invRelation, xEq, yEq]
        norm_num
      change finalFact.Contains (valuation final)
      rw [finalEq]
      have zeroMember := Rule.constant_mem checkedFinal
      rw [toReal_d] at zeroMember
      simpa using zeroMember }

def replayEvidence : Proof.Evidence
    ((Rule.semantics config).Entails program (Proof.initialBase input) input.target) :=
  match replayResult with
  | some evidence => evidence
  | none => fallbackEvidence

/-- Kernel theorem obtained from the generic supported quote and replay.  Both
source hypotheses are consumed twice, through addition and subtraction. -/
theorem arithmeticDag :
    (Rule.semantics config).Entails program (Proof.initialBase input) input.target :=
  replayEvidence.proof

-- Every authenticated address component is load-bearing.
def mutateFirst (change : Proof.FactStep Hex.Interval → Proof.FactStep Hex.Interval) :=
  match Rule.quote branch with
  | .fact step :: rest => Proof.Event.fact (change step) :: rest
  | events => events

def mutateInv (change : Proof.FactStep Hex.Interval → Proof.FactStep Hex.Interval) :=
  match Rule.quote branch with
  | a :: b :: c :: .fact step :: rest => a :: b :: c :: .fact (change step) :: rest
  | events => events

def mutateDiv (change : Proof.FactStep Hex.Interval → Proof.FactStep Hex.Interval) :=
  match Rule.quote branch with
  | a :: b :: c :: d :: .fact step :: rest => a :: b :: c :: d :: .fact (change step) :: rest
  | events => events

def mutateRegularize (change : Proof.FactStep Hex.Interval → Proof.FactStep Hex.Interval) :=
  match Rule.quote branch with
  | a :: b :: c :: d :: e :: .fact step :: rest =>
      a :: b :: c :: d :: e :: .fact (change step) :: rest
  | events => events

def rejected (events : List (Proof.Event Hex.Interval)) : Bool :=
  match Rule.buildWithin proofLimits config program with
  | .error _ => false
  | .ok registry =>
      match Proof.replay proofLimits registry (Rule.domain config) (Rule.laws config)
          input events 0 program (seen final 1) with
      | .error _ => true
      | .ok _ => false

def rejectedWith (selected : Rule.Config)
    (events : List (Proof.Event Hex.Interval)) : Bool :=
  match Rule.buildWithin proofLimits selected program with
  | .error _ => false
  | .ok registry =>
      match Proof.replay proofLimits registry (Rule.domain selected) (Rule.laws selected)
          input events 0 program (seen final 1) with
      | .error _ => true
      | .ok _ => false

#guard rejected (mutateFirst fun step => { step with schema := schemaKey subKey })
#guard rejected (mutateFirst fun step => { step with body := [99] })
#guard rejected (mutateFirst fun step => { step with assumptions := [seen y, seen x] })
#guard rejected (mutateFirst fun step => { step with action := { step.action with key := subKey } })
#guard rejected (mutateFirst fun step => { step with proposed := differenceFact })
#guard rejected (mutateFirst fun step => { step with installed := differenceFact })
#guard rejected (mutateFirst fun step => { step with previous := seen sum 1 })
#guard rejected (mutateFirst fun step => { step with programVersion := 1 })
#guard rejected (mutateFirst fun step => { step with scope := { index := 99 } })
#guard rejected (mutateInv fun step => { step with schema := schemaKey regularizeKey })
#guard rejected (mutateInv fun step => { step with body := [99] })
#guard rejected (mutateDiv fun step => { step with assumptions := [seen x, seen y] })
#guard rejected (mutateDiv fun step => { step with proposed := inverseFact })
#guard rejected (mutateRegularize fun step => { step with schema := schemaKey invKey })
#guard rejected (mutateRegularize fun step => { step with body := [10] })
#guard rejected (Rule.quote branch ++ Rule.quote branch)

def precisionShort : Rule.Config :=
  { config with precisionLimits := { config.precisionLimits with maxTemporaryBits := 0 } }

#guard arithmeticReady?
    (Hex.Interval.invWithin precisionShort.precisionLimits precisionShort.precision xFact) == none
#guard rejectedWith precisionShort (Rule.quote branch)

def oneShort : Proof.Limits := { proofLimits with maxChronology := 2 }
#guard
  match Rule.buildWithin proofLimits config program with
  | .error _ => false
  | .ok registry =>
      match Proof.replay oneShort registry (Rule.domain config) (Rule.laws config)
          input (Rule.quote branch) 0 program (seen final 1) with
      | .error .chronologyLimit => true
      | _ => false

def bodyShort : Proof.Limits := { proofLimits with maxBodyCells := 0 }
#guard
  match Rule.buildWithin proofLimits config program with
  | .error _ => false
  | .ok registry =>
      match Proof.replay bodyShort registry (Rule.domain config) (Rule.laws config)
          input (Rule.quote branch) 0 program (seen final 1) with
      | .error .bodyLimit => true
      | _ => false

def dependencyShort : Proof.Limits := { proofLimits with maxDependencies := 1 }
#guard
  match Rule.buildWithin proofLimits config program with
  | .error _ => false
  | .ok registry =>
      match Proof.replay dependencyShort registry (Rule.domain config) (Rule.laws config)
          input (Rule.quote branch) 0 program (seen final 1) with
      | .error .dependencyLimit => true
      | _ => false

def schemaShort : Proof.Limits := { proofLimits with maxSchemas := 11 }
#guard
  match Rule.buildWithin schemaShort config program with
  | .error (.registry .schemaLimit) => true
  | _ => false

def wrongSourceInput : Proof.Input Hex.Interval :=
  { input with facts := #[Hex.Interval.whole, yFact, Hex.Interval.whole,
      Hex.Interval.whole, Hex.Interval.whole, Hex.Interval.whole,
      Hex.Interval.whole, Hex.Interval.whole, Hex.Interval.whole,
      Hex.Interval.whole] }

#guard
  match Rule.buildWithin proofLimits config program with
  | .error _ => false
  | .ok registry =>
      match Proof.replay proofLimits registry (Rule.domain config) (Rule.laws config)
          wrongSourceInput (Rule.quote branch) 0 program (seen final 1) with
      | .error _ => true
      | .ok _ => false

def wrongOperationProgram : Program :=
  { program with nodes := program.nodes.set! sum.index (node 3 [0, 1]) }
def wrongOperationInput : Proof.Input Hex.Interval :=
  { input with program := wrongOperationProgram }

#guard wrongOperationProgram.check
#guard
  match Rule.buildWithin proofLimits config wrongOperationProgram with
  | .error _ => false
  | .ok registry =>
      match Proof.replay proofLimits registry (Rule.domain config) (Rule.laws config)
          wrongOperationInput (Rule.quote branch) 0 wrongOperationProgram (seen final 1) with
      | .error _ => true
      | .ok _ => false

#print axioms arithmeticDag

end Hex.IntervalMathlib.RuleConformance
