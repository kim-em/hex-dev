/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Frontend
import HexIntervalMathlib.RuleConformance

/-!
# Supported arithmetic frontend conformance

The supported recursive frontend reconstructs the shared add/sub/mul prefix of
the independent rule canary, binds its exact source facts, replays the
quoted chronology, and closes conjunction, one-sided inequality, and equality
goals through ordinary kernel theorems.
-/

namespace Hex.IntervalMathlib.FrontendConformance

open Hex.Interval
open Hex.Interval.Proof

def limits : Frontend.Limits :=
  { maxSources := 2, maxOperations := 13, maxNodes := 5, maxDepth := 3 }
def config : Frontend.Config :=
  { rule := RuleConformance.config, reify := limits, proof := RuleConformance.proofLimits }

def term : Frontend.Term :=
  .mul (.add (.source 0) (.source 1)) (.sub (.source 0) (.source 1))

def result? := Frontend.reifyWithin config 2 term

def expectedProgram : Program :=
  { operations := RuleConformance.program.operations
    nodes := #[RuleConformance.node 0 [], RuleConformance.node 0 [],
      RuleConformance.node 2 [0, 1], RuleConformance.node 3 [0, 1],
      RuleConformance.node 4 [2, 3]] }

#guard
  match result? with
  | .ok result =>
      result.program == expectedProgram && result.target == RuleConformance.product &&
        result.entries.size == 5
  | .error _ => false

def result : Frontend.Result :=
  match result? with
  | .ok result => result
  | .error _ =>
      { program := expectedProgram
        target := RuleConformance.product
        entries := #[]
        sourceCount := 2 }

def input? := Frontend.inputWithin config RuleConformance.scope result
  #[RuleConformance.xFact, RuleConformance.yFact] RuleConformance.productFact

def input : Proof.Input Hex.Interval :=
  { scope := RuleConformance.scope
    program := expectedProgram
    facts := #[RuleConformance.xFact, RuleConformance.yFact, Hex.Interval.whole,
      Hex.Interval.whole, Hex.Interval.whole]
    target := { node := RuleConformance.product, fact := RuleConformance.productFact } }

#guard
  match input? with
  | .ok found => found == input
  | .error _ => false

def events : List (Proof.Event Hex.Interval) :=
  (Rule.quote RuleConformance.branch).take 3

#guard events.length == 3

def evidence? :=
  Frontend.replay config input events 0 expectedProgram
    (RuleConformance.seen RuleConformance.product 1)

#guard match evidence? with | .ok _ => true | .error _ => false

def shallow : Frontend.Config := { config with reify := { limits with maxDepth := 1 } }
def fewNodes : Frontend.Config := { config with reify := { limits with maxNodes := 4 } }
def fewSources : Frontend.Config := { config with reify := { limits with maxSources := 1 } }
def fewOperations : Frontend.Config :=
  { config with reify := { limits with maxOperations := 12 } }

#guard match Frontend.reifyWithin shallow 2 term with | .error .depthLimit => true | _ => false
#guard match Frontend.reifyWithin fewNodes 2 term with | .error .nodeLimit => true | _ => false
#guard match Frontend.reifyWithin fewSources 2 term with | .error .sourceLimit => true | _ => false
#guard
  match Frontend.reifyWithin fewOperations 2 term with
  | .error .operationLimit => true
  | _ => false
#guard
  match Frontend.reifyWithin config 2 (.source 2) with
  | .error (.sourceIndex 2) => true
  | _ => false
#guard
  match Frontend.inputWithin config RuleConformance.scope result #[RuleConformance.xFact]
      RuleConformance.productFact with
  | .error .wrongSourceCount => true
  | _ => false

def wrongEntryNode : Frontend.Result :=
  let bad : Frontend.Entry := { term := .source 0, node := { index := 1 } }
  { result with entries := result.entries.set! 0 bad }

def wrongEntryTerm : Frontend.Result :=
  let bad : Frontend.Entry :=
    { term := .mul (.source 0) (.source 1), node := { index := 2 } }
  { result with entries := result.entries.set! 2 bad }

def duplicateEntry : Frontend.Result :=
  let bad : Frontend.Entry := { term := .source 0, node := { index := 1 } }
  { result with entries := result.entries.set! 1 bad }

#guard
  match Frontend.inputWithin config RuleConformance.scope wrongEntryNode
      #[RuleConformance.xFact, RuleConformance.yFact] RuleConformance.productFact with
  | .error .malformedResult => true
  | _ => false
#guard
  match Frontend.inputWithin config RuleConformance.scope wrongEntryTerm
      #[RuleConformance.xFact, RuleConformance.yFact] RuleConformance.productFact with
  | .error .malformedResult => true
  | _ => false
#guard
  match Frontend.inputWithin config RuleConformance.scope duplicateEntry
      #[RuleConformance.xFact, RuleConformance.yFact] RuleConformance.productFact with
  | .error .malformedResult => true
  | _ => false

#guard
  match Frontend.reifyWithin config 1 (.add .constant (.source 0)) with
  | .ok result => result.program.nodes ==
      #[RuleConformance.node 9 [], RuleConformance.node 0 [], RuleConformance.node 2 [0, 1]]
  | .error _ => false

#guard
  match Frontend.reifyWithin config 2
      (.regularize (.div (.inv (.source 0)) (.source 1))) with
  | .ok result => result.program.nodes ==
      #[RuleConformance.node 0 [], RuleConformance.node 10 [0],
        RuleConformance.node 0 [], RuleConformance.node 11 [1, 2],
        RuleConformance.node 12 [3]]
  | .error _ => false

def duplicateKey : Frontend.Config :=
  { rule := { config.rule with extraMeanings := #[Rule.sourceMeaning] }
    reify := { limits with maxOperations := 14 }
    proof := config.proof }

#guard
  match Frontend.reifyWithin duplicateKey 1 (.source 0) with
  | .error .malformedProgram => true
  | _ => false

theorem productReady :
    singletonWithin RuleConformance.endpoint (RuleConformance.d (-3)) =
      .ready RuleConformance.productFact :=
  Rule.ready?_eq (by rfl)

theorem productShape : RuleConformance.productFact.view =
    .bounds (.finite (RuleConformance.d (-3)) false)
      (.finite (RuleConformance.d (-3)) false) := by
  simpa [Raw.normalizeUnchecked, Raw.consistent] using
    view_singletonWithin_ready productReady

private theorem eq_of_mem_singleton {value : Dyadic} {result : Hex.Interval} {z : ℝ}
    (checked : Hex.Interval.singletonWithin RuleConformance.endpoint value = .ready result)
    (member : result.Contains z) : z = Hex.Interval.toReal value := by
  change result.view.Contains z at member
  rw [Hex.Interval.view_singletonWithin_ready checked,
    Hex.Interval.contains_normalize] at member
  exact le_antisymm member.2 member.1

private theorem toReal_d (value : Int) :
    Hex.Interval.toReal (RuleConformance.d value) = value := by
  change ((Dyadic.ofInt value).toRat : ℝ) = value
  rw [show Dyadic.ofInt value = (value : Dyadic) by rfl, Dyadic.toRat_intCast]
  norm_num

def fallbackEvidence : Proof.Evidence
    ((Rule.semantics config.rule).Entails input.program
      (Proof.initialBase input) input.target) :=
  { proof := by
      intro valuation model assumptions
      change NodeId → ℝ at valuation
      have xMember : RuleConformance.xFact.Contains (valuation RuleConformance.x) := by
        exact assumptions { node := RuleConformance.x, fact := RuleConformance.xFact } (by
          simp [Proof.initialBase, input, RuleConformance.x])
      have yMember : RuleConformance.yFact.Contains (valuation RuleConformance.y) := by
        exact assumptions { node := RuleConformance.y, fact := RuleConformance.yFact } (by
          simp [Proof.initialBase, input, RuleConformance.y])
      have sumRelation : valuation RuleConformance.sum =
          valuation RuleConformance.x + valuation RuleConformance.y :=
        Rule.binaryRelation (config := config.rule) (valuation := valuation)
          (node := RuleConformance.sum) (left := RuleConformance.x)
          (right := RuleConformance.y) (index := 2)
          (relation := fun left right => left + right)
          (Rule.nodeMeaning config.rule model (node := RuleConformance.sum) (by rfl))
          (Or.inl ⟨rfl, rfl⟩)
      have subRelation : valuation RuleConformance.difference =
          valuation RuleConformance.x - valuation RuleConformance.y :=
        Rule.binaryRelation (config := config.rule) (valuation := valuation)
          (node := RuleConformance.difference) (left := RuleConformance.x)
          (right := RuleConformance.y) (index := 3)
          (relation := fun left right => left - right)
          (Rule.nodeMeaning config.rule model (node := RuleConformance.difference) (by rfl))
          (Or.inr (Or.inl ⟨rfl, rfl⟩))
      have mulRelation : valuation RuleConformance.product =
          valuation RuleConformance.sum * valuation RuleConformance.difference :=
        Rule.binaryRelation (config := config.rule) (valuation := valuation)
          (node := RuleConformance.product) (left := RuleConformance.sum)
          (right := RuleConformance.difference) (index := 4)
          (relation := fun left right => left * right)
          (Rule.nodeMeaning config.rule model (node := RuleConformance.product) (by rfl))
          (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      have xEq := eq_of_mem_singleton RuleConformance.checkedX xMember
      have yEq := eq_of_mem_singleton RuleConformance.checkedY yMember
      rw [toReal_d] at xEq yEq
      have productEq : valuation RuleConformance.product = -3 := by
        rw [mulRelation, sumRelation, subRelation, xEq, yEq]
        norm_num
      change RuleConformance.productFact.Contains (valuation RuleConformance.product)
      rw [productEq]
      have member := Rule.constant_mem productReady
      rw [toReal_d] at member
      simpa using member }

def evidence : Proof.Evidence
    ((Rule.semantics config.rule).Entails input.program
      (Proof.initialBase input) input.target) :=
  match evidence? with
  | .ok found => found
  | .error _ => fallbackEvidence

theorem closesConjunction (valuation : NodeId → ℝ)
    (model : Program.Models (Rule.meanings config.rule) input.program valuation)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (valuation fact.node)) :
    (Lower.finite (RuleConformance.d (-3)) false).Contains
        (valuation RuleConformance.product) ∧
      (Upper.finite (RuleConformance.d (-3)) false).Contains
        (valuation RuleConformance.product) := by
  exact Frontend.closeBounds config input evidence valuation model assumptions
    (.finite (RuleConformance.d (-3)) false)
    (.finite (RuleConformance.d (-3)) false) productShape

theorem closesLower (valuation : NodeId → ℝ)
    (model : Program.Models (Rule.meanings config.rule) input.program valuation)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (valuation fact.node)) :
    toReal (RuleConformance.d (-3)) ≤ valuation RuleConformance.product := by
  exact Frontend.closeLower config input evidence valuation model assumptions
    (RuleConformance.d (-3)) false (.finite (RuleConformance.d (-3)) false) productShape

theorem closesEquality (valuation : NodeId → ℝ)
    (model : Program.Models (Rule.meanings config.rule) input.program valuation)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (valuation fact.node)) :
    valuation RuleConformance.product = toReal (RuleConformance.d (-3)) := by
  exact Frontend.closeSingleton config input evidence valuation model assumptions
    (RuleConformance.d (-3)) productShape

#print axioms closesConjunction
#print axioms closesLower
#print axioms closesEquality

end Hex.IntervalMathlib.FrontendConformance
