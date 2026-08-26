/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import HexInterval.Experiment.MixedFunctions
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

/-!
# Real semantics for the mixed sine/exponential canary

The sine package first proves a unit-range fact.  The exponential package can
only emit its upper bound when that exact fact is present, so its replay proof
must consume the sine event reconstructed by the generic frontend.
-/

namespace Hex.Interval.Experiment.MixedFunctions

open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .unit, x => -1 ≤ x ∧ x ≤ 1
  | .atMostThree, x => x ≤ 3
  | .empty, _ => False

def sourceModel : OperationSemantics.Model ℝ :=
  { operation := sourceOperation
    relation := fun inputs _ => inputs = [] }

def sineModel : OperationSemantics.Model ℝ :=
  { operation := sineOperation
    relation := fun inputs output =>
      match inputs with
      | [input] => output = Real.sin input
      | _ => False }

def expModel : OperationSemantics.Model ℝ :=
  { operation := expOperation
    relation := fun inputs output =>
      match inputs with
      | [input] => output = Real.exp input
      | _ => False }

def operationModels : Array (OperationSemantics.Model ℝ) :=
  #[sourceModel, sineModel, expModel]

def semantics : Semantics Bound :=
  OperationSemantics.semantics operationModels Contains

theorem containsMeet (left right : Bound) (x : ℝ) :
    Contains (left.meet right) x ↔ Contains left x ∧ Contains right x := by
  have unitThree : (-1 ≤ x ∧ x ≤ 1) → x ≤ 3 := fun bounds =>
    bounds.2.trans (by norm_num)
  cases left <;> cases right <;>
    simp_all [Bound.meet, Contains]

def boundSchema : FactDomainSchema semantics :=
  { top := fun _ => .all
    topSound := by
      intro _ _ _ _ _ _
      trivial
    proveMeet := fun _ _ previous proposed installed =>
      if exact : installed = previous.meet proposed then
        some
          { proof := by
              subst installed
              intro valuation _
              exact containsMeet previous proposed (valuation _) }
      else
        none }

def laws : Laws semantics :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change Contains fact (valuation left) ↔ Contains fact (valuation right)
      rw [values] }

def stableLaw : StableLaw semantics :=
  OperationSemantics.stableLaw operationModels Contains

theorem sineEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = ({ index := 1 } : OpId))
    (arguments : instruction.args = [input]) :
    semantics.Entails graph assumptions { node := output, fact := .unit } := by
  intro valuation model _
  change NodeId → ℝ at valuation
  obtain ⟨meaning, meaningAt, related⟩ :=
    model.2 output instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have outputEq : valuation output = Real.sin (valuation input) := by
    simpa [sineModel, arguments, List.map] using related
  change -1 ≤ valuation output ∧ valuation output ≤ 1
  rw [outputEq]
  exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

theorem expEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = ({ index := 2 } : OpId))
    (arguments : instruction.args = [input])
    (exactAssumptions :
      assumptions = [{ node := input, fact := .unit }]) :
    semantics.Entails graph assumptions
      { node := output, fact := .atMostThree } := by
  intro valuation model holds
  change NodeId → ℝ at valuation
  obtain ⟨meaning, meaningAt, related⟩ :=
    model.2 output instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have outputEq : valuation output = Real.exp (valuation input) := by
    simpa [expModel, arguments, List.map] using related
  have inputRange : Contains .unit (valuation input) :=
    holds { node := input, fact := .unit } (by simp [exactAssumptions])
  change valuation output ≤ 3
  rw [outputEq]
  exact (Real.exp_le_exp.mpr inputRange.2).trans Real.exp_one_lt_three.le

private theorem factWith (fact : NodeFact Bound) {value : Bound}
    (equal : fact.fact = value) :
    fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

def sineFactSchema : PackedFactSchema semantics where
  rule := sineRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body => if body == [Bound.unit.code] then some () else none
  replay := fun _ _ context _ =>
    if proposedFact : context.proposed.fact = .unit then
      match found : context.program.node? context.proposed.node with
      | some instruction =>
          if operation : instruction.op = ({ index := 1 } : OpId) then
            match arguments : instruction.args with
            | [input] =>
                some
                  { proof := by
                      rw [factWith context.proposed proposedFact]
                      exact sineEntails context.program context.assumptions
                        context.proposed.node instruction input found operation
                        arguments }
            | _ => none
          else none
      | none => none
    else none

def expFactSchema : PackedFactSchema semantics where
  rule := expRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body =>
    if body == [Bound.atMostThree.code] then some () else none
  replay := fun _ _ context _ =>
    if proposedFact : context.proposed.fact = .atMostThree then
      match found : context.program.node? context.proposed.node with
      | some instruction =>
          if operation : instruction.op = ({ index := 2 } : OpId) then
            match arguments : instruction.args with
            | [input] =>
                if exactAssumptions :
                    context.assumptions = [{ node := input, fact := .unit }] then
                  some
                    { proof := by
                        rw [factWith context.proposed proposedFact]
                        exact expEntails context.program context.assumptions
                          context.proposed.node instruction input found operation
                          arguments exactAssumptions }
                else none
            | _ => none
          else none
      | none => none
    else none

def sourceProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[] }
    emit := { schemas := [] } }

def sineProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[sineFactSchema] }
    emit :=
      { schemas :=
          [{ key := sineFactSchema.key, handle := ``sineFactSchema }] } }

def expProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[expFactSchema] }
    emit :=
      { schemas :=
          [{ key := expFactSchema.key, handle := ``expFactSchema }] } }

def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof, sineProof, expProof]

end Hex.Interval.Experiment.MixedFunctions
