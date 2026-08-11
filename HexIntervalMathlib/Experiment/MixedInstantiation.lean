/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import HexInterval.Experiment.MixedInstantiation
public import HexIntervalMathlib.Experiment.MixedFunctions
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

/-!
# Real semantics for mixed-function instantiation
-/

namespace Hex.Interval.Experiment.MixedInstantiation

open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

def Contains : Bound → ℝ → Prop := MixedFunctions.Contains

def sourceModel : OperationSemantics.Model ℝ :=
  { operation := sourceOperation
    relation := fun inputs _ => inputs = [] }

def negationModel : OperationSemantics.Model ℝ :=
  { operation := negationOperation
    relation := fun inputs output =>
      match inputs with
      | [input] => output = -input
      | _ => False }

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
  #[sourceModel, negationModel, sineModel, expModel]

def semantics : Semantics Bound :=
  OperationSemantics.semantics operationModels Contains

theorem containsMeet (left right : Bound) (x : ℝ) :
    Contains (MixedFunctions.Bound.meet left right) x ↔
      Contains left x ∧ Contains right x := by
  exact MixedFunctions.containsMeet left right x

def boundSchema : FactDomainSchema semantics :=
  { top := fun _ => .all
    topSound := by
      intro _ _ _ _ _ _
      trivial
    proveMeet := fun _ _ previous proposed installed =>
      if exact : installed = MixedFunctions.Bound.meet previous proposed then
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
    (operation : instruction.op = ({ index := 2 } : OpId))
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

theorem negationEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = ({ index := 1 } : OpId))
    (arguments : instruction.args = [input])
    (exactAssumptions : assumptions = [{ node := input, fact := .unit }]) :
    semantics.Entails graph assumptions { node := output, fact := .unit } := by
  intro valuation model holds
  change NodeId → ℝ at valuation
  obtain ⟨meaning, meaningAt, related⟩ :=
    model.2 output instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have outputEq : valuation output = -valuation input := by
    simpa [negationModel, arguments, List.map] using related
  have inputRange : Contains .unit (valuation input) :=
    holds { node := input, fact := .unit } (by simp [exactAssumptions])
  change -1 ≤ valuation output ∧ valuation output ≤ 1
  rw [outputEq]
  exact ⟨neg_le_neg inputRange.2, neg_le.mp inputRange.1⟩

theorem expEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = ({ index := 3 } : OpId))
    (arguments : instruction.args = [input])
    (exactAssumptions : assumptions = [{ node := input, fact := .unit }]) :
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

theorem programPrefix : ProgramPrefix baseProgram extendedProgram := by
  refine
    { operationSize := by simp [baseProgram, extendedProgram]
      nodeSize := by simp [baseProgram, extendedProgram]
      operationAt := ?_
      nodeAt := ?_ }
  · intro index within
    simp [baseProgram, extendedProgram]
  · intro index within
    cases index with
    | zero => rfl
    | succ index =>
        cases index with
        | zero => rfl
        | succ index =>
            cases index with
            | zero => rfl
            | succ index =>
                cases index with
                | zero => rfl
                | succ index =>
                    have lower : 4 ≤ index + 1 + 1 + 1 + 1 :=
                      Nat.le_add_left 4 index
                    exact False.elim (Nat.not_lt_of_ge lower (by
                      simpa [baseProgram] using within))

theorem sameOperations : baseProgram.operations = extendedProgram.operations := rfl

noncomputable def extendValuation (valuation : NodeId → ℝ) : NodeId → ℝ :=
  fun observed =>
    if observed = node 4 then Real.sin (valuation (node 0))
    else if observed = node 5 then -Real.sin (valuation (node 0))
    else valuation observed

theorem extension : semantics.Extends baseProgram extendedProgram := by
  intro valuation model
  obtain ⟨oldMeaning0, oldAt0, oldRelated0⟩ :=
    model.2 (node 0) sourceInstruction (by rfl)
  obtain ⟨oldMeaning1, oldAt1, oldRelated1⟩ :=
    model.2 (node 1) negatedSourceInstruction (by rfl)
  obtain ⟨oldMeaning2, oldAt2, oldRelated2⟩ :=
    model.2 (node 2) sineNegatedSourceInstruction (by rfl)
  obtain ⟨oldMeaning3, oldAt3, oldRelated3⟩ :=
    model.2 (node 3) expSineInstruction (by rfl)
  simp [operationModels, sourceInstruction] at oldAt0
  simp [operationModels, negatedSourceInstruction] at oldAt1
  simp [operationModels, sineNegatedSourceInstruction] at oldAt2
  simp [operationModels, expSineInstruction] at oldAt3
  subst oldMeaning0
  subst oldMeaning1
  subst oldMeaning2
  subst oldMeaning3
  refine ⟨extendValuation valuation, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa [baseProgram, extendedProgram] using model.1
    · intro observed instruction found
      rcases observed with ⟨index⟩
      cases index with
      | zero =>
          simp [extendedProgram, baseProgram, Program.node?] at found
          subst instruction
          refine ⟨sourceModel, by rfl, ?_⟩
          simp [sourceModel, sourceInstruction, extendValuation, node] at oldRelated0 ⊢
      | succ index =>
          cases index with
          | zero =>
              simp [extendedProgram, baseProgram, Program.node?] at found
              subst instruction
              refine ⟨negationModel, by rfl, ?_⟩
              simpa [negationModel, negatedSourceInstruction, extendValuation, node,
                List.map] using oldRelated1
          | succ index =>
              cases index with
              | zero =>
                  simp [extendedProgram, baseProgram, Program.node?] at found
                  subst instruction
                  refine ⟨sineModel, by rfl, ?_⟩
                  simpa [sineModel, sineNegatedSourceInstruction, extendValuation, node,
                    List.map] using oldRelated2
              | succ index =>
                  cases index with
                  | zero =>
                      simp [extendedProgram, baseProgram, Program.node?] at found
                      subst instruction
                      refine ⟨expModel, by rfl, ?_⟩
                      simpa [expModel, expSineInstruction, extendValuation, node,
                        List.map] using oldRelated3
                  | succ index =>
                      cases index with
                      | zero =>
                          simp [extendedProgram, baseProgram, Program.node?] at found
                          subst instruction
                          refine ⟨sineModel, by rfl, ?_⟩
                          simp [sineModel, sineSourceInstruction, extendValuation, node,
                            List.map]
                      | succ index =>
                          cases index with
                          | zero =>
                              simp [extendedProgram, baseProgram, Program.node?] at found
                              subst instruction
                              refine ⟨negationModel, by rfl, ?_⟩
                              simp [negationModel, negatedSineInstruction,
                                extendValuation, node, List.map]
                          | succ index =>
                              simp [extendedProgram, baseProgram, Program.node?] at found
  · intro observed within
    have notFour : observed ≠ node 4 := by
      intro equal
      subst observed
      simp [baseProgram, node] at within
    have notFive : observed ≠ node 5 := by
      intro equal
      subst observed
      simp [baseProgram, node] at within
    simp [extendValuation, notFour, notFive]

def stable : StableStep semantics baseProgram extendedProgram :=
  stableLaw.stable (by rfl) (by rfl) programPrefix sameOperations

theorem targetWithin : (node 3).index < baseProgram.nodes.size := by
  decide

/-- Pull a proof over the instantiated graph back to the exact caller graph. -/
def closeEvidence {base : List (NodeFact Bound)}
    (baseWithin : FactsWithin baseProgram base)
    (extensionEvidence : Evidence (semantics.Extends baseProgram extendedProgram))
    (final : Evidence (semantics.Entails extendedProgram base checkerInput.target)) :
    Evidence (semantics.Entails baseProgram base checkerInput.target) :=
  closeBase (input := checkerInput) stable baseWithin targetWithin
    extensionEvidence final

theorem oddnessEntails :
    semantics.EntailsEq extendedProgram [] (node 2) (node 5) := by
  intro valuation model _
  change NodeId → ℝ at valuation
  obtain ⟨negMeaning, negAt, negRelated⟩ :=
    model.2 (node 1) negatedSourceInstruction (by rfl)
  obtain ⟨oldSinMeaning, oldSinAt, oldSinRelated⟩ :=
    model.2 (node 2) sineNegatedSourceInstruction (by rfl)
  obtain ⟨sinMeaning, sinAt, sinRelated⟩ :=
    model.2 (node 4) sineSourceInstruction (by rfl)
  obtain ⟨newNegMeaning, newNegAt, newNegRelated⟩ :=
    model.2 (node 5) negatedSineInstruction (by rfl)
  simp [operationModels, negatedSourceInstruction] at negAt
  simp [operationModels, sineNegatedSourceInstruction] at oldSinAt
  simp [operationModels, sineSourceInstruction] at sinAt
  simp [operationModels, negatedSineInstruction] at newNegAt
  subst negMeaning
  subst oldSinMeaning
  subst sinMeaning
  subst newNegMeaning
  have negated : valuation (node 1) = -valuation (node 0) := by
    simpa [negationModel, negatedSourceInstruction, List.map] using negRelated
  have oldSine : valuation (node 2) = Real.sin (valuation (node 1)) := by
    simpa [sineModel, sineNegatedSourceInstruction, List.map] using oldSinRelated
  have sine : valuation (node 4) = Real.sin (valuation (node 0)) := by
    simpa [sineModel, sineSourceInstruction, List.map] using sinRelated
  have newNegated : valuation (node 5) = -valuation (node 4) := by
    simpa [negationModel, negatedSineInstruction, List.map] using newNegRelated
  calc
    valuation (node 2) = Real.sin (valuation (node 1)) := oldSine
    _ = Real.sin (-valuation (node 0)) := congrArg Real.sin negated
    _ = -Real.sin (valuation (node 0)) := Real.sin_neg _
    _ = -valuation (node 4) := congrArg Neg.neg sine.symm
    _ = valuation (node 5) := newNegated.symm

private theorem factWith (fact : NodeFact Bound) {value : Bound}
    (equal : fact.fact = value) :
    fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

def sineFactSchema : PackedFactSchema semantics where
  rule := sineRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body =>
    if body == [MixedFunctions.Bound.unit.code] then some () else none
  replay := fun _ _ context _ =>
    if programEq : context.program = extendedProgram then
      if proposedFact : context.proposed.fact = .unit then
        match found : context.program.node? context.proposed.node with
        | some instruction =>
            if operation : instruction.op = ({ index := 2 } : OpId) then
              match arguments : instruction.args with
              | [input] =>
                  some
                    { proof := by
                        rw [factWith context.proposed proposedFact]
                        exact sineEntails context.program context.assumptions
                          context.proposed.node instruction input found operation arguments }
              | _ => none
            else none
        | none => none
      else none
    else none

def negationFactSchema : PackedFactSchema semantics where
  rule := negationRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body =>
    if body == [MixedFunctions.Bound.unit.code] then some () else none
  replay := fun _ _ context _ =>
    if programEq : context.program = extendedProgram then
      if proposedFact : context.proposed.fact = .unit then
        match found : context.program.node? context.proposed.node with
        | some instruction =>
            if operation : instruction.op = ({ index := 1 } : OpId) then
              match arguments : instruction.args with
              | [input] =>
                  if exactAssumptions :
                      context.assumptions = [{ node := input, fact := .unit }] then
                    some
                      { proof := by
                          rw [factWith context.proposed proposedFact]
                          exact negationEntails context.program context.assumptions
                            context.proposed.node instruction input found operation
                            arguments exactAssumptions }
                  else none
              | _ => none
            else none
        | none => none
      else none
    else none

def expFactSchema : PackedFactSchema semantics where
  rule := expRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body =>
    if body == [MixedFunctions.Bound.atMostThree.code] then some () else none
  replay := fun _ _ context _ =>
    if programEq : context.program = extendedProgram then
      if proposedFact : context.proposed.fact = .atMostThree then
        match found : context.program.node? context.proposed.node with
        | some instruction =>
            if operation : instruction.op = ({ index := 3 } : OpId) then
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
    else none

def oddnessInstanceSchema : PackedInstanceSchema semantics where
  rule := oddnessRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body => if body == [1] then some () else none
  replay := fun _ _ context _ =>
    if beforeEq : context.before = baseProgram then
      if afterEq : context.after = extendedProgram then
        some
          { proof := by
              simpa only [beforeEq, afterEq] using extension }
      else none
    else none

def oddnessEqualitySchema : PackedEqualitySchema semantics where
  rule := oddnessRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body => if body == [1] then some () else none
  replay := fun _ _ context _ =>
    if programEq : context.program = extendedProgram then
      if assumptionsEq : context.assumptions = [] then
        if leftEq : context.edge.left = node 2 then
          if rightEq : context.edge.right = node 5 then
            some
              { proof := by
                  simpa only [programEq, assumptionsEq, leftEq, rightEq] using
                    oddnessEntails }
          else none
        else none
      else none
    else none

def sourceProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[] }
    emit := { schemas := [] } }

def negationProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[negationFactSchema] }
    emit :=
      { schemas :=
          [{ key := negationFactSchema.key, handle := ``negationFactSchema }] } }

def sineProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic :=
      { factSchemas := #[sineFactSchema]
        instanceSchemas := #[oddnessInstanceSchema]
        equalitySchemas := #[oddnessEqualitySchema] }
    emit :=
      { schemas :=
          [{ key := sineFactSchema.key, handle := ``sineFactSchema },
           { key := oddnessInstanceSchema.key, handle := ``oddnessInstanceSchema },
           { key := oddnessEqualitySchema.key, handle := ``oddnessEqualitySchema }] } }

def expProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[expFactSchema] }
    emit :=
      { schemas :=
          [{ key := expFactSchema.key, handle := ``expFactSchema }] } }

def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof, negationProof, sineProof, expProof]

end Hex.Interval.Experiment.MixedInstantiation
