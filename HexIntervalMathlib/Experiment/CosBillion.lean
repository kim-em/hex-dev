/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.CosBillion
public import HexIntervalMathlib.Experiment.SinTenInterval
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Proof replay for `Real.cos (10^10)`

The executable package supplies an explicit large quotient and rational
residual window.  Replay checks those fields against a 20-decimal constant
enclosure, proves a local cosine sign, and reconstructs the original node by
the ordinary cosine periodicity theorem.
-/

namespace Hex.IntervalMathlib.Experiment.CosBillion

open Hex.Interval
open Hex.Interval.Experiment
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics
open Hex.Interval.Experiment.CosBillion

noncomputable def ratValue (q : Hex.Interval.Experiment.CosBillion.Rat) : ℝ :=
  q.num / q.den

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .interval interval, value =>
      (if interval.lowerOpen then ratValue interval.lower < value
        else ratValue interval.lower ≤ value) ∧
      (if interval.upperOpen then value < ratValue interval.upper
        else value ≤ ratValue interval.upper)

namespace DecimalPi

noncomputable def Claim : Prop :=
  Hex.IntervalMathlib.Experiment.SinTen.MachinReplay.Claim finePiCandidate

theorem claim : Claim := by
  constructor
  · change
      ((314159265358979323846 : ℝ) / 100000000000000000000) < Real.pi
    convert Real.pi_gt_d20 using 1
    norm_num
  · change
      Real.pi < ((314159265358979323847 : ℝ) / 100000000000000000000)
    convert Real.pi_lt_d20 using 1
    norm_num

def evidence : Evidence Claim := { proof := claim }

end DecimalPi

def sourceModel : Model ℝ :=
  { operation := sourceOperation, relation := fun _ output => output = 10 ^ 10 }
def cosineModel : Model ℝ :=
  { operation := cosineOperation
    relation := fun inputs output =>
      match inputs with
      | [input] => output = Real.cos input
      | _ => False }
def piModel : Model ℝ :=
  { operation := piOperation, relation := fun _ output => output = Real.pi }
def residualModel : Model ℝ :=
  { operation := residualOperation
    relation := fun inputs output =>
      match inputs with
      | [source, pi] => output = source - quotient * pi
      | _ => False }
def negationModel : Model ℝ :=
  { operation := negationOperation
    relation := fun inputs output =>
      match inputs with
      | [input] => output = -input
      | _ => False }

def operationModels : Array (Model ℝ) :=
  #[sourceModel, cosineModel, piModel, residualModel, negationModel]

def semantics : Semantics Bound :=
  OperationSemantics.semantics operationModels Contains

def boundSchema : FactDomainSchema semantics where
  top := fun _ => .all
  topSound := by intros; trivial
  proveMeet := fun _ target previous proposed installed =>
    if same : previous = proposed then
      if exact : installed = previous then
        some
          { proof := by
              subst proposed
              subst installed
              intro valuation _
              change Contains previous (valuation target) ↔
                Contains previous (valuation target) ∧ Contains previous (valuation target)
              simp }
      else none
    else if rightTop : proposed = .all then
      if installedEq : installed = previous then
        some
          { proof := by
              subst proposed
              subst installed
              intro valuation _
              change Contains previous (valuation target) ↔
                Contains previous (valuation target) ∧ Contains .all (valuation target)
              simp [Contains] }
      else none
    else if leftTop : previous = .all then
      if installedEq : installed = proposed then
        some
          { proof := by
              subst previous
              subst installed
              intro valuation _
              change Contains proposed (valuation target) ↔
                Contains .all (valuation target) ∧ Contains proposed (valuation target)
              simp [Contains] }
      else none
    else none

def laws : Laws semantics :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change Contains fact (valuation left) ↔ Contains fact (valuation right)
      rw [values] }

def stableLaw : StableLaw semantics :=
  OperationSemantics.stableLaw operationModels Contains

def stable : StableStep semantics program program :=
  stableLaw.stable (by rfl) (by rfl) (ProgramPrefix.refl program) (by rfl)

theorem constantEntailsOf (provider : Evidence DecimalPi.Claim) :
    semantics.Entails program [] { node := node 2, fact := finePiFact } := by
  intro valuation model _
  change NodeId → ℝ at valuation
  obtain ⟨meaning, meaningAt, related⟩ :=
    model.2 (node 2) piInstruction (by rfl)
  simp [operationModels, piInstruction] at meaningAt
  subst meaning
  have output : valuation (node 2) = Real.pi := by
    simpa [piModel, piInstruction] using related
  change Contains finePiFact (valuation (node 2))
  simp only [Contains, finePiFact, openInterval, rat, ratValue, if_true]
  rw [output]
  simpa [DecimalPi.Claim,
    Hex.IntervalMathlib.Experiment.SinTen.MachinReplay.Claim,
    Hex.IntervalMathlib.Experiment.SinTen.candidateValue, finePiCandidate]
    using provider.proof

theorem constantEntails :
    semantics.Entails program [] { node := node 2, fact := finePiFact } :=
  constantEntailsOf DecimalPi.evidence

theorem reductionEntails :
    semantics.Entails program
      [{ node := node 0, fact := .all }, { node := node 2, fact := finePiFact }]
      { node := node 3, fact := residualFact } := by
  intro valuation model holds
  change NodeId → ℝ at valuation
  obtain ⟨sourceMeaning, sourceAt, sourceRelated⟩ :=
    model.2 (node 0) sourceInstruction (by rfl)
  obtain ⟨residualMeaning, residualAt, residualRelated⟩ :=
    model.2 (node 3) residualInstruction (by rfl)
  simp [operationModels, sourceInstruction] at sourceAt
  simp [operationModels, residualInstruction] at residualAt
  subst sourceMeaning
  subst residualMeaning
  have sourceValue : valuation (node 0) = 10 ^ 10 := by
    simpa [sourceModel, sourceInstruction] using sourceRelated
  have residualValue :
      valuation (node 3) = valuation (node 0) - quotient * valuation (node 2) := by
    simpa [residualModel, residualInstruction, List.map] using residualRelated
  have piBounds := holds { node := node 2, fact := finePiFact } (by simp)
  change Contains finePiFact (valuation (node 2)) at piBounds
  change Contains residualFact (valuation (node 3))
  simp only [Contains, finePiFact, residualFact, openInterval, rat, ratValue,
    if_true] at piBounds ⊢
  rw [residualValue, sourceValue]
  norm_num [quotient, finePiCandidate] at piBounds ⊢
  constructor <;> nlinarith

theorem localEntails :
    semantics.Entails program [{ node := node 3, fact := residualFact }]
      { node := node 4, fact := negativeFact } := by
  intro valuation model holds
  change NodeId → ℝ at valuation
  obtain ⟨meaning, meaningAt, related⟩ :=
    model.2 (node 4) localInstruction (by rfl)
  simp [operationModels, localInstruction] at meaningAt
  subst meaning
  have output : valuation (node 4) = Real.cos (valuation (node 3)) := by
    simpa [cosineModel, localInstruction, List.map] using related
  have residualBounds := holds { node := node 3, fact := residualFact } (by simp)
  change Contains residualFact (valuation (node 3)) at residualBounds
  simp only [Contains, residualFact, openInterval, rat, ratValue,
    if_true] at residualBounds
  have localNegative : Real.cos (valuation (node 3)) < 0 := by
    apply Real.cos_neg_of_pi_div_two_lt_of_lt
    · nlinarith [Real.pi_lt_four]
    · nlinarith [Real.pi_gt_three]
  change Contains negativeFact (valuation (node 4))
  simp only [Contains, negativeFact, rat, ratValue, if_true]
  rw [output]
  norm_num
  exact ⟨Real.neg_one_le_cos _, localNegative⟩

theorem negationEntails :
    semantics.Entails program [{ node := node 4, fact := negativeFact }]
      { node := node 5, fact := positiveFact } := by
  intro valuation model holds
  change NodeId → ℝ at valuation
  obtain ⟨meaning, meaningAt, related⟩ :=
    model.2 (node 5) negatedInstruction (by rfl)
  simp [operationModels, negatedInstruction] at meaningAt
  subst meaning
  have output : valuation (node 5) = -valuation (node 4) := by
    simpa [negationModel, negatedInstruction, List.map] using related
  have negative := holds { node := node 4, fact := negativeFact } (by simp)
  change Contains negativeFact (valuation (node 4)) at negative
  change Contains positiveFact (valuation (node 5))
  simp only [Contains, negativeFact, positiveFact, rat, ratValue, if_true] at negative ⊢
  rw [output]
  norm_num at negative ⊢
  constructor <;> linarith

theorem periodicEntails :
    semantics.EntailsEq program [{ node := node 3, fact := residualFact }]
      (node 1) (node 5) := by
  intro valuation model _
  change NodeId → ℝ at valuation
  obtain ⟨targetMeaning, targetAt, targetRelated⟩ :=
    model.2 (node 1) targetInstruction (by rfl)
  obtain ⟨sourceMeaning, sourceAt, sourceRelated⟩ :=
    model.2 (node 0) sourceInstruction (by rfl)
  obtain ⟨residualMeaning, residualAt, residualRelated⟩ :=
    model.2 (node 3) residualInstruction (by rfl)
  obtain ⟨localMeaning, localAt, localRelated⟩ :=
    model.2 (node 4) localInstruction (by rfl)
  obtain ⟨negMeaning, negAt, negRelated⟩ :=
    model.2 (node 5) negatedInstruction (by rfl)
  simp [operationModels, targetInstruction] at targetAt
  simp [operationModels, sourceInstruction] at sourceAt
  simp [operationModels, residualInstruction] at residualAt
  simp [operationModels, localInstruction] at localAt
  simp [operationModels, negatedInstruction] at negAt
  subst targetMeaning
  subst sourceMeaning
  subst residualMeaning
  subst localMeaning
  subst negMeaning
  have targetValue : valuation (node 1) = Real.cos (valuation (node 0)) := by
    simpa [cosineModel, targetInstruction, List.map] using targetRelated
  have residualValue :
      valuation (node 3) = valuation (node 0) - quotient * valuation (node 2) := by
    simpa [residualModel, residualInstruction, List.map] using residualRelated
  have piValue : valuation (node 2) = Real.pi := by
    obtain ⟨piMeaning, piAt, piRelated⟩ := model.2 (node 2) piInstruction (by rfl)
    simp [operationModels, piInstruction] at piAt
    subst piMeaning
    simpa [piModel, piInstruction] using piRelated
  have localValue : valuation (node 4) = Real.cos (valuation (node 3)) := by
    simpa [cosineModel, localInstruction, List.map] using localRelated
  have negValue : valuation (node 5) = -valuation (node 4) := by
    simpa [negationModel, negatedInstruction, List.map] using negRelated
  have periodic :
      Real.cos (valuation (node 0) - quotient * Real.pi) =
        -Real.cos (valuation (node 0)) := by
    rw [Real.cos_sub_nat_mul_pi]
    norm_num [quotient]
  rw [targetValue, negValue, localValue, residualValue, piValue, periodic]
  exact (neg_neg (Real.cos (valuation (node 0)))).symm

def exactAction (action : Action) (key : RuleKey) (target : NodeId) : Bool :=
  action.key == key && action.node == target

def constantSchema : PackedFactSchema semantics where
  rule := constantRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body => if body == [1] then some () else none
  replay := fun _ action context _ =>
    if exactAction action constantRuleKey (node 2) then
      if graph : context.program = program then
        if assumptions : context.assumptions = [] then
          if proposed : context.proposed = { node := node 2, fact := finePiFact } then
            some { proof := by simpa only [graph, assumptions, proposed] using constantEntails }
          else none
        else none
      else none
    else none

def reductionSchema : PackedFactSchema semantics where
  rule := reductionRuleKey
  schema := 1
  Certificate := ReductionCertificate
  decode := decodeReduction?
  replay := fun _ action context certificate =>
    if exactAction action reductionRuleKey (node 3) then
      if accepted : certificate = reductionCertificate then
        if graph : context.program = program then
          if assumptions : context.assumptions =
              [{ node := node 0, fact := .all },
               { node := node 2, fact := finePiFact }] then
            if proposed : context.proposed = { node := node 3, fact := residualFact } then
              some
                { proof := by
                    simpa only [graph, assumptions, proposed] using reductionEntails }
            else none
          else none
        else none
      else none
    else none

def localSchema : PackedFactSchema semantics where
  rule := localRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body => if body == [3] then some () else none
  replay := fun _ action context _ =>
    if exactAction action localRuleKey (node 4) then
      if graph : context.program = program then
        if assumptions : context.assumptions = [{ node := node 3, fact := residualFact }] then
          if proposed : context.proposed = { node := node 4, fact := negativeFact } then
            some { proof := by simpa only [graph, assumptions, proposed] using localEntails }
          else none
        else none
      else none
    else none

def negationSchema : PackedFactSchema semantics where
  rule := negationRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body => if body == [4] then some () else none
  replay := fun _ action context _ =>
    if exactAction action negationRuleKey (node 5) then
      if graph : context.program = program then
        if assumptions : context.assumptions = [{ node := node 4, fact := negativeFact }] then
          if proposed : context.proposed = { node := node 5, fact := positiveFact } then
            some { proof := by simpa only [graph, assumptions, proposed] using negationEntails }
          else none
        else none
      else none
    else none

def identityInstanceSchema : PackedInstanceSchema semantics where
  rule := identityRuleKey
  schema := 1
  Certificate := Nat
  decode := fun body => match body with | [q] => some q | _ => none
  replay := fun _ action context certificate =>
    if exactAction action identityRuleKey (node 3) then
      if accepted : certificate = quotient then
        if before : context.before = program then
          if after : context.after = program then
            some
              { proof := by
                  simpa only [before, after] using (extendRefl semantics program).proof }
          else none
        else none
      else none
    else none

def identityEqualitySchema : PackedEqualitySchema semantics where
  rule := identityRuleKey
  schema := 1
  Certificate := Nat
  decode := fun body => match body with | [q] => some q | _ => none
  replay := fun _ action context certificate =>
    if exactAction action identityRuleKey (node 3) then
      if accepted : certificate = quotient then
        if graph : context.program = program then
          if assumptions : context.assumptions = [{ node := node 3, fact := residualFact }] then
            if left : context.edge.left = node 1 then
              if right : context.edge.right = node 5 then
                some
                  { proof := by
                      simpa only [graph, assumptions, left, right] using periodicEntails }
              else none
            else none
          else none
        else none
      else none
    else none

def sourceProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[] }, emit := { schemas := [] } }
def constantProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[constantSchema] }
    emit := { schemas := [{ key := constantSchema.key, handle := ``constantSchema }] } }
def reductionProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic :=
      { factSchemas := #[reductionSchema]
        instanceSchemas := #[identityInstanceSchema]
        equalitySchemas := #[identityEqualitySchema] }
    emit :=
      { schemas :=
          [{ key := reductionSchema.key, handle := ``reductionSchema },
           { key := identityInstanceSchema.key, handle := ``identityInstanceSchema },
           { key := identityEqualitySchema.key, handle := ``identityEqualitySchema }] } }
def localProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[localSchema] }
    emit := { schemas := [{ key := localSchema.key, handle := ``localSchema }] } }
def negationProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[negationSchema] }
    emit := { schemas := [{ key := negationSchema.key, handle := ``negationSchema }] } }

def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof, localProof, constantProof, reductionProof, negationProof]

def baseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .all }, { node := node 1, fact := .all },
   { node := node 2, fact := .all }, { node := node 3, fact := .all },
   { node := node 4, fact := .all }, { node := node 5, fact := .all }]

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [program, node]

def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

theorem basePrefix : ProgramPrefix program program :=
  ProgramPrefix.refl program

theorem programPrefix : ProgramPrefix program program :=
  ProgramPrefix.refl program

theorem sameOperations : program.operations = program.operations := rfl

theorem targetWithin : (node 1).index < program.nodes.size := by decide

def closeEvidence (final : Evidence (semantics.Entails program baseFacts checkerInput.target)) :
    Evidence (semantics.Entails program baseFacts checkerInput.target) := final

noncomputable def valuation : NodeId → ℝ
  | ⟨0⟩ => 10 ^ 10
  | ⟨1⟩ => Real.cos (10 ^ 10)
  | ⟨2⟩ => Real.pi
  | ⟨3⟩ => 10 ^ 10 - quotient * Real.pi
  | ⟨4⟩ => Real.cos (10 ^ 10 - quotient * Real.pi)
  | ⟨5⟩ => -Real.cos (10 ^ 10 - quotient * Real.pi)
  | _ => 0

theorem valuationModels : semantics.models program valuation := by
  refine ⟨by simp [program, operations, operationModels, sourceModel,
    cosineModel, piModel, residualModel, negationModel], ?_⟩
  rintro ⟨index⟩ instruction found
  cases index with
  | zero =>
      simp [Program.node?, program] at found
      subst instruction
      exact ⟨sourceModel, by rfl, by rfl⟩
  | succ index =>
      cases index with
      | zero =>
          simp [Program.node?, program] at found
          subst instruction
          exact ⟨cosineModel, by rfl, by rfl⟩
      | succ index =>
          cases index with
          | zero =>
              simp [Program.node?, program] at found
              subst instruction
              exact ⟨piModel, by rfl, by rfl⟩
          | succ index =>
              cases index with
              | zero =>
                  simp [Program.node?, program] at found
                  subst instruction
                  exact ⟨residualModel, by rfl, by rfl⟩
              | succ index =>
                  cases index with
                  | zero =>
                      simp [Program.node?, program] at found
                      subst instruction
                      exact ⟨cosineModel, by rfl, by rfl⟩
                  | succ index =>
                      cases index with
                      | zero =>
                          simp [Program.node?, program] at found
                          subst instruction
                          exact ⟨negationModel, by rfl, by rfl⟩
                      | succ index => simp [Program.node?, program] at found

theorem baseHolds :
    ∀ fact ∈ baseFacts, semantics.holds program valuation fact := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

end Hex.IntervalMathlib.Experiment.CosBillion

end
