/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.SinTenInterval
public import HexIntervalMathlib.Experiment.SinTen
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

/-!
# Proof semantics for the endpoint-valued sine canary

The executable scheduler remains unaware of real numbers and transcendental
functions. These package-owned schemas replay its exact endpoint facts against
ordinary real semantics.
-/

namespace Hex.IntervalMathlib.Experiment.SinTenInterval

open Hex.Interval
open Hex.Interval.Experiment
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics
open Hex.Interval.Experiment.SinTenInterval

noncomputable def ratValue
    (q : Hex.Interval.Experiment.SinTenInterval.Rat) : ℝ :=
  q.num / q.den

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .interval interval, value =>
      (if interval.lowerOpen then ratValue interval.lower < value
        else ratValue interval.lower ≤ value) ∧
      (if interval.upperOpen then value < ratValue interval.upper
        else value ≤ ratValue interval.upper)

def sourceModel : OperationSemantics.Model ℝ :=
  { operation := sourceOperation
    relation := fun _ output => output = 10 }

def sineModel : OperationSemantics.Model ℝ :=
  { operation := sineOperation
    relation := fun inputs output =>
      match inputs with
      | [input] => output = Real.sin input
      | _ => False }

def piModel : OperationSemantics.Model ℝ :=
  { operation := piOperation
    relation := fun _ output => output = Real.pi }

def residualModel : OperationSemantics.Model ℝ :=
  { operation := residualOperation
    relation := fun inputs output =>
      match inputs with
      | [source, pi] => output = source - 3 * pi
      | _ => False }

def negationModel : OperationSemantics.Model ℝ :=
  { operation := negationOperation
    relation := fun inputs output =>
      match inputs with
      | [input] => output = -input
      | _ => False }

def operationModels : Array (OperationSemantics.Model ℝ) :=
  #[sourceModel, sineModel, piModel, residualModel, negationModel]

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
                    cases index with
                    | zero => rfl
                    | succ index =>
                        have lower : 5 ≤ index + 1 + 1 + 1 + 1 + 1 :=
                          Nat.le_add_left 5 index
                        exact False.elim (Nat.not_lt_of_ge lower (by
                          simpa [baseProgram] using within))

theorem sameOperations : baseProgram.operations = extendedProgram.operations := rfl

noncomputable def extendValuation (valuation : NodeId → ℝ) : NodeId → ℝ :=
  fun observed => if observed = node 5 then -valuation (node 4) else valuation observed

theorem extension : semantics.Extends baseProgram extendedProgram := by
  intro valuation model
  obtain ⟨old0, at0, related0⟩ := model.2 (node 0) sourceInstruction (by rfl)
  obtain ⟨old1, at1, related1⟩ := model.2 (node 1) targetSineInstruction (by rfl)
  obtain ⟨old2, at2, related2⟩ := model.2 (node 2) piInstruction (by rfl)
  obtain ⟨old3, at3, related3⟩ := model.2 (node 3) residualInstruction (by rfl)
  obtain ⟨old4, at4, related4⟩ := model.2 (node 4) localSineInstruction (by rfl)
  simp [operationModels, sourceInstruction] at at0
  simp [operationModels, targetSineInstruction] at at1
  simp [operationModels, piInstruction] at at2
  simp [operationModels, residualInstruction] at at3
  simp [operationModels, localSineInstruction] at at4
  subst old0
  subst old1
  subst old2
  subst old3
  subst old4
  refine ⟨extendValuation valuation, ?_, ?_⟩
  · refine ⟨by simpa [baseProgram, extendedProgram] using model.1, ?_⟩
    intro observed instruction found
    rcases observed with ⟨index⟩
    cases index with
    | zero =>
        simp [extendedProgram, baseProgram, Program.node?] at found
        subst instruction
        refine ⟨sourceModel, by rfl, ?_⟩
        simpa [sourceModel, sourceInstruction, extendValuation, node] using related0
    | succ index =>
        cases index with
        | zero =>
            simp [extendedProgram, baseProgram, Program.node?] at found
            subst instruction
            refine ⟨sineModel, by rfl, ?_⟩
            simpa [sineModel, targetSineInstruction, extendValuation, node, List.map]
              using related1
        | succ index =>
            cases index with
            | zero =>
                simp [extendedProgram, baseProgram, Program.node?] at found
                subst instruction
                refine ⟨piModel, by rfl, ?_⟩
                simpa [piModel, piInstruction, extendValuation, node] using related2
            | succ index =>
                cases index with
                | zero =>
                    simp [extendedProgram, baseProgram, Program.node?] at found
                    subst instruction
                    refine ⟨residualModel, by rfl, ?_⟩
                    simpa [residualModel, residualInstruction, extendValuation, node,
                      List.map] using related3
                | succ index =>
                    cases index with
                    | zero =>
                        simp [extendedProgram, baseProgram, Program.node?] at found
                        subst instruction
                        refine ⟨sineModel, by rfl, ?_⟩
                        simpa [sineModel, localSineInstruction, extendValuation, node,
                          List.map] using related4
                    | succ index =>
                        cases index with
                        | zero =>
                            simp [extendedProgram, baseProgram, Program.node?] at found
                            subst instruction
                            refine ⟨negationModel, by rfl, ?_⟩
                            simp [negationModel, negatedLocalSineInstruction,
                              extendValuation, node, List.map]
                        | succ index =>
                            simp [extendedProgram, baseProgram, Program.node?] at found
  · intro observed within
    have notFive : observed ≠ node 5 := by
      intro equal
      subst observed
      simp [baseProgram, node] at within
    simp [extendValuation, notFive]

def stable : StableStep semantics baseProgram extendedProgram :=
  stableLaw.stable (by rfl) (by rfl) programPrefix sameOperations

theorem constantEntails :
    semantics.Entails baseProgram [] { node := node 2, fact := piFact } := by
  intro valuation model _
  change NodeId → ℝ at valuation
  obtain ⟨meaning, meaningAt, related⟩ :=
    model.2 (node 2) piInstruction (by rfl)
  simp [operationModels, piInstruction] at meaningAt
  subst meaning
  have output : valuation (node 2) = Real.pi := by
    simpa [piModel, piInstruction] using related
  change Contains piFact (valuation (node 2))
  simp only [Contains, piFact, openInterval, rat, ratValue, if_true]
  rw [output]
  norm_num
  exact Hex.IntervalMathlib.Experiment.SinTen.MachinReplay.pi_bounds

theorem reductionEntails :
    semantics.Entails baseProgram
      [{ node := node 0, fact := .all }, { node := node 2, fact := piFact }]
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
  have sourceValue : valuation (node 0) = 10 := by
    simpa [sourceModel, sourceInstruction] using sourceRelated
  have residualValue :
      valuation (node 3) = valuation (node 0) - 3 * valuation (node 2) := by
    simpa [residualModel, residualInstruction, List.map] using residualRelated
  have piBounds : (3 : ℝ) < valuation (node 2) ∧ valuation (node 2) < 16 / 5 := by
    have := holds { node := node 2, fact := piFact } (by simp)
    change Contains piFact (valuation (node 2)) at this
    simpa [Contains, piFact, openInterval, rat, ratValue] using this
  change Contains residualFact (valuation (node 3))
  simp only [Contains, residualFact, openInterval, rat, ratValue, if_true]
  rw [residualValue, sourceValue]
  constructor <;> linarith

theorem localEntails :
    semantics.Entails baseProgram
      [{ node := node 3, fact := residualFact }]
      { node := node 4, fact := positiveFact } := by
  intro valuation model holds
  change NodeId → ℝ at valuation
  obtain ⟨meaning, meaningAt, related⟩ :=
    model.2 (node 4) localSineInstruction (by rfl)
  simp [operationModels, localSineInstruction] at meaningAt
  subst meaning
  have output : valuation (node 4) = Real.sin (valuation (node 3)) := by
    simpa [sineModel, localSineInstruction, List.map] using related
  have residualBounds :
      (2 / 5 : ℝ) < valuation (node 3) ∧ valuation (node 3) < 1 := by
    have := holds { node := node 3, fact := residualFact } (by simp)
    change Contains residualFact (valuation (node 3)) at this
    simpa [Contains, residualFact, openInterval, rat, ratValue] using this
  change Contains positiveFact (valuation (node 4))
  simp only [Contains, positiveFact, rat, ratValue, if_true]
  rw [output]
  norm_num
  exact ⟨Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (residualBounds.2.trans (by
        have := Hex.IntervalMathlib.Experiment.SinTen.MachinReplay.pi_bounds.1
        linarith)),
    Real.sin_le_one _⟩

theorem negationEntails :
    semantics.Entails extendedProgram
      [{ node := node 4, fact := positiveFact }]
      { node := node 5, fact := negativeFact } := by
  intro valuation model holds
  change NodeId → ℝ at valuation
  obtain ⟨meaning, meaningAt, related⟩ :=
    model.2 (node 5) negatedLocalSineInstruction (by rfl)
  simp [operationModels, negatedLocalSineInstruction] at meaningAt
  subst meaning
  have output : valuation (node 5) = -valuation (node 4) := by
    simpa [negationModel, negatedLocalSineInstruction, List.map] using related
  have positive : 0 < valuation (node 4) ∧ valuation (node 4) ≤ 1 := by
    have := holds { node := node 4, fact := positiveFact } (by simp)
    change Contains positiveFact (valuation (node 4)) at this
    simpa [Contains, positiveFact, rat, ratValue] using this
  change Contains negativeFact (valuation (node 5))
  simp only [Contains, negativeFact, rat, ratValue, if_true]
  rw [output]
  norm_num
  exact ⟨positive.2, positive.1⟩

theorem periodicEntails :
    semantics.EntailsEq extendedProgram
      [{ node := node 3, fact := residualFact }] (node 1) (node 5) := by
  intro valuation model _
  change NodeId → ℝ at valuation
  obtain ⟨targetMeaning, targetAt, targetRelated⟩ :=
    model.2 (node 1) targetSineInstruction (by rfl)
  obtain ⟨sourceMeaning, sourceAt, sourceRelated⟩ :=
    model.2 (node 0) sourceInstruction (by rfl)
  obtain ⟨residualMeaning, residualAt, residualRelated⟩ :=
    model.2 (node 3) residualInstruction (by rfl)
  obtain ⟨localMeaning, localAt, localRelated⟩ :=
    model.2 (node 4) localSineInstruction (by rfl)
  obtain ⟨negMeaning, negAt, negRelated⟩ :=
    model.2 (node 5) negatedLocalSineInstruction (by rfl)
  simp [operationModels, targetSineInstruction] at targetAt
  simp [operationModels, sourceInstruction] at sourceAt
  simp [operationModels, residualInstruction] at residualAt
  simp [operationModels, localSineInstruction] at localAt
  simp [operationModels, negatedLocalSineInstruction] at negAt
  subst targetMeaning
  subst sourceMeaning
  subst residualMeaning
  subst localMeaning
  subst negMeaning
  have targetValue : valuation (node 1) = Real.sin (valuation (node 0)) := by
    simpa [sineModel, targetSineInstruction, List.map] using targetRelated
  have sourceValue : valuation (node 0) = 10 := by
    simpa [sourceModel, sourceInstruction] using sourceRelated
  have residualValue :
      valuation (node 3) = valuation (node 0) - 3 * valuation (node 2) := by
    simpa [residualModel, residualInstruction, List.map] using residualRelated
  have piValue : valuation (node 2) = Real.pi := by
    obtain ⟨piMeaning, piAt, piRelated⟩ := model.2 (node 2) piInstruction (by rfl)
    simp [operationModels, piInstruction] at piAt
    subst piMeaning
    simpa [piModel, piInstruction] using piRelated
  have localValue : valuation (node 4) = Real.sin (valuation (node 3)) := by
    simpa [sineModel, localSineInstruction, List.map] using localRelated
  have negValue : valuation (node 5) = -valuation (node 4) := by
    simpa [negationModel, negatedLocalSineInstruction, List.map] using negRelated
  have periodic : Real.sin (10 - 3 * Real.pi) = -Real.sin 10 := by
    convert (Real.sin_sub_nat_mul_pi 10 3) using 1 <;> norm_num
  rw [targetValue, sourceValue, negValue, localValue, residualValue, sourceValue, piValue]
  calc
    Real.sin 10 = -(-Real.sin 10) := (neg_neg _).symm
    _ = -Real.sin (10 - 3 * Real.pi) := congrArg Neg.neg periodic.symm

def constantSchema : PackedFactSchema semantics where
  rule := constantRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body => if body == [1] then some () else none
  replay := fun _ _ context _ =>
    if graph : context.program = baseProgram then
      if assumptions : context.assumptions = [] then
        if proposed : context.proposed = { node := node 2, fact := piFact } then
          some { proof := by simpa only [graph, assumptions, proposed] using constantEntails }
        else none
      else none
    else none

def reductionSchema : PackedFactSchema semantics where
  rule := reductionRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body => if body == [2] then some () else none
  replay := fun _ _ context _ =>
    if graph : context.program = baseProgram then
      if assumptions : context.assumptions =
          [{ node := node 0, fact := .all }, { node := node 2, fact := piFact }] then
        if proposed : context.proposed = { node := node 3, fact := residualFact } then
          some { proof := by simpa only [graph, assumptions, proposed] using reductionEntails }
        else none
      else none
    else none

def localSchema : PackedFactSchema semantics where
  rule := localRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body => if body == [3] then some () else none
  replay := fun _ _ context _ =>
    if graph : context.program = baseProgram then
      if assumptions : context.assumptions = [{ node := node 3, fact := residualFact }] then
        if proposed : context.proposed = { node := node 4, fact := positiveFact } then
          some { proof := by simpa only [graph, assumptions, proposed] using localEntails }
        else none
      else none
    else none

def negationSchema : PackedFactSchema semantics where
  rule := negationRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body => if body == [4] then some () else none
  replay := fun _ _ context _ =>
    if graph : context.program = extendedProgram then
      if assumptions : context.assumptions = [{ node := node 4, fact := positiveFact }] then
        if proposed : context.proposed = { node := node 5, fact := negativeFact } then
          some { proof := by simpa only [graph, assumptions, proposed] using negationEntails }
        else none
      else none
    else none

def identityInstanceSchema : PackedInstanceSchema semantics where
  rule := identityRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body => if body == [1] then some () else none
  replay := fun _ _ context _ =>
    if before : context.before = baseProgram then
      if after : context.after = extendedProgram then
        some { proof := by simpa only [before, after] using extension }
      else none
    else none

def identityEqualitySchema : PackedEqualitySchema semantics where
  rule := identityRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body => if body == [1] then some () else none
  replay := fun _ _ context _ =>
    if graph : context.program = extendedProgram then
      if assumptions : context.assumptions =
          [{ node := node 3, fact := residualFact }] then
        if left : context.edge.left = node 1 then
          if right : context.edge.right = node 5 then
            some
              { proof := by
                  simpa only [graph, assumptions, left, right] using periodicEntails }
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

def semanticPackages : Array (SemanticReplay.Package semantics) :=
  proofPackages.map fun package => package.semantic

def baseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .all }, { node := node 1, fact := .all },
   { node := node 2, fact := .all }, { node := node 3, fact := .all },
   { node := node 4, fact := .all }]

theorem baseWithin : FactsWithin baseProgram baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [baseProgram, node]

theorem basePrefix : ProgramPrefix baseProgram baseProgram :=
  ProgramPrefix.refl baseProgram

def initialExtension : Evidence (semantics.Extends baseProgram baseProgram) :=
  extendRefl semantics baseProgram

theorem targetWithin : (node 1).index < baseProgram.nodes.size := by decide

def closeEvidence
    (extensionEvidence : Evidence (semantics.Extends baseProgram extendedProgram))
    (final : Evidence (semantics.Entails extendedProgram baseFacts checkerInput.target)) :
    Evidence (semantics.Entails baseProgram baseFacts checkerInput.target) :=
  closeBase (input := checkerInput) stable baseWithin targetWithin
    extensionEvidence final

noncomputable def valuation : NodeId → ℝ
  | ⟨0⟩ => 10
  | ⟨1⟩ => Real.sin 10
  | ⟨2⟩ => Real.pi
  | ⟨3⟩ => 10 - 3 * Real.pi
  | ⟨4⟩ => Real.sin (10 - 3 * Real.pi)
  | _ => 0

theorem valuationModels : semantics.models baseProgram valuation := by
  refine ⟨by simp [baseProgram, operations, operationModels, sourceModel, sineModel,
    piModel, residualModel, negationModel], ?_⟩
  rintro ⟨index⟩ instruction found
  cases index with
  | zero =>
      simp [Program.node?, baseProgram] at found
      subst instruction
      exact ⟨sourceModel, by rfl, by rfl⟩
  | succ index =>
      cases index with
      | zero =>
          simp [Program.node?, baseProgram] at found
          subst instruction
          exact ⟨sineModel, by rfl, by rfl⟩
      | succ index =>
          cases index with
          | zero =>
              simp [Program.node?, baseProgram] at found
              subst instruction
              exact ⟨piModel, by rfl, by rfl⟩
          | succ index =>
              cases index with
              | zero =>
                  simp [Program.node?, baseProgram] at found
                  subst instruction
                  exact ⟨residualModel, by rfl, by rfl⟩
              | succ index =>
                  cases index with
                  | zero =>
                      simp [Program.node?, baseProgram] at found
                      subst instruction
                      exact ⟨sineModel, by rfl, by rfl⟩
                  | succ index => simp [Program.node?, baseProgram] at found

theorem baseHolds :
    ∀ fact ∈ baseFacts, semantics.holds baseProgram valuation fact := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> trivial

end Hex.IntervalMathlib.Experiment.SinTenInterval

end
