/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import HexInterval.Experiment.ProofEmitter
public import HexInterval.Experiment.SineSign

@[expose] public section

/-!
# Real semantics for the arbitrary sine-sign vertical

The executable side knows only opaque operation keys and a small finite range
lattice.  This companion supplies their real interpretation.  The proof chain
is intentionally split into an oddness instantiator, a sine propagator, a
negation propagator, and generic equality transport.
-/

namespace Hex.Interval.Experiment.SineSign

open Propagator SemanticReplay ChronologicalReplay ProofEmitter

/-! ## Real interpretation -/

/-- Meaning of the Mathlib-free range lattice over the reals. -/
def Contains : Range -> ℝ -> Prop
  | .all, _ => True
  | .unit, x => 0 ≤ x ∧ x ≤ 1
  | .nonnegative, x => 0 ≤ x
  | .nonpositive, x => x ≤ 0
  | .zero, x => x = 0
  | .empty, _ => False

/-- Real semantics of the five-node vertical.  Each implication is guarded by
an exact node lookup, so the same interpretation restricts to the caller's
three-node prefix.  Operation keys remain package-owned; no central function
language is introduced. -/
def Models (program : Program) (valuation : NodeId -> ℝ) : Prop :=
  (program.node? (node 1) = some negatedSourceInstruction ->
      valuation (node 1) = -valuation (node 0)) ∧
  (program.node? (node 2) = some sineNegatedSourceInstruction ->
      valuation (node 2) = Real.sin (valuation (node 1))) ∧
  (program.node? (node 3) = some sineSourceInstruction ->
      valuation (node 3) = Real.sin (valuation (node 0))) ∧
  (program.node? (node 4) = some negatedSineInstruction ->
      valuation (node 4) = -valuation (node 3))

/-- The generic replay protocol instantiated with real values and range
membership. -/
def semantics : SemanticReplay.Semantics Range :=
  { Value := ℝ
    models := Models
    holds := fun _ valuation fact => Contains fact.fact (valuation fact.node) }

theorem containsMeet (left right : Range) (x : ℝ) :
    Contains (left.meet right) x ↔ Contains left x ∧ Contains right x := by
  cases left <;> cases right <;>
    constructor <;> intro holds <;>
      simp_all [Range.meet, Contains] <;> linarith

/-- The range lattice independently checks every executable intersection. -/
def rangeSchema : FactDomainSchema semantics :=
  { top := fun _ => .all
    topSound := by
      intro _ valuation node _ _ _
      change Contains .all (valuation node)
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

/-! ## Package theorem lemmas -/

/-- Semantic theorem behind every `[0,1] ↦ [0,∞)` sine proposal. -/
theorem sineEntails :
    semantics.Entails extendedProgram
      [{ node := node 0, fact := .unit }]
      { node := node 3, fact := .nonnegative } := by
  change ∀ valuation : NodeId -> ℝ, Models extendedProgram valuation ->
    (∀ assumption,
      assumption ∈
          ([{ node := node 0, fact := .unit }] : List (NodeFact Range)) ->
        Contains assumption.fact (valuation assumption.node)) ->
    Contains .nonnegative (valuation (node 3))
  intro valuation model assumptions
  have inputRange := assumptions { node := node 0, fact := .unit } (by simp)
  change 0 ≤ valuation (node 0) ∧ valuation (node 0) ≤ 1 at inputRange
  change 0 ≤ valuation (node 3)
  rw [model.2.2.1 (by rfl)]
  exact Real.sin_nonneg_of_nonneg_of_le_pi inputRange.1
    (inputRange.2.trans (by linarith [Real.one_le_pi_div_two]))

/-- Semantic theorem behind every `[0,∞) ↦ (-∞,0]` negation proposal. -/
theorem negationEntails :
    semantics.Entails extendedProgram
      [{ node := node 3, fact := .nonnegative }]
      { node := node 4, fact := .nonpositive } := by
  change ∀ valuation : NodeId -> ℝ, Models extendedProgram valuation ->
    (∀ assumption,
      assumption ∈
          ([{ node := node 3, fact := .nonnegative }] : List (NodeFact Range)) ->
        Contains assumption.fact (valuation assumption.node)) ->
    Contains .nonpositive (valuation (node 4))
  intro valuation model assumptions
  have inputRange := assumptions
    { node := node 3, fact := .nonnegative } (by simp)
  change 0 ≤ valuation (node 3) at inputRange
  change valuation (node 4) ≤ 0
  rw [model.2.2.2 (by rfl)]
  exact neg_nonpos.mpr inputRange

/-! ## The exact oddness instantiation -/

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
                have lower : 3 ≤ index + 1 + 1 + 1 :=
                  Nat.le_add_left 3 index
                exact False.elim (Nat.not_lt_of_ge lower (by
                  simpa [baseProgram] using within))

/-- Extend an old valuation with the two expressions proposed by the matcher. -/
noncomputable def extendValuation (valuation : NodeId -> ℝ) : NodeId -> ℝ :=
  fun observed =>
    if observed = node 3 then Real.sin (valuation (node 0))
    else if observed = node 4 then -Real.sin (valuation (node 0))
    else valuation observed

theorem extension : semantics.Extends baseProgram extendedProgram := by
  change ∀ valuation : NodeId -> ℝ, Models baseProgram valuation ->
    ∃ extended : NodeId -> ℝ,
      Models extendedProgram extended ∧
        ∀ node, node.index < baseProgram.nodes.size -> valuation node = extended node
  intro valuation model
  refine ⟨extendValuation valuation, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro _
      have old := model.1 (by rfl)
      simpa [extendValuation, node] using old
    · intro _
      have old := model.2.1 (by rfl)
      simpa [extendValuation, node] using old
    · intro _
      simp [extendValuation, node]
    · intro _
      simp [extendValuation, node]
  · intro observed within
    have old : observed.index < 3 := by
      simpa [baseProgram] using within
    have notThree : observed ≠ node 3 := by
      intro equal
      subst observed
      simp [node] at old
    have notFour : observed ≠ node 4 := by
      intro equal
      subst observed
      simp [node] at old
    simp [extendValuation, notThree, notFour]

/-- The real interpretation restricts along the matcher's append-only step,
and old facts keep the same meaning. -/
def stable : StableStep semantics baseProgram extendedProgram :=
  { programPrefix
    modelsBefore := by
      intro valuation model
      change Models extendedProgram valuation at model
      change Models baseProgram valuation
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro _
        exact model.1 (by rfl)
      · intro _
        exact model.2.1 (by rfl)
      · intro impossible
        simp [baseProgram, Program.node?, node] at impossible
      · intro impossible
        simp [baseProgram, Program.node?, node] at impossible
    holdsOld := by
      intro oldValue newValue fact _ _ _ agreement
      change Contains fact.fact (oldValue fact.node) ↔
        Contains fact.fact (newValue fact.node)
      rw [agreement] }

theorem oddnessEntails :
    semantics.EntailsEq extendedProgram [] (node 2) (node 4) := by
  change ∀ valuation : NodeId -> ℝ, Models extendedProgram valuation ->
    (∀ assumption, assumption ∈ ([] : List (NodeFact Range)) ->
      Contains assumption.fact (valuation assumption.node)) ->
    valuation (node 2) = valuation (node 4)
  intro valuation model _
  have negated := model.1 (by rfl)
  have original := model.2.1 (by rfl)
  have positive := model.2.2.1 (by rfl)
  have negative := model.2.2.2 (by rfl)
  calc
    valuation (node 2) = Real.sin (valuation (node 1)) := original
    _ = Real.sin (-valuation (node 0)) := congrArg Real.sin negated
    _ = -Real.sin (valuation (node 0)) := Real.sin_neg _
    _ = -valuation (node 3) := congrArg Neg.neg positive.symm
    _ = valuation (node 4) := negative.symm

/-! ## Immutable theorem schemas for the executable packages -/

def sineFactSchema : PackedFactSchema semantics where
  rule := sineRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body => if body == [Range.nonnegative.code] then some () else none
  replay := fun _ _ context _ =>
    if programEq : context.program = extendedProgram then
      if assumptionsEq : context.assumptions =
          [{ node := node 0, fact := .unit }] then
        if proposedEq : context.proposed =
            { node := node 3, fact := .nonnegative } then
          some
            { proof := by
                simpa only [programEq, assumptionsEq, proposedEq] using
                  sineEntails }
        else none
      else none
    else none

def negationFactSchema : PackedFactSchema semantics where
  rule := negationRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body => if body == [Range.nonpositive.code] then some () else none
  replay := fun _ _ context _ =>
    if programEq : context.program = extendedProgram then
      if assumptionsEq : context.assumptions =
          [{ node := node 3, fact := .nonnegative }] then
        if proposedEq : context.proposed =
            { node := node 4, fact := .nonpositive } then
          some
            { proof := by
                simpa only [programEq, assumptionsEq, proposedEq] using
                  negationEntails }
        else none
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
          if rightEq : context.edge.right = node 4 then
            some
              { proof := by
                  simpa only [programEq, assumptionsEq, leftEq, rightEq] using
                    oddnessEntails }
          else none
        else none
      else none
    else none

def semanticPackages : Array (SemanticReplay.Package semantics) :=
  #[{ factSchemas := #[] },
    { factSchemas := #[negationFactSchema] },
    { factSchemas := #[sineFactSchema]
      instanceSchemas := #[oddnessInstanceSchema]
      equalitySchemas := #[oddnessEqualitySchema] }]

/-! ## Tactic-side schema contributions -/

/-- The negation package exposes only its own fact theorem to proof emitters. -/
def negationEmit : EmitPackage :=
  { schemas :=
      [{ key := negationFactSchema.key
         declaration := ``negationFactSchema }] }

/-- The sine/oddness package exposes its fact, instantiation, and equality
schemas.  Their full replay addresses remain distinct even though all three
use numeric payload schema `1`. -/
def sineEmit : EmitPackage :=
  { schemas :=
      [{ key := sineFactSchema.key
         declaration := ``sineFactSchema },
       { key := oddnessInstanceSchema.key
         declaration := ``oddnessInstanceSchema },
       { key := oddnessEqualitySchema.key
         declaration := ``oddnessEqualitySchema }] }

/-! ## Ordinary emitted proof chain -/

def baseFacts : List (NodeFact Range) :=
  [{ node := node 0, fact := .unit },
   { node := node 1, fact := .all },
   { node := node 2, fact := .all }]

def previousAll (target : NodeId) :
    Evidence
      (semantics.Entails extendedProgram baseFacts
        { node := target, fact := .all }) :=
  { proof := by
      change ∀ valuation : NodeId -> ℝ, Models extendedProgram valuation ->
        (∀ assumption, assumption ∈ baseFacts ->
          Contains assumption.fact (valuation assumption.node)) ->
        Contains .all (valuation target)
      intro _ _ _
      trivial }

def meetAll (target : NodeId) (fact : Range) :
    Evidence
      (∀ valuation, semantics.models extendedProgram valuation ->
        (semantics.holds extendedProgram valuation { node := target, fact } ↔
          semantics.holds extendedProgram valuation
              { node := target, fact := .all } ∧
            semantics.holds extendedProgram valuation
              { node := target, fact })) :=
  { proof := by
      intro valuation _
      change Contains fact (valuation target) ↔
        Contains .all (valuation target) ∧ Contains fact (valuation target)
      simp [Contains] }

def sineRuleEvidence :
    Evidence
      (semantics.Entails extendedProgram
        [{ node := node 0, fact := .unit }]
        { node := node 3, fact := .nonnegative }) :=
  { proof := sineEntails }

def sineInputSound :
    Evidence
      (InputsSound semantics extendedProgram baseFacts
        [{ node := node 0, fact := .unit }]) :=
  { proof := by
      intro input member
      simp only [List.mem_singleton] at member
      subst input
      intro _ _ assumptions
      exact assumptions _ (by simp [baseFacts]) }

/-- Installed fact from the independent sine propagator. -/
def sineEvidence :
    Evidence
      (semantics.Entails extendedProgram baseFacts
        { node := node 3, fact := .nonnegative }) :=
  installRule sineRuleEvidence (meetAll (node 3) .nonnegative)
    (previousAll (node 3)) sineInputSound

def negationRuleEvidence :
    Evidence
      (semantics.Entails extendedProgram
        [{ node := node 3, fact := .nonnegative }]
        { node := node 4, fact := .nonpositive }) :=
  { proof := negationEntails }

def negationInputSound :
    Evidence
      (InputsSound semantics extendedProgram baseFacts
        [{ node := node 3, fact := .nonnegative }]) :=
  { proof := by
      intro input member
      simp only [List.mem_singleton] at member
      subst input
      exact sineEvidence.proof }

/-- Installed fact from the separate negation propagator. -/
def negationEvidence :
    Evidence
      (semantics.Entails extendedProgram baseFacts
        { node := node 4, fact := .nonpositive }) :=
  installRule negationRuleEvidence (meetAll (node 4) .nonpositive)
    (previousAll (node 4)) negationInputSound

def oddnessAction : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := oddnessRuleKey
    node := node 2
    kind := .instantiate
    effort := 0
    generation := 0
    inputs := [] }

def oddnessEdge : EqualityEdge :=
  { left := node 2
    right := node 4
    generation := 1
    origin := oddnessAction
    payload := payload 1 }

def oddnessDomain : SameDomain extendedProgram (node 2) (node 4) :=
  { leftNode := sineNegatedSourceInstruction
    rightNode := negatedSineInstruction
    leftAt := by rfl
    rightAt := by rfl
    domainEq := rfl }

def noInputs :
    Evidence (InputsSound semantics extendedProgram baseFacts []) :=
  { proof := by simp [InputsSound] }

/-- Generic equality transport moves the negation result back to the caller's
original `sin (-x)` node. -/
def transportedEvidence :
    Evidence
      (semantics.Entails extendedProgram baseFacts
        { node := node 2, fact := .nonpositive }) :=
  installTransport laws oddnessEdge oddnessDomain (Or.inl ⟨rfl, rfl⟩)
    { proof := oddnessEntails } (meetAll (node 2) .nonpositive)
    (previousAll (node 2)) negationEvidence noInputs

def checkerInput : CheckerInput Range :=
  { baseProgram
    initialFacts := #[.unit, .all, .all]
    target := { node := node 2, fact := .nonpositive } }

theorem baseWithin : FactsWithin baseProgram baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [baseProgram, node]

/-- Final closure returns the enlarged-network proof to the caller's exact
program and target. -/
def targetEvidence :
    Evidence
      (semantics.Entails baseProgram baseFacts checkerInput.target) :=
  closeBase (input := checkerInput) stable baseWithin
    (by simp [checkerInput, baseProgram, node]) { proof := extension }
    transportedEvidence

noncomputable def baseValuation (x : ℝ) : NodeId -> ℝ
  | ⟨0⟩ => x
  | ⟨1⟩ => -x
  | ⟨2⟩ => Real.sin (-x)
  | _ => 0

theorem baseModels (x : ℝ) : Models baseProgram (baseValuation x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _
    simp [baseValuation, node]
  · intro _
    simp [baseValuation, node]
  · intro impossible
    simp [baseProgram, Program.node?, node] at impossible
  · intro impossible
    simp [baseProgram, Program.node?, node] at impossible

/-- Ordinary kernel theorem produced by the arbitrary-function proof chain.
The upper hypothesis is consumed by the sine propagator rather than by a
rational-normalization backend. -/
theorem sin_neg_nonpositive {x : ℝ} (nonnegative : 0 ≤ x) (atMostOne : x ≤ 1) :
    Real.sin (-x) ≤ 0 := by
  have result := targetEvidence.proof (baseValuation x) (baseModels x) (by
    intro assumption member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨nonnegative, atMostOne⟩
    · trivial
    · trivial)
  exact result

end Hex.Interval.Experiment.SineSign
