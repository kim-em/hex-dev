/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalAlgebraic.Experiment.PolynomialDispatch
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics
public import HexRealRootsMathlib.Isolations
public import HexRootsMathlib.Examples
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Proof boundary for specialized polynomial dispatch

The runtime dispatcher may call either specialized engine, but its result is
not semantic evidence.  These schemas independently authenticate the graph,
coefficient recipe, backend payload, and exact output fact, then invoke the
real Sturm or complex NK/Pellet correspondence theorems.
-/

namespace Hex.Interval.Experiment.PolynomialDispatch

open Polynomial
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics
open Hex

noncomputable section

def variableModel (R : Type) [CommRing R] (key : OpKey) :
    OperationSemantics.Model R :=
  { operation := nullary key
    relation := fun inputs _ => inputs = [] }

def constantModel (R : Type) [CommRing R] (key : OpKey) (value : Int) :
    OperationSemantics.Model R :=
  { operation := nullary key
    relation := fun inputs output => inputs = [] ∧ output = value }

def binaryModel (R : Type) [CommRing R] (key : OpKey) (combine : R → R → R) :
    OperationSemantics.Model R :=
  { operation := binary key
    relation := fun inputs output =>
      match inputs with
      | [left, right] => output = combine left right
      | _ => False }

def unsupportedModel (R : Type) [CommRing R] : OperationSemantics.Model R :=
  { operation := unary expKey, relation := fun _ _ => False }

/-- A query carries the distinguished indeterminate as its first argument and
the evaluated polynomial subgraph as its second.  It may return that point
only when the polynomial value is zero. -/
def queryModel (R : Type) [CommRing R] (key : OpKey) :
    OperationSemantics.Model R :=
  { operation := binary key
    relation := fun inputs output =>
      match inputs with
      | [point, value] => output = point ∧ value = 0
      | _ => False }

def algebraModels (R : Type) [CommRing R] :
    Array (OperationSemantics.Model R) :=
  #[variableModel R variableKey, variableModel R otherVariableKey,
    constantModel R oneKey 1, constantModel R twoKey 2,
    binaryModel R addKey (fun x y => x + y),
    binaryModel R subKey (fun x y => x - y),
    binaryModel R mulKey (fun x y => x * y), unsupportedModel R,
    queryModel R realRootsKey, queryModel R complexRootsKey]

def realModels : Array (OperationSemantics.Model ℝ) := algebraModels ℝ
def complexModels : Array (OperationSemantics.Model ℂ) := algebraModels ℂ

def RealContains : Bound → ℝ → Prop
  | .all, _ => True
  | .cubeTwoReal, x => (5 : ℝ) / 4 < x ∧ x ≤ 21 / 16
  | .pisotComplex, _ => False
  | .empty, _ => False

def ComplexContains : Bound → ℂ → Prop
  | .all, _ => True
  | .cubeTwoReal, _ => False
  | .pisotComplex, z =>
      z ∈ HexRootsMathlib.DyadicSquare.closedSquare
          HexRootsMathlib.Examples.pisotLowerSquare ∨
        z ∈ HexRootsMathlib.DyadicSquare.closedSquare
          HexRootsMathlib.Examples.pisotUpperSquare ∨
        z ∈ HexRootsMathlib.DyadicSquare.closedSquare
          HexRootsMathlib.Examples.pisotRealSquare
  | .empty, _ => False

def realSemantics : Semantics Bound :=
  OperationSemantics.semantics realModels RealContains

def complexSemantics : Semantics Bound :=
  OperationSemantics.semantics complexModels ComplexContains

theorem realContainsMeet (left right : Bound) (x : ℝ) :
    RealContains (left.meet right) x ↔
      RealContains left x ∧ RealContains right x := by
  cases left <;> cases right <;> simp [Bound.meet, RealContains]

theorem complexContainsMeet (left right : Bound) (x : ℂ) :
    ComplexContains (left.meet right) x ↔
      ComplexContains left x ∧ ComplexContains right x := by
  cases left <;> cases right <;> simp [Bound.meet, ComplexContains]

def realBoundSchema : FactDomainSchema realSemantics :=
  { top := fun _ => .all
    topSound := by intro _ _ _ _ _ _; trivial
    proveMeet := fun _ _ previous proposed installed =>
      if exact : installed = previous.meet proposed then
        some
          { proof := by
              subst installed
              intro valuation _
              exact realContainsMeet previous proposed (valuation _) }
      else none }

def complexBoundSchema : FactDomainSchema complexSemantics :=
  { top := fun _ => .all
    topSound := by intro _ _ _ _ _ _; trivial
    proveMeet := fun _ _ previous proposed installed =>
      if exact : installed = previous.meet proposed then
        some
          { proof := by
              subst installed
              intro valuation _
              exact complexContainsMeet previous proposed (valuation _) }
      else none }

def realLaws : Laws realSemantics :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change RealContains fact (valuation left) ↔ RealContains fact (valuation right)
      rw [values] }

def complexLaws : Laws complexSemantics :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change ComplexContains fact (valuation left) ↔ ComplexContains fact (valuation right)
      rw [values] }

/-! ## Specialized backend correspondence -/

def cubeTwoIsolation : RealRootIsolation cubeTwo :=
  { interval :=
      { lower := cubeTwoLower, upper := cubeTwoUpper, lt := by decide }
    count_one := by decide }

def cubeTwoOutput : RealRootIsolations cubeTwo :=
  { isolations := #[cubeTwoIsolation]
    ordered := by
      intro i j hij
      fin_cases i
      fin_cases j
      simp at hij
    complete := by decide }

theorem cubeTwo_ne_zero : cubeTwo ≠ 0 := by
  intro equal
  have coefficient := congrArg (fun p : ZPoly => p.coeff 3) equal
  norm_num [cubeTwo, cubeTwoCode] at coefficient

theorem cubeTwo_squareFree : ZPoly.SquareFreeRat cubeTwo :=
  HexRealRootsMathlib.squareFreeRat_of_hasSquarefreeSturmChain cubeTwo (by decide)

theorem toPolyReal_cubeTwo :
    HexRealRootsMathlib.toPolyℝ cubeTwo = X ^ 3 - 2 := by
  simp [cubeTwo, cubeTwoCode, HexRealRootsMathlib.toPolyℝ,
    HexPolyMathlib.toPolynomial_ofCoeffs, Finset.sum_range_succ]
  ring

/-- The complete Sturm result places every real root, not merely a selected
witness, in the dispatched interval. -/
theorem cubeTwo_bounds {x : ℝ} (root : x ^ 3 - 2 = 0) :
    (5 : ℝ) / 4 < x ∧ x ≤ 21 / 16 := by
  have polynomialRoot : (HexRealRootsMathlib.toPolyℝ cubeTwo).IsRoot x := by
    rw [toPolyReal_cubeTwo, Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_ofNat]
    exact root
  obtain ⟨isolation, ⟨member, lower, upper⟩, _⟩ :=
    cubeTwoOutput.isolates cubeTwo_ne_zero cubeTwo_squareFree x polynomialRoot
  simp [cubeTwoOutput] at member
  subst isolation
  norm_num [cubeTwoIsolation, cubeTwoLower, cubeTwoUpper,
    Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow] at lower upper
  exact ⟨lower, upper⟩

/-- Completeness of the complex specialized engine's three certified atoms. -/
theorem pisot_covered {z : ℂ} (root : z ^ 3 - z - 1 = 0) :
    ComplexContains .pisotComplex z := by
  have polynomialRoot :
      (HexRootsMathlib.toPolyℂ HexRootsMathlib.Examples.pisot).eval z = 0 := by
    rw [HexRootsMathlib.Examples.toPolyℂ_pisot]
    simpa using root
  have nonzero : HexRootsMathlib.toPolyℂ HexRootsMathlib.Examples.pisot ≠ 0 := by
    rw [HexRootsMathlib.Examples.toPolyℂ_pisot]
    intro equal
    have coefficient := congrArg (fun p : ℂ[X] => p.coeff 3) equal
    norm_num [coeff_X_pow] at coefficient
    rw [coeff_X, coeff_one] at coefficient
    norm_num at coefficient
  have member : z ∈
      (HexRootsMathlib.toPolyℂ HexRootsMathlib.Examples.pisot).roots.toFinset :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots nonzero).mpr polynomialRoot)
  rw [HexRootsMathlib.Examples.pisot_roots] at member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact Or.inr (Or.inr HexRootsMathlib.Examples.pisotRealRoot_spec.2)
  · exact Or.inl HexRootsMathlib.Examples.pisotLowerRoot_spec.2
  · exact Or.inr (Or.inl HexRootsMathlib.Examples.pisotUpperRoot_spec.2)

/-! ## Fixed-graph semantic extraction -/

private theorem relationAt {R : Type} [CommRing R]
    (models : Array (OperationSemantics.Model R))
    (graph : Program) (valuation : NodeId → R)
    (modeled : OperationSemantics.Models models graph valuation)
    (target : NodeId) (instruction : Node)
    (found : graph.node? target = some instruction) :
    ∃ meaning, models[instruction.op.index]? = some meaning ∧
      meaning.relation (instruction.args.map valuation) (valuation target) := by
  obtain ⟨meaning, meaningAt, related⟩ := modeled.2 target instruction found
  exact ⟨meaning, meaningAt, related⟩

theorem realEntails :
    realSemantics.Entails realProgram []
      { node := node 5, fact := .cubeTwoReal } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models realModels realProgram valuation →
      (∀ assumption, assumption ∈ ([] : List (NodeFact Bound)) →
        RealContains assumption.fact (valuation assumption.node)) →
        RealContains .cubeTwoReal (valuation (node 5))
  intro valuation modeled _
  have two : valuation (node 1) = 2 := by
    obtain ⟨meaning, meaningAt, related⟩ := relationAt realModels realProgram valuation modeled
      (node 1) (instruction 3) (by simp [realProgram, Program.node?, node])
    simp [instruction, realModels, algebraModels] at meaningAt
    subst meaning
    simpa [constantModel, instruction] using related
  have square : valuation (node 2) = valuation (node 0) * valuation (node 0) := by
    obtain ⟨meaning, meaningAt, related⟩ := relationAt realModels realProgram valuation modeled
      (node 2) (instruction 6 [node 0, node 0])
        (by simp [realProgram, Program.node?, node])
    simp [instruction, realModels, algebraModels] at meaningAt
    subst meaning
    simpa [binaryModel, instruction] using related
  have cube : valuation (node 3) = valuation (node 2) * valuation (node 0) := by
    obtain ⟨meaning, meaningAt, related⟩ := relationAt realModels realProgram valuation modeled
      (node 3) (instruction 6 [node 2, node 0])
        (by simp [realProgram, Program.node?, node])
    simp [instruction, realModels, algebraModels] at meaningAt
    subst meaning
    simpa [binaryModel, instruction] using related
  have polynomial : valuation (node 4) = valuation (node 3) - valuation (node 1) := by
    obtain ⟨meaning, meaningAt, related⟩ := relationAt realModels realProgram valuation modeled
      (node 4) (instruction 5 [node 3, node 1])
        (by simp [realProgram, Program.node?, node])
    simp [instruction, realModels, algebraModels] at meaningAt
    subst meaning
    simpa [binaryModel, instruction] using related
  have query : valuation (node 5) = valuation (node 0) ∧ valuation (node 4) = 0 := by
    obtain ⟨meaning, meaningAt, related⟩ := relationAt realModels realProgram valuation modeled
      (node 5) (instruction 8 [node 0, node 4])
        (by simp [realProgram, Program.node?, node])
    simp [instruction, realModels, algebraModels] at meaningAt
    subst meaning
    simpa [queryModel, instruction] using related
  change RealContains .cubeTwoReal (valuation (node 5))
  rw [query.1]
  apply cubeTwo_bounds
  rw [polynomial, cube, square, two] at query
  nlinarith [query.2]

theorem complexEntails :
    complexSemantics.Entails complexProgram []
      { node := node 6, fact := .pisotComplex } := by
  change ∀ valuation : NodeId → ℂ,
    OperationSemantics.Models complexModels complexProgram valuation →
      (∀ assumption, assumption ∈ ([] : List (NodeFact Bound)) →
        ComplexContains assumption.fact (valuation assumption.node)) →
        ComplexContains .pisotComplex (valuation (node 6))
  intro valuation modeled _
  have one : valuation (node 1) = 1 := by
    obtain ⟨meaning, meaningAt, related⟩ := relationAt complexModels complexProgram valuation modeled
      (node 1) (instruction 2) (by simp [complexProgram, Program.node?, node])
    simp [instruction, complexModels, algebraModels] at meaningAt
    subst meaning
    simpa [constantModel, instruction] using related
  have square : valuation (node 2) = valuation (node 0) * valuation (node 0) := by
    obtain ⟨meaning, meaningAt, related⟩ := relationAt complexModels complexProgram valuation modeled
      (node 2) (instruction 6 [node 0, node 0])
        (by simp [complexProgram, Program.node?, node])
    simp [instruction, complexModels, algebraModels] at meaningAt
    subst meaning
    simpa [binaryModel, instruction] using related
  have cube : valuation (node 3) = valuation (node 2) * valuation (node 0) := by
    obtain ⟨meaning, meaningAt, related⟩ := relationAt complexModels complexProgram valuation modeled
      (node 3) (instruction 6 [node 2, node 0])
        (by simp [complexProgram, Program.node?, node])
    simp [instruction, complexModels, algebraModels] at meaningAt
    subst meaning
    simpa [binaryModel, instruction] using related
  have subtractX : valuation (node 4) = valuation (node 3) - valuation (node 0) := by
    obtain ⟨meaning, meaningAt, related⟩ := relationAt complexModels complexProgram valuation modeled
      (node 4) (instruction 5 [node 3, node 0])
        (by simp [complexProgram, Program.node?, node])
    simp [instruction, complexModels, algebraModels] at meaningAt
    subst meaning
    simpa [binaryModel, instruction] using related
  have polynomial : valuation (node 5) = valuation (node 4) - valuation (node 1) := by
    obtain ⟨meaning, meaningAt, related⟩ := relationAt complexModels complexProgram valuation modeled
      (node 5) (instruction 5 [node 4, node 1])
        (by simp [complexProgram, Program.node?, node])
    simp [instruction, complexModels, algebraModels] at meaningAt
    subst meaning
    simpa [binaryModel, instruction] using related
  have query : valuation (node 6) = valuation (node 0) ∧ valuation (node 5) = 0 := by
    obtain ⟨meaning, meaningAt, related⟩ := relationAt complexModels complexProgram valuation modeled
      (node 6) (instruction 9 [node 0, node 5])
        (by simp [complexProgram, Program.node?, node])
    simp [instruction, complexModels, algebraModels] at meaningAt
    subst meaning
    simpa [queryModel, instruction] using related
  change ComplexContains .pisotComplex (valuation (node 6))
  rw [query.1]
  apply pisot_covered
  rw [polynomial, subtractX, cube, square, one] at query
  simpa [pow_succ] using query.2

/-! ## Replay schemas -/

def realFactSchema : PackedFactSchema realSemantics where
  rule := realRuleKey
  schema := 1
  Certificate := DispatchCertificate
  decode := decodeReal?
  replay := fun _ action context decoded =>
    if certificateShape : decoded = realCertificate then
      if programShape : context.program = realProgram then
        if actionNode : action.node = node 5 then
          if targetNode : context.proposed.node = node 5 then
            if targetFact : context.proposed.fact = .cubeTwoReal then
              if noAssumptions : context.assumptions = [] then
                some
                  { proof := by
                      have proposed : context.proposed =
                          { node := node 5, fact := .cubeTwoReal } := by
                        cases proposedShape : context.proposed with
                        | mk proposedNode proposedFact =>
                          have nodeShape : proposedNode = node 5 := by
                            simpa [proposedShape] using targetNode
                          have factShape : proposedFact = .cubeTwoReal := by
                            simpa [proposedShape] using targetFact
                          rw [nodeShape, factShape]
                      rw [programShape, proposed, noAssumptions]
                      exact realEntails }
              else none
            else none
          else none
        else none
      else none
    else none

def complexFactSchema : PackedFactSchema complexSemantics where
  rule := complexRuleKey
  schema := 2
  Certificate := DispatchCertificate
  decode := decodeComplex?
  replay := fun _ action context decoded =>
    if certificateShape : decoded = complexCertificate then
      if programShape : context.program = complexProgram then
        if actionNode : action.node = node 6 then
          if targetNode : context.proposed.node = node 6 then
            if targetFact : context.proposed.fact = .pisotComplex then
              if noAssumptions : context.assumptions = [] then
                some
                  { proof := by
                      have proposed : context.proposed =
                          { node := node 6, fact := .pisotComplex } := by
                        cases proposedShape : context.proposed with
                        | mk proposedNode proposedFact =>
                          have nodeShape : proposedNode = node 6 := by
                            simpa [proposedShape] using targetNode
                          have factShape : proposedFact = .pisotComplex := by
                            simpa [proposedShape] using targetFact
                          rw [nodeShape, factShape]
                      rw [programShape, proposed, noAssumptions]
                      exact complexEntails }
              else none
            else none
          else none
        else none
      else none
    else none

def realStableLaw : StableLaw realSemantics :=
  OperationSemantics.stableLaw realModels RealContains

def complexStableLaw : StableLaw complexSemantics :=
  OperationSemantics.stableLaw complexModels ComplexContains

def realProofPackage : ProofRegistry.Package realSemantics Lean.Name :=
  { semantic := { factSchemas := #[realFactSchema] }
    emit := { schemas := [{ key := realFactSchema.key, handle := ``realFactSchema }] } }

def complexProofPackage : ProofRegistry.Package complexSemantics Lean.Name :=
  { semantic := { factSchemas := #[complexFactSchema] }
    emit :=
      { schemas := [{ key := complexFactSchema.key, handle := ``complexFactSchema }] } }

def realProofPackages : Array (ProofRegistry.Package realSemantics Lean.Name) :=
  #[realProofPackage]

def complexProofPackages : Array (ProofRegistry.Package complexSemantics Lean.Name) :=
  #[complexProofPackage]

def realBaseFacts : List (NodeFact Bound) :=
  (List.range realProgram.nodes.size).map fun index =>
    { node := node index, fact := .all }

def complexBaseFacts : List (NodeFact Bound) :=
  (List.range complexProgram.nodes.size).map fun index =>
    { node := node index, fact := .all }

def realCheckerInput : CheckerInput Bound :=
  { baseProgram := realProgram
    initialFacts := Array.replicate realProgram.nodes.size .all
    target := { node := node 5, fact := .cubeTwoReal } }

def complexCheckerInput : CheckerInput Bound :=
  { baseProgram := complexProgram
    initialFacts := Array.replicate complexProgram.nodes.size .all
    target := { node := node 6, fact := .pisotComplex } }

theorem realBaseWithin : FactsWithin realProgram realBaseFacts := by
  intro fact member
  simp [realBaseFacts] at member
  obtain ⟨index, bound, rfl⟩ := member
  simp [realProgram, node] at bound ⊢
  omega

theorem complexBaseWithin : FactsWithin complexProgram complexBaseFacts := by
  intro fact member
  simp [complexBaseFacts] at member
  obtain ⟨index, bound, rfl⟩ := member
  simp [complexProgram, node] at bound ⊢
  omega

theorem realPrefix : ProgramPrefix realProgram realProgram := ProgramPrefix.refl _
theorem complexPrefix : ProgramPrefix complexProgram complexProgram := ProgramPrefix.refl _
theorem realOperations : realProgram.operations = realProgram.operations := rfl
theorem complexOperations : complexProgram.operations = complexProgram.operations := rfl

def realExtension : Evidence (realSemantics.Extends realProgram realProgram) :=
  extendRefl realSemantics realProgram

def complexExtension : Evidence (complexSemantics.Extends complexProgram complexProgram) :=
  extendRefl complexSemantics complexProgram

noncomputable def realValuation (x : ℝ) : NodeId → ℝ
  | ⟨0⟩ => x
  | ⟨1⟩ => 2
  | ⟨2⟩ => x * x
  | ⟨3⟩ => x * x * x
  | ⟨4⟩ => x * x * x - 2
  | ⟨5⟩ => x
  | _ => 0

theorem realValuationModels {x : ℝ} (root : x ^ 3 - 2 = 0) :
    realSemantics.models realProgram (realValuation x) := by
  refine ⟨by simp [realProgram, operations, realModels, algebraModels, variableModel,
    constantModel, binaryModel, unsupportedModel, queryModel, nullary, unary, binary], ?_⟩
  rintro ⟨index⟩ actual found
  change realProgram.nodes[index]? = some actual at found
  have indexBound := (Array.getElem?_eq_some_iff.mp found).1
  simp [realProgram] at indexBound
  interval_cases index <;>
    simp [realProgram, instruction] at found <;>
    subst actual <;>
    simp_all [realModels, algebraModels, variableModel, constantModel, binaryModel,
      queryModel, realValuation, node, pow_succ]

noncomputable def complexValuation (z : ℂ) : NodeId → ℂ
  | ⟨0⟩ => z
  | ⟨1⟩ => 1
  | ⟨2⟩ => z * z
  | ⟨3⟩ => z * z * z
  | ⟨4⟩ => z * z * z - z
  | ⟨5⟩ => z * z * z - z - 1
  | ⟨6⟩ => z
  | _ => 0

theorem complexValuationModels {z : ℂ} (root : z ^ 3 - z - 1 = 0) :
    complexSemantics.models complexProgram (complexValuation z) := by
  refine ⟨by simp [complexProgram, operations, complexModels, algebraModels, variableModel,
    constantModel, binaryModel, unsupportedModel, queryModel, nullary, unary, binary], ?_⟩
  rintro ⟨index⟩ actual found
  change complexProgram.nodes[index]? = some actual at found
  have indexBound := (Array.getElem?_eq_some_iff.mp found).1
  simp [complexProgram] at indexBound
  interval_cases index <;>
    simp [complexProgram, instruction] at found <;>
    subst actual <;>
    simp_all [complexModels, algebraModels, variableModel, constantModel, binaryModel,
      queryModel, complexValuation, node, pow_succ]

theorem closeReal
    (result : Evidence
      (realSemantics.Entails realProgram realBaseFacts realCheckerInput.target))
    {x : ℝ} (root : x ^ 3 - 2 = 0) :
    (5 : ℝ) / 4 < x ∧ x ≤ 21 / 16 := by
  have closed := result.proof (realValuation x) (realValuationModels root) (by
    intro fact member
    simp [realBaseFacts] at member
    rcases member with ⟨index, bound, rfl⟩
    trivial)
  exact closed

theorem closeComplex
    (result : Evidence
      (complexSemantics.Entails complexProgram complexBaseFacts complexCheckerInput.target))
    {z : ℂ} (root : z ^ 3 - z - 1 = 0) :
    ComplexContains .pisotComplex z := by
  have closed := result.proof (complexValuation z) (complexValuationModels root) (by
    intro fact member
    simp [complexBaseFacts] at member
    rcases member with ⟨index, bound, rfl⟩
    trivial)
  exact closed

end

end Hex.Interval.Experiment.PolynomialDispatch
