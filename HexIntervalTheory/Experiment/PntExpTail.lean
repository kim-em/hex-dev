/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntExpTail
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

/-!
# Real semantics for the PNT+ exponential-tail probe

The provider checks its package-owned reduction certificate in three steps:

1. use Mathlib's proved point enclosure for `exp (-1)`;
2. use `exp_nat_mul` to reduce `exp (-231)` to a natural power; and
3. compare `(46/125)^231` with the exact rational denoted by `1e-100`.

Monotonicity then reuses that single boundary certificate for every input at
most `-231`.  No LeanCert declaration or PNT+ theorem is imported.
-/

namespace Hex.Interval.Experiment.PntExpTail

open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

/-- Mathematical meaning of the finite tail facts. -/
def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .atMostNeg231, x => x ≤ -231
  | .atMostNeg230, x => x ≤ -230
  | .belowTenNeg100, x => x < 1 / (10 : ℝ) ^ 100
  | .empty, _ => False

def sourceModel : OperationSemantics.Model ℝ :=
  { operation := sourceOperation
    relation := fun inputs _ => inputs = [] }

def expModel : OperationSemantics.Model ℝ :=
  { operation := expOperation
    relation := fun inputs output =>
      match inputs with
      | [input] => output = Real.exp input
      | _ => False }

def operationModels : Array (OperationSemantics.Model ℝ) :=
  #[sourceModel, expModel]

def semantics : Semantics Bound :=
  OperationSemantics.semantics operationModels Contains

theorem containsMeet (left right : Bound) (x : ℝ) :
    Contains (left.meet right) x ↔ Contains left x ∧ Contains right x := by
  cases left <;> cases right <;> simp [Bound.meet, Contains]
  all_goals
    intro upper
    have thresholdPositive : 0 < (1 / (10 : ℝ) ^ 100) := by positivity
    linarith

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

/-- Lean scientific notation denotes the exact rational threshold used by the
certificate; no floating-point conversion occurs. -/
theorem scientificThreshold : (1e-100 : ℝ) = 1 / (10 : ℝ) ^ 100 := by
  norm_num [OfScientific.ofScientific]

/-- Load-bearing boundary certificate.  The only analytic point input is the
proved outward enclosure for `exp (-1)`; the large argument is handled by
natural-power range reduction and exact rational comparison. -/
theorem boundaryRat : Real.exp (-(231 : ℝ)) < 1 / (10 : ℝ) ^ 100 := by
  have point : Real.exp (-1) < (46 : ℝ) / 125 :=
    Real.exp_neg_one_lt_d9.trans (by norm_num)
  have powered : Real.exp (-1) ^ 231 < ((46 : ℝ) / 125) ^ 231 :=
    pow_lt_pow_left₀ point (Real.exp_pos (-1)).le (by norm_num)
  rw [← Real.exp_nat_mul] at powered
  have reduced : Real.exp (-(231 : ℝ)) < ((46 : ℝ) / 125) ^ 231 := by
    convert powered using 1
    norm_num
  calc
    Real.exp (-(231 : ℝ)) < ((46 : ℝ) / 125) ^ 231 := reduced
    _ < 1 / (10 : ℝ) ^ 100 := by norm_num

/-- Scientific-notation spelling of the checked rational boundary. -/
theorem boundary : Real.exp (-(231 : ℝ)) < 1e-100 := by
  rw [scientificThreshold]
  exact boundaryRat

/-- Monotone reuse of the checked boundary for every more-negative input. -/
theorem tailOfUpper {y : ℝ} (hy : y ≤ -231) :
    Real.exp y < 1 / (10 : ℝ) ^ 100 :=
  lt_of_le_of_lt (Real.exp_le_exp.mpr hy) boundaryRat

/-- The requested `231 → 230` mutation changes a true boundary into a false
statement.  A lower point enclosure for `exp (-1)`, the same range reduction,
and exact rational arithmetic exhibit the counter-bound. -/
theorem reject230 : ¬ Real.exp (-(230 : ℝ)) < 1e-100 := by
  have point : (9196986029 : ℝ) / 25000000000 < Real.exp (-1) := by
    have stronger := Real.exp_neg_one_gt_d9
    norm_num at stronger ⊢
    linarith
  have powered :
      ((9196986029 : ℝ) / 25000000000) ^ 230 < Real.exp (-1) ^ 230 :=
    pow_lt_pow_left₀ point (by norm_num) (by norm_num)
  rw [← Real.exp_nat_mul] at powered
  have reduced :
      ((9196986029 : ℝ) / 25000000000) ^ 230 <
        Real.exp (-(230 : ℝ)) := by
    convert powered using 1
    norm_num
  have rational :
      (1e-100 : ℝ) < ((9196986029 : ℝ) / 25000000000) ^ 230 := by
    norm_num [OfScientific.ofScientific]
  linarith

theorem tailEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input])
    (inputFacts : assumptions = [{ node := input, fact := .atMostNeg231 }]) :
    semantics.Entails graph assumptions
      { node := output, fact := .belowTenNeg100 } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .belowTenNeg100 (valuation output)
  intro valuation model holds
  have inputUpper : valuation input ≤ -231 := by
    exact holds { node := input, fact := .atMostNeg231 } (by simp [inputFacts])
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have outputEq : valuation output = Real.exp (valuation input) := by
    simpa [expModel, arguments, List.map] using related
  change valuation output < 1 / (10 : ℝ) ^ 100
  rw [outputEq]
  exact tailOfUpper inputUpper

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) :
    fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

/-- Replay accepts only the package-owned range-reduction certificate and the
exact `x ≤ -231` watched fact. -/
def tailFactSchema : PackedFactSchema semantics where
  rule := tailRuleKey
  schema := 1
  Certificate := ReductionCertificate
  decode := decodeCertificate?
  replay := fun _ _ context certificate =>
    if certificateShape : certificate = tailCertificate then
      if proposedFact : context.proposed.fact = .belowTenNeg100 then
        match found : context.program.node? context.proposed.node with
        | some instruction =>
            if operation : instruction.op = ({ index := 1 } : OpId) then
              match arguments : instruction.args with
              | [input] =>
                  if inputFacts : context.assumptions =
                      [{ node := input, fact := .atMostNeg231 }] then
                    some
                      { proof := by
                          have proposedEq :
                              context.proposed =
                                { node := context.proposed.node,
                                  fact := .belowTenNeg100 } := by
                            exact factWith context.proposed proposedFact
                          rw [proposedEq]
                          exact
                            tailEntails context.program context.assumptions
                              context.proposed.node instruction input found
                              operation arguments inputFacts }
                  else
                    none
              | _ => none
            else
              none
        | none => none
      else
        none
    else
      none

def stableLaw : StableLaw semantics :=
  OperationSemantics.stableLaw operationModels Contains

def sourceEmit : EmitPackage Lean.Name := { schemas := [] }

def expEmit : EmitPackage Lean.Name :=
  { schemas :=
      [{ key := tailFactSchema.key
         handle := ``tailFactSchema }] }

def sourceProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[] }
    emit := sourceEmit }

def expProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[tailFactSchema] }
    emit := expEmit }

def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof, expProof]

def baseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .atMostNeg231 },
    { node := node 1, fact := .all }]

def checkerInput : CheckerInput Bound :=
  { baseProgram := program
    initialFacts := #[.atMostNeg231, .all]
    target := { node := node 1, fact := .belowTenNeg100 } }

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [program, node]

theorem basePrefix : ProgramPrefix program program :=
  ProgramPrefix.refl program

theorem sameOperations : program.operations = program.operations := rfl

def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

noncomputable def valuation (x : ℝ) : NodeId → ℝ
  | ⟨0⟩ => -x
  | ⟨1⟩ => Real.exp (-x)
  | _ => 0

theorem valuationModels (x : ℝ) : semantics.models program (valuation x) := by
  refine ⟨?_, ?_⟩
  · simp [program, operations, operationModels, sourceModel, expModel]
  rintro ⟨index⟩ instruction found
  cases index with
  | zero =>
      simp [Program.node?, program, sourceInstruction] at found
      subst instruction
      exact ⟨sourceModel, by rfl, by rfl⟩
  | succ index =>
      cases index with
      | zero =>
          simp [Program.node?, program, expInstruction] at found
          subst instruction
          exact ⟨expModel, by rfl, by rfl⟩
      | succ index =>
          simp [Program.node?, program] at found

/-- Close emitted generic evidence to the reusable PNT+ tail theorem. -/
theorem closeTail (x : ℝ) (hx : 231 ≤ x)
    (result : Evidence
      (semantics.Entails program baseFacts checkerInput.target)) :
    Real.exp (-x) < 1e-100 := by
  rw [scientificThreshold]
  exact result.proof (valuation x) (valuationModels x) (by
    intro fact member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change -x ≤ (-231 : ℝ)
      linarith
    · trivial)

end Hex.Interval.Experiment.PntExpTail
