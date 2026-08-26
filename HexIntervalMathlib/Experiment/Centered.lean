/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import HexIntervalMathlib.Experiment.DyadicInterval
public import HexInterval.Experiment.DyadicRules

@[expose] public section

/-!
# Real semantics for the centered arbitrary-function package

The executable package treats its operation key opaquely. This companion gives
that key the meaning `x ↦ 1/4 - (x - 1/2)^2` and owns the theorem behind the
package's `[0,1] ↦ [0,1/4]` proposal. Generic replay contains no centered-
function case.
-/

namespace Hex.Interval.Experiment.Centered

open Propagator SemanticReplay
open DyadicInterval DyadicRules

/-- The canonical caller interval used by the first centered canary. -/
def unitRange : DyadicInterval.Fact :=
  ⟨.bounds (.finite 0 false) (.finite 1 false), by decide⟩

/-- Exact range of the centered form over `[0,1]`. -/
def quarterRange : DyadicInterval.Fact :=
  ⟨.bounds (.finite 0 false) (.finite quarter false), by decide⟩

def threeSixteenths : Dyadic := Dyadic.ofIntWithPrec 3 4

def threeQuarters : Dyadic := Dyadic.ofIntWithPrec 3 2

/-- Output band which forces the input into the middle half of the domain. -/
def highRange : DyadicInterval.Fact :=
  ⟨.bounds (.finite threeSixteenths false) (.finite quarter false), by decide⟩

/-- Backward image of `highRange` under the centered function. -/
def middleRange : DyadicInterval.Fact :=
  ⟨.bounds (.finite quarter false) (.finite threeQuarters false), by decide⟩

@[simp]
theorem toReal_half : DyadicInterval.toReal half = (1 / 2 : ℝ) := by
  norm_num [DyadicInterval.toReal, half,
    Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]

@[simp]
theorem toReal_one : DyadicInterval.toReal 1 = (1 : ℝ) := by
  rw [DyadicInterval.toReal,
    show (1 : Dyadic) = ((1 : Int) : Dyadic) from rfl,
    Dyadic.toRat_intCast]
  norm_num

@[simp]
theorem toReal_quarter : DyadicInterval.toReal quarter = (1 / 4 : ℝ) := by
  norm_num [DyadicInterval.toReal, quarter,
    Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]

@[simp]
theorem toReal_threeSixteenths :
    DyadicInterval.toReal threeSixteenths = (3 / 16 : ℝ) := by
  norm_num [threeSixteenths, DyadicInterval.toReal,
    Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]

@[simp]
theorem toReal_threeQuarters :
    DyadicInterval.toReal threeQuarters = (3 / 4 : ℝ) := by
  norm_num [threeQuarters, DyadicInterval.toReal,
    Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]

/-- Function-package contribution to a program model. Other operations remain
the responsibility of their own packages. -/
def Models (program : Program) (valuation : NodeId → ℝ) : Prop :=
  ∀ output instruction,
    program.node? output = some instruction →
    ∀ operation,
      program.operation? instruction.op = some operation →
      operation.key = centeredOp →
      ∃ input, instruction.args = [input] ∧
        valuation output =
          (1 / 4 : ℝ) - (valuation input - (1 / 2 : ℝ)) ^ 2

/-- Exact interval facts interpreted over the centered package's real model. -/
def semantics : Semantics DyadicInterval.Fact :=
  DyadicInterval.realSemantics Models

/-- A local endpoint budget for proof-side meet checking. Semantic rule replay
does not depend on the planner's chosen budget. -/
def endpointLimit : EndpointLimit :=
  { maxEndpointHeight := 128, maxAlignmentShift := 64 }

/-- Shared exact fact-domain theorem under the centered semantics. -/
def domain : FactDomainSchema semantics :=
  DyadicInterval.factSchema endpointLimit Models

theorem centeredEntails (program : Program)
    (assumptions : List (NodeFact DyadicInterval.Fact))
    (output : NodeId) (instruction : Node) (operation : Operation)
    (input : NodeId)
    (found : program.node? output = some instruction)
    (operationFound : program.operation? instruction.op = some operation)
    (key : operation.key = centeredOp)
    (arguments : instruction.args = [input])
    (exactAssumptions : assumptions = [{ node := input, fact := unitRange }]) :
    semantics.Entails program assumptions { node := output, fact := quarterRange } := by
  intro valuation model assumptionHolds
  change NodeId → ℝ at valuation
  change Models program valuation at model
  obtain ⟨actualInput, actualArguments, outputEq⟩ :=
    model output instruction found operation operationFound key
  have sameInput : actualInput = input := by
    simpa [arguments] using actualArguments.symm
  subst actualInput
  have inputRange := assumptionHolds { node := input, fact := unitRange } (by
    simp [exactAssumptions])
  change unitRange.Contains (valuation input) at inputRange
  change quarterRange.Contains (valuation output)
  simp only [unitRange, quarterRange, DyadicInterval.Fact.Contains, rawContains,
    lowerContains,
    upperContains, DyadicInterval.toReal_zero, toReal_one,
    toReal_quarter] at inputRange ⊢
  rw [outputEq]
  constructor <;> nlinarith [sq_nonneg (valuation input - (1 / 2 : ℝ))]

theorem backwardEntails (program : Program)
    (assumptions : List (NodeFact DyadicInterval.Fact))
    (input output : NodeId) (instruction : Node) (operation : Operation)
    (found : program.node? output = some instruction)
    (operationFound : program.operation? instruction.op = some operation)
    (key : operation.key = centeredOp)
    (arguments : instruction.args = [input])
    (exactAssumptions : assumptions = [{ node := output, fact := highRange }]) :
    semantics.Entails program assumptions { node := input, fact := middleRange } := by
  intro valuation model assumptionHolds
  change NodeId → ℝ at valuation
  change Models program valuation at model
  obtain ⟨actualInput, actualArguments, outputEq⟩ :=
    model output instruction found operation operationFound key
  have sameInput : actualInput = input := by
    simpa [arguments] using actualArguments.symm
  subst actualInput
  have outputRange := assumptionHolds { node := output, fact := highRange } (by
    simp [exactAssumptions])
  change highRange.Contains (valuation output) at outputRange
  change middleRange.Contains (valuation input)
  simp only [highRange, middleRange, DyadicInterval.Fact.Contains, rawContains,
    lowerContains, upperContains, toReal_threeSixteenths, toReal_quarter,
    toReal_threeQuarters] at outputRange ⊢
  rw [outputEq] at outputRange
  constructor <;>
    nlinarith [sq_nonneg (valuation input - (1 / 4 : ℝ)),
      sq_nonneg (valuation input - (3 / 4 : ℝ))]

private theorem factWith (fact : NodeFact DyadicInterval.Fact)
    {value : DyadicInterval.Fact}
    (equal : fact.fact = value) :
    fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

/-- Package-owned transparent schema for the executable centered contractor's
empty schema-zero payload. -/
def centeredFactSchema : PackedFactSchema semantics where
  rule := centeredForwardKey
  schema := 0
  Certificate := Unit
  decode := fun body => if body.isEmpty then some () else none
  replay := fun _ _ context _ =>
    if proposedFact : context.proposed.fact = quarterRange then
      match found : context.program.node? context.proposed.node with
      | some instruction =>
          match operationFound : context.program.operation? instruction.op with
          | some operation =>
              if key : operation.key = centeredOp then
                match arguments : instruction.args with
                | [input] =>
                    if exactAssumptions :
                        context.assumptions = [{ node := input, fact := unitRange }]
                    then
                      some
                        { proof := by
                            have proposedEq :
                                context.proposed =
                                  { node := context.proposed.node,
                                    fact := quarterRange } :=
                              factWith context.proposed proposedFact
                            rw [proposedEq]
                            exact centeredEntails context.program
                              context.assumptions context.proposed.node
                              instruction operation input found operationFound
                              key arguments exactAssumptions }
                    else none
                | _ => none
              else none
          | none => none
      | none => none
    else none

/-- Package-owned backward contractor. The exact output band is part of the
schema, while the generic replay layer remains unaware of the function. -/
def backwardFactSchema (backwardKey : RuleKey) : PackedFactSchema semantics where
  rule := backwardKey
  schema := 0
  Certificate := Unit
  decode := fun body => if body.isEmpty then some () else none
  replay := fun _ _ context _ =>
    if proposedFact : context.proposed.fact = middleRange then
      match context.assumptions with
      | [{ node := output, fact := outputFact }] =>
          if outputExact : outputFact = highRange then
            match found : context.program.node? output with
            | some instruction =>
                match operationFound : context.program.operation? instruction.op with
                | some operation =>
                    if key : operation.key = centeredOp then
                      match arguments : instruction.args with
                      | [input] =>
                          if inputExact : input = context.proposed.node then
                            some
                              { proof := by
                                  rw [factWith context.proposed proposedFact]
                                  have result := backwardEntails context.program
                                    [{ node := output, fact := outputFact }]
                                    input output instruction operation found
                                    operationFound key arguments (by simp [outputExact])
                                  simpa only [inputExact] using result }
                          else none
                      | _ => none
                    else none
                | none => none
            | none => none
          else none
      | _ => none
    else none

end Hex.Interval.Experiment.Centered
