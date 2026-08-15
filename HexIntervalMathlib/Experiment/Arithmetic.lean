/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.DyadicInterval
public import HexInterval.Experiment.DyadicRules

@[expose] public section

/-!
# Real semantics for exact arithmetic propagators

This companion supplies the first package-owned arithmetic replay schema for
the Mathlib-free dyadic registry. The generic proof emitter remains unaware of
subtraction: it checks the rule address and event links, then invokes the
schema below on the exact ordered input facts. This experiment is a package
callback/proof adapter, not another public interval subtraction API; the
supported resource-checked operation is `Hex.Interval.subWithin`.
-/

namespace Hex.Interval.Experiment.Arithmetic

open Propagator SemanticReplay
open DyadicInterval DyadicRules

/-- Real meaning contributed by the arithmetic package for subtraction nodes.
Other operation keys remain available for independent semantic packages. -/
def Models (program : Program) (valuation : NodeId → ℝ) : Prop :=
  ∀ output instruction,
    program.node? output = some instruction →
    ∀ operation,
      program.operation? instruction.op = some operation →
      operation.key = subOp →
      ∃ left right, instruction.args = [left, right] ∧
        valuation output = valuation left - valuation right

/-- Exact dyadic facts interpreted over the arithmetic package's real model. -/
def semantics : Semantics DyadicInterval.Fact :=
  DyadicInterval.realSemantics Models

/-- Shared exact fact-domain laws at the replay budget selected by the caller. -/
def domain (limit : EndpointLimit) : FactDomainSchema semantics :=
  DyadicInterval.factSchema limit Models

/-- Semantic theorem behind every successful executable forward-subtraction
proposal, with no restriction to bounded or closed facts. -/
theorem subEntails (limit : EndpointLimit) (program : Program)
    (assumptions : List (NodeFact DyadicInterval.Fact))
    (output : NodeId) (instruction : Node) (operation : Operation)
    (left right : NodeFact DyadicInterval.Fact)
    (result : DyadicInterval.Fact)
    (found : program.node? output = some instruction)
    (operationFound : program.operation? instruction.op = some operation)
    (key : operation.key = subOp)
    (arguments : instruction.args = [left.node, right.node])
    (exactAssumptions : assumptions = [left, right])
    (computed : DyadicInterval.sub limit left.fact right.fact = .ready result) :
    semantics.Entails program assumptions { node := output, fact := result } := by
  intro valuation model assumptionHolds
  change Models program valuation at model
  obtain ⟨actualLeft, actualRight, actualArguments, outputEq⟩ :=
    model output instruction found operation operationFound key
  have sameArguments : [actualLeft, actualRight] = [left.node, right.node] := by
    rw [← actualArguments, arguments]
  injection sameArguments with leftEq tailEq
  injection tailEq with rightEq
  subst actualLeft
  subst actualRight
  have leftContains := assumptionHolds left (by simp [exactAssumptions])
  have rightContains := assumptionHolds right (by simp [exactAssumptions])
  change result.Contains (valuation output)
  rw [outputEq]
  exact DyadicInterval.contains_sub computed leftContains rightContains

/-- Package-owned transparent schema for schema-zero subtraction payloads.
It recomputes the exact checked interval result and accepts every canonical cut
shape supported by the Mathlib-free operation. -/
def subFactSchema (limit : EndpointLimit) : PackedFactSchema semantics where
  rule := subForwardKey
  schema := 0
  Certificate := Unit
  decode := fun body => if body.isEmpty then some () else none
  replay := fun _ _ context _ =>
    match context.assumptions with
    | [left, right] =>
        match found : context.program.node? context.proposed.node with
        | some instruction =>
            match operationFound : context.program.operation? instruction.op with
            | some operation =>
                if key : operation.key = subOp then
                  if arguments : instruction.args = [left.node, right.node] then
                    if computed : DyadicInterval.sub limit left.fact right.fact =
                        .ready context.proposed.fact then
                      some
                        { proof := by
                            exact subEntails limit context.program
                              [left, right] context.proposed.node instruction operation
                              left right context.proposed.fact found operationFound key
                              arguments rfl computed }
                    else none
                  else none
                else none
            | none => none
        | none => none
    | _ => none

end Hex.Interval.Experiment.Arithmetic
