/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.DyadicInterval
import HexInterval.Experiment.ProofEmitter

/-!
# Exact interval semantics conformance

These checks connect the Mathlib-free interval implementation to its real-set
meaning.  They deliberately mix strict and closed cuts and independently
unbounded inputs, then use the generic proof-emission closure combinator.
-/

namespace Hex.IntervalMathlib.DyadicIntervalConformance

open Hex.Interval Hex.Interval.Experiment
open Propagator SemanticReplay ProofEmitter
open DyadicInterval

private def real : DomainId := { index := 0 }

private def source : Operation :=
  { key := { name := "dyadic-semantics.source" }, inputs := [], output := real }

private def sourceNode : Node :=
  { domain := real, op := { index := 0 }, args := [] }

private def program : Program :=
  { operations := #[source], nodes := #[sourceNode] }

private def node : NodeId := { index := 0 }

private def limit : EndpointLimit :=
  { maxEndpointHeight := 64, maxAlignmentShift := 64 }

private def fact (lower : Lower) (upper : Upper)
    (consistent : (Raw.bounds lower upper).CutConsistent) : Fact :=
  ⟨.bounds lower upper, consistent⟩

private def closedZeroTwo : Fact :=
  fact (.finite 0 false) (.finite 2 false) (by decide)

private def openZeroThree : Fact :=
  fact (.finite 0 true) (.finite 3 false) (by decide)

private def openZeroTwo : Fact :=
  fact (.finite 0 true) (.finite 2 false) (by decide)

private def nonnegative : Fact :=
  fact (.finite 0 false) .unbounded (by decide)

private def belowThree : Fact :=
  fact .unbounded (.finite 3 true) (by decide)

private def zeroThree : Fact :=
  fact (.finite 0 false) (.finite 3 true) (by decide)

private def singletonZero : Fact :=
  fact (.finite 0 false) (.finite 0 false) (by decide)

private def positive : Fact :=
  fact (.finite 0 true) .unbounded (by decide)

private def trivialModels (_ : Program) (_ : NodeId → ℝ) : Prop := True

private def semantics := DyadicInterval.realSemantics trivialModels

private def domain := DyadicInterval.factSchema limit trivialModels

#guard intersect limit closedZeroTwo openZeroThree == .ready openZeroTwo
#guard intersect limit nonnegative belowThree == .ready zeroThree
#guard intersect limit singletonZero positive == .ready .empty

/-- Strictness and endpoint selection are reflected exactly in real
membership, not merely in the executable representation. -/
example (x : ℝ) :
    openZeroTwo.Contains x ↔
      closedZeroTwo.Contains x ∧ openZeroThree.Contains x := by
  exact contains_intersect (limit := limit) (by decide) x

/-- Independently unbounded inputs intersect to the expected half-open
bounded interval. -/
example (x : ℝ) :
    zeroThree.Contains x ↔ nonnegative.Contains x ∧ belowThree.Contains x := by
  exact contains_intersect (limit := limit) (by decide) x

/-- A closed singleton and the corresponding strict lower half-line have
empty intersection. -/
example (x : ℝ) :
    Fact.empty.Contains x ↔ singletonZero.Contains x ∧ positive.Contains x := by
  exact contains_intersect (limit := limit) (by decide) x

private def base : List (NodeFact Fact) :=
  [{ node, fact := openZeroTwo }]

private def established :
    Evidence (semantics.Entails program base { node, fact := openZeroTwo }) :=
  ProofEmitter.assumed (by simp [base])

private def closed :
    Option (Evidence (semantics.Entails program base { node, fact := nonnegative })) :=
  ProofEmitter.closeFact domain program base node openZeroTwo nonnegative established

#guard closed.isSome

/-- The generic proof frontend can weaken an established exact interval using
the independent fact-domain theorem. -/
theorem intervalWeakens :
    semantics.Entails program base { node, fact := nonnegative } :=
  ProofEmitter.proofOfReplay closed (by rfl)

/--
info: 'Hex.IntervalMathlib.DyadicIntervalConformance.intervalWeakens' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms intervalWeakens

end Hex.IntervalMathlib.DyadicIntervalConformance
