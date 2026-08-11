/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import HexInterval.Experiment.ProofFrontend
public import HexInterval.Experiment.ExpSign

@[expose] public section

/-!
# Real semantics for exponential-sign propagation

This companion interprets the independent Mathlib-free exponential package
over `ℝ` and contributes its semantic replay theorem and frontend handle.
-/

namespace Hex.Interval.Experiment.ExpSign

open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .nonnegative, x => 0 ≤ x
  | .empty, _ => False

def Models (graph : Program) (valuation : NodeId → ℝ) : Prop :=
  graph.node? (node 1) = some expInstruction →
    valuation (node 1) = Real.exp (valuation (node 0))

def semantics : Semantics Bound :=
  { Value := ℝ
    models := Models
    holds := fun _ valuation fact => Contains fact.fact (valuation fact.node) }

theorem containsMeet (left right : Bound) (x : ℝ) :
    Contains (left.meet right) x ↔ Contains left x ∧ Contains right x := by
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

theorem expEntails (assumptions : List (NodeFact Bound)) :
    semantics.Entails program assumptions
      { node := node 1, fact := .nonnegative } := by
  intro valuation model _
  change (0 : ℝ) ≤ valuation (node 1)
  rw [model (by rfl)]
  exact (Real.exp_pos _).le

def expFactSchema : PackedFactSchema semantics where
  rule := expRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body =>
    if body == [Bound.nonnegative.code] then some () else none
  replay := fun _ _ context _ =>
    if graphEq : context.program = program then
      if proposedEq : context.proposed =
          ({ node := node 1, fact := .nonnegative } : NodeFact Bound) then
        some
          { proof := by
              simpa only [graphEq, proposedEq] using
                expEntails context.assumptions }
      else
        none
    else
      none

theorem nodeAtPrefix {before after : Program}
    (stepPrefix : ProgramPrefix before after)
    (target : NodeId) (instruction : Node)
    (found : before.node? target = some instruction) :
    after.node? target = some instruction := by
  have within : target.index < before.nodes.size := by
    by_contra outside
    simp [Program.node?, outside] at found
  rw [Program.node?, stepPrefix.nodeAt target.index within]
  exact found

def stableLaw : StableLaw semantics :=
  { stable := by
      intro before after _ _ stepPrefix _
      refine
        { programPrefix := stepPrefix
          modelsBefore := ?_
          holdsOld := ?_ }
      · intro valuation model found
        exact model (nodeAtPrefix stepPrefix _ _ found)
      · intro oldValue newValue fact _ _ _ agreement
        change Contains fact.fact (oldValue fact.node) ↔
          Contains fact.fact (newValue fact.node)
        rw [agreement] }

def sourceEmit : EmitPackage Lean.Name := { schemas := [] }

def expEmit : EmitPackage Lean.Name :=
  { schemas :=
      [{ key := expFactSchema.key
         handle := ``expFactSchema }] }

def sourceProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[] }
    emit := sourceEmit }

def expProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[expFactSchema] }
    emit := expEmit }

def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof, expProof]

def semanticPackages : Array (SemanticReplay.Package semantics) :=
  proofPackages.map (fun package => package.semantic)

def baseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .all }, { node := node 1, fact := .all }]

def checkerInput : CheckerInput Bound :=
  { baseProgram := program
    initialFacts := #[.all, .all]
    target := { node := node 1, fact := .nonnegative } }

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
  | ⟨0⟩ => x
  | ⟨1⟩ => Real.exp x
  | _ => 0

theorem valuationModels (x : ℝ) : Models program (valuation x) := by
  intro _
  rfl

/-- Turn the generic emitted evidence into the ordinary user theorem. -/
theorem closeExp (x : ℝ)
    (result : Evidence
      (semantics.Entails program baseFacts checkerInput.target)) :
    0 ≤ Real.exp x := by
  have holds := result.proof (valuation x) (valuationModels x)
    (by
      intro fact member
      simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> trivial)
  exact holds

end Hex.Interval.Experiment.ExpSign
