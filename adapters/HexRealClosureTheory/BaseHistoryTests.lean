/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseHistoryTests
public import HexRealClosureTheory.ConstructedCatalog

public section
namespace Hex.RealClosure.BaseContext.HistoryModelTests
open OrderedFn OrderedFn.Oracle

/-- A finite reader answers only at the two supplied native predecessors. -/
def reader {registry : Registry} (parent child : RealPrefix registry)
    (first second : ConstantKey) (one : parent.Step first) (two : child.Step second)
    (current : RealPrefix registry) (wanted : ConstantKey) : Option (current.Step wanted) :=
  match HistoryTests.offer parent first one current wanted with
  | some step => some step
  | none => HistoryTests.offer child second two current wanted

section

variable {registry : Registry} (parent : RealPrefix.Model registry)
variable (first second : ConstantKey) (one : parent.context.Step first)
variable (τ : ℝ) (contained : ∀ δ, 0 < δ → Contains ((registry first).get one.present δ) τ)
variable (transcendental : letI : Field parent.context.Carrier := HexPolyTheory.fieldOfGrind
  Real.RelativeTranscendence parent.interpretation.hom τ)
variable (two : RealPrefix.Step (RealPrefix.Model.context (parent.append first one τ contained
    transcendental)) second)

private theorem different : (parent.append first one τ contained transcendental).context.keys ≠
    parent.context.keys := by
  rw [parent.append_context first one τ contained transcendental, RealPrefix.append_keys]
  intro same
  have lengths := congrArg List.length same
  simp only [List.length_append, List.length_singleton] at lengths
  exact Nat.add_one_ne_self _ lengths

include parent first second one τ contained transcendental two

/-- The first packet is supplied at the seed, with no law at other models. -/
theorem read_first : (reader parent.context (parent.append first one τ contained
    transcendental).context first second one two) parent.context first = some one := by
  simp [reader, HistoryTests.offer]

/-- The second packet is supplied at the actual newly constructed model. -/
theorem read_second : (reader parent.context (parent.append first one τ contained
    transcendental).context first second one two) (parent.append first one τ contained
    transcendental).context second = some two := by
  have distinct := different parent first one τ contained transcendental
  simp [reader, HistoryTests.offer, distinct]

/-- Both native progress requirements hold on this finite reader's path. -/
theorem ready_two (freshFirst : first ∉ parent.context.keys)
    (freshSecond : second ∉ (parent.append first one τ contained transcendental).context.keys) :
    RealPrefix.Ready (reader parent.context (parent.append first one τ contained
        transcendental).context first second one two) parent.context [first, second] := by
  simp only [RealPrefix.Ready, ite_eq_right freshFirst]
  refine ⟨one, read_first parent first second one τ contained transcendental two, ?_⟩
  rw [← parent.append_context first one τ contained transcendental]
  simp only [ite_eq_right freshSecond]
  exact ⟨two, read_second parent first second one τ contained transcendental two, trivial⟩

/-- The finite two-stage reader satisfies path-local semantic validity from
only its two actual provider premises, without any final target model. -/
theorem valid_two (σ : ℝ)
    (secondContained : ∀ δ, 0 < δ → Contains ((registry second).get two.present δ) σ)
    (secondTranscendental : letI : Field (parent.append first one τ contained
        transcendental).context.Carrier := HexPolyTheory.fieldOfGrind
      Real.RelativeTranscendence (parent.append first one τ contained
          transcendental).interpretation.hom σ)
    (freshFirst : first ∉ parent.context.keys) (freshSecond : second ∉ (parent.append first one
        τ contained transcendental).context.keys) :
    parent.Valid (reader parent.context (parent.append first one τ contained
        transcendental).context first second one two) [first, second] := by
  simp only [RealPrefix.Model.Valid, ite_eq_right freshFirst]
  intro step supplied
  have same : one = step := Option.some.inj
    ((read_first parent first second one τ contained transcendental two).symm.trans supplied)
  subst step
  refine ⟨τ, contained, transcendental, ?_⟩
  simp only [ite_eq_right freshSecond]
  intro step supplied
  have same : two = step := Option.some.inj
    ((read_second parent first second one τ contained transcendental two).symm.trans supplied)
  subst step
  exact ⟨σ, secondContained, secondTranscendental, trivial⟩

/-- Actual two-stage construction and installation have a realization derived
from the two local analytic premises. Neither a target nor its model is input. -/
theorem install_two (catalog : Catalog registry) (depth : Nat) (σ : ℝ)
    (secondContained : ∀ δ, 0 < δ → Contains ((registry second).get two.present δ) σ)
    (secondTranscendental : letI : Field (parent.append first one τ contained
        transcendental).context.Carrier := HexPolyTheory.fieldOfGrind
      Real.RelativeTranscendence (parent.append first one τ contained
          transcendental).interpretation.hom σ)
    (freshFirst : first ∉ parent.context.keys) (freshSecond : second ∉ (parent.append first one
        τ contained transcendental).context.keys) :
    ∃ packet : catalog.Construction (reader parent.context (parent.append first one τ contained
        transcendental).context first second one two) parent.context [first, second],
      catalog.construct? (reader parent.context (parent.append first one τ contained
          transcendental).context first second one two) parent.context [first, second] = some packet
          ∧
      Nonempty (packet.target.finish.extend depth).Realization := by
  have ready := ready_two parent first second one τ contained transcendental two freshFirst
      freshSecond
  have valid := valid_two parent first second one τ contained transcendental two σ
    secondContained secondTranscendental freshFirst freshSecond
  have built := parent.extend?_success (reader parent.context (parent.append first one τ
      contained transcendental).context first second one two) [first, second] ready
  obtain ⟨packet, produced⟩ := Option.isSome_iff_exists.mp
    (catalog.construct?_success (reader parent.context (parent.append first one τ contained
        transcendental).context first second one two) parent.context [first, second] built)
  exact ⟨packet, produced, packet.realization (reader parent.context (parent.append first one τ
      contained transcendental).context first second one two) parent [first, second] valid depth⟩

end

/-- Containment, width and relative transcendence derive both native progress
packets, path readiness, path validity and the actual installed realization.
No native progress packet or model of the completed history is supplied. -/
theorem install_providers {registry : Registry} (catalog : Catalog registry) (depth : Nat)
    (parent : RealPrefix.Model registry) (first second : ConstantKey)
    (present : (registry first).isSome = true) (τ : ℝ)
    (contained : ∀ δ, 0 < δ → Contains ((registry first).get present δ) τ)
    (width : ∀ δ, 0 < δ → ((registry first).get present δ).width ≤ δ)
    (transcendental : letI : Field parent.context.Carrier := HexPolyTheory.fieldOfGrind
      Real.RelativeTranscendence parent.interpretation.hom τ) :
    let one := parent.progress first present τ contained width transcendental
    let child := parent.append first one τ contained transcendental
    ∀ (secondPresent : (registry second).isSome = true) (σ : ℝ)
      (secondContained : ∀ δ, 0 < δ → Contains ((registry second).get secondPresent δ) σ)
      (secondWidth : ∀ δ, 0 < δ → ((registry second).get secondPresent δ).width ≤ δ)
      (secondTranscendental : letI : Field child.context.Carrier := HexPolyTheory.fieldOfGrind
        Real.RelativeTranscendence child.interpretation.hom σ)
      (_freshFirst : first ∉ parent.context.keys) (_freshSecond : second ∉ child.context.keys),
    let two := child.progress second secondPresent σ secondContained secondWidth secondTranscendental
    let read := reader parent.context child.context first second one two
    RealPrefix.Ready read parent.context [first, second] ∧
      parent.Valid read [first, second] ∧
      ∃ packet : catalog.Construction read parent.context [first, second],
        catalog.construct? read parent.context [first, second] = some packet ∧
        Nonempty (packet.target.finish.extend depth).Realization := by
  intro one child secondPresent σ secondContained secondWidth secondTranscendental
    freshFirst freshSecond two read
  exact ⟨ready_two parent first second one τ contained transcendental two freshFirst freshSecond,
    valid_two parent first second one τ contained transcendental two σ secondContained
      secondTranscendental freshFirst freshSecond,
    install_two parent first second one τ contained transcendental two catalog depth σ
      secondContained secondTranscendental freshFirst freshSecond⟩

end Hex.RealClosure.BaseContext.HistoryModelTests
