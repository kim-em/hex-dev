/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import HexInterval.Experiment.DyadicInterval
public import HexInterval.Experiment.SemanticReplay

@[expose] public section

/-!
# Real semantics for exact dyadic interval facts

This companion interprets the Mathlib-free open, closed, and independently
unbounded interval representation as subsets of `ℝ`.  Its first proof-facing
obligation is the fact-domain law: a successful executable intersection means
exactly conjunction of the two input facts.
-/

namespace Hex.Interval.Experiment.DyadicInterval

open Propagator SemanticReplay

/-- Mathematical real value of a Core dyadic. -/
def toReal (value : Dyadic) : ℝ := (value.toRat : ℝ)

@[simp]
theorem toReal_zero : toReal 0 = 0 := by
  simp [toReal, Dyadic.toRat_zero]

theorem toReal_lt {left right : Dyadic} (h : left < right) :
    toReal left < toReal right := by
  exact (Rat.cast_lt (K := ℝ)).2 (Dyadic.toRat_lt_toRat_iff.2 h)

theorem toReal_lt_iff {left right : Dyadic} :
    toReal left < toReal right ↔ left < right := by
  exact (Rat.cast_lt (K := ℝ)).trans Dyadic.toRat_lt_toRat_iff

theorem toReal_inj {left right : Dyadic} :
    toReal left = toReal right ↔ left = right := by
  constructor
  · intro equal
    apply Dyadic.toRat_inj.mp
    exact Rat.cast_injective equal
  · exact fun equal => congrArg toReal equal

/-- Meaning of a lower interval cut. -/
def lowerContains : Lower → ℝ → Prop
  | .unbounded, _ => True
  | .finite value false, x => toReal value ≤ x
  | .finite value true, x => toReal value < x

/-- Meaning of an upper interval cut. -/
def upperContains : Upper → ℝ → Prop
  | .finite value false, x => x ≤ toReal value
  | .finite value true, x => x < toReal value
  | .unbounded, _ => True

/-- Mathematical membership in raw interval cuts. -/
def rawContains : Raw → ℝ → Prop
  | .empty, _ => False
  | .bounds lower upper, x => lowerContains lower x ∧ upperContains upper x

/-- Mathematical membership in one canonical engine fact. -/
def Fact.Contains (fact : Fact) (x : ℝ) : Prop := rawContains fact.raw x

private theorem rawContains_normalize (raw : Raw) (x : ℝ) :
    rawContains raw.normalizeUnchecked x ↔ rawContains raw x := by
  cases raw with
  | empty => simp [rawContains, Raw.normalizeUnchecked]
  | bounds lower upper =>
      cases lower with
      | unbounded =>
          simp [rawContains, Raw.normalizeUnchecked, Raw.consistent]
      | finite lower lowerStrict =>
          cases upper with
          | unbounded =>
              simp [rawContains, Raw.normalizeUnchecked, Raw.consistent]
          | finite upper upperStrict =>
              by_cases less : lower < upper
              · simp [rawContains, Raw.normalizeUnchecked, Raw.consistent, less]
              · by_cases equal : lower = upper
                · subst upper
                  cases lowerStrict <;> cases upperStrict
                  · simp [rawContains, lowerContains, upperContains,
                      Raw.normalizeUnchecked, Raw.consistent]
                  · have impossible : ¬(toReal lower ≤ x ∧ x < toReal lower) := by
                      rintro ⟨lowerBound, upperBound⟩
                      linarith
                    simp [rawContains, lowerContains, upperContains,
                      Raw.normalizeUnchecked, Raw.consistent, less, impossible]
                  · have impossible : ¬(toReal lower < x ∧ x ≤ toReal lower) := by
                      rintro ⟨lowerBound, upperBound⟩
                      linarith
                    simp [rawContains, lowerContains, upperContains,
                      Raw.normalizeUnchecked, Raw.consistent, less, impossible]
                  · have impossible : ¬(toReal lower < x ∧ x < toReal lower) := by
                      rintro ⟨lowerBound, upperBound⟩
                      linarith
                    simpa [rawContains, lowerContains, upperContains,
                      Raw.normalizeUnchecked, Raw.consistent, less] using impossible
                · have realNotLess : ¬toReal lower < toReal upper := by
                    simpa only [toReal_lt_iff] using less
                  have realNotEqual : toReal lower ≠ toReal upper := by
                    intro same
                    exact equal (toReal_inj.mp same)
                  have realGreater : toReal upper < toReal lower :=
                    lt_of_le_of_ne (le_of_not_gt realNotLess) (Ne.symm realNotEqual)
                  cases lowerStrict <;> cases upperStrict
                  · have impossible : ¬(toReal lower ≤ x ∧ x ≤ toReal upper) := by
                      rintro ⟨lowerBound, upperBound⟩
                      linarith
                    simpa [rawContains, lowerContains, upperContains,
                      Raw.normalizeUnchecked, Raw.consistent, less, equal] using impossible

                  · have impossible : ¬(toReal lower ≤ x ∧ x < toReal upper) := by
                      rintro ⟨lowerBound, upperBound⟩
                      linarith
                    simpa [rawContains, lowerContains, upperContains,
                      Raw.normalizeUnchecked, Raw.consistent, less, equal] using impossible

                  · have impossible : ¬(toReal lower < x ∧ x ≤ toReal upper) := by
                      rintro ⟨lowerBound, upperBound⟩
                      linarith
                    simpa [rawContains, lowerContains, upperContains,
                      Raw.normalizeUnchecked, Raw.consistent, less, equal] using impossible

                  · have impossible : ¬(toReal lower < x ∧ x < toReal upper) := by
                      rintro ⟨lowerBound, upperBound⟩
                      linarith
                    simpa [rawContains, lowerContains, upperContains,
                      Raw.normalizeUnchecked, Raw.consistent, less, equal] using impossible

private theorem compareChecked_lt {limit : EndpointLimit} {left right : Dyadic}
    (checked : compareChecked limit left right = .ok .lt) : left < right := by
  cases fits : CompareCost.allowed limit (CompareCost.ofDyadic left right) with
  | false =>
      unfold compareChecked at checked
      simp only [fits, Bool.not_false, ↓reduceIte] at checked
      change Except.error _ = Except.ok Ordering.lt at checked
      contradiction
  | true =>
      by_cases less : left < right
      · exact less
      · by_cases equal : left = right
        · subst right
          have selfNotLess : ¬left < left := fun h => (lt_irrefl _ (toReal_lt h))
          unfold compareChecked at checked
          simp only [fits, Bool.not_true, selfNotLess, ↓reduceIte] at checked
          change Except.ok Ordering.eq = Except.ok Ordering.lt at checked
          contradiction
        · unfold compareChecked at checked
          simp only [fits, Bool.not_true, less, equal, ↓reduceIte] at checked
          change Except.ok Ordering.gt = Except.ok Ordering.lt at checked
          contradiction

private theorem compareChecked_eq {limit : EndpointLimit} {left right : Dyadic}
    (checked : compareChecked limit left right = .ok .eq) : left = right := by
  cases fits : CompareCost.allowed limit (CompareCost.ofDyadic left right) with
  | false =>
      unfold compareChecked at checked
      simp only [fits, Bool.not_false, ↓reduceIte] at checked
      change Except.error _ = Except.ok Ordering.eq at checked
      contradiction
  | true =>
      by_cases less : left < right
      · unfold compareChecked at checked
        simp only [fits, Bool.not_true, less, ↓reduceIte] at checked
        change Except.ok Ordering.lt = Except.ok Ordering.eq at checked
        contradiction
      · by_cases equal : left = right
        · exact equal
        · unfold compareChecked at checked
          simp only [fits, Bool.not_true, less, equal, ↓reduceIte] at checked
          change Except.ok Ordering.gt = Except.ok Ordering.eq at checked
          contradiction

private theorem compareChecked_gt {limit : EndpointLimit} {left right : Dyadic}
    (checked : compareChecked limit left right = .ok .gt) : right < left := by
  cases fits : CompareCost.allowed limit (CompareCost.ofDyadic left right) with
  | false =>
      unfold compareChecked at checked
      simp only [fits, Bool.not_false, ↓reduceIte] at checked
      change Except.error _ = Except.ok Ordering.gt at checked
      contradiction
  | true =>
      by_cases less : left < right
      · unfold compareChecked at checked
        simp only [fits, Bool.not_true, less, ↓reduceIte] at checked
        change Except.ok Ordering.lt = Except.ok Ordering.gt at checked
        contradiction
      · by_cases equal : left = right
        · subst right
          have selfNotLess : ¬left < left := fun h => (lt_irrefl _ (toReal_lt h))
          unfold compareChecked at checked
          simp only [fits, Bool.not_true, selfNotLess, ↓reduceIte] at checked
          change Except.ok Ordering.eq = Except.ok Ordering.gt at checked
          contradiction
        · apply Dyadic.not_lt.mp
          intro leftLeRight
          exact equal (Dyadic.le_antisymm leftLeRight (Dyadic.not_le.mp less))

private theorem lowerContains_intersect {limit : EndpointLimit}
    {left right result : Lower} {x : ℝ}
    (checked : intersectLower limit left right = .ok result) :
    lowerContains result x ↔ lowerContains left x ∧ lowerContains right x := by
  cases left with
  | unbounded =>
      change Except.ok right = Except.ok result at checked
      injection checked with same
      subst result
      simp [lowerContains]
  | finite left leftStrict =>
      cases right with
      | unbounded =>
          change Except.ok (.finite left leftStrict) = Except.ok result at checked
          injection checked with same
          subst result
          simp [lowerContains]
      | finite right rightStrict =>
          simp only [intersectLower] at checked
          cases compared : compareChecked limit left right with
          | error cost =>
              rw [compared] at checked
              change Except.error cost = Except.ok result at checked
              contradiction
          | ok ordering =>
              rw [compared] at checked
              cases ordering with
              | lt =>
                  change Except.ok (.finite right rightStrict) =
                    Except.ok result at checked
                  injection checked with same
                  subst result
                  have order := compareChecked_lt compared
                  have realOrder := toReal_lt order
                  constructor
                  · intro rightBound
                    refine ⟨?_, rightBound⟩
                    cases leftStrict <;> cases rightStrict <;>
                      simp [lowerContains] at rightBound ⊢ <;> linarith
                  · exact fun bounds => bounds.2
              | eq =>
                  change Except.ok (.finite left (leftStrict || rightStrict)) =
                    Except.ok result at checked
                  injection checked with same
                  subst result
                  have same := compareChecked_eq compared
                  subst right
                  cases leftStrict <;> cases rightStrict
                  · simp [lowerContains]
                  · change toReal left < x ↔ toReal left ≤ x ∧ toReal left < x
                    constructor
                    · exact fun bound => ⟨le_of_lt bound, bound⟩
                    · exact fun bounds => bounds.2
                  · change toReal left < x ↔ toReal left < x ∧ toReal left ≤ x
                    constructor
                    · exact fun bound => ⟨bound, le_of_lt bound⟩
                    · exact fun bounds => bounds.1
                  · simp [lowerContains]
              | gt =>
                  change Except.ok (.finite left leftStrict) =
                    Except.ok result at checked
                  injection checked with same
                  subst result
                  have order := compareChecked_gt compared
                  have realOrder := toReal_lt order
                  constructor
                  · intro leftBound
                    refine ⟨leftBound, ?_⟩
                    cases leftStrict <;> cases rightStrict <;>
                      simp [lowerContains] at leftBound ⊢ <;> linarith
                  · exact fun bounds => bounds.1

private theorem upperContains_intersect {limit : EndpointLimit}
    {left right result : Upper} {x : ℝ}
    (checked : intersectUpper limit left right = .ok result) :
    upperContains result x ↔ upperContains left x ∧ upperContains right x := by
  cases left with
  | unbounded =>
      change Except.ok right = Except.ok result at checked
      injection checked with same
      subst result
      simp [upperContains]
  | finite left leftStrict =>
      cases right with
      | unbounded =>
          change Except.ok (.finite left leftStrict) = Except.ok result at checked
          injection checked with same
          subst result
          simp [upperContains]
      | finite right rightStrict =>
          simp only [intersectUpper] at checked
          cases compared : compareChecked limit left right with
          | error cost =>
              rw [compared] at checked
              change Except.error cost = Except.ok result at checked
              contradiction
          | ok ordering =>
              rw [compared] at checked
              cases ordering with
              | lt =>
                  change Except.ok (.finite left leftStrict) =
                    Except.ok result at checked
                  injection checked with same
                  subst result
                  have order := compareChecked_lt compared
                  have realOrder := toReal_lt order
                  constructor
                  · intro leftBound
                    refine ⟨leftBound, ?_⟩
                    cases leftStrict <;> cases rightStrict <;>
                      simp [upperContains] at leftBound ⊢ <;> linarith
                  · exact fun bounds => bounds.1
              | eq =>
                  change Except.ok (.finite left (leftStrict || rightStrict)) =
                    Except.ok result at checked
                  injection checked with same
                  subst result
                  have same := compareChecked_eq compared
                  subst right
                  cases leftStrict <;> cases rightStrict
                  · simp [upperContains]
                  · change x < toReal left ↔ x ≤ toReal left ∧ x < toReal left
                    constructor
                    · exact fun bound => ⟨le_of_lt bound, bound⟩
                    · exact fun bounds => bounds.2
                  · change x < toReal left ↔ x < toReal left ∧ x ≤ toReal left
                    constructor
                    · exact fun bound => ⟨bound, le_of_lt bound⟩
                    · exact fun bounds => bounds.1
                  · simp [upperContains]
              | gt =>
                  change Except.ok (.finite right rightStrict) =
                    Except.ok result at checked
                  injection checked with same
                  subst result
                  have order := compareChecked_gt compared
                  have realOrder := toReal_lt order
                  constructor
                  · intro rightBound
                    refine ⟨?_, rightBound⟩
                    cases leftStrict <;> cases rightStrict <;>
                      simp [upperContains] at rightBound ⊢ <;> linarith
                  · exact fun bounds => bounds.2

/-- Executable exact intersection has exactly set-intersection semantics,
including empty results, strict tied cuts, and unbounded ends. -/
theorem contains_intersect {limit : EndpointLimit} {left right result : Fact}
    (checked : intersect limit left right = .ready result) (x : ℝ) :
    result.Contains x ↔ left.Contains x ∧ right.Contains x := by
  cases left with
  | mk leftRaw leftConsistent =>
      cases right with
      | mk rightRaw rightConsistent =>
          cases leftRaw with
          | empty =>
              change Result.ready .empty = .ready result at checked
              injection checked with same
              subst result
              simp [Fact.Contains, Fact.empty, rawContains]
          | bounds leftLower leftUpper =>
              cases rightRaw with
              | empty =>
                  change Result.ready .empty = .ready result at checked
                  injection checked with same
                  subst result
                  simp [Fact.Contains, Fact.empty, rawContains]
              | bounds rightLower rightUpper =>
                  simp only [intersect] at checked
                  cases lowerChecked : intersectLower limit leftLower rightLower with
                  | error cost =>
                      simp [lowerChecked] at checked
                  | ok lower =>
                      cases upperChecked : intersectUpper limit leftUpper rightUpper with
                      | error cost =>
                          simp [lowerChecked, upperChecked] at checked
                      | ok upper =>
                          simp [lowerChecked, upperChecked, normalize] at checked
                          split at checked
                          · contradiction
                          · injection checked with installed
                            subst result
                            change
                              rawContains
                                (Raw.normalizeUnchecked (.bounds lower upper)) x ↔ _
                            rw [rawContains_normalize]
                            change
                              lowerContains lower x ∧ upperContains upper x ↔
                                (lowerContains leftLower x ∧
                                  upperContains leftUpper x) ∧
                                  lowerContains rightLower x ∧
                                    upperContains rightUpper x
                            rw [lowerContains_intersect lowerChecked,
                              upperContains_intersect upperChecked]
                            aesop

/-- Attach exact interval facts to any operation semantics over real-valued
program nodes. -/
def realSemantics (models : Program -> (NodeId -> ℝ) -> Prop) : Semantics Fact :=
  { Value := ℝ
    models
    holds := fun _ valuation fact => fact.fact.Contains (valuation fact.node) }

/-- Proof-side meet checker for one configured executable interval domain. -/
def factSchema (limit : EndpointLimit)
    (models : Program -> (NodeId -> ℝ) -> Prop) :
    FactDomainSchema (realSemantics models) :=
  { top := fun _ => .whole
    topSound := by
      intro _ _ _ _ _ _
      simp [realSemantics, Fact.Contains, Fact.whole, rawContains,
        lowerContains, upperContains]
    proveMeet := fun program node previous proposed installed =>
      match checked : intersect limit previous proposed with
      | .ready result =>
          if exact : result = installed then
            some
              { proof := by
                  subst installed
                  intro valuation _
                  change
                    result.Contains (valuation node) ↔
                      previous.Contains (valuation node) ∧
                        proposed.Contains (valuation node)
                  exact contains_intersect checked (valuation node) }
          else
            none
      | .inapplicable | .resourceLimit _ => none }

end Hex.Interval.Experiment.DyadicInterval
