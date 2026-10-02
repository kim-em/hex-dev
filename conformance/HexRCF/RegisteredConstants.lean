/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public meta import Lean.Elab.Command

public section

open Hex.RCF.RealCoefficients Hex.OrderedFn.Oracle
open Lean Meta Qq

set_option Elab.async false

namespace Hex.RCF.RegisteredConstants

-- These are synthetic caller registrations, not bundled analytic providers.
@[irreducible] noncomputable def supplied : ℝ := Real.sqrt 3
@[irreducible] noncomputable def uncertain : ℝ := Real.sqrt 7

def suppliedBounds (_ : Rat) : Bounds := ⟨1, 2, by decide⟩
def uncertainBounds (_ : Rat) : Bounds := ⟨-4, 4, by decide⟩

@[rcf_constant] def suppliedRegistration : Registration supplied where
  version := 1
  approximation := suppliedBounds
  containment δ _ := by
    simp only [supplied, suppliedBounds, Contains]
    constructor
    · norm_num [Real.le_sqrt]
    · norm_num [Real.sqrt_le_iff]

@[rcf_constant] def uncertainRegistration : Registration uncertain where
  version := 1
  approximation := uncertainBounds
  containment δ _ := by
    simp only [uncertain, uncertainBounds, Contains]
    constructor
    · norm_num only [Rat.cast_neg, Rat.cast_ofNat]
      nlinarith [Real.sqrt_nonneg 7]
    · norm_num [Real.sqrt_le_iff]

theorem positiveSquare : ∀ x : ℝ, x ^ 2 + supplied > 0 := by rcf

theorem positiveInverse : ∀ x : ℝ, x ^ 2 + 1 / supplied > 0 := by rcf

theorem suppliedWitness : ∃ x : ℝ, x = supplied ∧ 0 < x ∧ x < 3 := by rcf

/-- error: rcf: missing rcf_constant registration for Real.pi -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + Real.pi > 0 := by rcf

example : ∀ x : ℝ, x / supplied = x * supplied⁻¹ := by rcf
example : ∀ x : ℝ, x ^ 2 + supplied ^ 2 > 0 := by rcf
example : ∀ x : ℝ, x ^ 2 + supplied⁻¹ > 0 := by rcf
example (a : ℝ) (h : a = supplied) : ∀ x : ℝ, x ^ 2 + a > 0 := by rcf
example (a : ℝ) (h : supplied = a) : ∀ x : ℝ, x ^ 2 + a > 0 := by rcf

example (h : (1 : ℝ) < 0) : ∀ x : ℝ, x ^ 2 + supplied < 0 := by
  fail_if_success rcf
  exact (not_lt_of_ge (by norm_num) h).elim

example : ∀ x : ℝ, x ^ 2 + uncertain > 0 := by
  fail_if_success rcf
  intro x
  have h : 0 < uncertain := by unfold uncertain; positivity
  nlinarith [sq_nonneg x]

example : ∀ x : ℝ, x ^ 2 + supplied + 0 / (supplied - supplied) > 0 := by
  fail_if_success rcf
  intro x
  simp only [zero_div, add_zero]
  exact positiveSquare x

/-- info: 'Hex.RCF.RegisteredConstants.positiveSquare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms positiveSquare

/-- info: 'Hex.RCF.RegisteredConstants.positiveInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms positiveInverse

/-- info: 'Hex.RCF.RegisteredConstants.suppliedWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms suppliedWitness

attribute [rcf_constant] uncertainRegistration suppliedRegistration

private meta def refuses (action : MetaM α) : MetaM Unit := do
  let before ← getMCtx
  let declarations := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let failed ← tryCatchRuntimeEx (action *> pure false) (fun _ => pure true)
  unless failed do throwError "expected finite evidence rejection"
  unless (← getMCtx).mvarCounter == before.mvarCounter do
    throwError "failed finite API leaked metavariables"
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == declarations do
    throwError "failed finite API leaked auxiliary declarations"

run_elab do
  unless (← Registration.names) == #[``suppliedRegistration, ``uncertainRegistration] do
    throwError "constant registry is not sorted and deduplicated"
  let target := q(∀ x : ℝ, x ^ 2 + 1 / supplied > 0)
  let before ← getMCtx
  let prepared ← Finite.prepare target
  unless prepared.registry.map Prod.fst == #[``suppliedRegistration] do
    throwError "preparation bound an unused provider"
  unless (← getMCtx).mvarCounter == before.mvarCounter do
    throwError "successful preparation changed caller metavariables"
  unless prepared.source.divisors.size == 1 do throwError "lost original divisor"
  let certificate ← Finite.build prepared
  let _ ← Finite.check prepared.source certificate
  let leaf ← Finite.prepare q(∀ x : ℝ, x ^ 2 + supplied > 0)
  let leafCertificate ← Finite.build leaf
  let some evidence := leaf.coefficients[0]? | throwError "missing coefficient"
  unless evidence.observations.size == 1 do throwError "missing callback observation"
  let some observation := evidence.observations[0]? | throwError "missing observation"
  let corrupt (o : Finite.Observation) : MetaM Unit :=
    refuses (Finite.check leaf.source { leafCertificate with prepared :=
      { leaf with coefficients := #[{ evidence with observations := #[o] }] } })
  corrupt { observation with declaration := ``Nat.zero }
  corrupt { observation with subject := q(uncertain) }
  corrupt { observation with version := 999 }
  corrupt { observation with request := 1 }
  corrupt { observation with bounds := Bounds.singleton 0 }
  corrupt { observation with identity := q(True.intro) }
  corrupt { observation with containment := q(True.intro) }
  refuses (Finite.check leaf.source { leafCertificate with prepared :=
    { leaf with coefficients := #[{ evidence with observations := #[] }] } })
  let other ← Finite.prepare q(∀ x : ℝ, x ^ 2 + uncertain + 10 > 0)
  let some otherEvidence := other.coefficients[0]? | throwError "missing other enclosure"
  refuses (Finite.check leaf.source { leafCertificate with prepared :=
    { leaf with coefficients := #[{ evidence with observations := otherEvidence.observations }] } })
  refuses (Finite.check prepared.source
    { certificate with prepared := { prepared with guards := #[] } })
  refuses (Finite.check prepared.source
    { certificate with prepared := { prepared with request := 1 } })
  refuses (Finite.check prepared.source
    { certificate with prepared := { prepared with registry := #[] } })
  let stale := prepared.registry.map (fun (name, _) => (name, mkNatLit 999))
  refuses (Finite.check prepared.source
    { certificate with prepared := { prepared with registry := stale } })
  refuses (Finite.check { prepared.source with original := q(True) } certificate)
  refuses (Finite.check prepared.source { certificate with proof := q(True.intro) })
  let swapped := prepared.coefficients.map fun evidence =>
    { evidence with source := q(uncertain) }
  refuses (Finite.check prepared.source
    { certificate with prepared := { prepared with coefficients := swapped } })
  let wrongBounds := prepared.coefficients.map fun evidence =>
    { evidence with bounds := Bounds.singleton 0 }
  refuses (Finite.check prepared.source
    { certificate with prepared := { prepared with coefficients := wrongBounds } })
  let wrongLiterals := prepared.coefficients.map fun evidence =>
    { evidence with literal := q(True) }
  refuses (Finite.check prepared.source
    { certificate with prepared := { prepared with coefficients := wrongLiterals } })
  let missingProof ← prepared.coefficients.mapM fun evidence => do
    return { evidence with proof := ← mkSorry (← inferType evidence.proof) true }
  refuses (Finite.check prepared.source
    { certificate with prepared := { prepared with coefficients := missingProof } })
  refuses (Finite.prepare q(∀ x : ℝ, x ^ 2 + supplied + 0 / (supplied - supplied) > 0))
  refuses (Finite.prepare q(∀ x : ℝ, x ^ 2 + supplied + 0 / uncertain > 0))
  let unresolved ← Finite.prepare q(∀ x : ℝ, x ^ 2 + uncertain > 0)
  refuses (Finite.build unresolved)
  refuses (Finite.prepare target 0)

def duplicateRegistration : Registration supplied := suppliedRegistration

def malformedRegistration : Nat := 1

def cancelledBounds (_ : Rat) : Bounds := ⟨-1, 1, by decide⟩
def cancelledRegistration : Registration (Real.sin (0 / (supplied - supplied))) where
  version := 1
  approximation := cancelledBounds
  containment δ _ := by
    simp [Contains, cancelledBounds]

def binderRegistration : Registration (Real.sin (sSup {t : ℝ | 1 / t < 1})) where
  version := 1
  approximation := cancelledBounds
  containment δ _ := by
    simpa [Contains, cancelledBounds] using
      And.intro (Real.neg_one_le_sin _) (Real.sin_le_one _)

def quotientRegistration : Registration (Real.sin (1 / supplied)) where
  version := 1
  approximation := cancelledBounds
  containment δ _ := by
    simpa [Contains, cancelledBounds] using
      And.intro (Real.neg_one_le_sin _) (Real.sin_le_one _)

def squareRegistration : Registration (Real.sqrt 2) where
  version := 1
  approximation := suppliedBounds
  containment δ _ := by
    simp only [Contains, suppliedBounds]
    constructor
    · norm_num [Real.le_sqrt]
    · norm_num [Real.sqrt_le_iff]

-- Test attributes against a saved environment, so imports of this module do
-- not acquire a duplicate registration or altered global state.
run_elab do
  let saved ← saveState
  try
    let .ok attr := getAttributeImpl (← getEnv) `rcf_constant |
      throwError "missing registration attribute"
    let stx ← `(attr| rcf_constant)
    let failed ← tryCatchRuntimeEx
      (attr.add ``malformedRegistration stx .global *> pure false)
      (fun _ => pure true)
    unless failed do throwError "malformed registration was admitted"
    attr.add ``quotientRegistration stx .global
    let prepared ← Finite.prepare q(∀ x : ℝ, x ^ 2 + 2 + Real.sin (1 / supplied) > 0)
    unless prepared.source.coefficients == #[q(Real.sin (1 / supplied))] &&
        prepared.source.divisors == #[q(supplied)] do
      throwError "whole-subject normalization changed the provider or lost its guard"
    let _ ← Finite.check prepared.source (← Finite.build prepared)
    attr.add ``cancelledRegistration stx .global
    -- Whole-subject registration must retain divisions inside analytic syntax,
    -- including beneath zero multiplication, zero powers and an empty domain.
    refuses (Finite.prepare q(∀ x : ℝ,
      x ^ 2 + supplied + 0 * Real.sin (0 / (supplied - supplied)) > 0))
    refuses (Finite.prepare q(∀ x : ℝ,
      x ^ 2 + (Real.sin (0 / (supplied - supplied))) ^ 0 > 0))
    refuses (Finite.prepare q(∀ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 0 →
      x ^ 2 + Real.sin (0 / (supplied - supplied)) > 0))
    attr.add ``binderRegistration stx .global
    let .error (.unsupported _ message) ← Reify.prepare
        q(∀ x : ℝ, x ^ 2 + Real.sin (sSup {t : ℝ | 1 / t < 1}) > 0) {}
        #[q(Real.sin (sSup {t : ℝ | 1 / t < 1}))] |
      throwError "binder-dependent divisor was not rejected structurally"
    unless message == "division inside a registered subject must have a closed divisor" do
      throwError "binder-dependent divisor has the wrong diagnostic"
    let complexSubject : Q(ℝ) := q(Real.sin (‖Complex.I / (0 : ℂ)‖))
    let .error (.unsupported _ message) ← Reify.prepare
        q(∀ x : ℝ, x ^ 2 + $complexSubject > 0) {} #[complexSubject] |
      throwError "other-carrier division was not rejected structurally"
    unless message == "division inside a registered subject must be real or rational" do
      throwError "other-carrier division has the wrong diagnostic"
    attr.add ``duplicateRegistration stx .global
    let failed ← tryCatchRuntimeEx (Registration.entries *> pure false) (fun _ => pure true)
    unless failed do throwError "duplicate subject was admitted"
    refuses (Finite.prepare q(∀ x : ℝ, x ^ 2 + supplied > 0))
    -- An unrelated duplicate is not part of the source's provider context.
    let prepared ← Finite.prepare q(∀ x : ℝ, x ^ 2 + uncertain + 10 > 0)
    let _ ← Finite.check prepared.source (← Finite.build prepared)
    attr.add ``squareRegistration stx .global
    let names ← Hex.RCF.handlerNames
    let some exactIndex := names.idxOf? ``RealCoefficients.Tactic.handle |
      throwError "missing exact algebraic handler"
    let some suppliedIndex := names.idxOf? ``RealCoefficients.Tactic.supplied |
      throwError "missing supplied-bound handler"
    unless exactIndex < suppliedIndex do throwError "finite handler precedes exact algebraic handler"
    let goal ← mkFreshExprMVar q(∀ x : ℝ, x ^ 2 - 2 * Real.sqrt 2 * x + 2 ≥ 0)
    let action : Elab.TermElabM (List MVarId) := Elab.Term.withSynthesize do
      Elab.Tactic.run goal.mvarId! <| Elab.Tactic.withoutRecover
        (Elab.Tactic.evalTactic (← `(tactic| rcf)) *> Elab.Tactic.pruneSolvedGoals)
    unless (← action.run' {} {}).isEmpty do throwError "exact algebraic regression failed"
    Hex.RCF.checkAxioms `registeredAlgebraicRegression (← instantiateMVars goal)
  finally saved.restore

end Hex.RCF.RegisteredConstants
