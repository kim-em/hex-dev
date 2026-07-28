/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRoots.Var

public section

/-!
# Multiplication-only Sturm replay checks

An RCF certificate supplies a literal integer-polynomial chain together with
positive three-term recurrence scales. The executable checker in this file
uses only coefficient equality, integer arithmetic, and linear walks over the
literal arrays. The Mathlib-facing soundness theorems live in
`HexRCF.SturmReplay`.
-/

namespace Hex.RCF

/-- One positive three-term recurrence in a generalized Sturm replay. -/
structure SturmStep where
  /-- Positive scale on the polynomial two positions before the new term. -/
  leftScale : Int
  /-- Quotient multiplying the preceding polynomial. -/
  quotient : ZPoly
  /-- Positive scale on the new polynomial. -/
  rightScale : Int

/-- A literal generalized Sturm chain and its multiplication-only replay. -/
structure SturmReplay where
  /-- The chain `[f, s₁, …, sₙ]`. -/
  chain : Array ZPoly
  /-- Positive integer `δ` satisfying `f' = δ s₁`. -/
  derivScale : Int
  /-- The three-term identities for consecutive chain triples. -/
  steps : Array SturmStep

namespace SturmReplay

/-- Boolean validation of a supplied positive three-term identity. -/
@[expose]
def checkStep (a b c : ZPoly) (step : SturmStep) : Bool :=
  decide (0 < step.leftScale) &&
  decide (0 < step.rightScale) &&
  DensePoly.beqCoeffs (DensePoly.scale step.leftScale a)
    (step.quotient * b - DensePoly.scale step.rightScale c)

/-- Validate recurrence steps and the terminal nonzero constant. -/
@[expose]
def checkSteps : ZPoly → ZPoly → List ZPoly → List SturmStep → Bool
  | _, b, [], [] => decide (b.size = 1)
  | a, b, c :: rest, step :: steps =>
      checkStep a b c step && checkSteps b c rest steps
  | _, _, _, _ => false

/-- Every literal polynomial in a chain is nonzero. -/
@[expose]
def checkNonzero : List ZPoly → Bool
  | [] => true
  | p :: rest => !p.isZero && checkNonzero rest

/-- Consecutive literal chain degrees strictly decrease. -/
@[expose]
def checkDegrees : List ZPoly → Bool
  | a :: b :: rest =>
      decide (b.degree?.getD 0 < a.degree?.getD 0) && checkDegrees (b :: rest)
  | _ => true

/-- Executable generalized Sturm replay checker.

All polynomial comparisons use `DensePoly.beqCoeffs`, avoiding structural
array equality during kernel reduction. Nonzero checking before strict degree
descent makes `degree?.getD 0` unambiguous and implies that an accepted head
has positive degree. Degree descent is retained as an explicit certificate
invariant even though the abstract `IsSturmChain` consequence does not need
it. -/
@[expose]
def check (f : ZPoly) (cert : SturmReplay) : Bool :=
  match cert.chain.toList with
  | a :: s₁ :: rest =>
      decide (2 ≤ cert.chain.size) &&
      DensePoly.beqCoeffs a f &&
      checkNonzero (a :: s₁ :: rest) &&
      checkDegrees (a :: s₁ :: rest) &&
      decide (cert.steps.size + 2 = cert.chain.size) &&
      decide (0 < cert.derivScale) &&
      DensePoly.beqCoeffs (DensePoly.derivative f)
        (DensePoly.scale cert.derivScale s₁) &&
      checkSteps a s₁ rest cert.steps.toList
  | _ => false

/-- Literal Sturm variation drop across the dyadic interval
`(I.lower, I.upper]`. -/
@[expose]
def count (cert : SturmReplay) (I : DyadicInterval) : Int :=
  (Hex.sturmVarAt cert.chain I.lower : Int) - Hex.sturmVarAt cert.chain I.upper

/-- Literal Sturm variation drop from negative to positive infinity. -/
@[expose]
def total (cert : SturmReplay) : Int :=
  (Hex.sturmVarNegInf cert.chain : Int) - Hex.sturmVarPosInf cert.chain

/-- Proposition-level adjacent degree descent mirrored by `checkDegrees`. -/
@[expose]
def DegreesDescend : List ZPoly → Prop
  | a :: b :: rest =>
      b.degree?.getD 0 < a.degree?.getD 0 ∧ DegreesDescend (b :: rest)
  | _ => True

/-- A successful nonzero walk proves every chain entry nonzero. -/
theorem checkNonzero_sound {chain : List ZPoly}
    (h : checkNonzero chain = true) : ∀ q ∈ chain, q ≠ 0 := by
  induction chain with
  | nil => simp
  | cons p rest ih =>
      simp only [checkNonzero, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hp, hrest⟩ := h
      have hp0 : p ≠ 0 := by
        have hpos := (DensePoly.isZero_eq_false_iff p).mp hp
        intro hzero
        subst p
        simp at hpos
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hp0
      · exact ih hrest q hq

/-- A successful degree walk proves proposition-level adjacent descent. -/
theorem checkDegrees_sound {chain : List ZPoly}
    (h : checkDegrees chain = true) : DegreesDescend chain := by
  induction chain with
  | nil => trivial
  | cons a rest ih =>
      cases rest with
      | nil => trivial
      | cons b rest =>
          simp only [checkDegrees, Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨h.1, ih h.2⟩

/-- The head of an accepted replay is nonzero. -/
theorem head_ne_zero {f : ZPoly} {cert : SturmReplay}
    (h : cert.check f = true) : f ≠ 0 := by
  unfold check at h
  match hm : cert.chain.toList with
  | [] => rw [hm] at h; simp at h
  | [_] => rw [hm] at h; simp at h
  | a :: s₁ :: rest =>
      rw [hm] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨_hsize, hhead⟩, hnz⟩, _hdegrees⟩, _hcount⟩,
        _hderivPos⟩, _hderiv⟩, _hsteps⟩ := h
      have ha : a = f := DensePoly.eq_of_beqCoeffs hhead
      subst a
      exact checkNonzero_sound hnz f (by simp)

end SturmReplay

end Hex.RCF
