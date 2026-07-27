/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRootsMathlib.LiteralChain

public section

/-!
# Multiplication-only Sturm replay certificates

An RCF certificate supplies a literal integer-polynomial chain together with
positive three-term recurrence scales. The executable checker in this file
uses only coefficient equality, integer arithmetic, and linear walks over the
literal arrays. Its soundness theorem packages the accepted data as
`HexRealRootsMathlib.ZReplay`, ready for the literal Sturm count theorems.
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

/-- Validate recurrence steps and the terminal nonzero constant. Its recursive
shape matches `HexRealRootsMathlib.ZReplay`. -/
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

/-- Kernel-facing consequences of an accepted generalized Sturm replay. The
existential form keeps this a proposition while exposing the literal list
decomposition needed by downstream count proofs. -/
@[expose]
def Valid (f : ZPoly) (cert : SturmReplay) : Prop :=
  ∃ (s₁ : ZPoly) (rest : List ZPoly),
    cert.chain.toList = f :: s₁ :: rest ∧
      HexRealRootsMathlib.ZReplay f s₁ rest ∧
        (∀ q ∈ f :: s₁ :: rest, q ≠ 0) ∧
          DegreesDescend (f :: s₁ :: rest) ∧
            0 < cert.derivScale ∧
              DensePoly.derivative f = DensePoly.scale cert.derivScale s₁ ∧
                cert.steps.size + 2 = cert.chain.size

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

/-- A successful identity check supplies the existential recurrence expected
by `HexRealRootsMathlib.ZReplay`. -/
theorem checkStep_sound {a b c : ZPoly} {step : SturmStep}
    (h : checkStep a b c step = true) :
    HexRealRootsMathlib.ZReplayStep a b c := by
  simp only [checkStep, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨step.leftScale, step.quotient, step.rightScale,
    h.1.1, h.1.2, DensePoly.eq_of_beqCoeffs h.2⟩

/-- A successful recurrence walk constructs an abstract integer replay. -/
theorem checkSteps_sound {a b : ZPoly} {rest : List ZPoly}
    {steps : List SturmStep} (h : checkSteps a b rest steps = true) :
    HexRealRootsMathlib.ZReplay a b rest := by
  induction rest generalizing a b steps with
  | nil =>
      cases steps with
      | nil =>
          simp only [checkSteps, decide_eq_true_eq] at h
          exact .pair h
      | cons _ _ => simp [checkSteps] at h
  | cons c rest ih =>
      cases steps with
      | nil => simp [checkSteps] at h
      | cons step steps =>
          simp only [checkSteps, Bool.and_eq_true] at h
          exact .cons (checkStep_sound h.1) (ih h.2)

/-- Soundness of the executable generalized Sturm replay checker. -/
theorem check_sound {f : ZPoly} {cert : SturmReplay}
    (h : cert.check f = true) : cert.Valid f := by
  unfold check at h
  match hm : cert.chain.toList with
  | [] => rw [hm] at h; simp at h
  | [_] => rw [hm] at h; simp at h
  | a :: s₁ :: rest =>
      rw [hm] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨hsize, hhead⟩, hnz⟩, hdegrees⟩, hcount⟩,
        hderivPos⟩, hderiv⟩, hsteps⟩ := h
      have ha : a = f := DensePoly.eq_of_beqCoeffs hhead
      subst a
      refine ⟨s₁, rest, hm, checkSteps_sound hsteps, ?_, ?_, hderivPos, ?_, hcount⟩
      · exact checkNonzero_sound hnz
      · exact checkDegrees_sound hdegrees
      · exact DensePoly.eq_of_beqCoeffs hderiv

/-- The head of an accepted replay is nonzero. -/
theorem head_ne_zero {f : ZPoly} {cert : SturmReplay}
    (h : cert.check f = true) : f ≠ 0 := by
  obtain ⟨s₁, rest, _hchain, _hrep, hnz, _hdegrees, _hpos, _hderiv, _hcount⟩ :=
    check_sound h
  exact hnz f (by simp)

/-- An accepted replay is a Sturm chain after casting its literal entries to
real polynomials. -/
theorem isChain_of_check {f : ZPoly} {cert : SturmReplay}
    (h : cert.check f = true) :
    Sturm.IsSturmChain (HexRealRootsMathlib.toPolyℝ f)
      (cert.chain.toList.map HexRealRootsMathlib.toPolyℝ) := by
  obtain ⟨s₁, rest, hchain, hrep, hnz, _hdegrees, hpos, hderiv, _hcount⟩ :=
    check_sound h
  rw [hchain]
  exact hrep.isChain hnz cert.derivScale hpos hderiv

/-- An accepted replay proves that the real cast of its head is squarefree. -/
theorem squarefree_of_check {f : ZPoly} {cert : SturmReplay}
    (h : cert.check f = true) :
    Squarefree (HexRealRootsMathlib.toPolyℝ f) := by
  obtain ⟨_s₁, _rest, _hchain, hrep, _hnz, _hdegrees, hpos, hderiv, _hcount⟩ :=
    check_sound h
  exact hrep.squarefree cert.derivScale hpos hderiv

/-- The literal variation drop of an accepted replay counts exactly the real
roots in the supplied half-open interval. This acts directly on the
certificate array, avoiding a list-to-array round trip. -/
theorem count_eq_card_roots {f : ZPoly} {cert : SturmReplay}
    (h : cert.check f = true) (I : DyadicInterval) :
    cert.count I =
      (HexRealRootsMathlib.Literal.rootsIn
        (HexRealRootsMathlib.toPolyℝ f) I).card := by
  obtain ⟨s₁, rest, _hchain, _hrep, hnz, _hdegrees, _hpos, _hderiv, _hcount⟩ :=
    check_sound h
  unfold count
  apply HexRealRootsMathlib.literalCount_eq_card_roots f cert.chain
  · intro hf
    exact hnz f (by simp) (HexRealRootsMathlib.toPolyℝ_eq_zero_iff.mp hf)
  · exact squarefree_of_check h
  · exact isChain_of_check h

/-- The literal infinite-endpoint variation drop of an accepted replay counts
exactly all real roots of its head. This acts directly on the certificate
array. -/
theorem total_eq_card_roots {f : ZPoly} {cert : SturmReplay}
    (h : cert.check f = true) :
    cert.total = (HexRealRootsMathlib.toPolyℝ f).roots.card := by
  obtain ⟨s₁, rest, _hchain, _hrep, hnz, _hdegrees, _hpos, _hderiv, _hcount⟩ :=
    check_sound h
  unfold total
  apply HexRealRootsMathlib.literalRootCount_eq_card_roots f cert.chain
  · intro hf
    exact hnz f (by simp) (HexRealRootsMathlib.toPolyℝ_eq_zero_iff.mp hf)
  · exact squarefree_of_check h
  · exact isChain_of_check h

end SturmReplay

end Hex.RCF
