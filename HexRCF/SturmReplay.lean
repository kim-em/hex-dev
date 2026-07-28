/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SturmCheck
public import HexRealRootsMathlib.LiteralChain

public section

/-!
# Soundness of multiplication-only Sturm replay certificates

The Mathlib-free data and executable checker live in `HexRCF.SturmCheck`.
The theorems in this file package accepted data as
`HexRealRootsMathlib.ZReplay`, ready for the literal Sturm count theorems.
-/

namespace Hex.RCF

namespace SturmReplay

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
