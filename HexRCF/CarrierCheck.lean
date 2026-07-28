/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Syntax
public import HexRCF.SturmCheck

public section

/-!
# Multiplication-checkable RCF carriers

The carrier checker recomputes the nonconstant atom polynomials and their
product from the reflected sentence. A certificate supplies a proposed
square-free carrier, two factor witnesses, two nonzero integer scales, and a
multiplication-only Sturm replay for the carrier. Checking uses only exact
polynomial arithmetic, differentiation, coefficient equality, and the replay
checker. Real-polynomial consequences live in `HexRCF.Carrier`.
-/

namespace Hex.RCF

/-- Check that every polynomial in a literal list has positive degree. -/
@[expose]
def checkPosDegrees : List ZPoly → Bool
  | [] => true
  | p :: ps => decide (0 < p.degree?.getD 0) && checkPosDegrees ps

/-- Multiplication-checkable witnesses that a polynomial is a square-free
carrier for the atom product of a sentence. -/
structure CarrierCert where
  /-- Proposed square-free carrier `P`. -/
  carrier : ZPoly
  /-- Repeated-factor witness `R`. -/
  repeated : ZPoly
  /-- Derivative quotient witness `S`. -/
  derivPart : ZPoly
  /-- Nonzero scale `k` in `Q = scale k (P * R)`. -/
  factorScale : Int
  /-- Nonzero scale `d` in `scale d Q' = R * S`. -/
  derivScale : Int
  /-- Generalized Sturm replay proving the carrier squarefree. -/
  replay : SturmReplay

namespace CarrierCert

/-- Executable carrier validation. The atom product is recomputed from the
sentence and is never supplied by the certificate. -/
@[expose]
def check (s : Sentence) (cert : CarrierCert) : Bool :=
  let q := s.product
  -- `Sentence.polys` filters by this predicate. Retaining the explicit walk
  -- states the certificate condition at the point where it is checked.
  checkPosDegrees s.polys &&
  decide (0 < q.degree?.getD 0) &&
  !cert.repeated.isZero &&
  decide (cert.factorScale ≠ 0) &&
  decide (cert.derivScale ≠ 0) &&
  DensePoly.beqCoeffs q
    (DensePoly.scale cert.factorScale (cert.carrier * cert.repeated)) &&
  DensePoly.beqCoeffs (DensePoly.scale cert.derivScale (DensePoly.derivative q))
    (cert.repeated * cert.derivPart) &&
  cert.replay.check cert.carrier

/-- Proposition-level facts recovered from the Boolean carrier checker. -/
@[expose]
def Valid (s : Sentence) (cert : CarrierCert) : Prop :=
  let q := s.product
  (∀ p ∈ s.polys, 0 < p.degree?.getD 0) ∧
  0 < q.degree?.getD 0 ∧
  cert.repeated ≠ 0 ∧
  cert.factorScale ≠ 0 ∧
  cert.derivScale ≠ 0 ∧
  q = DensePoly.scale cert.factorScale (cert.carrier * cert.repeated) ∧
  DensePoly.scale cert.derivScale (DensePoly.derivative q) =
    cert.repeated * cert.derivPart ∧
  cert.replay.check cert.carrier = true

/-- A successful positive-degree walk proves its proposition-level form. -/
theorem checkPosDegrees_sound {ps : List ZPoly} (h : checkPosDegrees ps = true) :
    ∀ p ∈ ps, 0 < p.degree?.getD 0 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      simp only [checkPosDegrees, Bool.and_eq_true, decide_eq_true_eq] at h
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact h.1
      · exact ih h.2 q hq

/-- Soundness of the executable carrier checker. -/
theorem check_sound {s : Sentence} {cert : CarrierCert}
    (h : cert.check s = true) : cert.Valid s := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hdegrees, hqdeg⟩, hr0⟩, hk0⟩, hd0⟩, hfactor⟩,
    hderiv⟩, hreplay⟩ := h
  refine ⟨checkPosDegrees_sound hdegrees, hqdeg, ?_, hk0, hd0, ?_, ?_, hreplay⟩
  · simp only [Bool.not_eq_true'] at hr0
    have hr := (DensePoly.isZero_eq_false_iff cert.repeated).mp hr0
    intro hzero
    rw [hzero] at hr
    simp at hr
  · exact DensePoly.eq_of_beqCoeffs hfactor
  · exact DensePoly.eq_of_beqCoeffs hderiv

/-- The carrier replay component recovered from the combined checker. -/
theorem replay_of_check {s : Sentence} {cert : CarrierCert}
    (h : cert.check s = true) : cert.replay.check cert.carrier = true :=
  (check_sound h).2.2.2.2.2.2.2

/-- An accepted carrier certificate has a nonzero carrier polynomial. -/
theorem carrier_ne_zero {s : Sentence} {cert : CarrierCert}
    (h : cert.check s = true) : cert.carrier ≠ 0 := by
  obtain ⟨_hdegrees, _hqdeg, _hr0, _hk0, _hd0, _hfactor, _hderiv, hreplay⟩ :=
    check_sound h
  exact SturmReplay.head_ne_zero hreplay

/-- A positive literal degree implies a nonzero executable polynomial. -/
private theorem ne_zero_of_degree_pos {p : ZPoly}
    (h : 0 < p.degree?.getD 0) : p ≠ 0 := by
  intro hp
  subst p
  simp [DensePoly.degree?] at h

/-- The recomputed atom product is nonzero for an accepted certificate. -/
theorem product_ne_zero {s : Sentence} {cert : CarrierCert}
    (h : cert.check s = true) : s.product ≠ 0 :=
  ne_zero_of_degree_pos (check_sound h).2.1

end CarrierCert

end Hex.RCF
