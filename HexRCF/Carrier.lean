/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Language
public import HexRCF.SturmReplay
public import HexRealRootsMathlib.SquareFreeCore

public section

/-!
# Certified square-free carriers for reflected RCF sentences

The carrier checker recomputes the nonconstant atom polynomials and their
product from the reflected sentence.  A certificate supplies a proposed
square-free carrier, two factor witnesses, two nonzero integer scales, and a
multiplication-only Sturm replay for the carrier.  Checking uses only exact
polynomial arithmetic, differentiation, coefficient equality, and the replay
checker.
-/

namespace Hex.RCF

open HexRealRootsMathlib Polynomial

/-- All atom polynomials in a formula, in deterministic left-to-right order. -/
@[expose]
def Formula.polys : Formula → List ZPoly
  | .atom a => [a.p]
  | .tt | .ff => []
  | .not φ => φ.polys
  | .and φ ψ | .or φ ψ | .imp φ ψ => φ.polys ++ ψ.polys

/-- The body of a one-quantifier sentence. -/
@[expose]
def Sentence.formula : Sentence → Formula
  | .forallReal φ | .existsReal φ | .forallIoc _ _ φ | .existsIoc _ _ φ => φ

/-- The positive-degree atom polynomials used by the carrier decomposition.
Constant atoms remain in the reflected formula but, after their truth values
are evaluated, do not contribute carrier boundaries. -/
@[expose]
def Sentence.polys (s : Sentence) : List ZPoly :=
  s.formula.polys.filter fun p => decide (0 < p.degree?.getD 0)

/-- The product of all nonconstant atom polynomials. -/
@[expose]
def Sentence.product (s : Sentence) : ZPoly := s.polys.prod

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

/-- Executable carrier validation.  The atom product is recomputed from the
sentence and is never supplied by the certificate. -/
@[expose]
def check (s : Sentence) (cert : CarrierCert) : Bool :=
  let q := s.product
  -- `Sentence.polys` filters by this predicate; retaining the explicit walk
  -- makes the certificate contract visible at its trust boundary.
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

/-- An accepted carrier is squarefree after casting to real coefficients. -/
theorem squarefree {s : Sentence} {cert : CarrierCert}
    (h : cert.check s = true) : Squarefree (toPolyℝ cert.carrier) :=
  by
    obtain ⟨_hdegrees, _hqdeg, _hr0, _hk0, _hd0, _hfactor, _hderiv, hreplay⟩ :=
      check_sound h
    exact SturmReplay.squarefree_of_check hreplay

/-- A positive literal degree implies a nonzero executable polynomial. -/
private theorem ne_zero_of_degree_pos {p : ZPoly} (h : 0 < p.degree?.getD 0) : p ≠ 0 := by
  intro hp
  subst p
  simp [DensePoly.degree?] at h

/-- The recomputed atom product is nonzero for an accepted certificate. -/
theorem product_ne_zero {s : Sentence} {cert : CarrierCert}
    (h : cert.check s = true) : s.product ≠ 0 :=
  ne_zero_of_degree_pos (check_sound h).2.1

/-- Exact scalar-and-factor identities imply that the proposed factor and the
original polynomial have the same real roots. -/
theorem isRoot_factor_iff {q p r t : ZPoly} {k d : Int}
    (hq0 : q ≠ 0) (hk0 : k ≠ 0) (hd0 : d ≠ 0)
    (hfactorZ : q = DensePoly.scale k (p * r))
    (hderivZ : DensePoly.scale d (DensePoly.derivative q) = r * t) (x : ℝ) :
    (toPolyℝ p).IsRoot x ↔ (toPolyℝ q).IsRoot x := by
  have hq0ℝ : toPolyℝ q ≠ 0 := fun hzero => hq0 (toPolyℝ_eq_zero_iff.mp hzero)
  have hk : ((k : Int) : ℝ) ≠ 0 := by exact_mod_cast hk0
  have hd : ((d : Int) : ℝ) ≠ 0 := by exact_mod_cast hd0
  have hfactor := congrArg toPolyℝ hfactorZ
  rw [toPolyℝ_scale, toPolyℝ_mul] at hfactor
  have hderiv := congrArg toPolyℝ hderivZ
  rw [toPolyℝ_scale, toPolyℝ_derivative, toPolyℝ_mul] at hderiv
  have hqcr : toPolyℝ q =
      (Polynomial.C (k : ℝ) * toPolyℝ p) * toPolyℝ r := by
    rw [hfactor]
    ring
  have hrd : toPolyℝ r ∣ derivative (toPolyℝ q) := by
    refine ⟨Polynomial.C ((d : ℝ)⁻¹) * toPolyℝ t, ?_⟩
    have hcancel : Polynomial.C ((d : ℝ)⁻¹) *
        Polynomial.C (d : ℝ) = (1 : ℝ[X]) := by
      rw [← Polynomial.C_mul]
      simp [hd]
    calc
      derivative (toPolyℝ q) =
          (Polynomial.C ((d : ℝ)⁻¹) * Polynomial.C (d : ℝ)) *
            derivative (toPolyℝ q) := by rw [hcancel, one_mul]
      _ = Polynomial.C ((d : ℝ)⁻¹) *
          (Polynomial.C (d : ℝ) * derivative (toPolyℝ q)) := by ring
      _ = Polynomial.C ((d : ℝ)⁻¹) * (toPolyℝ r * toPolyℝ t) := by rw [hderiv]
      _ = toPolyℝ r * (Polynomial.C ((d : ℝ)⁻¹) * toPolyℝ t) := by ring
  have hgen := HexRealRootsMathlib.isRoot_left_iff_of_mul_of_dvd_derivative
    hq0ℝ hqcr hrd x
  have hscale :
      (Polynomial.C (k : ℝ) * toPolyℝ p).IsRoot x ↔ (toPolyℝ p).IsRoot x := by
    simp only [Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_C, mul_eq_zero]
    simp [hk]
  exact hscale.symm.trans hgen

/-- Exact identities accepted by the checker imply that the carrier and
recomputed atom product have the same real roots. -/
theorem isRoot_carrier_iff_product {s : Sentence} {cert : CarrierCert}
    (h : cert.check s = true) (x : ℝ) :
    (toPolyℝ cert.carrier).IsRoot x ↔ (toPolyℝ s.product).IsRoot x := by
  obtain ⟨_hdegrees, _hqdeg, _hr0, hk0, hd0, hfactor, hderiv, _hreplay⟩ :=
    check_sound h
  exact isRoot_factor_iff (product_ne_zero h) hk0 hd0 hfactor hderiv x

end CarrierCert

/-- A real root of a product of literal integer polynomials is exactly a root
of one list member. -/
theorem isRoot_prod_iff {ps : List ZPoly} (x : ℝ) :
    (toPolyℝ ps.prod).IsRoot x ↔ ∃ p ∈ ps, (toPolyℝ p).IsRoot x := by
  induction ps with
  | nil => simp [Polynomial.IsRoot, toPolyℝ]
  | cons p ps ih =>
      rw [List.prod_cons, toPolyℝ_mul]
      simp only [Polynomial.IsRoot, Polynomial.eval_mul, mul_eq_zero]
      have ih' : (toPolyℝ ps.prod).eval x = 0 ↔
          ∃ q ∈ ps, (toPolyℝ q).eval x = 0 := by
        simpa only [Polynomial.IsRoot] using ih
      rw [ih']
      aesop

/-- The accepted carrier roots are exactly the union of the roots of the
nonconstant atom polynomials recomputed from the sentence. -/
theorem CarrierCert.isRoot_iff_atom {s : Sentence} {cert : CarrierCert}
    (h : cert.check s = true) (x : ℝ) :
    (toPolyℝ cert.carrier).IsRoot x ↔
      ∃ p ∈ s.polys, (toPolyℝ p).IsRoot x := by
  rw [cert.isRoot_carrier_iff_product h x]
  unfold Sentence.product
  exact isRoot_prod_iff x

end Hex.RCF
