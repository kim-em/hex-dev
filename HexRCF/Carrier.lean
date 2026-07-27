/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.CarrierCheck
public import HexRCF.Language
public import HexRCF.SturmReplay
public import HexRealRootsMathlib.SquareFreeCore

public section

/-!
# Real-root semantics of certified RCF carriers

The Mathlib-free certificate and checker live in `HexRCF.CarrierCheck`. The
theorems in this file prove that an accepted carrier is squarefree and has
exactly the roots of the sentence's nonconstant atom polynomials.
-/

namespace Hex.RCF

open HexRealRootsMathlib Polynomial

namespace CarrierCert

/-- An accepted carrier is squarefree after casting to real coefficients. -/
theorem squarefree {s : Sentence} {cert : CarrierCert}
    (h : cert.check s = true) : Squarefree (toPolyℝ cert.carrier) :=
  by
    obtain ⟨_hdegrees, _hqdeg, _hr0, _hk0, _hd0, _hfactor, _hderiv, hreplay⟩ :=
      check_sound h
    exact SturmReplay.squarefree_of_check hreplay

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
