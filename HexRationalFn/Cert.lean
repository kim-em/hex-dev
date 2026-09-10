/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRationalFn.Field

public section

namespace Hex.RationalFn

universe u
variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
open DensePoly

/-- Raw normalization data with Bézout witnesses for kernel replay. -/
structure Cert (K : Type u) [Lean.Grind.Field K] [DecidableEq K] where
  /-- Proposed canonical numerator. -/
  num : DensePoly K
  /-- Proposed canonical denominator. -/
  den : DensePoly K
  /-- Coefficient of the numerator in a Bézout identity. -/
  s : DensePoly K
  /-- Coefficient of the denominator in a Bézout identity. -/
  t : DensePoly K

/-- Check input validity, monicity, fraction equality and a Bézout identity. -/
@[expose]
def check (p q : DensePoly K) (cert : Cert K) : Bool :=
  decide (q ≠ 0 ∧ cert.den.leadingCoeff = 1 ∧ cert.num * q = p * cert.den ∧
    cert.s * cert.num + cert.t * cert.den = 1)

/-- Accepted data satisfy exactly the four advertised certificate conditions. -/
theorem check_iff (p q : DensePoly K) (cert : Cert K) :
    check p q cert = true ↔ q ≠ 0 ∧ cert.den.leadingCoeff = 1 ∧
      cert.num * q = p * cert.den ∧ cert.s * cert.num + cert.t * cert.den = 1 := by
  simp only [check, decide_eq_true_eq]

/-- Construct a canonical value from an accepted certificate, without Euclidean search. -/
@[expose]
def ofCert (p q : DensePoly K) (cert : Cert K) (h : check p q cert = true) : RationalFn K :=
  have hc := (check_iff p q cert).mp h
  ofCoprime cert.num cert.den hc.2.1 ⟨cert.s, cert.t, hc.2.2.2⟩

/-- Kernel replay identifies the certified pair with the unique normalization. -/
theorem check_sound (p q : DensePoly K) (cert : Cert K) (h : check p q cert = true) :
    ofCert p q cert h = normalize p q ((check_iff p q cert).mp h).1 :=
  normalize_unique defaultPlan p q ((check_iff p q cert).mp h).1 _
    ((check_iff p q cert).mp h).2.2.1

/-- Checked certificate construction returns none precisely when replay fails. -/
@[expose]
def ofCert? (p q : DensePoly K) (cert : Cert K) : Option (RationalFn K) :=
  if h : check p q cert = true then some (ofCert p q cert h) else none

/-- Certificate construction fails exactly when its Boolean check is false. -/
theorem ofCert?_eq_none (p q : DensePoly K) (cert : Cert K) :
    ofCert? p q cert = none ↔ check p q cert = false := by
  unfold ofCert?
  split <;> simp_all

/-- Generate a normalized pair and rescaled extended-gcd witnesses. -/
@[expose]
def certifyWith (plan : MulPlan K) (p q : DensePoly K) (hq : q ≠ 0) : Cert K :=
  let f := normalizeWith plan p q hq
  let r := xgcdWith plan f.num f.den
  let c := r.gcd.leadingCoeff⁻¹
  ⟨f.num, f.den, scale c r.left, scale c r.right⟩

/-- Every generated certificate is accepted by the independent replay checker. -/
theorem certify_checks (plan : MulPlan K) (p q : DensePoly K) (hq : q ≠ 0) :
    check p q (certifyWith plan p q hq) = true := by
  apply (check_iff _ _ _).mpr
  let f := normalizeWith plan p q hq
  refine ⟨hq, f.monic_den, normalizeWith_spec plan p q hq, ?_⟩
  change scale (xgcdWith plan f.num f.den).gcd.leadingCoeff⁻¹
      (xgcdWith plan f.num f.den).left * f.num +
    scale (xgcdWith plan f.num f.den).gcd.leadingCoeff⁻¹
      (xgcdWith plan f.num f.den).right * f.den = 1
  rw [xgcdWith_eq, ← scale_mul, ← scale_mul, ← scale_add, xgcd_bezout,
    xgcd_gcd_eq_gcd, ← monicize_eq_scale]
  exact f.coprime

end Hex.RationalFn
