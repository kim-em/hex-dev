/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Fintype.Option
import HasseWeil.HasseBound

/-!
# Finite affine elliptic-curve points

The affine point type supplied by Mathlib consists of the point at infinity
and nonsingular coordinate pairs. Over a finite field this makes the point
type finite. We use Chris Birkbeck's proved Hasse bound in AINTLIB
(Apache 2.0) for the mathematical estimate. Its axiom-clean capstone uses
Frobenius and `1 − Frobenius` Weil-pairing scaling, coprime pencil scaling,
and a nonnegative kernel-cardinality quadratic form. This supplies the
substantial degree/Frobenius infrastructure used here; the independent
fixed-point correspondence used by ECPP is in `Frobenius.lean`.
-/

namespace Hex.ECPP

open WeierstrassCurve

noncomputable instance {F : Type*} [CommRing F] [Fintype F]
    (W : WeierstrassCurve.Affine F) : Fintype W.Point := by
  classical
  letI : Fintype (WithZero {xy : F × F // W.Nonsingular xy.fst xy.snd}) :=
    Fintype.ofEquiv
      (Option {xy : F × F // W.Nonsingular xy.fst xy.snd}) (Equiv.refl _)
  exact Fintype.ofEquiv
    (WithZero {xy : F × F // W.Nonsingular xy.fst xy.snd})
    (W.nonsingularPointEquiv).symm

end Hex.ECPP

namespace Hex.ECPP

open WeierstrassCurve

/-- The integer Hasse inequality used by ECPP. The underlying theorem is
`HasseWeil.WeilPairing.hasse_bound`, with only the standard Lean axioms. -/
theorem hasse_sq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.toAffine.IsElliptic] :
    ((Fintype.card F : ℤ) + 1 - (Fintype.card W.toAffine.Point : ℤ)) ^ 2 ≤
      4 * (Fintype.card F : ℤ) := by
  have h := HasseWeil.WeilPairing.hasse_bound W
  change |((Fintype.card W.toAffine.Point : ℝ) - (Fintype.card F : ℝ) - 1)| ≤
    2 * Real.sqrt (Fintype.card F : ℝ) at h
  have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h
  rw [sq_abs, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (Fintype.card F : ℝ))] at hsq
  have hreal :
      ((Fintype.card F : ℝ) + 1 - (Fintype.card W.toAffine.Point : ℝ)) ^ 2 ≤
        4 * (Fintype.card F : ℝ) := by nlinarith
  exact_mod_cast hreal

end Hex.ECPP
