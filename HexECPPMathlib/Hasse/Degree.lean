/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.Fintype.Option
public import HasseWeil.HasseBound

/-!
# Counting elliptic curve points and applying Hasse's bound

Mathlib's affine point type includes the point at infinity and nonsingular
coordinate pairs. Over a finite field it is a finite type, so we can speak
of the number of points on the curve.

Hasse's theorem bounds the difference between that number and `|F| + 1` by
`2*√|F|`. We import Chris Birkbeck's proof from AINTLIB (Apache 2.0), then
express the bound as the integer inequality `t² ≤ 4*|F|`. This is the form
used to prove primality from an ECPP certificate. The imported theorem's
dependencies are audited to allow only Lean's standard axioms.

The related interpretation of prime-field points as Frobenius fixed points
is provided in `HexECPPMathlib.Hasse.Frobenius`.
-/

@[expose] public section

namespace Hex.ECPP

open WeierstrassCurve

/-- Over a finite ring, the nonsingular affine points and infinity form a
finite type, via Mathlib's nonsingular-point equivalence. -/
noncomputable instance pointFintype {F : Type*} [CommRing F] [Fintype F]
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

/-- Hasse's bound on the number of points of an elliptic curve over a finite
field, written as an exact integer inequality. If `N` is the point count
and `r` the field size, `(r + 1 - N)² ≤ 4*r`.
The proof uses AINTLIB's `HasseWeil.WeilPairing.hasse_bound`, whose
dependencies contain only the standard Lean axioms. -/
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
