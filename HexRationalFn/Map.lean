/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRationalFn.Field
public import HexPoly.Interpret

public section

namespace Hex.RationalFn

universe u v
variable {K : Type u} {L : Type v}
variable [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]

/-- Map a canonical fraction through a coefficient-field embedding. The mapped
pair remains canonical, so transport does not run polynomial gcd. -/
@[expose] def mapCoeffs (f : K → L) (hz : ∀ a, f a = 0 ↔ a = 0)
    (h1 : f 1 = 1)
    (hs : ∀ a b, f (a - b) = f a - f b)
    (hm : ∀ a b, f (a * b) = f a * f b)
    (hd : ∀ a b, f (a / b) = f a / f b)
    (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
    (q : RationalFn K) : RationalFn L :=
  ⟨DensePoly.Interpret.map f hz q.num,
    DensePoly.Interpret.map f hz q.den,
    by
      change (DensePoly.Interpret.map f hz q.den).leadingCoeff = 1
      rw [DensePoly.Interpret.map_leading, q.monic_den, h1],
    by
      rw [← DensePoly.Interpret.map_gcd f hz hs hm hd q.num q.den,
        ← DensePoly.Interpret.map_monicize f hz hm hi]
      rw [q.coprime, DensePoly.Interpret.map_one f hz h1]⟩

@[simp] theorem mapCoeffs_num (f : K → L) (hz : ∀ a, f a = 0 ↔ a = 0)
    (h1 : f 1 = 1) (hs : ∀ a b, f (a - b) = f a - f b)
    (hm : ∀ a b, f (a * b) = f a * f b)
    (hd : ∀ a b, f (a / b) = f a / f b)
    (hi : ∀ a, f a⁻¹ = (f a)⁻¹) (q : RationalFn K) :
    (mapCoeffs f hz h1 hs hm hd hi q).num = DensePoly.Interpret.map f hz q.num := rfl

@[simp] theorem mapCoeffs_den (f : K → L) (hz : ∀ a, f a = 0 ↔ a = 0)
    (h1 : f 1 = 1) (hs : ∀ a b, f (a - b) = f a - f b)
    (hm : ∀ a b, f (a * b) = f a * f b)
    (hd : ∀ a b, f (a / b) = f a / f b)
    (hi : ∀ a, f a⁻¹ = (f a)⁻¹) (q : RationalFn K) :
    (mapCoeffs f hz h1 hs hm hd hi q).den = DensePoly.Interpret.map f hz q.den := rfl

/-- Lift a fraction into the next rational-function coefficient field. -/
@[expose] def liftConstants (q : RationalFn K) : RationalFn (RationalFn K) :=
  mapCoeffs (C (K := K)) C_eq_zero_iff C_one C_sub C_mul
    (fun a b => by
      simp only [Lean.Grind.Field.div_eq_mul_inv, C_mul, C_inv])
    C_inv q

end Hex.RationalFn
