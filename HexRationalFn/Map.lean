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

section Laws

variable (f : K → L) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hd : ∀ a b, f (a / b) = f a / f b) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)

include hs in
private theorem coeff_add (a b : K) : f (a + b) = f a + f b := by
  have subtract := hs (a + b) b
  have cancel : a + b - b = a := by grind
  rw [cancel] at subtract
  grind

/-- Coefficient transport preserves and reflects canonical zero. -/
theorem mapCoeffs_eq_zero (q : RationalFn K) :
    mapCoeffs f hz h1 hs hm hd hi q = 0 ↔ q = 0 := by
  rw [← num_eq_zero, mapCoeffs_num, DensePoly.Interpret.map_eq_zero, num_eq_zero]

@[simp] theorem mapCoeffs_zero : mapCoeffs f hz h1 hs hm hd hi 0 = 0 :=
  (mapCoeffs_eq_zero f hz h1 hs hm hd hi 0).mpr rfl

@[simp] theorem mapCoeffs_one : mapCoeffs f hz h1 hs hm hd hi 1 = 1 := by
  apply ext
  · change DensePoly.Interpret.map f hz (1 : DensePoly K) = 1
    exact DensePoly.Interpret.map_one f hz h1
  · change DensePoly.Interpret.map f hz (1 : DensePoly K) = 1
    exact DensePoly.Interpret.map_one f hz h1

/-- Map the actual cross-product equation of a fraction presentation. -/
theorem Represents.mapCoeffs {q : RationalFn K} {a b : DensePoly K}
    (represented : Represents q a b) :
    Represents (mapCoeffs f hz h1 hs hm hd hi q)
      (DensePoly.Interpret.map f hz a) (DensePoly.Interpret.map f hz b) := by
  unfold Represents at represented ⊢
  rw [mapCoeffs_num, mapCoeffs_den,
    ← DensePoly.Interpret.map_mul f hz (coeff_add f hs) hm,
    ← DensePoly.Interpret.map_mul f hz (coeff_add f hs) hm]
  exact congrArg (DensePoly.Interpret.map f hz) represented

/-- Coefficient transport commutes with canonical fraction addition. -/
theorem mapCoeffs_add (a b : RationalFn K) :
    mapCoeffs f hz h1 hs hm hd hi (a + b) =
      mapCoeffs f hz h1 hs hm hd hi a + mapCoeffs f hz h1 hs hm hd hi b := by
  have left := ((represents_self a).add (represents_self b)).mapCoeffs f hz h1 hs hm hd hi
  have right := (represents_self (mapCoeffs f hz h1 hs hm hd hi a)).add
    (represents_self (mapCoeffs f hz h1 hs hm hd hi b))
  simp only [DensePoly.Interpret.map_add f hz (coeff_add f hs),
    DensePoly.Interpret.map_mul f hz (coeff_add f hs) hm] at left
  exact left.eq right (DensePoly.mul_ne_zero
    (mapCoeffs f hz h1 hs hm hd hi a).den_ne_zero
    (mapCoeffs f hz h1 hs hm hd hi b).den_ne_zero)

/-- Coefficient transport commutes with canonical fraction multiplication. -/
theorem mapCoeffs_mul (a b : RationalFn K) :
    mapCoeffs f hz h1 hs hm hd hi (a * b) =
      mapCoeffs f hz h1 hs hm hd hi a * mapCoeffs f hz h1 hs hm hd hi b := by
  have left := ((represents_self a).mul (represents_self b)).mapCoeffs f hz h1 hs hm hd hi
  have right := (represents_self (mapCoeffs f hz h1 hs hm hd hi a)).mul
    (represents_self (mapCoeffs f hz h1 hs hm hd hi b))
  simp only [DensePoly.Interpret.map_mul f hz (coeff_add f hs) hm] at left
  exact left.eq right (DensePoly.mul_ne_zero
    (mapCoeffs f hz h1 hs hm hd hi a).den_ne_zero
    (mapCoeffs f hz h1 hs hm hd hi b).den_ne_zero)

/-- Coefficient transport commutes with negation. -/
theorem mapCoeffs_neg (a : RationalFn K) :
    mapCoeffs f hz h1 hs hm hd hi (-a) = -mapCoeffs f hz h1 hs hm hd hi a := by
  have left := (represents_self a).neg.mapCoeffs f hz h1 hs hm hd hi
  have right := (represents_self (mapCoeffs f hz h1 hs hm hd hi a)).neg
  simp only [DensePoly.Interpret.map_neg f hz hs] at left
  exact left.eq right (mapCoeffs f hz h1 hs hm hd hi a).den_ne_zero

/-- Coefficient transport commutes with subtraction. -/
theorem mapCoeffs_sub (a b : RationalFn K) :
    mapCoeffs f hz h1 hs hm hd hi (a - b) =
      mapCoeffs f hz h1 hs hm hd hi a - mapCoeffs f hz h1 hs hm hd hi b := by
  simp only [Lean.Grind.Ring.sub_eq_add_neg, mapCoeffs_add, mapCoeffs_neg]

/-- Coefficient transport commutes with totalized inversion. -/
theorem mapCoeffs_inv (a : RationalFn K) :
    mapCoeffs f hz h1 hs hm hd hi a⁻¹ = (mapCoeffs f hz h1 hs hm hd hi a)⁻¹ := by
  by_cases zero : a = 0
  · simp [zero]
  · have numerator : a.num ≠ 0 := fun h => zero ((num_eq_zero a).mp h)
    have mapped : (mapCoeffs f hz h1 hs hm hd hi a).num ≠ 0 := by
      rw [mapCoeffs_num]
      exact fun h => numerator ((DensePoly.Interpret.map_eq_zero f hz a.num).mp h)
    have left := (show Represents a⁻¹ a.den a.num from inv_spec a numerator).mapCoeffs
      f hz h1 hs hm hd hi
    have right : Represents (mapCoeffs f hz h1 hs hm hd hi a)⁻¹
        (mapCoeffs f hz h1 hs hm hd hi a).den (mapCoeffs f hz h1 hs hm hd hi a).num :=
      inv_spec (mapCoeffs f hz h1 hs hm hd hi a) mapped
    exact left.eq right mapped

/-- Coefficient transport commutes with division. -/
theorem mapCoeffs_div (a b : RationalFn K) :
    mapCoeffs f hz h1 hs hm hd hi (a / b) =
      mapCoeffs f hz h1 hs hm hd hi a / mapCoeffs f hz h1 hs hm hd hi b := by
  simp only [Lean.Grind.Field.div_eq_mul_inv, mapCoeffs_mul, mapCoeffs_inv]

/-- Coefficient transport carries a constant to the corresponding constant. -/
theorem mapCoeffs_C (a : K) :
    mapCoeffs f hz h1 hs hm hd hi (C a) = C (f a) := by
  apply ext
  · change DensePoly.Interpret.map f hz (DensePoly.C a) = DensePoly.C (f a)
    simp [DensePoly.C, DensePoly.Interpret.map_ofCoeffs]
  · change DensePoly.Interpret.map f hz (1 : DensePoly K) = 1
    exact DensePoly.Interpret.map_one f hz h1

end Laws

/-- Lift a fraction into the next rational-function coefficient field. -/
@[expose] def liftConstants (q : RationalFn K) : RationalFn (RationalFn K) :=
  mapCoeffs (C (K := K)) C_eq_zero_iff C_one C_sub C_mul
    (fun a b => by
      simp only [Lean.Grind.Field.div_eq_mul_inv, C_mul, C_inv])
    C_inv q

end Hex.RationalFn

/-- info: 'Hex.RationalFn.mapCoeffs_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RationalFn.mapCoeffs_add

/-- info: 'Hex.RationalFn.mapCoeffs_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RationalFn.mapCoeffs_mul

/-- info: 'Hex.RationalFn.mapCoeffs_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RationalFn.mapCoeffs_inv
