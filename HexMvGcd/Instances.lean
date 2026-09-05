/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.ExtGcd
public import HexMvGcd.Normalize
public import HexPolyFp.Field
public import HexPolyFp.PrimeField
public import HexResultant.ExactDiv

@[expose] public section
set_option backward.proofsInPublic true

/-!
Base coefficient instances for the multivariate gcd kernel.

The field gcd convention is `0` only for the pair `(0, 0)` and `1`
otherwise. `normUnit` is defined at zero as `1`, as required by
`LawfulGcdOps`; the inverse is used only on nonzero inputs.
-/

namespace Hex

/-! # Integers -/

@[reducible] instance instGcdOpsInt : GcdOps Int where
  gcd a b := (Int.gcd a b : Int)
  exactDiv a b := a / b
  isUnit a := decide (a = 1 ∨ a = -1)
  normUnit a := if a < 0 then -1 else 1

instance instBezoutOpsInt : BezoutOps Int where
  gcd := GcdOps.gcd
  exactDiv := GcdOps.exactDiv
  isUnit := GcdOps.isUnit
  normUnit := GcdOps.normUnit
  xgcd a b :=
    let r := HexArith.Int.extGcd a b
    (r.2.1, r.2.2)

private theorem int_normalize_eq_natAbs (a : Int) :
    a * (if a < 0 then -1 else 1) = (a.natAbs : Int) := by
  by_cases h : a < 0
  · rw [ite_eq_left h,
      Int.ofNat_natAbs_of_nonpos (Int.le_of_lt h)]
    omega
  · rw [ite_eq_right h,
      Int.ofNat_natAbs_of_nonneg (Int.le_of_not_gt h)]
    omega

instance instLawfulGcdOpsInt : LawfulGcdOps Int := by
  constructor
  · intro a b
    rfl
  · decide
  · intro a b h
    exact Int.mul_eq_zero.mp h
  · intro a b
    exact Int.gcd_dvd_left a b
  · intro a b
    exact Int.gcd_dvd_right a b
  · intro a b d hda hdb
    exact Int.dvd_coe_gcd hda hdb
  · intro a b
    change
      (Int.gcd a b : Int) *
          (if (Int.gcd a b : Int) < 0 then -1 else 1) =
        (Int.gcd a b : Int)
    rw [int_normalize_eq_natAbs, Int.natAbs_natCast]
  · intro a b hb
    exact Int.mul_ediv_cancel a hb
  · intro a
    change decide (a = 1 ∨ a = -1) = true ↔ ∃ b, a * b = 1
    rw [decide_eq_true_eq]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨1, by decide⟩
      · exact ⟨-1, by decide⟩
    · rintro ⟨b, hab⟩
      have habAbs := congrArg Int.natAbs hab
      rw [Int.natAbs_mul] at habAbs
      have haAbs : a.natAbs = 1 :=
        Nat.eq_one_of_mul_eq_one_right (by simpa using habAbs)
      exact Int.natAbs_eq_iff.mp haAbs
  · intro a
    change ∃ b, (if a < 0 then -1 else 1) * b = 1
    by_cases h : a < 0
    · exact ⟨-1, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  · intro a b
    change
      a * b * (if a * b < 0 then -1 else 1) =
        (a * (if a < 0 then -1 else 1)) *
          (b * (if b < 0 then -1 else 1))
    rw [int_normalize_eq_natAbs, int_normalize_eq_natAbs,
      int_normalize_eq_natAbs, Int.natAbs_mul, Int.natCast_mul]
  · intro a
    change
      (a * (if a < 0 then -1 else 1)) *
          (if a * (if a < 0 then -1 else 1) < 0 then -1 else 1) =
        a * (if a < 0 then -1 else 1)
    rw [int_normalize_eq_natAbs, int_normalize_eq_natAbs,
      Int.natAbs_natCast]
  · intro a ha
    change decide (a = 1 ∨ a = -1) = true at ha
    rw [decide_eq_true_eq] at ha
    rcases ha with rfl | rfl <;> decide

instance instLawfulBezoutOpsInt : LawfulBezoutOps Int := by
  constructor
  intro a b
  simp only [BezoutOps.xgcd]
  rw [HexArith.Int.extGcd_bezout_gcd]
  symm
  change
    (Int.gcd a b : Int) *
        (if (Int.gcd a b : Int) < 0 then -1 else 1) =
      (Int.gcd a b : Int)
  rw [int_normalize_eq_natAbs, Int.natAbs_natCast]

/-! # Rationals -/

/-- Divisibility in a field, stated in the same multiplication orientation as
the polynomial instances. -/
instance instDvdRat : Dvd Rat where
  dvd a b := ∃ c, b = a * c

def ratXgcd (a b : Rat) : Rat × Rat :=
  if a = 0 then
    if b = 0 then (0, 0) else (0, b⁻¹)
  else
    (a⁻¹, 0)

@[reducible] instance instGcdOpsRat : GcdOps Rat where
  gcd a b := if a = 0 ∧ b = 0 then 0 else 1
  exactDiv a b := a / b
  isUnit a := decide (a ≠ 0)
  normUnit a := if a = 0 then 1 else a⁻¹

instance instBezoutOpsRat : BezoutOps Rat where
  gcd := GcdOps.gcd
  exactDiv := GcdOps.exactDiv
  isUnit := GcdOps.isUnit
  normUnit := GcdOps.normUnit
  xgcd := ratXgcd

instance instLawfulGcdOpsRat : LawfulGcdOps Rat := by
  constructor
  · intro a b
    rfl
  · decide
  · intro a b h
    exact Rat.mul_eq_zero.mp h
  · intro a b
    change ∃ c, a = (if a = 0 ∧ b = 0 then 0 else 1) * c
    by_cases h : a = 0 ∧ b = 0
    · exact ⟨0, by simp [h]⟩
    · exact ⟨a, by simp [h]⟩
  · intro a b
    change ∃ c, b = (if a = 0 ∧ b = 0 then 0 else 1) * c
    by_cases h : a = 0 ∧ b = 0
    · exact ⟨0, by simp [h]⟩
    · exact ⟨b, by simp [h]⟩
  · intro a b d hda hdb
    change ∃ c, (if a = 0 ∧ b = 0 then 0 else 1) = d * c
    by_cases hab : a = 0 ∧ b = 0
    · exact ⟨0, by simp [hab]⟩
    · have hd : d ≠ 0 := by
        intro hd
        rcases hda with ⟨ca, ha⟩
        rcases hdb with ⟨cb, hb⟩
        apply hab
        simp [hd] at ha hb
        exact ⟨ha, hb⟩
      exact ⟨d⁻¹, by rw [ite_eq_right hab, Rat.mul_inv_cancel d hd]⟩
  · intro a b
    change
      (if a = 0 ∧ b = 0 then 0 else 1) *
          (if (if a = 0 ∧ b = 0 then 0 else 1) = 0 then 1
            else (if a = 0 ∧ b = 0 then 0 else 1)⁻¹) =
        (if a = 0 ∧ b = 0 then 0 else 1)
    by_cases h : a = 0 ∧ b = 0
    · simp [h]
    · simp only [h, ite_false]
      change (1 : Rat) * (if (1 : Rat) = 0 then 1 else 1⁻¹) = 1
      rw [ite_eq_right (by decide)]
      exact Rat.mul_inv_cancel 1 (by decide)
  · intro a b hb
    exact Rat.mul_div_cancel hb
  · intro a
    change decide (a ≠ 0) = true ↔ ∃ b, a * b = 1
    rw [decide_eq_true_eq]
    constructor
    · intro ha
      exact ⟨a⁻¹, Rat.mul_inv_cancel a ha⟩
    · rintro ⟨b, hab⟩ ha
      subst a
      simp at hab
  · intro a
    change ∃ b, (if a = 0 then 1 else a⁻¹) * b = 1
    by_cases ha : a = 0
    · exact ⟨1, by simp [ha]⟩
    · exact ⟨a, by rw [ite_eq_right ha, Rat.inv_mul_cancel a ha]⟩
  · intro a b
    change
      a * b * (if a * b = 0 then 1 else (a * b)⁻¹) =
        (a * (if a = 0 then 1 else a⁻¹)) *
          (b * (if b = 0 then 1 else b⁻¹))
    by_cases ha : a = 0
    · simp [ha]
    · by_cases hb : b = 0
      · simp [hb]
      · have hab : a * b ≠ 0 := fun h =>
          ha ((Rat.mul_eq_zero.mp h).resolve_right hb)
        simp [ha, hb, hab, Rat.mul_inv_cancel]
  · intro a
    change
      (a * (if a = 0 then 1 else a⁻¹)) *
          (if a * (if a = 0 then 1 else a⁻¹) = 0 then 1
            else (a * (if a = 0 then 1 else a⁻¹))⁻¹) =
        a * (if a = 0 then 1 else a⁻¹)
    by_cases ha : a = 0 <;> simp [ha, Rat.mul_inv_cancel]
  · intro a ha
    change a * (if a = 0 then 1 else a⁻¹) = 1
    change decide (a ≠ 0) = true at ha
    have hne : a ≠ 0 := by simpa only [decide_eq_true_eq] using ha
    rw [ite_eq_right hne, Rat.mul_inv_cancel a hne]

instance instLawfulBezoutOpsRat : LawfulBezoutOps Rat := by
  constructor
  intro a b
  change
    let uv := ratXgcd a b
    uv.1 * a + uv.2 * b =
      (if a = 0 ∧ b = 0 then 0 else 1) *
        (if (if a = 0 ∧ b = 0 then 0 else 1) = 0 then 1
          else (if a = 0 ∧ b = 0 then 0 else 1)⁻¹)
  have inv_one : (1 : Rat)⁻¹ = 1 := by
    have h := Rat.mul_inv_cancel (1 : Rat) (by decide)
    rw [Lean.Grind.Semiring.one_mul] at h
    exact h
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · simp [ratXgcd, ha, hb]
      grind
    · simp [ratXgcd, ha, hb, Rat.inv_mul_cancel, inv_one]
      grind
  · simp [ratXgcd, ha, Rat.inv_mul_cancel, inv_one]
    grind

/-! # Bounded prime fields -/

namespace ZMod64

variable {p : Nat} [hp : Bounds p] [PrimeModulus p]

def fieldXgcd (a b : @ZMod64 p hp) : @ZMod64 p hp × @ZMod64 p hp :=
  if a = 0 then
    if b = 0 then (0, 0) else (0, b⁻¹)
  else
    (a⁻¹, 0)

end ZMod64

/-- Field divisibility, in multiplication orientation. -/
instance instDvdZMod64 {p : Nat} [hp : ZMod64.Bounds p] :
    Dvd (@ZMod64 p hp) where
  dvd a b := ∃ c, b = a * c

@[reducible] instance instGcdOpsZMod64 {p : Nat} [hp : ZMod64.Bounds p] :
    GcdOps (@ZMod64 p hp) where
  gcd a b := if a = 0 ∧ b = 0 then 0 else 1
  exactDiv a b := a / b
  isUnit a := decide (a ≠ 0)
  normUnit a := if a = 0 then 1 else a⁻¹

instance instBezoutOpsZMod64 {p : Nat} [hp : ZMod64.Bounds p] :
    BezoutOps (@ZMod64 p hp) where
  gcd := GcdOps.gcd
  exactDiv := GcdOps.exactDiv
  isUnit := GcdOps.isUnit
  normUnit := GcdOps.normUnit
  xgcd := ZMod64.fieldXgcd

instance instLawfulGcdOpsZMod64 {p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] :
    @LawfulGcdOps (@ZMod64 p hp) _ _ _ _ instDvdZMod64 instGcdOpsZMod64 := by
  constructor
  · intro a b
    rfl
  · exact fun h =>
      ZMod64.one_ne_zero_of_prime (ZMod64.PrimeModulus.prime (p := p)) h
  · intro a b h
    exact ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero_of_prime_modulus h
  · intro a b
    change ∃ c, a = (if a = 0 ∧ b = 0 then 0 else 1) * c
    by_cases h : a = 0 ∧ b = 0
    · exact ⟨0, by simp [h]⟩
    · exact ⟨a, by simp [h]⟩
  · intro a b
    change ∃ c, b = (if a = 0 ∧ b = 0 then 0 else 1) * c
    by_cases h : a = 0 ∧ b = 0
    · exact ⟨0, by simp [h]⟩
    · exact ⟨b, by simp [h]⟩
  · intro a b d hda hdb
    change ∃ c, (if a = 0 ∧ b = 0 then 0 else 1) = d * c
    by_cases hab : a = 0 ∧ b = 0
    · exact ⟨0, by simp [hab]⟩
    · have hd : d ≠ 0 := by
        intro hd
        rcases hda with ⟨ca, ha⟩
        rcases hdb with ⟨cb, hb⟩
        apply hab
        simp [hd] at ha hb
        exact ⟨ha, hb⟩
      exact ⟨d⁻¹, by
        rw [ite_eq_right hab]
        have hdinv : d * d⁻¹ = 1 := by
          change d * ZMod64.inv d = 1
          exact ZMod64.mul_inv_eq_one_of_ne_zero hd
        exact hdinv.symm⟩
  · intro a b
    change
      (if a = 0 ∧ b = 0 then 0 else 1) *
          (if (if a = 0 ∧ b = 0 then 0 else 1) = 0 then 1
            else (if a = 0 ∧ b = 0 then 0 else 1)⁻¹) =
        (if a = 0 ∧ b = 0 then 0 else 1)
    by_cases h : a = 0 ∧ b = 0
    · simp [h]
    · simp only [h, ite_false]
      change (1 : ZMod64 p) * (if (1 : ZMod64 p) = 0 then 1 else 1⁻¹) = 1
      have hone : (1 : ZMod64 p) ≠ 0 := fun h =>
        ZMod64.one_ne_zero_of_prime (ZMod64.PrimeModulus.prime (p := p)) h
      rw [ite_eq_right hone]
      change (1 : ZMod64 p) * ZMod64.inv 1 = 1
      exact ZMod64.mul_inv_eq_one_of_ne_zero hone
  · intro a b hb
    change a * b * b⁻¹ = a
    have hbinv : b * b⁻¹ = 1 := by
      change b * ZMod64.inv b = 1
      exact ZMod64.mul_inv_eq_one_of_ne_zero hb
    rw [Lean.Grind.Semiring.mul_assoc, hbinv,
      Lean.Grind.Semiring.mul_one]
  · intro a
    change decide (a ≠ 0) = true ↔ ∃ b, a * b = 1
    rw [decide_eq_true_eq]
    constructor
    · intro ha
      refine ⟨a⁻¹, ?_⟩
      change a * ZMod64.inv a = 1
      exact ZMod64.mul_inv_eq_one_of_ne_zero ha
    · rintro ⟨b, hab⟩ ha
      subst a
      rw [Lean.Grind.Semiring.zero_mul] at hab
      exact ZMod64.one_ne_zero_of_prime
        (ZMod64.PrimeModulus.prime (p := p)) hab.symm
  · intro a
    change ∃ b, (if a = 0 then 1 else a⁻¹) * b = 1
    by_cases ha : a = 0
    · exact ⟨1, by simp [ha]⟩
    · exact ⟨a, by
        rw [ite_eq_right ha]
        change ZMod64.inv a * a = 1
        exact ZMod64.inv_mul_eq_one_of_ne_zero ha⟩
  · intro a b
    change
      a * b * (if a * b = 0 then 1 else (a * b)⁻¹) =
        (a * (if a = 0 then 1 else a⁻¹)) *
          (b * (if b = 0 then 1 else b⁻¹))
    by_cases ha : a = 0
    · simp [ha]
    · by_cases hb : b = 0
      · simp [hb]
      · have hab : a * b ≠ 0 := by
          intro h
          rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero_of_prime_modulus h with
            h | h
          · exact ha h
          · exact hb h
        have habInv : a * b * (a * b)⁻¹ = 1 := by
          change a * b * ZMod64.inv (a * b) = 1
          exact ZMod64.mul_inv_eq_one_of_ne_zero hab
        have haInv : a * a⁻¹ = 1 := by
          change a * ZMod64.inv a = 1
          exact ZMod64.mul_inv_eq_one_of_ne_zero ha
        have hbInv : b * b⁻¹ = 1 := by
          change b * ZMod64.inv b = 1
          exact ZMod64.mul_inv_eq_one_of_ne_zero hb
        rw [ite_eq_right ha, ite_eq_right hb,
          ite_eq_right hab, habInv, haInv, hbInv]
        exact (Lean.Grind.Semiring.one_mul 1).symm
  · intro a
    change
      (a * (if a = 0 then 1 else a⁻¹)) *
          (if a * (if a = 0 then 1 else a⁻¹) = 0 then 1
            else (a * (if a = 0 then 1 else a⁻¹))⁻¹) =
        a * (if a = 0 then 1 else a⁻¹)
    by_cases ha : a = 0
    · simp [ha]
    · have haInv : a * a⁻¹ = 1 := by
        change a * ZMod64.inv a = 1
        exact ZMod64.mul_inv_eq_one_of_ne_zero ha
      rw [ite_eq_right ha, haInv]
      have hone : (1 : ZMod64 p) ≠ 0 := fun h =>
        ZMod64.one_ne_zero_of_prime (ZMod64.PrimeModulus.prime (p := p)) h
      have honeInv : (1 : ZMod64 p) * (1 : ZMod64 p)⁻¹ = 1 := by
        change (1 : ZMod64 p) * ZMod64.inv 1 = 1
        exact ZMod64.mul_inv_eq_one_of_ne_zero hone
      rw [ite_eq_right hone, honeInv]
  · intro a ha
    change decide (a ≠ 0) = true at ha
    have hne : a ≠ 0 := by simpa only [decide_eq_true_eq] using ha
    change a * (if a = 0 then 1 else a⁻¹) = 1
    rw [ite_eq_right hne]
    change a * ZMod64.inv a = 1
    exact ZMod64.mul_inv_eq_one_of_ne_zero hne

instance instLawfulBezoutOpsZMod64 {p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] :
    @LawfulBezoutOps (@ZMod64 p hp) _ _ _ _ instDvdZMod64 instBezoutOpsZMod64
      instLawfulGcdOpsZMod64 := by
  constructor
  intro a b
  change
    let uv := ZMod64.fieldXgcd a b
    uv.1 * a + uv.2 * b =
      (if a = 0 ∧ b = 0 then 0 else 1) *
        (if (if a = 0 ∧ b = 0 then 0 else 1) = 0 then 1
          else (if a = 0 ∧ b = 0 then 0 else 1)⁻¹)
  have one_ne : (1 : ZMod64 p) ≠ 0 := fun h =>
    ZMod64.one_ne_zero_of_prime (ZMod64.PrimeModulus.prime (p := p)) h
  have inv_one : (1 : ZMod64 p)⁻¹ = 1 := by
    have h : (1 : ZMod64 p) * (1 : ZMod64 p)⁻¹ = 1 := by
      change (1 : ZMod64 p) * ZMod64.inv 1 = 1
      exact ZMod64.mul_inv_eq_one_of_ne_zero one_ne
    rw [Lean.Grind.Semiring.one_mul] at h
    exact h
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · simp [ZMod64.fieldXgcd, ha, hb]
    · have hbinv : b⁻¹ * b = 1 := by
        change ZMod64.inv b * b = 1
        exact ZMod64.inv_mul_eq_one_of_ne_zero hb
      simp [ZMod64.fieldXgcd, ha, hb, hbinv, inv_one]
  · have hainv : a⁻¹ * a = 1 := by
      change ZMod64.inv a * a = 1
      exact ZMod64.inv_mul_eq_one_of_ne_zero ha
    simp [ZMod64.fieldXgcd, ha, hainv, inv_one]

/-! # Univariate prime-field polynomials -/

namespace FpPoly

variable {p : Nat} [hp : ZMod64.Bounds p] [ZMod64.PrimeModulus p]

/-- Unit which makes the leading coefficient one, with `1` at zero. -/
@[reducible] def normUnit (f : @FpPoly p hp) : @FpPoly p hp :=
  if f = 0 then 1 else DensePoly.C f.leadingCoeff⁻¹

/-- The Euclidean gcd made monic by its leading coefficient. -/
@[reducible] def normalizedGcd (f g : @FpPoly p hp) : @FpPoly p hp :=
  let d := DensePoly.gcd f g
  d * normUnit d

/-- Extended-gcd coefficients scaled by the same unit as the gcd. -/
def normalizedXgcd (f g : @FpPoly p hp) : @FpPoly p hp × @FpPoly p hp :=
  let r := DensePoly.xgcd f g
  let u := normUnit r.gcd
  (r.left * u, r.right * u)

private theorem coeffOne_ne_zero :
    (1 : ZMod64 p) ≠ 0 := fun h =>
  ZMod64.one_ne_zero_of_prime (ZMod64.PrimeModulus.prime (p := p)) h

private theorem one_ne_zero : (1 : FpPoly p) ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) h
  change (DensePoly.C (1 : ZMod64 p)).coeff 0 =
    (0 : FpPoly p).coeff 0 at hcoeff
  rw [DensePoly.coeff_C, DensePoly.coeff_zero] at hcoeff
  exact coeffOne_ne_zero hcoeff

private theorem inv_ne_zero {c : ZMod64 p} (hc : c ≠ 0) : c⁻¹ ≠ 0 := by
  intro hinv
  change ZMod64.inv c = 0 at hinv
  have hone := ZMod64.inv_mul_eq_one_of_ne_zero hc
  rw [hinv, Lean.Grind.Semiring.zero_mul] at hone
  exact coeffOne_ne_zero hone.symm

omit [ZMod64.PrimeModulus p] in
private theorem C_mul_C_eq (a b : ZMod64 p) :
    (DensePoly.C a * DensePoly.C b : FpPoly p) = DensePoly.C (a * b) := by
  rw [C_mul_eq_scale]
  apply DensePoly.ext_coeff
  intro n
  have hzero : a * (0 : ZMod64 p) = 0 := Lean.Grind.Semiring.mul_zero a
  rw [DensePoly.coeff_scale _ _ _ hzero, DensePoly.coeff_C,
    DensePoly.coeff_C]
  cases n <;> rfl

omit [ZMod64.PrimeModulus p] in
private theorem scale_mul_scale (a b : ZMod64 p) (f g : FpPoly p) :
    DensePoly.scale a f * DensePoly.scale b g =
      DensePoly.scale (a * b) (f * g) := by
  rw [← C_mul_eq_scale, ← C_mul_eq_scale, ← C_mul_eq_scale,
    ← C_mul_C_eq]
  calc
    (DensePoly.C a * f) * (DensePoly.C b * g) =
        ((DensePoly.C a * f) * DensePoly.C b) * g :=
      (DensePoly.mul_assoc_poly _ _ _).symm
    _ = (DensePoly.C a * (f * DensePoly.C b)) * g := by
      exact congrArg (fun x : FpPoly p => x * g)
        (DensePoly.mul_assoc_poly _ _ _)
    _ = (DensePoly.C a * (DensePoly.C b * f)) * g := by
      exact congrArg (fun x : FpPoly p => x * g)
        (congrArg (fun x : FpPoly p => DensePoly.C a * x)
          (DensePoly.mul_comm_poly f (DensePoly.C b)))
    _ = ((DensePoly.C a * DensePoly.C b) * f) * g := by
      exact congrArg (fun x : FpPoly p => x * g)
        (DensePoly.mul_assoc_poly _ _ _).symm
    _ = (DensePoly.C a * DensePoly.C b) * (f * g) :=
      DensePoly.mul_assoc_poly _ _ _

omit [ZMod64.PrimeModulus p] in
private theorem eq_C_of_size_one {f : FpPoly p} (hsize : f.size = 1) :
    f = DensePoly.C (f.coeff 0) := by
  apply DensePoly.ext_coeff
  intro n
  cases n with
  | zero =>
      rw [DensePoly.coeff_C]
      simp
  | succ n =>
      rw [DensePoly.coeff_eq_zero_of_size_le f (by omega),
        DensePoly.coeff_C]
      simp

omit [ZMod64.PrimeModulus p] in
private theorem coeff_zero_ne_zero_of_size_one {f : FpPoly p}
    (hsize : f.size = 1) : f.coeff 0 ≠ 0 := by
  have hlast := DensePoly.coeff_last_ne_zero_of_pos_size f (by omega)
  rwa [hsize] at hlast

omit [ZMod64.PrimeModulus p] in
private theorem canonical_eq_scale {f : FpPoly p} (hf : f ≠ 0) :
    f * normUnit f = DensePoly.scale f.leadingCoeff⁻¹ f := by
  rw [normUnit, ite_eq_right hf]
  calc
    f * DensePoly.C f.leadingCoeff⁻¹ =
        DensePoly.C f.leadingCoeff⁻¹ * f :=
      DensePoly.mul_comm_poly _ _
    _ = DensePoly.scale f.leadingCoeff⁻¹ f :=
      C_mul_eq_scale _ _

private theorem canonical_monic {f : FpPoly p} (hf : f ≠ 0) :
    DensePoly.Monic (f * normUnit f) := by
  rw [canonical_eq_scale hf]
  have hsize : f.size ≠ 0 := Nat.ne_of_gt (size_pos_of_ne_zero hf)
  have hlead : f.leadingCoeff ≠ 0 :=
    DensePoly.leadingCoeff_ne_zero_of_pos_size f (Nat.pos_of_ne_zero hsize)
  unfold DensePoly.Monic
  rw [leadingCoeff_scale_of_ne_zero_of_nonzero (inv_ne_zero hlead) f hsize]
  exact ZMod64.inv_mul_eq_one_of_ne_zero hlead

private theorem canonical_fixed_of_monic {f : FpPoly p}
    (hf : DensePoly.Monic f) : f * normUnit f = f := by
  have hf0 : f ≠ 0 := by
    intro hzero
    subst f
    exact coeffOne_ne_zero hf.symm
  have hinvOne : ZMod64.inv (1 : ZMod64 p) = 1 := by
    have h := ZMod64.inv_mul_eq_one_of_ne_zero (p := p) coeffOne_ne_zero
    rw [Lean.Grind.Semiring.mul_one] at h
    exact h
  rw [canonical_eq_scale hf0, hf]
  change DensePoly.scale (ZMod64.inv (1 : ZMod64 p)) f = f
  rw [hinvOne, scale_one_left]

private theorem canonical_idem (f : FpPoly p) :
    (f * normUnit f) * normUnit (f * normUnit f) = f * normUnit f := by
  by_cases hf : f = 0
  · subst f
    simp [normUnit]
  · exact canonical_fixed_of_monic (canonical_monic hf)

private theorem canonical_mul (f g : FpPoly p) :
    f * g * normUnit (f * g) =
      (f * normUnit f) * (g * normUnit g) := by
  by_cases hf : f = 0
  · subst f
    simp [normUnit]
  · by_cases hg : g = 0
    · subst g
      simp [normUnit]
    · have hfg : f * g ≠ 0 := mul_ne_zero_of_ne_zero hf hg
      rw [canonical_eq_scale hfg, canonical_eq_scale hf,
        canonical_eq_scale hg, leadingCoeff_mul f g hf hg,
        Lean.Grind.Field.inv_mul]
      exact (scale_mul_scale _ _ f g).symm

private theorem canonical_eq_one_of_size_one {f : FpPoly p}
    (hsize : f.size = 1) : f * normUnit f = 1 := by
  have hf : f ≠ 0 := by
    intro hzero
    rw [hzero] at hsize
    contradiction
  have hc : f.coeff 0 ≠ 0 := coeff_zero_ne_zero_of_size_one hsize
  have hcancel : (f.coeff 0)⁻¹ * f.coeff 0 = 1 := by
    change ZMod64.inv (f.coeff 0) * f.coeff 0 = 1
    exact ZMod64.inv_mul_eq_one_of_ne_zero hc
  rw [canonical_eq_scale hf, eq_C_of_size_one hsize,
    DensePoly.leadingCoeff_C, ← C_mul_eq_scale, C_mul_C_eq, hcancel]
  rfl

private theorem normUnit_is_unit (f : FpPoly p) :
    ∃ g, normUnit f * g = 1 := by
  by_cases hf : f = 0
  · exact ⟨1, by simp [normUnit, hf]⟩
  · have hlead : f.leadingCoeff ≠ 0 :=
      DensePoly.leadingCoeff_ne_zero_of_pos_size f (size_pos_of_ne_zero hf)
    have hcancel : f.leadingCoeff⁻¹ * f.leadingCoeff = 1 := by
      change ZMod64.inv f.leadingCoeff * f.leadingCoeff = 1
      exact ZMod64.inv_mul_eq_one_of_ne_zero hlead
    refine ⟨DensePoly.C f.leadingCoeff, ?_⟩
    rw [normUnit, ite_eq_right hf, C_mul_C_eq, hcancel]
    rfl

private theorem canonical_dvd_self (f : FpPoly p) :
    f * normUnit f ∣ f := by
  by_cases hf : f = 0
  · subst f
    exact ⟨0, by simp [normUnit]⟩
  · have hlead : f.leadingCoeff ≠ 0 :=
      DensePoly.leadingCoeff_ne_zero_of_pos_size f (size_pos_of_ne_zero hf)
    have hcancel : f.leadingCoeff⁻¹ * f.leadingCoeff = 1 := by
      change ZMod64.inv f.leadingCoeff * f.leadingCoeff = 1
      exact ZMod64.inv_mul_eq_one_of_ne_zero hlead
    refine ⟨DensePoly.C f.leadingCoeff, ?_⟩
    symm
    calc
      (f * normUnit f) * DensePoly.C f.leadingCoeff =
          (f * DensePoly.C f.leadingCoeff⁻¹) *
            DensePoly.C f.leadingCoeff := by
              rw [normUnit, ite_eq_right hf]
      _ = f * (DensePoly.C f.leadingCoeff⁻¹ *
            DensePoly.C f.leadingCoeff) :=
          DensePoly.mul_assoc_poly _ _ _
      _ = f * DensePoly.C (f.leadingCoeff⁻¹ * f.leadingCoeff) := by
          rw [C_mul_C_eq]
      _ = f * DensePoly.C (1 : ZMod64 p) := by rw [hcancel]
      _ = f := DensePoly.mul_one_right_poly f

omit [ZMod64.PrimeModulus p] in
private theorem self_dvd_canonical (f : FpPoly p) :
    f ∣ f * normUnit f := ⟨normUnit f, rfl⟩

omit [ZMod64.PrimeModulus p] in
private theorem dvd_trans {a b c : FpPoly p} (hab : a ∣ b) (hbc : b ∣ c) :
    a ∣ c := by
  rcases hab with ⟨x, hx⟩
  rcases hbc with ⟨y, hy⟩
  exact ⟨x * y, hy.trans (hx ▸ DensePoly.mul_assoc_poly a x y)⟩

private theorem size_one_of_mul_eq_one {a b : FpPoly p}
    (h : a * b = 1) : a.size = 1 ∧ b.size = 1 := by
  have ha : a ≠ 0 := by
    intro ha
    exact one_ne_zero (by rw [← h, ha, FpPoly.zero_mul])
  have hb : b ≠ 0 := by
    intro hb
    exact one_ne_zero (by rw [← h, hb, FpPoly.mul_zero])
  have hsize := size_mul_eq_add_sub_one a b ha hb
  have hone : (1 : FpPoly p).size = 1 :=
    DensePoly.size_one coeffOne_ne_zero
  rw [h, hone] at hsize
  have hapos := size_pos_of_ne_zero ha
  have hbpos := size_pos_of_ne_zero hb
  omega

end FpPoly

/-- Canonical dense-polynomial ring instance exposed for `FpPoly`. -/
instance instCommRingFpPoly {p : Nat} [hp : ZMod64.Bounds p] :
    Lean.Grind.CommRing (@FpPoly p hp) :=
  Hex.instGrindCommRingDensePoly

@[reducible] instance instGcdOpsFpPoly {p : Nat} [hp : ZMod64.Bounds p] :
    GcdOps (@FpPoly p hp) where
  gcd := FpPoly.normalizedGcd
  exactDiv f g := f / g
  isUnit f := decide (f.size = 1)
  normUnit := FpPoly.normUnit

instance instBezoutOpsFpPoly {p : Nat} [hp : ZMod64.Bounds p] :
    BezoutOps (@FpPoly p hp) where
  gcd := GcdOps.gcd
  exactDiv := GcdOps.exactDiv
  isUnit := GcdOps.isUnit
  normUnit := GcdOps.normUnit
  xgcd := FpPoly.normalizedXgcd

instance instLawfulGcdOpsFpPoly {p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] :
    @LawfulGcdOps (@FpPoly p hp) instCommRingFpPoly _ _ _ _ instGcdOpsFpPoly := by
  constructor
  · intro a b
    rfl
  · exact FpPoly.one_ne_zero
  · intro a b h
    by_cases ha : a = 0
    · exact Or.inl ha
    · by_cases hb : b = 0
      · exact Or.inr hb
      · exact False.elim (FpPoly.mul_ne_zero_of_ne_zero ha hb h)
  · intro a b
    exact FpPoly.dvd_trans
      (FpPoly.canonical_dvd_self (DensePoly.gcd a b))
      (DensePoly.gcd_dvd_left a b)
  · intro a b
    exact FpPoly.dvd_trans
      (FpPoly.canonical_dvd_self (DensePoly.gcd a b))
      (DensePoly.gcd_dvd_right a b)
  · intro a b d hda hdb
    exact FpPoly.dvd_trans (DensePoly.dvd_gcd d a b hda hdb)
      (FpPoly.self_dvd_canonical (DensePoly.gcd a b))
  · intro a b
    exact FpPoly.canonical_idem (DensePoly.gcd a b)
  · intro a b hb
    letI : ExactDivLaws (FpPoly p) :=
      instExactDivLawsDensePoly (R := ZMod64 p)
    exact ExactDivLaws.mul_div_cancel_right a b hb
  · intro a
    change decide (a.size = 1) = true ↔ ∃ b, a * b = 1
    rw [decide_eq_true_eq]
    constructor
    · intro ha
      refine ⟨FpPoly.normUnit a, ?_⟩
      exact FpPoly.canonical_eq_one_of_size_one ha
    · rintro ⟨b, hab⟩
      exact (FpPoly.size_one_of_mul_eq_one hab).1
  · exact FpPoly.normUnit_is_unit
  · exact FpPoly.canonical_mul
  · exact FpPoly.canonical_idem
  · intro a ha
    change decide (a.size = 1) = true at ha
    rw [decide_eq_true_eq] at ha
    exact FpPoly.canonical_eq_one_of_size_one ha

instance instLawfulBezoutOpsFpPoly {p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] :
    @LawfulBezoutOps (@FpPoly p hp) instCommRingFpPoly _ _ _ _ instBezoutOpsFpPoly
      instLawfulGcdOpsFpPoly := by
  constructor
  intro f g
  change
    let r := DensePoly.xgcd f g
    let u := FpPoly.normUnit r.gcd
    (r.left * u) * f + (r.right * u) * g =
      FpPoly.normalizedGcd f g *
        FpPoly.normUnit (FpPoly.normalizedGcd f g)
  dsimp only
  have hfixed :
      FpPoly.normalizedGcd f g *
          FpPoly.normUnit (FpPoly.normalizedGcd f g) =
        FpPoly.normalizedGcd f g :=
    FpPoly.canonical_idem (DensePoly.gcd f g)
  rw [hfixed]
  change
    ((DensePoly.xgcd f g).left *
          FpPoly.normUnit (DensePoly.xgcd f g).gcd) * f +
        ((DensePoly.xgcd f g).right *
          FpPoly.normUnit (DensePoly.xgcd f g).gcd) * g =
      DensePoly.gcd f g * FpPoly.normUnit (DensePoly.gcd f g)
  let r := DensePoly.xgcd f g
  let u := FpPoly.normUnit r.gcd
  have hbez : r.left * f + r.right * g = r.gcd := by
    dsimp [r]
    exact DensePoly.xgcd_bezout f g
  have hleft : (r.left * u) * f = (r.left * f) * u := by
    calc
      (r.left * u) * f = r.left * (u * f) :=
        DensePoly.mul_assoc_poly _ _ _
      _ = r.left * (f * u) := by
        exact congrArg (fun x : FpPoly p => r.left * x)
          (DensePoly.mul_comm_poly u f)
      _ = (r.left * f) * u :=
        (DensePoly.mul_assoc_poly _ _ _).symm
  have hright : (r.right * u) * g = (r.right * g) * u := by
    calc
      (r.right * u) * g = r.right * (u * g) :=
        DensePoly.mul_assoc_poly _ _ _
      _ = r.right * (g * u) := by
        exact congrArg (fun x : FpPoly p => r.right * x)
          (DensePoly.mul_comm_poly u g)
      _ = (r.right * g) * u :=
        (DensePoly.mul_assoc_poly _ _ _).symm
  change (r.left * u) * f + (r.right * u) * g = _
  calc
    (r.left * u) * f + (r.right * u) * g =
        (r.left * f) * u + (r.right * g) * u := by
      rw [hleft, hright]
    _ = (r.left * f + r.right * g) * u :=
      (DensePoly.mul_add_left_poly _ _ _).symm
    _ = r.gcd * u := by rw [hbez]
    _ = DensePoly.gcd f g * FpPoly.normUnit (DensePoly.gcd f g) := by
      dsimp [r, u]
      rw [DensePoly.xgcd_gcd_eq_gcd]

/-! Instance-graph checks for every base coefficient family. -/

example : GcdOps Int := inferInstance
example : BezoutOps Int := inferInstance
example : LawfulGcdOps Int := inferInstance
example : GcdOps Rat := inferInstance
example : BezoutOps Rat := inferInstance
example : LawfulGcdOps Rat := inferInstance

example {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    GcdOps (ZMod64 p) := inferInstance
example {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    GcdOps (FpPoly p) := inferInstance
example {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    LawfulGcdOps (ZMod64 p) := inferInstance
example {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    LawfulBezoutOps (ZMod64 p) := inferInstance
example {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    LawfulGcdOps (FpPoly p) := inferInstance
example {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    LawfulBezoutOps (FpPoly p) := inferInstance

end Hex
