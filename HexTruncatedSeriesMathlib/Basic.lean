/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeries
public import Mathlib.Algebra.Ring.GrindInstances
public import Mathlib.Algebra.Ring.MinimalAxioms
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.PowerSeries.Trunc

public section

/-!
The quotient interpretation of fixed-precision truncated series.

This companion installs Mathlib's `CommRing` structure using the executable
operations from `HexTruncatedSeries`, constructs coefficient truncation as a
surjective ring homomorphism from `PowerSeries R`, computes its kernel as
`(X^n)`, and packages the resulting quotient equivalence.  It also derives the
precision-indexed natural inverses available in every rational algebra.
-/

namespace HexTruncatedSeriesMathlib

open Hex

universe u

variable {R : Type u} {n : Nat}

/-- The core natural cast obeys Mathlib's successor law. -/
theorem natCast_succ [CommRing R] (k : Nat) :
    (Nat.cast (k + 1) : TSeries R n) = Nat.cast k + 1 := by
  rw [← Hex.TSeries.ofNat_eq_natCast, ← Hex.TSeries.ofNat_eq_natCast]
  exact Hex.TSeries.ofNat_succ k

/-- The core natural scalar action obeys Mathlib's zero law. -/
theorem nsmul_zero [CommRing R] (a : TSeries R n) :
    (0 : Nat) • a = 0 := by
  change (Nat.cast 0 : TSeries R n) * a = 0
  rw [show (Nat.cast 0 : TSeries R n) = 0 by rfl, Hex.TSeries.zero_mul]

/-- The core natural scalar action obeys Mathlib's successor law. -/
theorem nsmul_succ [CommRing R] (k : Nat) (a : TSeries R n) :
    (k + 1) • a = k • a + a := by
  change (Nat.cast (k + 1) : TSeries R n) * a =
    Nat.cast k * a + a
  rw [natCast_succ, Hex.TSeries.right_distrib, Hex.TSeries.one_mul]

/-- Mathlib's commutative-ring structure on truncated series, pinned to the
executable operations from the Mathlib-free core. -/
instance commRing [CommRing R] : CommRing (TSeries R n) :=
  { CommRing.ofMinimalAxioms
      (R := TSeries R n)
      Hex.TSeries.add_assoc
      (fun a => (Hex.TSeries.add_comm 0 a).trans (Hex.TSeries.add_zero a))
      Hex.TSeries.neg_add_cancel
      Hex.TSeries.mul_assoc
      Hex.TSeries.mul_comm
      Hex.TSeries.one_mul
      Hex.TSeries.left_distrib with
    npow := fun k a => Hex.TSeries.pow a k
    npow_zero := fun a => Hex.TSeries.pow_zero' a
    npow_succ := fun k a => Hex.TSeries.pow_succ' a k
    natCast := (Hex.TSeries.instNatCast (R := R) (n := n)).natCast
    natCast_zero := by rfl
    natCast_succ := HexTruncatedSeriesMathlib.natCast_succ
    nsmul := (Hex.TSeries.instNSMul (R := R) (n := n)).smul
    nsmul_zero := HexTruncatedSeriesMathlib.nsmul_zero
    nsmul_succ := HexTruncatedSeriesMathlib.nsmul_succ
    intCast := (Hex.TSeries.instIntCast (R := R) (n := n)).intCast
    intCast_ofNat := by intro k; rfl
    intCast_negSucc := by intro k; rfl
    zsmul := (Hex.TSeries.instZSMul (R := R) (n := n)).smul
    zsmul_zero' := HexTruncatedSeriesMathlib.nsmul_zero
    zsmul_succ' := HexTruncatedSeriesMathlib.nsmul_succ
    zsmul_neg' := by intro k a; rfl
    sub := fun a b => Hex.TSeries.sub a b
    neg := fun a => Hex.TSeries.neg a
    sub_eq_add_neg := Hex.TSeries.sub_eq_add_neg }

/-- Truncate a Mathlib power series to the first `n` coefficients. -/
@[expose]
noncomputable def ofPowerSeries [CommRing R] (f : PowerSeries R) : TSeries R n :=
  Hex.TSeries.ofFn fun i => PowerSeries.coeff i f

/-- Coefficients of a truncated Mathlib power series agree below the
precision. -/
@[simp]
theorem coeff_ofPowerSeries [CommRing R] (f : PowerSeries R)
    (i : Nat) (hi : i < n) :
    (ofPowerSeries (n := n) f).coeff i = PowerSeries.coeff i f :=
  Hex.TSeries.coeff_ofFn _ i hi

/-- Truncation from power series is a ring homomorphism. -/
@[expose]
noncomputable def ofPowerSeriesHom [CommRing R] : PowerSeries R →+* TSeries R n where
  toFun := ofPowerSeries
  map_one' := by
    apply Hex.TSeries.ext
    intro i hi
    rw [coeff_ofPowerSeries _ i hi, Hex.TSeries.coeff_one i hi,
      PowerSeries.coeff_one]
  map_mul' := by
    intro f g
    apply Hex.TSeries.ext
    intro i hi
    rw [coeff_ofPowerSeries _ i hi, Hex.TSeries.coeff_mul _ _ i hi,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun j k => PowerSeries.coeff j f * PowerSeries.coeff k g) i]
    symm
    unfold Hex.TSeries.convCoeff
    calc
      (List.range (i + 1)).foldl
          (fun acc j => acc + (ofPowerSeries f).coeff j *
            (ofPowerSeries g).coeff (i - j)) 0 =
        (List.range (i + 1)).foldl
          (fun acc j => acc + PowerSeries.coeff j f *
            PowerSeries.coeff (i - j) g) 0 := by
          apply List.foldl_add_congr
          intro j hj
          rw [coeff_ofPowerSeries f j (by
            have := List.mem_range.mp hj
            omega), coeff_ofPowerSeries g (i - j) (by
            have := List.mem_range.mp hj
            omega)]
      _ = ∑ j ∈ Finset.range (i + 1),
          PowerSeries.coeff j f * PowerSeries.coeff (i - j) g := by
        let term := fun j => PowerSeries.coeff j f * PowerSeries.coeff (i - j) g
        calc
          (List.range (i + 1)).foldl (fun acc j => acc + term j) 0 =
              ((List.range (i + 1)).map term).sum := by
                rw [List.sum_eq_foldl, List.foldl_map]
          _ = ∑ j ∈ (List.range (i + 1)).toFinset, term j :=
            (List.sum_toFinset _ List.nodup_range).symm
          _ = ∑ j ∈ Finset.range (i + 1), term j := by
            congr 1
            ext j
            simp only [List.mem_toFinset, List.mem_range, Finset.mem_range]
  map_zero' := by
    apply Hex.TSeries.ext
    intro i hi
    rw [coeff_ofPowerSeries _ i hi, Hex.TSeries.coeff_zero]
    simp
  map_add' := by
    intro f g
    apply Hex.TSeries.ext
    intro i hi
    rw [coeff_ofPowerSeries _ i hi, Hex.TSeries.coeff_add _ _ i hi,
      coeff_ofPowerSeries f i hi, coeff_ofPowerSeries g i hi,
      map_add]

@[simp]
theorem ofPowerSeriesHom_apply [CommRing R] (f : PowerSeries R) :
    ofPowerSeriesHom (R := R) (n := n) f = ofPowerSeries f :=
  rfl

/-- Every truncated series is represented by a Mathlib power series. -/
theorem ofPowerSeriesHom_surjective [CommRing R] :
    Function.Surjective (ofPowerSeriesHom (R := R) (n := n)) := by
  intro a
  refine ⟨PowerSeries.mk a.coeff, ?_⟩
  change ofPowerSeries (PowerSeries.mk a.coeff) = a
  apply Hex.TSeries.ext
  intro i hi
  rw [coeff_ofPowerSeries _ i hi, PowerSeries.coeff_mk]

/-- The kernel of coefficient truncation is the principal ideal `(X^n)`. -/
theorem ker_ofPowerSeriesHom [CommRing R] :
    RingHom.ker (ofPowerSeriesHom (R := R) (n := n)) =
      Ideal.span {(PowerSeries.X : PowerSeries R) ^ n} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hf
    have hcoeff : ∀ i, i < n → PowerSeries.coeff i f = 0 := by
      intro i hi
      have h := congrArg (fun a : TSeries R n => a.coeff i) hf
      change (ofPowerSeries f).coeff i = (0 : TSeries R n).coeff i at h
      simpa [coeff_ofPowerSeries f i hi, Hex.TSeries.coeff_zero] using h
    have htrunc : PowerSeries.trunc n f = 0 := by
      ext i
      rw [PowerSeries.coeff_trunc]
      split
      · exact hcoeff i (by omega)
      · rfl
    refine ⟨PowerSeries.mk (fun i => PowerSeries.coeff (i + n) f), ?_⟩
    have hsplit := PowerSeries.eq_X_pow_mul_shift_add_trunc n f
    rw [htrunc] at hsplit
    simpa using hsplit
  · rintro ⟨q, hq⟩
    apply Hex.TSeries.ext
    intro i hi
    change (ofPowerSeries f).coeff i = (0 : TSeries R n).coeff i
    rw [hq, coeff_ofPowerSeries _ i hi, Hex.TSeries.coeff_zero,
      PowerSeries.coeff_X_pow_mul']
    simp [show ¬n ≤ i by omega]

/-- Fixed-precision series are power series modulo `X^n`. -/
noncomputable def quotEquiv [CommRing R] :
    (PowerSeries R ⧸ Ideal.span {(PowerSeries.X : PowerSeries R) ^ n}) ≃+*
      TSeries R n :=
  (Ideal.quotEquivOfEq
      (ker_ofPowerSeriesHom (R := R) (n := n)).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (ofPowerSeriesHom_surjective (R := R) (n := n)))

/-- The quotient equivalence sends a power-series representative to its
coefficient truncation. -/
@[simp]
theorem quotEquiv_mk [CommRing R] (f : PowerSeries R) :
    quotEquiv (R := R) (n := n) (Ideal.Quotient.mk _ f) =
      ofPowerSeries (n := n) f := by
  rfl

/-- A rational algebra contains every natural inverse required by the
Mathlib-free algorithms. -/
instance (priority := 800) natInversesOfAlgebra [CommRing R] [Algebra ℚ R]
    (m : Nat) : Hex.TSeries.NatInverses R m where
  invNat k := if k = 0 then 0 else algebraMap ℚ R ((k : ℚ)⁻¹)
  invNat_eq := by
    intro k hk _
    rw [if_neg (by omega)]
    rw [show (k : R) = algebraMap ℚ R (k : ℚ) by simp, ← map_mul,
      Rat.mul_inv_cancel _ (by simp; omega), map_one]

end HexTruncatedSeriesMathlib
