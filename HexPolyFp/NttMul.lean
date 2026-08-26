/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Ntt.Convolution
public import HexPolyFast.Karatsuba
public import HexPolyFp.Degree

public section

/-!
# Direct NTT multiplication over `F_p`

This file adapts a reusable target-modulus `NttPlan` to normalized
`FpPoly` values.  The executable failure channel records an unsuitable
transform length; a successful result is proved equal to the existing
schoolbook polynomial multiplication.
-/

namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

@[local simp] private theorem ofNat_zero_eq_zero :
    (0 : ZMod64 p) = Zero.zero := by
  apply (ZMod64.eq_iff_toNat_eq (0 : ZMod64 p) Zero.zero).mpr
  calc
    (0 : ZMod64 p).toNat = 0 := ZMod64.toNat_zero
    _ = (Zero.zero : ZMod64 p).toNat := ZMod64.toNat_zero.symm

private theorem zmod_zero_add (value : ZMod64 p) :
    Zero.zero + value = value := by
  calc
    Zero.zero + value = value + Zero.zero :=
      Lean.Grind.Semiring.add_comm _ _
    _ = value := Lean.Grind.Semiring.add_zero value

private theorem getD_addCoeffs (left right : List (ZMod64 p)) (n : Nat) :
    (ZMod64.Ntt.addCoeffs left right).getD n Zero.zero =
      left.getD n Zero.zero + right.getD n Zero.zero := by
  induction left generalizing right n with
  | nil => exact (zmod_zero_add _).symm
  | cons value values ih =>
      cases right with
      | nil =>
          change (value :: values).getD n Zero.zero =
            (value :: values).getD n Zero.zero + Zero.zero
          exact (Lean.Grind.Semiring.add_zero _).symm
      | cons coefficient coefficients =>
          cases n with
          | zero => rfl
          | succ n => simpa [ZMod64.Ntt.addCoeffs] using ih coefficients n

private theorem getD_map_mul (value : ZMod64 p)
    (coefficients : List (ZMod64 p)) (n : Nat) :
    (coefficients.map fun coefficient => value * coefficient).getD n Zero.zero =
      value * coefficients.getD n Zero.zero := by
  induction coefficients generalizing n with
  | nil => exact (Lean.Grind.Semiring.mul_zero value).symm
  | cons coefficient coefficients ih =>
      cases n with
      | zero => rfl
      | succ n => simpa using ih n

private theorem ofList_addCoeffs (left right : List (ZMod64 p)) :
    DensePoly.ofList (ZMod64.Ntt.addCoeffs left right) =
      (DensePoly.ofList left : FpPoly p) + DensePoly.ofList right := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_add_semiring, DensePoly.coeff_ofList,
    DensePoly.coeff_ofList, DensePoly.coeff_ofList]
  exact getD_addCoeffs left right n

private theorem ofList_map_mul (value : ZMod64 p)
    (coefficients : List (ZMod64 p)) :
    DensePoly.ofList (coefficients.map fun coefficient => value * coefficient) =
      DensePoly.scale value (DensePoly.ofList coefficients : FpPoly p) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_ofList,
    DensePoly.coeff_scale value _ n (Lean.Grind.Semiring.mul_zero value),
    DensePoly.coeff_ofList]
  exact getD_map_mul value coefficients n

private theorem ofList_zero_cons (coefficients : List (ZMod64 p)) :
    DensePoly.ofList (0 :: coefficients) =
      DensePoly.shift 1 (DensePoly.ofList coefficients : FpPoly p) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_ofList, DensePoly.coeff_shift]
  cases n with
  | zero => exact ofNat_zero_eq_zero (p := p)
  | succ n => simp [DensePoly.coeff_ofList]

private theorem ofList_cons (value : ZMod64 p)
    (coefficients : List (ZMod64 p)) :
    DensePoly.ofList (value :: coefficients) =
      DensePoly.C value +
        DensePoly.shift 1 (DensePoly.ofList coefficients : FpPoly p) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_ofList, DensePoly.coeff_add_semiring,
    DensePoly.coeff_C, DensePoly.coeff_shift]
  cases n with
  | zero => exact (Lean.Grind.Semiring.add_zero value).symm
  | succ n =>
      simpa [DensePoly.coeff_ofList] using
        (zmod_zero_add (p := p) (coefficients.getD n Zero.zero)).symm

/-- The independent NTT coefficient reference normalizes to the existing
schoolbook polynomial product. -/
theorem ofList_linearConvolution (left right : List (ZMod64 p)) :
    DensePoly.ofList (ZMod64.Ntt.linearConvolution left right) =
      (DensePoly.ofList left : FpPoly p) * DensePoly.ofList right := by
  induction left with
  | nil => simp [ZMod64.Ntt.linearConvolution]
  | cons value values ih =>
      cases right with
      | nil => simp [ZMod64.Ntt.linearConvolution]
      | cons coefficient coefficients =>
          rw [ZMod64.Ntt.linearConvolution, ofList_addCoeffs,
            ofList_map_mul, ofList_zero_cons, ih]
          let right : FpPoly p := DensePoly.ofList (coefficient :: coefficients)
          calc
            DensePoly.scale value right +
                DensePoly.shift 1 (DensePoly.ofList values * right) =
              DensePoly.C value * right +
                DensePoly.shift 1 (DensePoly.ofList values) * right := by
                  rw [FpPoly.C_mul_eq_scale]
                  exact congrArg (fun tail : FpPoly p =>
                    DensePoly.scale value right + tail)
                    (DensePoly.shift_mul 1
                      (DensePoly.ofList values : FpPoly p) right).symm
            _ = (DensePoly.C value +
                DensePoly.shift 1 (DensePoly.ofList values)) * right :=
              (DensePoly.mul_add_left_poly _ _ _).symm
            _ = DensePoly.ofList (value :: values) * right := by
              rw [ofList_cons]

private theorem getD_replicate_zero (count i : Nat) :
    (List.replicate count (Zero.zero : ZMod64 p)).getD i Zero.zero =
      Zero.zero := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      cases i with
      | zero => rfl
      | succ i => simpa [List.replicate_succ] using ih i

private theorem ofList_padTo (n : Nat) (coefficients : List (ZMod64 p)) :
    DensePoly.ofList (ZMod64.Ntt.padTo n coefficients) =
      (DensePoly.ofList coefficients : FpPoly p) := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_ofList, DensePoly.coeff_ofList]
  unfold ZMod64.Ntt.padTo
  by_cases hi : i < coefficients.length
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left hi]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (Nat.le_of_not_gt hi)]
    rw [show coefficients[i]? = none by
      exact List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    simp only [Option.getD_none]
    exact getD_replicate_zero (n - coefficients.length) (i - coefficients.length)

/-- Multiply two finite-field polynomials with a reusable plan for the target
modulus.  `none` means that the plan length is not exactly the least
power-of-two length covering the ordinary product. -/
def mulNtt? {n : Nat} [ZMod64.PrimeModulus p]
    (plan : ZMod64.NttPlan p n) (left right : FpPoly p) : Option (FpPoly p) :=
  (ZMod64.Ntt.ordinary? plan left.toArray right.toArray).map DensePoly.ofCoeffs

/-- Every successful direct NTT multiplication equals schoolbook
multiplication.  No unchecked root or capacity hypothesis is exposed to the
caller: both are carried by the plan and checked operation. -/
theorem mulNtt?_eq {n : Nat} [ZMod64.PrimeModulus p]
    (plan : ZMod64.NttPlan p n) (left right result : FpPoly p)
    (hresult : mulNtt? plan left right = some result) :
    result = left * right := by
  unfold mulNtt? at hresult
  cases hordinary : ZMod64.Ntt.ordinary? plan left.toArray right.toArray with
  | none => simp [hordinary] at hresult
  | some coefficients =>
    rw [hordinary] at hresult
    simp only [Option.map_some, Option.some.injEq] at hresult
    subst result
    have href := ZMod64.Ntt.ordinary?_eq_of_some plan
      left.toArray right.toArray coefficients hordinary
    subst coefficients
    let convolution := ZMod64.Ntt.linearConvolution
      left.toArray.toList right.toArray.toList
    calc
      DensePoly.ofCoeffs (ZMod64.Ntt.padTo n convolution).toArray =
          DensePoly.ofList (ZMod64.Ntt.padTo n convolution) := rfl
      _ = DensePoly.ofList convolution := ofList_padTo n convolution
      _ = DensePoly.ofList left.toArray.toList *
          DensePoly.ofList right.toArray.toList :=
        ofList_linearConvolution left.toArray.toList right.toArray.toList
      _ = left * right := by
        change DensePoly.ofList left.toList * DensePoly.ofList right.toList =
          left * right
        rw [DensePoly.ofList_toList, DensePoly.ofList_toList]

end FpPoly

end Hex
