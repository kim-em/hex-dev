/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Ntt.CrtInput
public import HexModular.CrtPlan
public import HexPolyFast.Karatsuba
public import HexPolyFp.Degree
public import HexPolyFp.PackedMul

public section

/-!
# NTT multiplication over `F_p`

This file adapts a reusable target-modulus `NttPlan` to normalized
`FpPoly` values and supplies the auxiliary-prime path for arbitrary target
moduli.  Executable failure channels record unsuitable transform lengths or
fixed-catalogue exhaustion; every successful result is proved equal to the
existing schoolbook polynomial multiplication.
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

/-! # Canonical integer lifts -/

private theorem getD_intAddCoeffs (left right : List Int) (n : Nat) :
    (ZMod64.Ntt.intAddCoeffs left right).getD n 0 =
      left.getD n 0 + right.getD n 0 := by
  induction left generalizing right n with
  | nil => simp [ZMod64.Ntt.intAddCoeffs]
  | cons value values ih =>
      cases right with
      | nil => simp [ZMod64.Ntt.intAddCoeffs]
      | cons coefficient coefficients =>
          cases n with
          | zero => rfl
          | succ n => simpa [ZMod64.Ntt.intAddCoeffs] using ih coefficients n

private theorem getD_intMapMul (value : Int) (coefficients : List Int)
    (n : Nat) :
    (coefficients.map fun coefficient => value * coefficient).getD n 0 =
      value * coefficients.getD n 0 := by
  induction coefficients generalizing n with
  | nil => simp
  | cons coefficient coefficients ih =>
      cases n with
      | zero => rfl
      | succ n => simpa using ih n

private theorem ofList_intAddCoeffs (left right : List Int) :
    DensePoly.ofList (ZMod64.Ntt.intAddCoeffs left right) =
      (DensePoly.ofList left : DensePoly Int) + DensePoly.ofList right := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_add_semiring, DensePoly.coeff_ofList,
    DensePoly.coeff_ofList, DensePoly.coeff_ofList]
  exact getD_intAddCoeffs left right n

private theorem ofList_intMapMul (value : Int) (coefficients : List Int) :
    DensePoly.ofList (coefficients.map fun coefficient => value * coefficient) =
      DensePoly.scale value (DensePoly.ofList coefficients : DensePoly Int) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_ofList,
    DensePoly.coeff_scale value _ n (Int.mul_zero value),
    DensePoly.coeff_ofList]
  exact getD_intMapMul value coefficients n

private theorem ofList_intZeroCons (coefficients : List Int) :
    DensePoly.ofList (0 :: coefficients) =
      DensePoly.shift 1 (DensePoly.ofList coefficients : DensePoly Int) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_ofList, DensePoly.coeff_shift]
  cases n with
  | zero => rfl
  | succ n => simp [DensePoly.coeff_ofList]

private theorem ofList_intCons (value : Int) (coefficients : List Int) :
    DensePoly.ofList (value :: coefficients) =
      DensePoly.C value +
        DensePoly.shift 1 (DensePoly.ofList coefficients : DensePoly Int) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_ofList, DensePoly.coeff_add_semiring,
    DensePoly.coeff_C, DensePoly.coeff_shift]
  cases n with
  | zero => exact (Lean.Grind.Semiring.add_zero value).symm
  | succ n =>
      simp [DensePoly.coeff_ofList]
      exact (Lean.Grind.Semiring.add_zero _).symm.trans
        (Lean.Grind.Semiring.add_comm _ _)

private theorem intShift_mul (d : Nat) (left right : DensePoly Int) :
    DensePoly.shift d left * right = DensePoly.shift d (left * right) := by
  calc
    DensePoly.shift d left * right =
        (DensePoly.monomial d 1 * left) * right := by
      rw [DensePoly.monomial_one_mul_poly_eq_shift]
    _ = DensePoly.monomial d 1 * (left * right) :=
      DensePoly.mul_assoc_poly _ _ _
    _ = DensePoly.shift d (left * right) :=
      DensePoly.monomial_one_mul_poly_eq_shift _ _

private theorem intScale_one (value : Int) :
    DensePoly.scale value (1 : DensePoly Int) = DensePoly.C value := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale _ _ _ (Int.mul_zero value)]
  change value * (DensePoly.C (1 : Int)).coeff n =
    (DensePoly.C value).coeff n
  rw [DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => grind
  | succ n => exact Int.mul_zero value

private theorem intC_mul_eq_scale (value : Int) (polynomial : DensePoly Int) :
    DensePoly.C value * polynomial = DensePoly.scale value polynomial := by
  have hscale := DensePoly.scale_mul value
    (1 : DensePoly Int) polynomial
  have hone : (1 : DensePoly Int) * polynomial = polynomial := by
    rw [DensePoly.mul_comm_poly, DensePoly.mul_one_right_poly]
  rw [hone, intScale_one] at hscale
  exact hscale.symm

private theorem ofList_intLinearConvolution (left right : List Int) :
    DensePoly.ofList (ZMod64.Ntt.intLinearConvolution left right) =
      (DensePoly.ofList left : DensePoly Int) * DensePoly.ofList right := by
  induction left with
  | nil =>
      rw [ZMod64.Ntt.intLinearConvolution]
      exact (DensePoly.zero_mul (S := Int) (DensePoly.ofList right)).symm
  | cons value values ih =>
      cases right with
      | nil =>
          rw [ZMod64.Ntt.intLinearConvolution]
          rw [DensePoly.mul_comm_poly]
          exact (DensePoly.zero_mul (S := Int)
            (DensePoly.ofList (value :: values))).symm
      | cons coefficient coefficients =>
          rw [ZMod64.Ntt.intLinearConvolution, ofList_intAddCoeffs,
            ofList_intMapMul, ofList_intZeroCons, ih]
          let right : DensePoly Int :=
            DensePoly.ofList (coefficient :: coefficients)
          calc
            DensePoly.scale value right +
                DensePoly.shift 1 (DensePoly.ofList values * right) =
              DensePoly.C value * right +
                DensePoly.shift 1 (DensePoly.ofList values) * right := by
                  rw [intC_mul_eq_scale]
                  exact congrArg (fun tail : DensePoly Int =>
                    DensePoly.scale value right + tail)
                    (intShift_mul 1
                      (DensePoly.ofList values : DensePoly Int) right).symm
            _ = (DensePoly.C value +
                DensePoly.shift 1 (DensePoly.ofList values)) * right :=
              (DensePoly.mul_add_left_poly _ _ _).symm
            _ = DensePoly.ofList (value :: values) * right := by
              rw [ofList_intCons]

private theorem foldl_add_natAbs_le (f : Nat → Int) (bound : Nat)
    (hf : ∀ i, (f i).natAbs ≤ bound) :
    ∀ (indices : List Nat) (acc : Int),
      (indices.foldl (fun value i => value + f i) acc).natAbs ≤
        acc.natAbs + indices.length * bound := by
  intro indices
  induction indices with
  | nil => intro acc; simp
  | cons i indices ih =>
      intro acc
      have htail := ih (acc + f i)
      have hhead : (acc + f i).natAbs ≤ acc.natAbs + bound :=
        Nat.le_trans (Int.natAbs_add_le acc (f i))
          (Nat.add_le_add_left (hf i) _)
      have hlength : (indices.length + 1) * bound =
          indices.length * bound + bound := Nat.succ_mul _ _
      simp only [List.foldl_cons, List.length_cons]
      omega

private theorem natAbs_mulCoeff_le (left right : DensePoly Int)
    (leftBound rightBound : Nat)
    (hleft : ∀ i, (left.coeff i).natAbs ≤ leftBound)
    (hright : ∀ i, (right.coeff i).natAbs ≤ rightBound) (n : Nat) :
    ((left * right).coeff n).natAbs ≤
      left.size * (leftBound * rightBound) := by
  rw [DensePoly.coeff_mul, DensePoly.mulCoeffSum_eq_diagonal]
  have hterm : ∀ i,
      (DensePoly.diagonalMulCoeffTerm left right n i).natAbs ≤
        leftBound * rightBound := by
    intro i
    unfold DensePoly.diagonalMulCoeffTerm
    by_cases h : n < i
    · simp [h]
    · rw [ite_eq_right h, Int.natAbs_mul]
      exact Nat.mul_le_mul (hleft i) (hright (n - i))
  have hsum := foldl_add_natAbs_le
    (DensePoly.diagonalMulCoeffTerm left right n)
    (leftBound * rightBound) hterm (List.range left.size) 0
  simpa using hsum

private theorem natAbs_mulCoeff_le_min (left right : DensePoly Int)
    (leftBound rightBound : Nat)
    (hleft : ∀ i, (left.coeff i).natAbs ≤ leftBound)
    (hright : ∀ i, (right.coeff i).natAbs ≤ rightBound) (n : Nat) :
    ((left * right).coeff n).natAbs ≤
      min left.size right.size * (leftBound * rightBound) := by
  by_cases hsize : left.size ≤ right.size
  · rw [Nat.min_eq_left hsize]
    exact natAbs_mulCoeff_le left right leftBound rightBound
      hleft hright n
  · rw [Nat.min_eq_right (Nat.le_of_not_ge hsize),
      DensePoly.mul_comm_poly]
    simpa [Nat.mul_comm] using natAbs_mulCoeff_le right left
      rightBound leftBound hright hleft n

private def intLift (polynomial : FpPoly p) : List Int :=
  polynomial.toArray.toList.map fun coefficient => Int.ofNat coefficient.toNat

private theorem length_intLift (polynomial : FpPoly p) :
    (intLift polynomial).length = polynomial.size := by
  simp [intLift]

private theorem intLift_cast (polynomial : FpPoly p) :
    (intLift polynomial).map (fun coefficient : Int =>
        (coefficient : ZMod64 p)) = polynomial.toList := by
  unfold intLift DensePoly.toList
  generalize polynomial.toArray.toList = coefficients
  induction coefficients with
  | nil => rfl
  | cons coefficient coefficients ih =>
      simp only [List.map_cons]
      congr 1
      change ZMod64.intCast p (.ofNat coefficient.toNat) = coefficient
      rw [ZMod64.intCast_ofNat, ZMod64.natCast_eq_ofNat,
        ZMod64.ofNat_toNat]

private theorem coeff_intLift_le (polynomial : FpPoly p) (i : Nat) :
    ((DensePoly.ofList (intLift polynomial) : DensePoly Int).coeff i).natAbs ≤
      p - 1 := by
  rw [DensePoly.coeff_ofList]
  by_cases hi : i < polynomial.size
  · have hi' : i < (intLift polynomial).length := by
      simpa [length_intLift] using hi
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi', Option.getD_some]
    simp only [intLift, List.getElem_map, Int.natAbs_ofNat']
    have hlt := (polynomial.toArray.toList[i]'(by simpa using hi)).toNat_lt
    omega
  · have hi' : (intLift polynomial).length ≤ i := by
      simpa [length_intLift] using Nat.le_of_not_gt hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi']
    exact Nat.zero_le _

private theorem size_intLift_le (polynomial : FpPoly p) :
    (DensePoly.ofList (intLift polynomial) : DensePoly Int).size ≤
      polynomial.size := by
  simpa [length_intLift] using
    (DensePoly.size_ofList_le (R := Int) (intLift polynomial))

private theorem getD_intReplicateZero (count i : Nat) :
    (List.replicate count (0 : Int)).getD i 0 = 0 := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      cases i with
      | zero => rfl
      | succ i => simpa [List.replicate_succ] using ih i

private theorem ofList_intPadTo (n : Nat) (coefficients : List Int) :
    DensePoly.ofList (ZMod64.Ntt.intPadTo n coefficients) =
      (DensePoly.ofList coefficients : DensePoly Int) := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_ofList, DensePoly.coeff_ofList]
  unfold ZMod64.Ntt.intPadTo
  by_cases hi : i < coefficients.length
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left hi]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_of_not_gt hi)]
    rw [show coefficients[i]? = none by
      exact List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    simp only [Option.getD_none]
    exact getD_intReplicateZero (n - coefficients.length)
      (i - coefficients.length)

private theorem getD_intReference (n i : Nat)
    (left right : FpPoly p) :
    (ZMod64.Ntt.intPadTo n
        (ZMod64.Ntt.intLinearConvolution
          (intLift left) (intLift right))).getD i (Zero.zero : Int) =
      ((DensePoly.ofList (intLift left) : DensePoly Int) *
        DensePoly.ofList (intLift right)).coeff i := by
  have hpad := ofList_intPadTo n
    (ZMod64.Ntt.intLinearConvolution (intLift left) (intLift right))
  have hconvolution := ofList_intLinearConvolution
    (intLift left) (intLift right)
  have h := congrArg (fun polynomial : DensePoly Int => polynomial.coeff i)
    (hpad.trans hconvolution)
  simpa [DensePoly.coeff_ofList] using h

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

/-! # Auxiliary-prime multiplication -/

/-- Least radix-two transform capacity covering the ordinary product. -/
@[expose] def nttLength (left right : FpPoly p) : Nat :=
  (left.size + right.size - 1).nextPowerOfTwo

/-- Absolute bound for the integer convolution of canonical representatives. -/
@[expose] def nttCrtBound (left right : FpPoly p) : Nat :=
  min left.size right.size * ((p - 1) * (p - 1))

private theorem intPadTo_cast (n : Nat) (coefficients : List Int) :
    (ZMod64.Ntt.intPadTo n coefficients).map
        (fun value : Int => (value : ZMod64 p)) =
      ZMod64.Ntt.padTo n
        (coefficients.map fun value : Int => (value : ZMod64 p)) := by
  simp [ZMod64.Ntt.intPadTo, ZMod64.Ntt.padTo, List.map_append,
    Lean.Grind.Ring.intCast_zero]

/-- Multiply canonical coefficient lifts through the fixed auxiliary-prime
catalogue, reconstruct over the integers, and reduce back modulo `p`.
`none` records a catalogue capacity or checked-plan failure. -/
def mulNttCrt? (left right : FpPoly p) : Option (FpPoly p) := do
  let n := nttLength left right
  let bound := nttCrtBound left right
  let selection ← ZMod64.Ntt.CrtSelection.build? n bound
  let images ← selection.images?
    (intLift left).toArray (intLift right).toArray
  let plan ← Modular.CrtPlan.build? selection.moduli
  let coefficients ← plan.reconstructVec? images.residueArray
  pure (DensePoly.ofCoeffs (coefficients.toArray.map
    fun value : Int => (value : ZMod64 p)))

/-- Every successful auxiliary-prime multiplication agrees with the
schoolbook finite-field product. -/
theorem mulNttCrt?_eq (left right result : FpPoly p)
    (hresult : mulNttCrt? left right = some result) :
    result = left * right := by
  unfold mulNttCrt? at hresult
  dsimp only at hresult
  let n := nttLength left right
  let bound := nttCrtBound left right
  change (do
    let selection ← ZMod64.Ntt.CrtSelection.build? n bound
    let images ← selection.images?
      (intLift left).toArray (intLift right).toArray
    let plan ← Modular.CrtPlan.build? selection.moduli
    let coefficients ← plan.reconstructVec? images.residueArray
    pure (DensePoly.ofCoeffs (coefficients.toArray.map
      fun value : Int => (value : ZMod64 p)))) = some result at hresult
  cases hselection : ZMod64.Ntt.CrtSelection.build? n bound with
  | none => simp [hselection] at hresult
  | some selection =>
      rw [hselection] at hresult
      change ((selection.images?
          (intLift left).toArray (intLift right).toArray).bind fun images =>
        (Modular.CrtPlan.build? selection.moduli).bind fun plan =>
          (plan.reconstructVec? images.residueArray).bind fun coefficients =>
            some (DensePoly.ofCoeffs (coefficients.toArray.map
              fun value : Int => (value : ZMod64 p)))) =
                some result at hresult
      cases himages : selection.images?
          (intLift left).toArray (intLift right).toArray with
      | none => simp [himages] at hresult
      | some images =>
          rw [himages] at hresult
          change ((Modular.CrtPlan.build? selection.moduli).bind fun plan =>
            (plan.reconstructVec? images.residueArray).bind fun coefficients =>
              some (DensePoly.ofCoeffs (coefficients.toArray.map
                fun value : Int => (value : ZMod64 p)))) =
                  some result at hresult
          cases hplan : Modular.CrtPlan.build? selection.moduli with
          | none => simp [hplan] at hresult
          | some plan =>
              rw [hplan] at hresult
              change ((plan.reconstructVec? images.residueArray).bind
                fun coefficients =>
                  some (DensePoly.ofCoeffs (coefficients.toArray.map
                    fun value : Int => (value : ZMod64 p)))) =
                      some result at hresult
              cases hreconstruct : plan.reconstructVec? images.residueArray with
              | none => simp [hreconstruct] at hresult
              | some coefficients =>
                  rw [hreconstruct] at hresult
                  simp only [Option.bind, Option.some.injEq] at hresult
                  let reference := ZMod64.Ntt.intPadTo n
                    (ZMod64.Ntt.intLinearConvolution
                      (intLift left) (intLift right))
                  have hreferenceSize : reference.length = n := by
                    simpa [reference] using images.referenceSize
                  let candidate : Vector Int n :=
                    ⟨reference.toArray, by simpa using hreferenceSize⟩
                  have hcandidate (j : Fin n) :
                      candidate[j] =
                        ((DensePoly.ofList (intLift left) : DensePoly Int) *
                          DensePoly.ofList (intLift right)).coeff j.val := by
                    change reference.toArray[j.val]'(by
                      simp [hreferenceSize]) = _
                    rw [List.getElem_toArray]
                    rw [List.getElem_eq_getD (h := by
                      simp [hreferenceSize])
                        (Zero.zero : Int)]
                    exact getD_intReference n j.val left right
                  have hmoduli : plan.moduli = selection.moduli :=
                    Modular.CrtPlan.build?_moduli hplan
                  have hstrict : 2 * bound < plan.modulus := by
                    rw [Modular.CrtPlan.modulus_eq_prod, hmoduli]
                    exact selection.enough_moduli
                  have hbound : ∀ j : Fin n,
                      2 * candidate[j].natAbs < plan.modulus := by
                    intro j
                    let leftLift : DensePoly Int :=
                      DensePoly.ofList (intLift left)
                    let rightLift : DensePoly Int :=
                      DensePoly.ofList (intLift right)
                    have hcoeff := natAbs_mulCoeff_le_min
                      leftLift rightLift (p - 1) (p - 1)
                      (coeff_intLift_le left) (coeff_intLift_le right) j.val
                    have hsizes : min leftLift.size rightLift.size ≤
                        min left.size right.size := by
                      have hleftSize : leftLift.size ≤ left.size := by
                        simpa [leftLift] using size_intLift_le left
                      have hrightSize : rightLift.size ≤ right.size := by
                        simpa [rightLift] using size_intLift_le right
                      apply Nat.le_min_of_le_of_le
                      · exact Nat.le_trans (Nat.min_le_left ..) hleftSize
                      · exact Nat.le_trans (Nat.min_le_right ..) hrightSize
                    have hcoeffBound :
                        ((leftLift * rightLift).coeff j.val).natAbs ≤ bound :=
                      Nat.le_trans hcoeff (by
                        unfold bound nttCrtBound
                        exact Nat.mul_le_mul_right
                          ((p - 1) * (p - 1)) hsizes)
                    rw [hcandidate]
                    exact Nat.lt_of_le_of_lt
                      (Nat.mul_le_mul_left 2 hcoeffBound) hstrict
                  have hcongr : ∀ i : Fin plan.moduli.size, ∀ j : Fin n,
                      candidate[j] % (plan.moduli[i] : Int) =
                        (images.residueArray.getD i.val
                          (Vector.replicate n 0))[j] %
                            (plan.moduli[i] : Int) := by
                    intro i j
                    have hi : i.val < selection.moduli.size := by
                      rw [← hmoduli]
                      exact i.isLt
                    let i' : Fin selection.moduli.size := ⟨i.val, hi⟩
                    have hmod : plan.moduli[i] = selection.moduli[i'] := by
                      have hget := congrArg
                        (fun moduli : Array Nat => moduli.getD i.val 0) hmoduli
                      have hleft : plan.moduli.getD i.val 0 =
                          plan.moduli[i] := by
                        rw [Array.getD_eq_getD_getElem?,
                          Array.getElem?_eq_getElem i.isLt]
                        rfl
                      have hright : selection.moduli.getD i.val 0 =
                          selection.moduli[i'] := by
                        rw [Array.getD_eq_getD_getElem?,
                          Array.getElem?_eq_getElem hi]
                        rfl
                      exact hleft.symm.trans (hget.trans hright)
                    rw [hmod]
                    rw [hcandidate]
                    rw [← getD_intReference n j.val left right]
                    exact images.congr i' j
                  have hrecovered : coefficients = candidate :=
                    Modular.CrtPlan.reconstructVec?_eq_candidate
                      hreconstruct hbound hcongr
                  subst coefficients
                  subst result
                  calc
                    DensePoly.ofCoeffs (candidate.toArray.map
                        fun value : Int => (value : ZMod64 p)) =
                      DensePoly.ofList (reference.map
                        fun value : Int => (value : ZMod64 p)) := by
                          change DensePoly.ofCoeffs (reference.toArray.map
                            fun value : Int => (value : ZMod64 p)) = _
                          unfold DensePoly.ofList
                          rw [List.map_toArray]
                    _ = DensePoly.ofList (ZMod64.Ntt.padTo n
                        ((ZMod64.Ntt.intLinearConvolution
                          (intLift left) (intLift right)).map
                            fun value : Int => (value : ZMod64 p))) := by
                      rw [← intPadTo_cast]
                    _ = DensePoly.ofList
                        ((ZMod64.Ntt.intLinearConvolution
                          (intLift left) (intLift right)).map
                            fun value : Int => (value : ZMod64 p)) :=
                      ofList_padTo n _
                    _ = DensePoly.ofList (ZMod64.Ntt.linearConvolution
                        ((intLift left).map
                          fun value : Int => (value : ZMod64 p))
                        ((intLift right).map
                          fun value : Int => (value : ZMod64 p))) := by
                      rw [ZMod64.Ntt.linearConvolution_intCast]
                    _ = left * right := by
                      rw [intLift_cast, intLift_cast,
                        ofList_linearConvolution,
                        DensePoly.ofList_toList, DensePoly.ofList_toList]

/-! # Total dispatch -/

/-- Shorter-size threshold below which the packed lazy-reduction kernel avoids
auxiliary-plan construction.  The forced-kernel sweep over `F_65537` keeps
packed multiplication ahead through `4096` coefficients per operand; CRT-NTT
is clearly ahead at `8192` and above.  Keeping the policy value named lets
modulus-specific sweeps recalibrate it without changing the dispatcher proof. -/
@[expose] def nttCrtCutoff : Nat := 8192

/-- Leaf cutoff for the generic Karatsuba fallback used when the fixed
auxiliary catalogue cannot serve a large request. -/
@[expose] def karatsubaCutoff : Nat := 32

/-- Total finite-field multiplication.  Small products use the packed
lazy-reduction kernel; large products try auxiliary-prime NTTs and fall back
to Karatsuba on normal catalogue exhaustion. -/
def mulFast (left right : FpPoly p) : FpPoly p :=
  if min left.size right.size < nttCrtCutoff then
    mulPackedFast left right
  else
    match mulNttCrt? left right with
    | some result => result
    | none => DensePoly.mulKaratsuba karatsubaCutoff left right

/-- The total finite-field dispatcher is independent of its crossover
constants and agrees with schoolbook multiplication. -/
theorem mulFast_eq (left right : FpPoly p) :
    mulFast left right = left * right := by
  unfold mulFast
  split
  · exact mulPackedFast_eq left right
  · split
    · rename_i result hresult
      exact mulNttCrt?_eq left right result hresult
    · exact DensePoly.mulKaratsuba_eq karatsubaCutoff left right

/-- Coefficient-owner multiplication plan for generic fast algorithms.  Full
products use `mulFast`, squaring and slices use the proved Karatsuba kernels. -/
def fastPlan : DensePoly.MulPlan (ZMod64 p) where
  mul := mulFast
  square := DensePoly.squareKaratsuba karatsubaCutoff
  slice := DensePoly.karatsubaSlice karatsubaCutoff
  mul_eq := mulFast_eq
  square_eq := DensePoly.squareKaratsuba_eq karatsubaCutoff
  coeff_slice := DensePoly.coeff_karatsubaSlice karatsubaCutoff

/-- Direct cyclic NTT multiplication.  Inputs shorter than the quotient
length are zero-padded; an input exceeding that length is rejected. -/
def mulCyclicNtt? {n : Nat} [ZMod64.PrimeModulus p]
    (plan : ZMod64.NttPlan p n) (left right : FpPoly p) : Option (FpPoly p) :=
  if left.size ≤ n ∧ right.size ≤ n then
    (ZMod64.Ntt.cyclic? plan
      (ZMod64.Ntt.padTo n left.toArray.toList).toArray
      (ZMod64.Ntt.padTo n right.toArray.toList).toArray).map DensePoly.ofCoeffs
  else
    none

/-- A successful direct cyclic transform is the independent schoolbook
product folded modulo `x^n - 1`. -/
theorem mulCyclicNtt?_eq {n : Nat} [ZMod64.PrimeModulus p]
    (plan : ZMod64.NttPlan p n) (left right result : FpPoly p)
    (hresult : mulCyclicNtt? plan left right = some result) :
    result = DensePoly.ofList
      (ZMod64.Ntt.cyclicConvolution n left.toList right.toList) := by
  unfold mulCyclicNtt? at hresult
  split at hresult
  next hfit =>
    have hleft : (ZMod64.Ntt.padTo n left.toArray.toList).toArray.size = n := by
      simp [ZMod64.Ntt.length_padTo, hfit.1]
    have hright : (ZMod64.Ntt.padTo n right.toArray.toList).toArray.size = n := by
      simp [ZMod64.Ntt.length_padTo, hfit.2]
    have href := ZMod64.Ntt.cyclic?_eq_reference plan
      (ZMod64.Ntt.padTo n left.toArray.toList).toArray
      (ZMod64.Ntt.padTo n right.toArray.toList).toArray hleft hright
    simp at href
    rw [href] at hresult
    simp only [Option.map_some, Option.some.injEq] at hresult
    subst result
    exact congrArg DensePoly.ofCoeffs
      (ZMod64.Ntt.cyclicConvolution_pad_inputs plan
        left.toArray.toList right.toArray.toList)
  next hfit => simp at hresult

/-- Direct negacyclic NTT multiplication through a primitive `2n`th-root
twist.  Inputs shorter than `n` are zero-padded and oversized inputs are
rejected. -/
def mulNegacyclicNtt? {n : Nat} [ZMod64.PrimeModulus p]
    (plan : ZMod64.Ntt.NegacyclicPlan p n)
    (left right : FpPoly p) : Option (FpPoly p) :=
  if left.size ≤ n ∧ right.size ≤ n then
    (ZMod64.Ntt.negacyclic? plan
      (ZMod64.Ntt.padTo n left.toArray.toList).toArray
      (ZMod64.Ntt.padTo n right.toArray.toList).toArray).map DensePoly.ofCoeffs
  else
    none

/-- A successful direct negacyclic transform is the independent schoolbook
product folded modulo `x^n + 1`. -/
theorem mulNegacyclicNtt?_eq {n : Nat} [ZMod64.PrimeModulus p]
    (plan : ZMod64.Ntt.NegacyclicPlan p n)
    (left right result : FpPoly p)
    (hresult : mulNegacyclicNtt? plan left right = some result) :
    result = DensePoly.ofList
      (ZMod64.Ntt.negacyclicConvolution n left.toList right.toList) := by
  unfold mulNegacyclicNtt? at hresult
  split at hresult
  next hfit =>
    have hleft : (ZMod64.Ntt.padTo n left.toArray.toList).toArray.size = n := by
      simp [ZMod64.Ntt.length_padTo, hfit.1]
    have hright : (ZMod64.Ntt.padTo n right.toArray.toList).toArray.size = n := by
      simp [ZMod64.Ntt.length_padTo, hfit.2]
    have href := ZMod64.Ntt.negacyclic?_eq_reference plan
      (ZMod64.Ntt.padTo n left.toArray.toList).toArray
      (ZMod64.Ntt.padTo n right.toArray.toList).toArray hleft hright
    simp at href
    rw [href] at hresult
    simp only [Option.map_some, Option.some.injEq] at hresult
    subst result
    exact congrArg DensePoly.ofCoeffs
      (ZMod64.Ntt.negacyclicConvolution_pad_inputs plan
        left.toArray.toList right.toArray.toList)
  next hfit => simp at hresult

end FpPoly

end Hex
