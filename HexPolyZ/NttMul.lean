/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Ntt.CrtInput
public import HexModular.CrtPlan
public import HexPolyZ.KroneckerMulti

public section

/-!
# Auxiliary-prime NTT multiplication over the integers

The fixed word-prime catalogue supplies modular convolution images and the
balanced CRT plan reconstructs all coefficients together.  A strict runtime
coefficient bound identifies the symmetric reconstruction with the existing
schoolbook `DensePoly Int` product.
-/

namespace Hex

namespace ZPoly

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

private theorem getD_map_mul (value : Int) (coefficients : List Int) (n : Nat) :
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
      (DensePoly.ofList left : ZPoly) + DensePoly.ofList right := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_add_semiring, DensePoly.coeff_ofList,
    DensePoly.coeff_ofList, DensePoly.coeff_ofList]
  exact getD_intAddCoeffs left right n

private theorem ofList_map_mul (value : Int) (coefficients : List Int) :
    DensePoly.ofList (coefficients.map fun coefficient => value * coefficient) =
      DensePoly.scale value (DensePoly.ofList coefficients : ZPoly) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_ofList,
    DensePoly.coeff_scale value _ n (Int.mul_zero value),
    DensePoly.coeff_ofList]
  exact getD_map_mul value coefficients n

private theorem ofList_zero_cons (coefficients : List Int) :
    DensePoly.ofList (0 :: coefficients) =
      DensePoly.shift 1 (DensePoly.ofList coefficients : ZPoly) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_ofList, DensePoly.coeff_shift]
  cases n with
  | zero => rfl
  | succ n => simp [DensePoly.coeff_ofList]

private theorem ofList_cons (value : Int) (coefficients : List Int) :
    DensePoly.ofList (value :: coefficients) =
      DensePoly.C value +
        DensePoly.shift 1 (DensePoly.ofList coefficients : ZPoly) := by
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

private theorem shift_mul (d : Nat) (left right : ZPoly) :
    DensePoly.shift d left * right = DensePoly.shift d (left * right) := by
  calc
    DensePoly.shift d left * right =
        (DensePoly.monomial d 1 * left) * right := by
      rw [DensePoly.monomial_one_mul_poly_eq_shift]
    _ = DensePoly.monomial d 1 * (left * right) :=
      DensePoly.mul_assoc_poly _ _ _
    _ = DensePoly.shift d (left * right) :=
      DensePoly.monomial_one_mul_poly_eq_shift _ _

/-- The independent integer coefficient convolution normalizes to the
existing schoolbook polynomial product. -/
theorem ofList_intLinearConvolution (left right : List Int) :
    DensePoly.ofList (ZMod64.Ntt.intLinearConvolution left right) =
      (DensePoly.ofList left : ZPoly) * DensePoly.ofList right := by
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
            ofList_map_mul, ofList_zero_cons, ih]
          let right : ZPoly := DensePoly.ofList (coefficient :: coefficients)
          calc
            DensePoly.scale value right +
                DensePoly.shift 1 (DensePoly.ofList values * right) =
              DensePoly.C value * right +
                DensePoly.shift 1 (DensePoly.ofList values) * right := by
                  rw [ZPoly.C_mul_eq_scale]
                  exact congrArg (fun tail : ZPoly =>
                    DensePoly.scale value right + tail)
                    (shift_mul 1
                      (DensePoly.ofList values : ZPoly) right).symm
            _ = (DensePoly.C value +
                DensePoly.shift 1 (DensePoly.ofList values)) * right :=
              (DensePoly.mul_add_left_poly _ _ _).symm
            _ = DensePoly.ofList (value :: values) * right := by
              rw [ofList_cons]

private theorem getD_replicate_zero (count i : Nat) :
    (List.replicate count (0 : Int)).getD i 0 = 0 := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      cases i with
      | zero => rfl
      | succ i => simpa [List.replicate_succ] using ih i

private theorem ofList_intPadTo (n : Nat) (coefficients : List Int) :
    DensePoly.ofList (ZMod64.Ntt.intPadTo n coefficients) =
      (DensePoly.ofList coefficients : ZPoly) := by
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
    exact getD_replicate_zero (n - coefficients.length)
      (i - coefficients.length)

private theorem getD_reference (n i : Nat) (left right : ZPoly) :
    (ZMod64.Ntt.intPadTo n
        (ZMod64.Ntt.intLinearConvolution left.toList right.toList)).getD i
          (Zero.zero : Int) =
      (left * right).coeff i := by
  have hpad := ofList_intPadTo n
    (ZMod64.Ntt.intLinearConvolution left.toList right.toList)
  have hconvolution := ofList_intLinearConvolution left.toList right.toList
  have h := congrArg (fun polynomial : ZPoly => polynomial.coeff i)
    (hpad.trans hconvolution)
  simpa [DensePoly.coeff_ofList, DensePoly.ofList_toList] using h

/-- Least radix-two transform capacity covering the ordinary product. -/
@[expose] def nttLength (left right : ZPoly) : Nat :=
  (left.size + right.size - 1).nextPowerOfTwo

/-- Multiply through the fixed auxiliary NTT-prime catalogue and balanced
batch CRT.  Failure records catalogue exhaustion or a failed checked plan;
callers that need a total operation can fall back to a Kronecker kernel. -/
def mulNttCrt? (left right : ZPoly) : Option ZPoly := do
  let n := nttLength left right
  let bound := coeffBudget left right
  let selection ← ZMod64.Ntt.CrtSelection.build? n bound
  let images ← selection.images? left.toArray right.toArray
  let plan ← Modular.CrtPlan.build? selection.moduli
  let coefficients ← plan.reconstructVec? images.residueArray
  pure (DensePoly.ofCoeffs coefficients.toArray)

/-- Every successful auxiliary-prime NTT multiplication is the existing
schoolbook integer polynomial product. -/
theorem mulNttCrt?_eq (left right result : ZPoly)
    (hresult : mulNttCrt? left right = some result) :
    result = left * right := by
  unfold mulNttCrt? at hresult
  dsimp only at hresult
  let n := nttLength left right
  let bound := coeffBudget left right
  change (do
    let selection ← ZMod64.Ntt.CrtSelection.build? n bound
    let images ← selection.images? left.toArray right.toArray
    let plan ← Modular.CrtPlan.build? selection.moduli
    let coefficients ← plan.reconstructVec? images.residueArray
    pure (DensePoly.ofCoeffs coefficients.toArray)) = some result at hresult
  cases hselection : ZMod64.Ntt.CrtSelection.build? n bound with
  | none => simp [hselection] at hresult
  | some selection =>
      rw [hselection] at hresult
      change ((selection.images? left.toArray right.toArray).bind fun images =>
        (Modular.CrtPlan.build? selection.moduli).bind fun plan =>
          (plan.reconstructVec? images.residueArray).bind fun coefficients =>
            some (DensePoly.ofCoeffs coefficients.toArray)) =
              some result at hresult
      cases himages : selection.images? left.toArray right.toArray with
      | none => simp [himages] at hresult
      | some images =>
          rw [himages] at hresult
          change ((Modular.CrtPlan.build? selection.moduli).bind fun plan =>
            (plan.reconstructVec? images.residueArray).bind fun coefficients =>
              some (DensePoly.ofCoeffs coefficients.toArray)) =
                some result at hresult
          cases hplan : Modular.CrtPlan.build? selection.moduli with
          | none => simp [hplan] at hresult
          | some plan =>
              rw [hplan] at hresult
              change ((plan.reconstructVec? images.residueArray).bind
                fun coefficients =>
                  some (DensePoly.ofCoeffs coefficients.toArray)) =
                    some result at hresult
              cases hreconstruct : plan.reconstructVec? images.residueArray with
              | none => simp [hreconstruct] at hresult
              | some coefficients =>
                  rw [hreconstruct] at hresult
                  simp only [Option.bind, Option.some.injEq] at hresult
                  let reference := ZMod64.Ntt.intPadTo n
                    (ZMod64.Ntt.intLinearConvolution
                      left.toArray.toList right.toArray.toList)
                  have hreferenceSize : reference.length = n := by
                    simpa [reference] using images.referenceSize
                  let candidate : Vector Int n :=
                    ⟨reference.toArray, by simpa using hreferenceSize⟩
                  have hcandidate (j : Fin n) :
                      candidate[j] = (left * right).coeff j.val := by
                    change reference.toArray[j.val]'(by
                      simpa [hreferenceSize] using j.isLt) = _
                    rw [List.getElem_toArray]
                    rw [List.getElem_eq_getD (h := by
                      simpa [hreferenceSize] using j.isLt)
                        (Zero.zero : Int)]
                    exact getD_reference n j.val left right
                  have hmoduli : plan.moduli = selection.moduli :=
                    Modular.CrtPlan.build?_moduli hplan
                  have hstrict : 2 * bound < plan.modulus := by
                    rw [Modular.CrtPlan.modulus_eq_prod]
                    rw [hmoduli]
                    exact selection.enough_moduli
                  have hbound : ∀ j : Fin n,
                      2 * candidate[j].natAbs < plan.modulus := by
                    intro j
                    rw [hcandidate]
                    have hcoeff := natAbs_mulCoeff_le_min left right
                      (maxAbs left) (maxAbs right)
                      (natAbs_coeff_le_maxAbs left)
                      (natAbs_coeff_le_maxAbs right) j.val
                    change ((left * right).coeff j.val).natAbs ≤ bound at hcoeff
                    omega
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
                    rw [← getD_reference n j.val left right]
                    exact images.congr i' j
                  have hrecovered : coefficients = candidate :=
                    Modular.CrtPlan.reconstructVec?_eq_candidate
                      hreconstruct hbound hcongr
                  subst coefficients
                  subst result
                  calc
                    DensePoly.ofCoeffs candidate.toArray =
                        DensePoly.ofList reference := rfl
                    _ = DensePoly.ofList
                        (ZMod64.Ntt.intLinearConvolution
                          left.toArray.toList right.toArray.toList) :=
                      ofList_intPadTo n _
                    _ = DensePoly.ofList left.toArray.toList *
                        DensePoly.ofList right.toArray.toList :=
                      ofList_intLinearConvolution
                        left.toArray.toList right.toArray.toList
                    _ = left * right := by
                      change DensePoly.ofList left.toList *
                        DensePoly.ofList right.toList = left * right
                      rw [DensePoly.ofList_toList, DensePoly.ofList_toList]

end ZPoly

end Hex
