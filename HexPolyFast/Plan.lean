/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly

public section

/-!
Explicit multiplication plans for dense polynomials.

The plan laws keep optimized kernels behind the existing schoolbook
`DensePoly` semantics.  Plans are values rather than typeclass instances, so
callers can select a coefficient-specific implementation locally.
-/

namespace Hex.DensePoly

universe u

attribute [local instance 1000] Lean.Grind.Semiring.ofNat

/-- A proof-carrying implementation of full, square, and clipped dense
polynomial multiplication.  `slice lo len a b` stores coefficients beginning
at degree `lo`, shifted down to degree zero. -/
structure MulPlan (R : Type u) [DecidableEq R] [Lean.Grind.CommRing R] where
  /-- A complete normalized product. -/
  mul : DensePoly R → DensePoly R → DensePoly R
  /-- A specialized square. -/
  square : DensePoly R → DensePoly R
  /-- `len` coefficients beginning at product degree `lo`, shifted down. -/
  slice : Nat → Nat → DensePoly R → DensePoly R → DensePoly R
  mul_eq : ∀ a b, mul a b = a * b
  square_eq : ∀ a, square a = a * a
  coeff_slice : ∀ lo len a b i,
    (slice lo len a b).coeff i =
      if i < len then (a * b).coeff (lo + i) else 0

variable {R : Type u} [DecidableEq R] [Lean.Grind.CommRing R]

/-- Kernel-facing clipped schoolbook product.  The definition is phrased by
the semantic product so its coefficient law is immediate; compiled code uses
`schoolbookSliceImpl`, which evaluates the requested schoolbook coefficient
folds directly and never materializes the full product. -/
@[expose]
noncomputable def schoolbookSlice (lo len : Nat) (a b : DensePoly R) :
    DensePoly R :=
  ofList ((List.range len).map fun i => (a * b).coeff (lo + i))

/-- Allocation-conscious runtime implementation of `schoolbookSlice`. -/
@[expose]
def schoolbookSliceImpl (lo len : Nat) (a b : DensePoly R) : DensePoly R :=
  ofList ((List.range len).map fun i => mulCoeffSum a b (lo + i))

/-- The direct coefficient-fold implementation agrees with the semantic
clipped product. -/
theorem schoolbookSlice_eq_impl (lo len : Nat) (a b : DensePoly R) :
    schoolbookSlice lo len a b = schoolbookSliceImpl lo len a b := by
  unfold schoolbookSlice schoolbookSliceImpl
  apply congrArg ofList
  apply List.map_congr_left
  intro i hi
  exact coeff_mul a b (lo + i)

/-- Compiled clipped schoolbook products use direct coefficient folds. -/
@[csimp]
theorem schoolbookSlice_csimp : @schoolbookSlice = @schoolbookSliceImpl := by
  funext R instDecEq instRing lo len a b
  exact schoolbookSlice_eq_impl lo len a b

/-- Coefficient law for a clipped schoolbook product. -/
theorem coeff_schoolbookSlice (lo len : Nat) (a b : DensePoly R) (i : Nat) :
    (schoolbookSlice lo len a b).coeff i =
      if i < len then (a * b).coeff (lo + i) else 0 := by
  unfold schoolbookSlice
  rw [coeff_ofList]
  by_cases hi : i < len
  · simp [List.getD, hi]
  · have hlen : (List.map (fun j => (a * b).coeff (lo + j))
        (List.range len)).length ≤ i := by simp; omega
    rw [List.getD_eq_getElem?_getD]
    simp [hi]
    change (Zero.zero : R) = (Zero.zero : R)
    rfl

/-- The reference plan backed by the existing allocation-conscious
schoolbook multiplication. -/
def schoolbookPlan : MulPlan R where
  mul := mulImpl
  square := fun a => mulImpl a a
  slice := schoolbookSlice
  mul_eq := fun a b => (mul_eq_mulImpl a b).symm
  square_eq := fun a => (mul_eq_mulImpl a a).symm
  coeff_slice := coeff_schoolbookSlice

/-- Multiply using an explicit plan. -/
@[inline]
def mulWith (plan : MulPlan R) (a b : DensePoly R) : DensePoly R :=
  plan.mul a b

/-- Square using an explicit plan. -/
@[inline]
def squareWith (plan : MulPlan R) (a : DensePoly R) : DensePoly R :=
  plan.square a

/-- Keep the first `len` coefficients of a planned product. -/
@[inline]
def mulLow (plan : MulPlan R) (len : Nat) (a b : DensePoly R) : DensePoly R :=
  plan.slice 0 len a b

/-- Keep `len` coefficients beginning at product degree `lo`. -/
@[inline]
def mulSlice (plan : MulPlan R) (lo len : Nat) (a b : DensePoly R) :
    DensePoly R :=
  plan.slice lo len a b

/-- The standard middle product for operands of sizes `m ≥ n > 0`.
The result contains product degrees `n - 1` through `m - 1`, shifted down. -/
@[inline]
def mulMiddle (plan : MulPlan R) (a b : DensePoly R)
    (_hsize : b.size ≤ a.size) (_hpos : 0 < b.size) : DensePoly R :=
  plan.slice (b.size - 1) (a.size - b.size + 1) a b

/-- Checked middle product.  Operands are ordered by size; an empty operand
has zero middle product. -/
def mulMiddleChecked (plan : MulPlan R) (a b : DensePoly R) : DensePoly R :=
  if ha : a.size = 0 then 0
  else if hb : b.size = 0 then 0
  else
    if hba : b.size ≤ a.size then
      mulMiddle plan a b hba (by omega)
    else
      mulMiddle plan b a (Nat.le_of_lt (Nat.lt_of_not_ge hba)) (by omega)

/-- Planned multiplication has the existing dense-polynomial semantics. -/
theorem mulWith_eq (plan : MulPlan R) (a b : DensePoly R) :
    mulWith plan a b = a * b :=
  plan.mul_eq a b

/-- Planned squaring has the existing dense-polynomial semantics. -/
theorem squareWith_eq (plan : MulPlan R) (a : DensePoly R) :
    squareWith plan a = a * a :=
  plan.square_eq a

/-- Coefficient law for a planned low product. -/
theorem coeff_mulLow (plan : MulPlan R) (len i : Nat) (a b : DensePoly R) :
    (mulLow plan len a b).coeff i =
      if i < len then (a * b).coeff i else 0 := by
  simpa [mulLow] using plan.coeff_slice 0 len a b i

/-- Coefficient law for an arbitrary planned slice. -/
theorem coeff_mulSlice (plan : MulPlan R) (lo len i : Nat)
    (a b : DensePoly R) :
    (mulSlice plan lo len a b).coeff i =
      if i < len then (a * b).coeff (lo + i) else 0 :=
  plan.coeff_slice lo len a b i

/-- Coefficient law for the standard proof-taking middle product. -/
theorem coeff_mulMiddle (plan : MulPlan R) (a b : DensePoly R)
    (hsize : b.size ≤ a.size) (hpos : 0 < b.size) (i : Nat) :
    (mulMiddle plan a b hsize hpos).coeff i =
      if i < a.size - b.size + 1 then
        (a * b).coeff (b.size - 1 + i)
      else 0 :=
  plan.coeff_slice (b.size - 1) (a.size - b.size + 1) a b i

end Hex.DensePoly
