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

variable {R : Type u} [DecidableEq R] [Lean.Grind.CommRing R]

/-- A polynomial whose coefficients vanish from `n` onward has size at most
`n`. -/
theorem size_le_of_coeff_zero_above {p : DensePoly R} {n : Nat}
    (hzero : ∀ i, n ≤ i → p.coeff i = 0) : p.size ≤ n := by
  by_cases hle : p.size ≤ n
  · exact hle
  · have hpos : 0 < p.size := by omega
    have hlast := coeff_last_ne_zero_of_pos_size p hpos
    exact False.elim (hlast (hzero (p.size - 1) (by omega)))

/-- Addition cannot increase size beyond the larger operand. -/
theorem size_add_le_max (p q : DensePoly R) :
    (p + q).size ≤ max p.size q.size := by
  apply size_le_of_coeff_zero_above
  intro i hi
  rw [coeff_add_semiring,
    coeff_eq_zero_of_size_le p (Nat.le_trans (Nat.le_max_left ..) hi),
    coeff_eq_zero_of_size_le q (Nat.le_trans (Nat.le_max_right ..) hi)]
  exact Lean.Grind.Semiring.add_zero 0

/-- Subtraction cannot increase size beyond the larger operand. -/
theorem size_sub_le_max (p q : DensePoly R) :
    (p - q).size ≤ max p.size q.size := by
  apply size_le_of_coeff_zero_above
  intro i hi
  rw [coeff_sub_ring,
    coeff_eq_zero_of_size_le p (Nat.le_trans (Nat.le_max_left ..) hi),
    coeff_eq_zero_of_size_le q (Nat.le_trans (Nat.le_max_right ..) hi)]
  exact SubZeroLaw.sub_zero_zero

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

/-- Fold one product diagonal. The left operand is the loop driver; callers
put the shorter operand there. Indices outside the valid convolution diagonal
perform no coefficient operation. -/
@[expose]
def schoolbookCoeff (a b : DensePoly R) (d : Nat) : R :=
  (List.range a.size).foldl
    (fun acc i =>
      if d < i then acc
      else if d - i < b.size then acc + a.coeff i * b.coeff (d - i)
      else acc)
    0

/-- The direct diagonal kernel agrees with the schoolbook product fold. -/
theorem schoolbookCoeff_eq_mulCoeffSum (a b : DensePoly R) (d : Nat) :
    schoolbookCoeff a b d = mulCoeffSum a b d := by
  rw [mulCoeffSum_eq_diagonal]
  unfold schoolbookCoeff
  have aux : ∀ (xs : List Nat) (acc : R),
      xs.foldl
          (fun acc i =>
            if d < i then acc
            else if d - i < b.size then acc + a.coeff i * b.coeff (d - i)
            else acc)
          acc =
        xs.foldl (fun acc i => acc + diagonalMulCoeffTerm a b d i) acc := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons i xs ih =>
        intro acc
        rw [List.foldl_cons, List.foldl_cons]
        unfold diagonalMulCoeffTerm
        by_cases hdi : d < i
        · rw [_root_.ite_eq_left hdi, _root_.ite_eq_left hdi]
          change xs.foldl _ acc = xs.foldl _ (acc + 0)
          rw [Lean.Grind.Semiring.add_zero]
          exact ih acc
        · rw [_root_.ite_eq_right hdi, _root_.ite_eq_right hdi]
          by_cases hib : d - i < b.size
          · rw [_root_.ite_eq_left hib]
            exact ih _
          · rw [_root_.ite_eq_right hib]
            have hbzero : b.coeff (d - i) = 0 :=
              coeff_eq_zero_of_size_le b (Nat.le_of_not_gt hib)
            rw [hbzero, Lean.Grind.Semiring.mul_zero, Lean.Grind.Semiring.add_zero]
            exact ih acc
  exact aux (List.range a.size) 0

/-- Allocation-conscious runtime implementation of `schoolbookSlice`.
Requests beyond the product support are discarded before entering the
coefficient folds, and the shorter operand drives each diagonal fold. -/
@[expose]
def schoolbookSliceImpl (lo len : Nat) (a b : DensePoly R) : DensePoly R :=
  if a.size = 0 then
    0
  else if b.size = 0 then
    0
  else
    let used := min len (a.size + b.size - 1 - lo)
    if a.size ≤ b.size then
      ofList ((List.range used).map fun i => schoolbookCoeff a b (lo + i))
    else
      ofList ((List.range used).map fun i => schoolbookCoeff b a (lo + i))

/-- The bounded coefficient-fold implementation agrees with the semantic
clipped product. -/
theorem schoolbookSlice_eq_impl (lo len : Nat) (a b : DensePoly R) :
    schoolbookSlice lo len a b = schoolbookSliceImpl lo len a b := by
  unfold schoolbookSliceImpl
  split
  · rename_i ha
    have haeq : a = 0 := (size_eq_zero_iff a).mp ha
    subst a
    apply ext_coeff
    intro i
    rw [coeff_schoolbookSlice, zero_mul, coeff_zero]
    split <;> rfl
  · rename_i ha
    split
    · rename_i hb
      have hbeq : b = 0 := (size_eq_zero_iff b).mp hb
      subst b
      apply ext_coeff
      intro i
      rw [coeff_schoolbookSlice, mul_comm_poly, zero_mul, coeff_zero]
      split <;> rfl
    · rename_i hb
      have hsupp := size_mul_le a b
      split
      · apply ext_coeff
        intro i
        rw [coeff_schoolbookSlice, coeff_ofList]
        by_cases hi : i < min len (a.size + b.size - 1 - lo)
        · have hil : i < len := Nat.lt_of_lt_of_le hi (Nat.min_le_left ..)
          rw [_root_.ite_eq_left hil]
          rw [List.getD_eq_getElem?_getD]
          simp [hi]
          rw [schoolbookCoeff_eq_mulCoeffSum]
          exact coeff_mul a b (lo + i)
        · rw [List.getD_eq_getElem?_getD]
          simp [hi]
          by_cases hil : i < len
          · rw [_root_.ite_eq_left hil]
            have hbound : (a * b).size ≤ lo + i :=
              Nat.le_trans hsupp (by omega)
            exact coeff_eq_zero_of_size_le (a * b) hbound
          · rw [_root_.ite_eq_right hil]
            rfl
      · apply ext_coeff
        intro i
        rw [coeff_schoolbookSlice, coeff_ofList]
        by_cases hi : i < min len (a.size + b.size - 1 - lo)
        · have hil : i < len := Nat.lt_of_lt_of_le hi (Nat.min_le_left ..)
          rw [_root_.ite_eq_left hil]
          rw [List.getD_eq_getElem?_getD]
          simp [hi]
          rw [schoolbookCoeff_eq_mulCoeffSum]
          rw [← coeff_mul b a (lo + i), mul_comm_poly]
        · rw [List.getD_eq_getElem?_getD]
          simp [hi]
          by_cases hil : i < len
          · rw [_root_.ite_eq_left hil]
            have hbound : (a * b).size ≤ lo + i :=
              Nat.le_trans hsupp (by omega)
            exact coeff_eq_zero_of_size_le (a * b) hbound
          · rw [_root_.ite_eq_right hil]
            rfl

/-- Compiled clipped schoolbook products use direct coefficient folds. -/
@[csimp]
theorem schoolbookSlice_csimp : @schoolbookSlice = @schoolbookSliceImpl := by
  funext R instDecEq instRing lo len a b
  exact schoolbookSlice_eq_impl lo len a b

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
