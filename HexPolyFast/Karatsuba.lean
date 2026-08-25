/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFast.Plan

public section

/-!
Splitting and algebraic assembly lemmas for Karatsuba multiplication.
-/

namespace Hex.DensePoly

universe u

attribute [local instance 1000] Lean.Grind.Semiring.ofNat

variable {R : Type u} [DecidableEq R] [Lean.Grind.CommRing R]

/-- Coefficients strictly below `k`. -/
@[expose]
def low (k : Nat) (p : DensePoly R) : DensePoly R :=
  ofList ((List.range k).map p.coeff)

/-- Coefficients at and above `k`, shifted down by `k`. -/
@[expose]
def high (k : Nat) (p : DensePoly R) : DensePoly R :=
  ofList ((List.range (p.size - k)).map fun i => p.coeff (k + i))

/-- Coefficient law for the low half. -/
theorem coeff_low (k : Nat) (p : DensePoly R) (i : Nat) :
    (low k p).coeff i = if i < k then p.coeff i else 0 := by
  unfold low
  rw [coeff_ofList]
  by_cases hi : i < k
  · simp [List.getD, hi]
  · rw [List.getD_eq_getElem?_getD]
    simp [hi]
    rfl

/-- Coefficient law for the shifted-down high half. -/
theorem coeff_high (k : Nat) (p : DensePoly R) (i : Nat) :
    (high k p).coeff i =
      if i < p.size - k then p.coeff (k + i) else 0 := by
  unfold high
  rw [coeff_ofList]
  by_cases hi : i < p.size - k
  · simp [List.getD, hi]
  · rw [List.getD_eq_getElem?_getD]
    simp [hi]
    rfl

/-- Splitting at `k` and shifting the high half back reconstructs the input. -/
theorem low_add_shift_high (k : Nat) (p : DensePoly R) :
    low k p + shift k (high k p) = p := by
  apply ext_coeff
  intro i
  have hz : (0 : R) + 0 = 0 := by grind
  rw [coeff_add _ _ _ hz, coeff_low, coeff_shift]
  by_cases hik : i < k
  · rw [_root_.ite_eq_left hik, _root_.ite_eq_left hik]
    change p.coeff i + (0 : R) = p.coeff i
    exact Lean.Grind.Semiring.add_zero _
  · have hki : k ≤ i := Nat.le_of_not_gt hik
    rw [_root_.ite_eq_right hik, _root_.ite_eq_right hik]
    by_cases hip : i < p.size
    · have hh : i - k < p.size - k := by omega
      rw [coeff_high, _root_.ite_eq_left hh]
      have hidx : k + (i - k) = i := by omega
      rw [hidx]
      grind
    · have hsize : p.size ≤ i := Nat.le_of_not_gt hip
      have hh : ¬ i - k < p.size - k := by omega
      rw [coeff_high, _root_.ite_eq_right hh,
        coeff_eq_zero_of_size_le p hsize]
      exact hz

/-- Nested shifts add their offsets. -/
theorem shift_shift (k l : Nat) (p : DensePoly R) :
    shift k (shift l p) = shift (k + l) p := by
  apply ext_coeff
  intro i
  rw [coeff_shift, coeff_shift, coeff_shift]
  by_cases hi : i < k
  · have hil : i < k + l := by omega
    simp [hi, hil]
  · by_cases hil : i - k < l
    · have hisum : i < k + l := by omega
      simp [hi, hil, hisum]
    · have hisum : ¬ i < k + l := by omega
      have hidx : i - k - l = i - (k + l) := by omega
      simp [hi, hil, hisum, hidx]

/-- A shifted left factor shifts the product. -/
theorem shift_mul (k : Nat) (p q : DensePoly R) :
    shift k p * q = shift k (p * q) := by
  calc
    shift k p * q = (monomial k 1 * p) * q := by
      rw [monomial_one_mul_poly_eq_shift]
    _ = monomial k 1 * (p * q) := mul_assoc_poly _ _ _
    _ = shift k (p * q) := monomial_one_mul_poly_eq_shift _ _

/-- A shifted right factor shifts the product. -/
theorem mul_shift (k : Nat) (p q : DensePoly R) :
    p * shift k q = shift k (p * q) := by
  calc
    p * shift k q = shift k q * p := mul_comm_poly _ _
    _ = shift k (q * p) := shift_mul _ _ _
    _ = shift k (p * q) := congrArg (shift k) (mul_comm_poly q p)

/-- Multiplying two shifted polynomials adds their offsets. -/
theorem shift_mul_shift (k l : Nat) (p q : DensePoly R) :
    shift k p * shift l q = shift (k + l) (p * q) := by
  rw [shift_mul, mul_shift, shift_shift]

/-- The three-product Karatsuba assembly identity. -/
theorem karatsuba_combine (k : Nat) (a₀ a₁ b₀ b₁ : DensePoly R) :
    let z₀ := a₀ * b₀
    let z₂ := a₁ * b₁
    let z₁ := (a₀ + a₁) * (b₀ + b₁) - z₀ - z₂
    z₀ + shift k z₁ + shift (2 * k) z₂ =
      (a₀ + shift k a₁) * (b₀ + shift k b₁) := by
  dsimp
  rw [mul_add_right_poly (a₀ + a₁) b₀ b₁,
    mul_add_left_poly a₀ a₁ b₀,
    mul_add_left_poly a₀ a₁ b₁,
    mul_add_right_poly (a₀ + shift k a₁) b₀ (shift k b₁),
    mul_add_left_poly a₀ (shift k a₁) b₀,
    mul_add_left_poly a₀ (shift k a₁) (shift k b₁),
    shift_mul, mul_shift, shift_mul_shift]
  have hkk : k + k = 2 * k := by omega
  rw [hkk]
  apply ext_coeff
  intro i
  have hzadd : (0 : R) + 0 = 0 := by grind
  have hzsub : (0 : R) - 0 = 0 := by grind
  simp only [coeff_add _ _ _ hzadd, coeff_sub _ _ _ hzsub, coeff_shift]
  have hzero : (Zero.zero : R) = 0 := rfl
  simp only [hzero]
  split <;> split <;> grind

/-- Fuelled three-product Karatsuba recursion.  Fuel is separate from the
cutoff so cutoff zero remains total; public callers provide at least the
larger operand size. -/
@[expose]
def karatsubaAux (cutoff : Nat) : Nat → DensePoly R → DensePoly R → DensePoly R
  | 0, a, b => mulImpl a b
  | fuel + 1, a, b =>
      if a.size ≤ max 1 cutoff || b.size ≤ max 1 cutoff then
        mulImpl a b
      else
        let k := (max a.size b.size + 1) / 2
        let a₀ := low k a
        let a₁ := high k a
        let b₀ := low k b
        let b₁ := high k b
        let z₀ := karatsubaAux cutoff fuel a₀ b₀
        let z₂ := karatsubaAux cutoff fuel a₁ b₁
        let z₁ := karatsubaAux cutoff fuel (a₀ + a₁) (b₀ + b₁) - z₀ - z₂
        z₀ + shift k z₁ + shift (2 * k) z₂

/-- Specialized three-square Karatsuba recursion. -/
@[expose]
def karatsubaSquareAux (cutoff : Nat) : Nat → DensePoly R → DensePoly R
  | 0, a => mulImpl a a
  | fuel + 1, a =>
      if a.size ≤ max 1 cutoff then
        mulImpl a a
      else
        let k := (a.size + 1) / 2
        let a₀ := low k a
        let a₁ := high k a
        let z₀ := karatsubaSquareAux cutoff fuel a₀
        let z₂ := karatsubaSquareAux cutoff fuel a₁
        let z₁ := karatsubaSquareAux cutoff fuel (a₀ + a₁) - z₀ - z₂
        z₀ + shift k z₁ + shift (2 * k) z₂

/-- Every fuelled Karatsuba product agrees with schoolbook multiplication. -/
theorem karatsubaAux_eq (cutoff fuel : Nat) (a b : DensePoly R) :
    karatsubaAux cutoff fuel a b = a * b := by
  induction fuel generalizing a b with
  | zero =>
      exact (mul_eq_mulImpl a b).symm
  | succ fuel ih =>
      rw [karatsubaAux]
      split
      · exact (mul_eq_mulImpl a b).symm
      · dsimp only
        rw [ih, ih, ih]
        rw [karatsuba_combine]
        rw [low_add_shift_high, low_add_shift_high]

/-- Every fuelled Karatsuba square agrees with ordinary squaring. -/
theorem karatsubaSquareAux_eq (cutoff fuel : Nat) (a : DensePoly R) :
    karatsubaSquareAux cutoff fuel a = a * a := by
  induction fuel generalizing a with
  | zero =>
      exact (mul_eq_mulImpl a a).symm
  | succ fuel ih =>
      rw [karatsubaSquareAux]
      split
      · exact (mul_eq_mulImpl a a).symm
      · dsimp only
        rw [ih, ih, ih]
        rw [karatsuba_combine]
        rw [low_add_shift_high]

/-- Balanced Karatsuba multiplication with an explicit schoolbook cutoff. -/
def mulKaratsubaBalanced (cutoff : Nat) (a b : DensePoly R) : DensePoly R :=
  karatsubaAux cutoff (max a.size b.size) a b

/-- Specialized Karatsuba squaring with an explicit schoolbook cutoff. -/
def squareKaratsuba (cutoff : Nat) (a : DensePoly R) : DensePoly R :=
  karatsubaSquareAux cutoff a.size a

/-- Balanced Karatsuba multiplication agrees exactly with `DensePoly.mul`. -/
theorem mulKaratsubaBalanced_eq (cutoff : Nat) (a b : DensePoly R) :
    mulKaratsubaBalanced cutoff a b = a * b :=
  karatsubaAux_eq cutoff _ a b

/-- Specialized Karatsuba squaring agrees exactly with `DensePoly.mul`. -/
theorem squareKaratsuba_eq (cutoff : Nat) (a : DensePoly R) :
    squareKaratsuba cutoff a = a * a :=
  karatsubaSquareAux_eq cutoff _ a

/-- Multiply a long operand by blocks of `blockSize` coefficients.  Each block
uses balanced Karatsuba; the shifted block products are accumulated without
padding the short operand to the long size. -/
@[expose]
def karatsubaBlocks (cutoff blockSize : Nat) :
    Nat → DensePoly R → DensePoly R → DensePoly R
  | 0, long, short => mulKaratsubaBalanced cutoff long short
  | fuel + 1, long, short =>
      if long.size = 0 then 0
      else
        mulKaratsubaBalanced cutoff (low blockSize long) short +
          shift blockSize
            (karatsubaBlocks cutoff blockSize fuel (high blockSize long) short)

/-- Blocked unbalanced multiplication agrees with the ordinary product for
every fuel value. -/
theorem karatsubaBlocks_eq (cutoff blockSize fuel : Nat)
    (long short : DensePoly R) :
    karatsubaBlocks cutoff blockSize fuel long short = long * short := by
  induction fuel generalizing long with
  | zero => exact mulKaratsubaBalanced_eq cutoff long short
  | succ fuel ih =>
      rw [karatsubaBlocks]
      split <;> rename_i hzero
      · have hlong : long = 0 := (size_eq_zero_iff long).mp hzero
        subst long
        exact (zero_mul short).symm
      · rw [mulKaratsubaBalanced_eq, ih, ← shift_mul,
          ← mul_add_left_poly, low_add_shift_high]

/-- Full Karatsuba multiplication.  Strongly skewed operands are processed in
blocks near the shorter size rather than padded to the longer size. -/
def mulKaratsuba (cutoff : Nat) (a b : DensePoly R) : DensePoly R :=
  if a.size = 0 || b.size = 0 then
    mulImpl a b
  else if 2 * b.size < a.size then
    karatsubaBlocks cutoff b.size a.size a b
  else if 2 * a.size < b.size then
    karatsubaBlocks cutoff a.size b.size b a
  else
    mulKaratsubaBalanced cutoff a b

/-- Full balanced-or-blocked Karatsuba multiplication agrees exactly with
`DensePoly.mul`. -/
theorem mulKaratsuba_eq (cutoff : Nat) (a b : DensePoly R) :
    mulKaratsuba cutoff a b = a * b := by
  unfold mulKaratsuba
  split
  · exact (mul_eq_mulImpl a b).symm
  · split
    · exact karatsubaBlocks_eq cutoff b.size a.size a b
    · split
      · rw [karatsubaBlocks_eq, mul_comm_poly]
      · exact mulKaratsubaBalanced_eq cutoff a b

/-- Extract `len` coefficients beginning at `lo` from an already-computed
polynomial, shifting them down to degree zero. -/
@[expose]
def coeffSlice (lo len : Nat) (p : DensePoly R) : DensePoly R :=
  ofList ((List.range len).map fun i => p.coeff (lo + i))

/-- Coefficient law for extracting a polynomial interval. -/
theorem coeff_coeffSlice (lo len : Nat) (p : DensePoly R) (i : Nat) :
    (coeffSlice lo len p).coeff i =
      if i < len then p.coeff (lo + i) else 0 := by
  unfold coeffSlice
  rw [coeff_ofList]
  by_cases hi : i < len
  · simp [List.getD, hi]
  · rw [List.getD_eq_getElem?_getD]
    simp [hi]
    rfl

/-- Truncating both inputs above `n` preserves every product coefficient
strictly below `n`. -/
theorem coeff_low_mul_low (n : Nat) (a b : DensePoly R) (i : Nat)
    (hi : i < n) :
    (low n a * low n b).coeff i = (a * b).coeff i := by
  have hdecomp :
      (low n a + shift n (high n a)) *
          (low n b + shift n (high n b)) = a * b := by
    rw [low_add_shift_high, low_add_shift_high]
  rw [← hdecomp]
  rw [mul_add_right_poly, mul_add_left_poly, mul_add_left_poly,
    shift_mul, mul_shift, shift_mul_shift]
  have hz : (0 : R) + 0 = 0 := by grind
  simp only [coeff_add _ _ _ hz, coeff_shift]
  have h2i : i < n + n := by omega
  have hzero : (Zero.zero : R) = 0 := rfl
  simp only [hzero]
  simp [hi, h2i]
  grind

/-- Prefix-pruned Karatsuba slice.  Coefficients of either operand above the
exclusive end of the requested interval cannot contribute, so they are
removed before the recursive product.  Unlike the former schoolbook fallback,
this retains Karatsuba recursion for every requested interval. -/
def karatsubaSlice (cutoff lo len : Nat) (a b : DensePoly R) : DensePoly R :=
  let hi := lo + len
  coeffSlice lo len
    (mulKaratsuba cutoff (low hi a) (low hi b))

/-- Prefix-pruned Karatsuba slicing has the exact planned-slice semantics. -/
theorem coeff_karatsubaSlice (cutoff lo len : Nat) (a b : DensePoly R)
    (i : Nat) :
    (karatsubaSlice cutoff lo len a b).coeff i =
      if i < len then (a * b).coeff (lo + i) else 0 := by
  unfold karatsubaSlice
  rw [coeff_coeffSlice]
  split <;> rename_i hi
  · rw [mulKaratsuba_eq]
    exact coeff_low_mul_low (lo + len) a b (lo + i) (by omega)
  · rfl

/-- A lawful Karatsuba plan. -/
def karatsubaPlan (cutoff : Nat) : MulPlan R where
  mul := mulKaratsuba cutoff
  square := squareKaratsuba cutoff
  slice := karatsubaSlice cutoff
  mul_eq := mulKaratsuba_eq cutoff
  square_eq := squareKaratsuba_eq cutoff
  coeff_slice := coeff_karatsubaSlice cutoff

end Hex.DensePoly
