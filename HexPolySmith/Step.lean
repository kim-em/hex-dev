/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolySmith.Contracts
public import HexPolySmith.ExactDiv

public section

/-!
The monic-normalising two-row step used by polynomial Smith reduction.

The all-zero input is handled separately: applying the displayed Bezout
formula there would produce a zero forward matrix because `0⁻¹ = 0`.
-/

namespace Hex.PolyMatrix

universe u

open Hex

/-- A two-row Bezout operation, its explicit inverse, and the resulting monic
pivot. The pivot is zero exactly on the `(0, 0)` branch. -/
structure PairStep (F : Type u) [Zero F] [DecidableEq F] where
  pivot : DensePoly F
  forward : Matrix (DensePoly F) 2 2
  inverse : Matrix (DensePoly F) 2 2

/-- The executable polynomial identity of order two. This is written with
`DensePoly.C` rather than the proof-oriented polynomial numeral instance, so
the step remains usable by the native evaluator. -/
@[expose]
def pairIdentity {F : Type u} [Lean.Grind.Field F] [DecidableEq F] :
    Matrix (DensePoly F) 2 2 :=
  let z : DensePoly F := Zero.zero
  let o : DensePoly F := DensePoly.C (One.one : F)
  #m[o, z; z, o]

def pairForward {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    (u : F) (s t qa qb : DensePoly F) : Matrix (DensePoly F) 2 2 :=
  #m[DensePoly.scale u s, DensePoly.scale u t;
     Zero.zero - DensePoly.scale u qb, DensePoly.scale u qa]

def pairInverse {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    (s t qa qb : DensePoly F) : Matrix (DensePoly F) 2 2 :=
  #m[qa, Zero.zero - t; qb, s]

/-- The monic-normalising Bezout step. Every polynomial quotient in the two
matrices is an exact quotient by the monic `pivot`. -/
@[expose]
def pairStep {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    (a b : DensePoly F) : PairStep F :=
  if a = Zero.zero ∧ b = Zero.zero then
    { pivot := Zero.zero
      forward := pairIdentity
      inverse := pairIdentity }
  else
    let x := DensePoly.xgcd a b
    let u := 1 / x.gcd.leadingCoeff
    let g := DensePoly.monicize x.gcd
    let qa := Hex.exactDiv a g
    let qb := Hex.exactDiv b g
    { pivot := g
      forward :=
        pairForward u x.left x.right qa qb
      inverse := pairInverse x.left x.right qa qb }

/-- Applying a two-by-two matrix to a pair, without routing executable code
through the proof-oriented matrix multiplication definition. -/
@[expose]
def applyPair {R : Type u} [Zero R] [Add R] [Mul R]
    (E : Matrix R 2 2) (a b : R) : R × R :=
  (E[((0 : Fin 2), (0 : Fin 2))] * a + E[((0 : Fin 2), (1 : Fin 2))] * b,
   E[((1 : Fin 2), (0 : Fin 2))] * a + E[((1 : Fin 2), (1 : Fin 2))] * b)

private theorem xgcdGcd_ne_zero {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {a b : DensePoly F} (h : ¬ (a = 0 ∧ b = 0)) :
    (DensePoly.xgcd a b).gcd ≠ 0 := by
  let x := DensePoly.xgcd a b
  have ha : x.gcd ∣ a := by
    rw [DensePoly.xgcd_gcd_eq_gcd]
    exact DensePoly.gcd_dvd_left a b
  have hb : x.gcd ∣ b := by
    rw [DensePoly.xgcd_gcd_eq_gcd]
    exact DensePoly.gcd_dvd_right a b
  intro hx
  apply h
  constructor
  · rcases ha with ⟨q, hq⟩
    rw [hx, DensePoly.zero_mul] at hq
    exact hq
  · rcases hb with ⟨q, hq⟩
    rw [hx, DensePoly.zero_mul] at hq
    exact hq

/-- The pivot produced by the pair step is zero only on the all-zero branch;
otherwise it is monic. -/
theorem pairStep_pivot_shape {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    (a b : DensePoly F) :
    (pairStep a b).pivot = 0 ∨ (pairStep a b).pivot.Monic := by
  unfold pairStep
  split
  case isTrue => exact Or.inl rfl
  case isFalse h => exact Or.inr (DensePoly.monic_monicize (xgcdGcd_ne_zero h))

/-- A pair step with a nonzero left input has a nonzero pivot. -/
theorem pairStep_pivot_ne_zero_left {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {a b : DensePoly F} (ha : a ≠ 0) :
    (pairStep a b).pivot ≠ 0 := by
  unfold pairStep
  split
  case isTrue h => exact False.elim (ha h.1)
  case isFalse h => exact DensePoly.monicize_ne_zero (xgcdGcd_ne_zero h)

/-- On the nondivisible branch, a pair step strictly lowers the pivot size. -/
theorem pairStep_pivot_size_lt_left {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {a b : DensePoly F} (ha : a ≠ 0) (hab : ¬a ∣ b) :
    (pairStep a b).pivot.size < a.size := by
  unfold pairStep
  split
  case isTrue h => exact False.elim (ha h.1)
  case isFalse =>
    change (DensePoly.monicize (DensePoly.xgcd a b).gcd).size < a.size
    rw [DensePoly.xgcd_gcd_eq_gcd]
    exact DensePoly.monicize_gcd_size_lt_left a b ha hab

/-- The forward Bezout matrix sends the input pair to its monic gcd and zero. -/
theorem pairStep_apply {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    (a b : DensePoly F) :
    applyPair (pairStep a b).forward a b = ((pairStep a b).pivot, 0) := by
  unfold pairStep
  split
  case isTrue h =>
    rcases h with ⟨rfl, rfl⟩
    change
      (DensePoly.C (1 : F) * (0 : DensePoly F) + 0 * 0,
        (0 : DensePoly F) * 0 + DensePoly.C (1 : F) * 0) = (0, 0)
    grind
  case isFalse h =>
    let x := DensePoly.xgcd a b
    let u := 1 / x.gcd.leadingCoeff
    let g := DensePoly.monicize x.gcd
    let qa := Hex.exactDiv a g
    let qb := Hex.exactDiv b g
    have hx : x.gcd ≠ 0 := xgcdGcd_ne_zero h
    have hg : g ≠ 0 := DensePoly.monicize_ne_zero hx
    have hga : g ∣ a := by
      apply DensePoly.monicize_dvd_of_dvd hx
      rw [DensePoly.xgcd_gcd_eq_gcd]
      exact DensePoly.gcd_dvd_left a b
    have hgb : g ∣ b := by
      apply DensePoly.monicize_dvd_of_dvd hx
      rw [DensePoly.xgcd_gcd_eq_gcd]
      exact DensePoly.gcd_dvd_right a b
    have ha : qa * g = a := DensePoly.exactDiv_mul_eq_of_dvd a g hg hga
    have hb : qb * g = b := DensePoly.exactDiv_mul_eq_of_dvd b g hg hgb
    have hbez : x.left * a + x.right * b = x.gcd := by
      simpa [x] using DensePoly.xgcd_bezout a b
    have hcross : DensePoly.scale u qb * qa = DensePoly.scale u qa * qb := by
      rw [← DensePoly.scale_mul, ← DensePoly.scale_mul,
        DensePoly.mul_comm_poly qb qa]
    apply Prod.ext
    · change DensePoly.scale u x.left * a + DensePoly.scale u x.right * b = g
      rw [← DensePoly.scale_mul, ← DensePoly.scale_mul,
        ← DensePoly.scale_add, hbez]
      unfold u g
      rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.one_mul,
        DensePoly.scale_inv_eq_monicize hx]
    · change (0 - DensePoly.scale u qb) * a + DensePoly.scale u qa * b = 0
      rw [← ha, ← hb]
      grind

private theorem finTwo_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  by_cases hi : i.val = 0
  · left
    exact Fin.ext hi
  · right
    apply Fin.ext
    omega

private theorem finRange_two : List.finRange 2 = [0, 1] := rfl

private theorem row_ofFn {R : Type u} {n m : Nat} (f : Fin n → Fin m → R)
    (i : Fin n) :
    Matrix.row (Matrix.ofFn f) i = Vector.ofFn fun j => f i j := by
  ext j hj
  let jj : Fin m := ⟨j, hj⟩
  show (Matrix.row (Matrix.ofFn f) i)[jj] = (Vector.ofFn fun j => f i j)[jj]
  rw [Matrix.getElem_row, Matrix.getElem_ofFn]
  simp

private theorem col_ofFn {R : Type u} {n m : Nat} (f : Fin n → Fin m → R)
    (j : Fin m) :
    Matrix.col (Matrix.ofFn f) j = Vector.ofFn fun i => f i j := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  show (Matrix.col (Matrix.ofFn f) j)[ii] = (Vector.ofFn fun i => f i j)[ii]
  rw [Matrix.getElem_col, Matrix.getElem_ofFn]
  simp

private theorem pairIdentity_eq_identity {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] :
    (pairIdentity (F := F)) = Matrix.identity 2 := by
  apply Matrix.ext_getElem
  intro i j
  rcases finTwo_cases i with rfl | rfl <;>
    rcases finTwo_cases j with rfl | rfl <;> rfl

private theorem negRight_cancel {R : Type u} [Lean.Grind.CommRing R]
    {a b c d : R} (h : a * b = c * d) : a * (0 - b) + c * d = 0 := by
  grind

private theorem negLeft_cancel {R : Type u} [Lean.Grind.CommRing R]
    {a b c d : R} (h : a * b = c * d) : (0 - a) * b + c * d = 0 := by
  grind

private theorem negMul_negMul {R : Type u} [Lean.Grind.CommRing R]
    (a b : R) : (0 - a) * (0 - b) = a * b := by
  grind

private theorem add_swap_eq_one {R : Type u} [Lean.Grind.CommRing R]
    {a b : R} (h : a + b = 1) : b + a = 1 := by
  grind

private theorem polyZero_eq_zero {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] : (Zero.zero : DensePoly F) = 0 := rfl

private theorem scaleMul_comm {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    (u : F) (p q : DensePoly F) :
    DensePoly.scale u p * q = DensePoly.scale u q * p := by
  rw [← DensePoly.scale_mul, ← DensePoly.scale_mul, DensePoly.mul_comm_poly p q]

private theorem pairMatrices_forward_inverse {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] (u : F) (s t qa qb : DensePoly F)
    (hsum : DensePoly.scale u s * qa + DensePoly.scale u t * qb = 1) :
    pairForward u s t qa qb * pairInverse s t qa qb = Matrix.identity 2 := by
  have hst : DensePoly.scale u s * t = DensePoly.scale u t * s :=
    scaleMul_comm u s t
  have hq : DensePoly.scale u qb * qa = DensePoly.scale u qa * qb :=
    scaleMul_comm u qb qa
  apply Matrix.ext_getElem
  intro i j
  rcases finTwo_cases i with rfl | rfl <;>
    rcases finTwo_cases j with rfl | rfl
  all_goals rw [Matrix.getElem_identity, Matrix.getElem_mul]
  · simpa [pairForward, pairInverse, polyZero_eq_zero, Vector.dotProduct, finRange_two, row_ofFn, col_ofFn,
      Matrix.row_identity,
      Matrix.getElem_col, Matrix.getElem_ofFn, Matrix.getElem_identity,
      Matrix.getElem_pair_eq_nested] using hsum
  · simpa [pairForward, pairInverse, polyZero_eq_zero, Vector.dotProduct, finRange_two, row_ofFn, col_ofFn,
      Matrix.row_identity,
      Matrix.getElem_col, Matrix.getElem_ofFn, Matrix.getElem_identity,
      Matrix.getElem_pair_eq_nested] using
      (negRight_cancel hst)
  · simpa [pairForward, pairInverse, polyZero_eq_zero, Vector.dotProduct, finRange_two, row_ofFn, col_ofFn,
      Matrix.row_identity,
      Matrix.getElem_col, Matrix.getElem_ofFn, Matrix.getElem_identity,
      Matrix.getElem_pair_eq_nested] using
      (negLeft_cancel hq)
  · have hlast : (0 - DensePoly.scale u qb) * (0 - t) +
        DensePoly.scale u qa * s = 1 := by
      rw [negMul_negMul, scaleMul_comm u qb t, scaleMul_comm u qa s]
      exact add_swap_eq_one hsum
    simpa [pairForward, pairInverse, polyZero_eq_zero, Vector.dotProduct, finRange_two, row_ofFn, col_ofFn,
      Matrix.row_identity,
      Matrix.getElem_col, Matrix.getElem_ofFn, Matrix.getElem_identity,
      Matrix.getElem_pair_eq_nested] using hlast

/-- The displayed inverse really is a right inverse of the forward Bezout
matrix, including the leading-coefficient normalization. -/
theorem pairStep_forward_inverse {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] (a b : DensePoly F) :
    (pairStep a b).forward * (pairStep a b).inverse = Matrix.identity 2 := by
  unfold pairStep
  split
  case isTrue =>
    change pairIdentity * pairIdentity = Matrix.identity 2
    rw [pairIdentity_eq_identity, Matrix.identity_mul]
  case isFalse h =>
    let x := DensePoly.xgcd a b
    let u := 1 / x.gcd.leadingCoeff
    let g := DensePoly.monicize x.gcd
    let qa := Hex.exactDiv a g
    let qb := Hex.exactDiv b g
    have hx : x.gcd ≠ 0 := xgcdGcd_ne_zero h
    have hg : g ≠ 0 := DensePoly.monicize_ne_zero hx
    have hga : g ∣ a := by
      apply DensePoly.monicize_dvd_of_dvd hx
      rw [DensePoly.xgcd_gcd_eq_gcd]
      exact DensePoly.gcd_dvd_left a b
    have hgb : g ∣ b := by
      apply DensePoly.monicize_dvd_of_dvd hx
      rw [DensePoly.xgcd_gcd_eq_gcd]
      exact DensePoly.gcd_dvd_right a b
    have ha : qa * g = a := DensePoly.exactDiv_mul_eq_of_dvd a g hg hga
    have hb : qb * g = b := DensePoly.exactDiv_mul_eq_of_dvd b g hg hgb
    have hbez : x.left * a + x.right * b = x.gcd := by
      simpa [x] using DensePoly.xgcd_bezout a b
    have hfactor : (x.left * qa + x.right * qb) * g = x.gcd := by
      rw [DensePoly.mul_add_left_poly, DensePoly.mul_assoc_poly,
        DensePoly.mul_assoc_poly, ha, hb]
      exact hbez
    have hscaled := congrArg (DensePoly.scale u) hfactor
    have hscale : DensePoly.scale u x.gcd = g := by
      unfold u g
      rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.one_mul,
        DensePoly.scale_inv_eq_monicize hx]
    rw [hscale] at hscaled
    have hsum : DensePoly.scale u x.left * qa + DensePoly.scale u x.right * qb = 1 := by
      apply Hex.ExactDivLaws.mul_right_cancel hg
      rw [Lean.Grind.Semiring.one_mul]
      rw [← DensePoly.scale_mul, ← DensePoly.scale_mul,
        ← DensePoly.scale_add, ← DensePoly.scale_mul]
      exact hscaled
    exact pairMatrices_forward_inverse u x.left x.right qa qb hsum

/-- The explicit inverse is also a left inverse. -/
theorem pairStep_inverse_forward {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] (a b : DensePoly F) :
    (pairStep a b).inverse * (pairStep a b).forward = Matrix.identity 2 :=
  Matrix.mul_eq_one_comm (pairStep_forward_inverse a b)

/-! Executable regression checks. These deliberately include non-monic gcds:
they detect either a missing factor of `u` or an erroneous factor in the
inverse, errors that monic-only examples cannot see. -/

private def ratPoly (xs : List Rat) : DensePoly Rat := DensePoly.ofList xs

private def pairStepChecks (a b : DensePoly Rat) : Bool :=
  let e := pairStep a b
  let z : DensePoly Rat := Zero.zero
  let o : DensePoly Rat := ratPoly [1]
  applyPair e.forward a b == (e.pivot, Zero.zero)
    && applyPair e.forward (applyPair e.inverse o z).1
      (applyPair e.inverse o z).2 == (o, z)
    && applyPair e.forward (applyPair e.inverse z o).1
      (applyPair e.inverse z o).2 == (z, o)
    && applyPair e.inverse (applyPair e.forward o z).1
      (applyPair e.forward o z).2 == (o, z)
    && applyPair e.inverse (applyPair e.forward z o).1
      (applyPair e.forward z o).2 == (z, o)

private def pairStepInputs : List (DensePoly Rat × DensePoly Rat) :=
  let x := ratPoly [0, 1]
  let xm1 := ratPoly [-1, 1]
  let xp1 := ratPoly [1, 1]
  [ (ratPoly [2, 4, 2], ratPoly [3, 3]),
    (xm1 * xp1, x * xp1),
    (x * xp1, xm1 * xp1),
    (Zero.zero, xp1), (xp1, Zero.zero), (Zero.zero, Zero.zero),
    (xp1, xp1), (ratPoly [1], xp1), (xp1, ratPoly [1]),
    (xp1, xp1 * x), (xp1 * x, xp1),
    (x, DensePoly.scale 2 x), (DensePoly.scale 2 x, x) ]

#guard pairStepInputs.all fun p => pairStepChecks p.1 p.2

end Hex.PolyMatrix
