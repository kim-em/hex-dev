import HexPolyZ.Basic

/-!
Executable Mignotte-bound helpers for `hex-poly-z`.

This module packages the integer computations that appear in the classical
Mignotte coefficient bound: binomial coefficients together with the Euclidean
norm upper bound of the ambient polynomial's coefficient vector. The
mathematical proof that these quantities bound factors lives in
`HexPolyZMathlib`.
-/
namespace Hex

namespace ZPoly

/-- Executable binomial coefficients for the Mignotte bound. -/
def binom (n k : Nat) : Nat :=
  if n < k then
    0
  else
    let kk := min k (n - k)
    (List.range kk).foldl (fun acc i => acc * (n - i) / (i + 1)) 1

/-- One Newton step for the natural-number square-root iteration. -/
private def sqrtStep (n x : Nat) : Nat :=
  (x + n / x) / 2

/-- A fuel-bounded Newton iteration for the natural floor square root. -/
private def sqrtAux (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x =>
      let next := sqrtStep n x
      if next ≥ x then
        x
      else
        sqrtAux n fuel next

/-- The floor of the square root of `n`. -/
def floorSqrt (n : Nat) : Nat :=
  if n = 0 then
    0
  else
    sqrtAux n (2 * n.log2 + 1) n

/-- The least natural number whose square is at least `n`. -/
def ceilSqrt (n : Nat) : Nat :=
  let r := floorSqrt n
  if r * r = n then
    r
  else
    r + 1

/-- The squared Euclidean norm of the coefficient vector of `f`. -/
def coeffNormSq (f : ZPoly) : Nat :=
  (List.range f.size).foldl (fun acc i => acc + (f.coeff i).natAbs ^ 2) 0

/-- A conservative natural-number upper bound on the Euclidean norm of the
coefficient vector of `f`. -/
def coeffL2NormBound (f : ZPoly) : Nat :=
  ceilSqrt (coeffNormSq f)

/-- The executable Mignotte bound for the `j`-th coefficient of a degree-`k`
factor of `f`, using the conservative `coeffL2NormBound`. -/
def mignotteCoeffBound (f : ZPoly) (k j : Nat) : Nat :=
  binom k j * coeffL2NormBound f

/--
Uniform executable coefficient bound used by the default integer
factorization entry point.

It takes the maximum of the executable Mignotte coefficient bounds over every
candidate factor degree up to `f.degree?.getD 0` and every coefficient index up
to that degree.
-/
def defaultFactorCoeffBound (f : ZPoly) : Nat :=
  let degreeBound := f.degree?.getD 0
  (List.range (degreeBound + 1)).foldl
    (fun acc k =>
      (List.range (k + 1)).foldl
        (fun acc j => max acc (mignotteCoeffBound f k j))
        acc)
    0

@[simp] theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by
  simp [binom]

@[simp] theorem binom_zero_succ (k : Nat) : binom 0 (k + 1) = 0 := by
  simp [binom]

theorem binom_eq_zero_of_lt {n k : Nat} (h : n < k) : binom n k = 0 := by
  simp [binom, h]

@[simp] theorem floorSqrt_zero : floorSqrt 0 = 0 := by
  simp [floorSqrt]

@[simp] theorem ceilSqrt_zero : ceilSqrt 0 = 0 := by
  simp [ceilSqrt]

theorem coeffNormSq_eq_sum (f : ZPoly) :
    coeffNormSq f =
      (List.range f.size).foldl (fun acc i => acc + (f.coeff i).natAbs ^ 2) 0 := rfl

theorem coeffL2NormBound_eq_ceilSqrt_coeffNormSq (f : ZPoly) :
    coeffL2NormBound f = ceilSqrt (coeffNormSq f) := rfl

theorem mignotteCoeffBound_eq (f : ZPoly) (k j : Nat) :
    mignotteCoeffBound f k j = binom k j * coeffL2NormBound f := rfl

theorem defaultFactorCoeffBound_eq (f : ZPoly) :
    defaultFactorCoeffBound f =
      let degreeBound := f.degree?.getD 0
      (List.range (degreeBound + 1)).foldl
        (fun acc k =>
          (List.range (k + 1)).foldl
            (fun acc j => max acc (mignotteCoeffBound f k j))
            acc)
        0 := rfl

@[simp] theorem coeffNormSq_zero : coeffNormSq (0 : ZPoly) = 0 := by
  rfl

@[simp] theorem coeffL2NormBound_zero : coeffL2NormBound (0 : ZPoly) = 0 := by
  simp [coeffL2NormBound]

@[simp] theorem mignotteCoeffBound_zero (k j : Nat) :
    mignotteCoeffBound (0 : ZPoly) k j = 0 := by
  simp [mignotteCoeffBound]

theorem mignotteCoeffBound_eq_zero_of_lt (f : ZPoly) (k j : Nat) (h : k < j) :
    mignotteCoeffBound f k j = 0 := by
  simp [mignotteCoeffBound, binom_eq_zero_of_lt h]

/--
Every executable Mignotte coefficient bound within the ambient degree range is
bounded by the default uniform factorization bound.
-/
theorem mignotteCoeffBound_le_defaultFactorCoeffBound
    (f : ZPoly) {k j : Nat} (hk : k ≤ f.degree?.getD 0) (hj : j ≤ k) :
    mignotteCoeffBound f k j ≤ defaultFactorCoeffBound f := by
  sorry

end ZPoly
end Hex
