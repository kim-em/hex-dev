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

private theorem four_mul_le_square_add (a b : Nat) :
    4 * (a * b) ≤ (a + b) ^ 2 := by
  by_cases h : a ≤ b
  · rcases Nat.exists_eq_add_of_le h with ⟨d, rfl⟩
    simp [Nat.pow_two]
    grind
  · have hba : b ≤ a := by omega
    rcases Nat.exists_eq_add_of_le hba with ⟨d, rfl⟩
    simp [Nat.pow_two]
    grind

private theorem mul_succ_le_midpoint_succ_sq (x q : Nat) :
    x * (q + 1) ≤ ((x + q) / 2 + 1) ^ 2 := by
  let a := (x + q) / 2 + 1
  have hmid : x + q + 1 ≤ 2 * a := by
    dsimp [a]
    omega
  have hamgm : 4 * (x * (q + 1)) ≤ (x + q + 1) ^ 2 := by
    simpa [Nat.add_assoc] using four_mul_le_square_add x (q + 1)
  have hsquare : (x + q + 1) ^ 2 ≤ (2 * a) ^ 2 := by
    exact Nat.pow_le_pow_left hmid 2
  have h4 : 4 * (x * (q + 1)) ≤ 4 * (a ^ 2) := by
    calc
      4 * (x * (q + 1)) ≤ (x + q + 1) ^ 2 := hamgm
      _ ≤ (2 * a) ^ 2 := hsquare
      _ = 4 * (a ^ 2) := by
          simp [Nat.pow_two]
          grind
  have hcancel := Nat.le_of_mul_le_mul_left h4 (by decide : 0 < 4)
  simpa [a] using hcancel

private theorem sqrtStep_upper_succ
    (n x : Nat) (hx : 0 < x) (_h : n ≤ (x + 1) ^ 2) :
    n ≤ (sqrtStep n x + 1) ^ 2 := by
  let q := n / x
  have hn_le : n ≤ x * (q + 1) := by
    calc
      n = x * q + n % x := by
        simpa [q] using (Nat.div_add_mod n x).symm
      _ ≤ x * q + x := Nat.add_le_add_left (Nat.le_of_lt (Nat.mod_lt n hx)) (x * q)
      _ = x * (q + 1) := by grind
  exact Nat.le_trans hn_le
    (by simpa [sqrtStep, q] using mul_succ_le_midpoint_succ_sq x q)

private theorem sqrtAux_upper_succ_core
    (n fuel x : Nat) (h : n ≤ (x + 1) ^ 2) :
    n ≤ (sqrtAux n fuel x + 1) ^ 2 := by
  induction fuel generalizing x with
  | zero =>
      simpa [sqrtAux] using h
  | succ fuel ih =>
      by_cases hx : 0 < x
      · unfold sqrtAux
        let next := sqrtStep n x
        by_cases hnext : next ≥ x
        · simp [next, hnext]
          exact h
        · simp [next, hnext]
          exact ih next (sqrtStep_upper_succ n x hx h)
      · have hxzero : x = 0 := by omega
        subst x
        simp [sqrtAux, sqrtStep]
        exact h

private theorem sqrtAux_upper_succ
    (n fuel x : Nat) (_hx : 0 < x) (h : n ≤ (x + 1) ^ 2) :
    n ≤ (sqrtAux n fuel x + 1) ^ 2 :=
  sqrtAux_upper_succ_core n fuel x h

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

/--
The square of `ceilSqrt n` is at least `n`.  This is the executable upper-square
bound used by the Mignotte coefficient norm chain: in the perfect-square branch
of `ceilSqrt`, equality holds; in the non-perfect-square branch, the bound
follows from the Newton iterator invariant `sqrtAux_upper_succ`.
-/
theorem le_ceilSqrt_sq (n : Nat) : n ≤ (ceilSqrt n) ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    simp
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hfloor : floorSqrt n = sqrtAux n (2 * n.log2 + 1) n := by
      unfold floorSqrt
      rw [if_neg hn]
    have hinit : n ≤ (n + 1) ^ 2 := by
      simp [Nat.pow_two]
      grind
    have hub : n ≤ (floorSqrt n + 1) ^ 2 := by
      rw [hfloor]
      exact sqrtAux_upper_succ n (2 * n.log2 + 1) n hn_pos hinit
    unfold ceilSqrt
    by_cases hsq : floorSqrt n * floorSqrt n = n
    · rw [if_pos hsq, Nat.pow_two]
      omega
    · rw [if_neg hsq]
      exact hub

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

@[simp] theorem defaultFactorCoeffBound_zero :
    defaultFactorCoeffBound (0 : ZPoly) = 0 := by
  unfold defaultFactorCoeffBound
  have hignore :
      ∀ (xs : List Nat) (init : Nat),
        xs.foldl (fun acc _ => acc) init = init := by
    intro xs
    induction xs with
    | nil =>
        intro init
        rfl
    | cons _ xs ih =>
        intro init
        simp [ih]
  have hfold :
      ∀ (ks : List Nat) (init : Nat),
        ks.foldl
          (fun acc k =>
            (List.range (k + 1)).foldl
              (fun acc j => max acc (mignotteCoeffBound (0 : ZPoly) k j))
              acc)
          init = init := by
    intro ks
    induction ks with
    | nil =>
        intro init
        rfl
    | cons k ks ih =>
        intro init
        simp [mignotteCoeffBound_zero, hignore]
  exact hfold (List.range (((0 : ZPoly).degree?).getD 0 + 1)) 0

theorem mignotteCoeffBound_eq_zero_of_lt (f : ZPoly) (k j : Nat) (h : k < j) :
    mignotteCoeffBound f k j = 0 := by
  simp [mignotteCoeffBound, binom_eq_zero_of_lt h]

private theorem le_foldl_max_left {α : Type} (xs : List α) (g : α → Nat) (init : Nat) :
    init ≤ xs.foldl (fun acc x => max acc (g x)) init := by
  induction xs generalizing init with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left init (g x)) (ih (max init (g x)))

private theorem le_foldl_max_of_mem {α : Type} (xs : List α) (g : α → Nat)
    {x : α} {init : Nat} (hx : x ∈ xs) :
    g x ≤ xs.foldl (fun acc y => max acc (g y)) init := by
  induction xs generalizing init with
  | nil =>
      cases hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      simp only [List.foldl_cons]
      cases hx with
      | inl h =>
          rw [h]
          exact Nat.le_trans (Nat.le_max_right init (g y))
            (le_foldl_max_left ys g (max init (g y)))
      | inr h =>
          exact ih h

private theorem mignotteCoeffBound_le_degree_innerFold
    (f : ZPoly) (k : Nat) {j init : Nat} (hj : j ≤ k) :
    mignotteCoeffBound f k j ≤
      (List.range (k + 1)).foldl
        (fun acc j => max acc (mignotteCoeffBound f k j))
        init := by
  exact le_foldl_max_of_mem (List.range (k + 1))
    (fun j => mignotteCoeffBound f k j)
    (List.mem_range.mpr (Nat.lt_succ_of_le hj))

private theorem defaultFactorCoeffBound_outerFold_preserves
    (f : ZPoly) (ks : List Nat) (init : Nat) :
    init ≤
      ks.foldl
        (fun acc k =>
          (List.range (k + 1)).foldl
            (fun acc j => max acc (mignotteCoeffBound f k j))
            acc)
        init := by
  induction ks generalizing init with
  | nil =>
      simp
  | cons k ks ih =>
      simp only [List.foldl_cons]
      exact Nat.le_trans
        (le_foldl_max_left (List.range (k + 1))
          (fun j => mignotteCoeffBound f k j) init)
        (ih ((List.range (k + 1)).foldl
          (fun acc j => max acc (mignotteCoeffBound f k j)) init))

private theorem mignotteCoeffBound_le_defaultFactorCoeffBound_fold
    (f : ZPoly) (ks : List Nat) {k j init : Nat} (hk : k ∈ ks) (hj : j ≤ k) :
    mignotteCoeffBound f k j ≤
      ks.foldl
        (fun acc k =>
          (List.range (k + 1)).foldl
            (fun acc j => max acc (mignotteCoeffBound f k j))
            acc)
        init := by
  induction ks generalizing init with
  | nil =>
      cases hk
  | cons k' ks ih =>
      simp only [List.mem_cons] at hk
      simp only [List.foldl_cons]
      cases hk with
      | inl h =>
          subst h
          exact Nat.le_trans
            (mignotteCoeffBound_le_degree_innerFold f k (j := j) (init := init) hj)
            (defaultFactorCoeffBound_outerFold_preserves f ks
              ((List.range (k + 1)).foldl
                (fun acc j => max acc (mignotteCoeffBound f k j)) init))
      | inr h =>
          exact ih h

/--
Every executable Mignotte coefficient bound within the ambient degree range is
bounded by the default uniform factorization bound.
-/
theorem mignotteCoeffBound_le_defaultFactorCoeffBound
    (f : ZPoly) {k j : Nat} (hk : k ≤ f.degree?.getD 0) (hj : j ≤ k) :
    mignotteCoeffBound f k j ≤ defaultFactorCoeffBound f := by
  unfold defaultFactorCoeffBound
  exact mignotteCoeffBound_le_defaultFactorCoeffBound_fold f
    (List.range (f.degree?.getD 0 + 1))
    (List.mem_range.mpr (Nat.lt_succ_of_le hk)) hj

theorem coeffL2NormBound_le_defaultFactorCoeffBound (f : ZPoly) :
    coeffL2NormBound f ≤ defaultFactorCoeffBound f := by
  simpa [mignotteCoeffBound] using
    (mignotteCoeffBound_le_defaultFactorCoeffBound f
      (k := 0) (j := 0) (Nat.zero_le _) (Nat.zero_le _))

/-- An additive natural-number `foldl` only increases (or preserves) its
accumulator. -/
private theorem le_foldl_add_self {α : Type} (xs : List α) (g : α → Nat)
    (init : Nat) :
    init ≤ xs.foldl (fun acc y => acc + g y) init := by
  induction xs generalizing init with
  | nil => simp
  | cons y ys ih =>
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_add_right init (g y)) (ih (init + g y))

/-- For an additive natural-number `foldl`, each summand at a member index is
bounded by the result. -/
private theorem le_foldl_add_of_mem {α : Type} (xs : List α) (g : α → Nat)
    {x : α} {init : Nat} (hx : x ∈ xs) :
    g x ≤ xs.foldl (fun acc y => acc + g y) init := by
  induction xs generalizing init with
  | nil => cases hx
  | cons head tail ih =>
      simp only [List.mem_cons] at hx
      simp only [List.foldl_cons]
      cases hx with
      | inl h =>
          subst h
          exact Nat.le_trans (Nat.le_add_left (g x) init)
            (le_foldl_add_self tail g (init + g x))
      | inr h => exact ih h

/-- The ceiling square root is positive on positive inputs. -/
private theorem ceilSqrt_pos_of_pos {n : Nat} (hn : 0 < n) :
    0 < ceilSqrt n := by
  have h : n ≤ (ceilSqrt n) ^ 2 := le_ceilSqrt_sq n
  by_cases hpos : 0 < ceilSqrt n
  · exact hpos
  · exfalso
    have hsq : ceilSqrt n = 0 := by omega
    rw [hsq, Nat.pow_two, Nat.zero_mul] at h
    omega

/-- A nonzero integer polynomial has positive squared Euclidean coefficient
norm: the last stored coefficient is nonzero and contributes a positive
summand to the fold. -/
theorem coeffNormSq_pos_of_ne_zero {f : ZPoly} (hf : f ≠ 0) :
    0 < coeffNormSq f := by
  have hsize : 0 < f.size := size_pos_of_ne_zero f hf
  have hi_lt : f.size - 1 < f.size := by omega
  have hi_mem : f.size - 1 ∈ List.range f.size := List.mem_range.mpr hi_lt
  have hcoeff_ne : f.coeff (f.size - 1) ≠ 0 :=
    DensePoly.coeff_last_ne_zero_of_pos_size f hsize
  have hnatabs : 0 < (f.coeff (f.size - 1)).natAbs :=
    Nat.pos_of_ne_zero (fun h => hcoeff_ne (Int.natAbs_eq_zero.mp h))
  have hsq_pos : 0 < (f.coeff (f.size - 1)).natAbs ^ 2 := by
    rw [Nat.pow_two]; exact Nat.mul_pos hnatabs hnatabs
  unfold coeffNormSq
  exact Nat.lt_of_lt_of_le hsq_pos
    (le_foldl_add_of_mem (List.range f.size)
      (fun i => (f.coeff i).natAbs ^ 2) hi_mem)

/-- A nonzero integer polynomial has positive conservative Euclidean
coefficient-norm upper bound. -/
theorem coeffL2NormBound_pos_of_ne_zero {f : ZPoly} (hf : f ≠ 0) :
    0 < coeffL2NormBound f := by
  unfold coeffL2NormBound
  exact ceilSqrt_pos_of_pos (coeffNormSq_pos_of_ne_zero hf)

/--
A nonzero integer polynomial has positive uniform default factor coefficient
bound.

This is the Mignotte-side fact downstream callers need to derive
`B ≠ 0` and the precision-modulus invariant `2 ≤ p ^ precisionForCoeffBound B p`
from `f ≠ 0` alone (combined with the standard `p ≥ 2` provenance from
the selected-prime primality lemma and `precisionForCoeffBound_spec`).
-/
theorem defaultFactorCoeffBound_pos_of_ne_zero {f : ZPoly} (hf : f ≠ 0) :
    0 < defaultFactorCoeffBound f :=
  Nat.lt_of_lt_of_le (coeffL2NormBound_pos_of_ne_zero hf)
    (coeffL2NormBound_le_defaultFactorCoeffBound f)

end ZPoly
end Hex
