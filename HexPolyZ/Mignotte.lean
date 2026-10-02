/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic
public import HexArith.Nat.Sqrt
import all HexArith.Nat.Sqrt
public import HexPolyZ.Decomposition

public section

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

/-- Compatibility name for the arithmetic floor square root. -/
abbrev floorSqrt := HexArith.Nat.floorSqrt

/-- Compatibility name for the arithmetic ceiling square root. -/
abbrev ceilSqrt := HexArith.Nat.ceilSqrt

/-- The squared Euclidean norm of the coefficient vector of `f`. -/
@[expose]
def coeffNormSq (f : ZPoly) : Nat :=
  (List.range f.size).foldl (fun acc i => acc + (f.coeff i).natAbs ^ 2) 0

/-- A conservative natural-number upper bound on the Euclidean norm of the
coefficient vector of `f`. -/
@[expose]
def coeffL2NormBound (f : ZPoly) : Nat :=
  ceilSqrt (coeffNormSq f)

/-- The executable Mignotte bound for the `j`-th coefficient of a degree-`k`
factor of `f`, using the conservative
{name}`Hex.ZPoly.coeffL2NormBound`. -/
@[expose]
def mignotteCoeffBound (f : ZPoly) (k j : Nat) : Nat :=
  Nat.binom k j * coeffL2NormBound f

/--
Uniform executable coefficient bound used by the default integer
factorization entry point.

It takes the maximum of the executable Mignotte coefficient bounds over every
candidate factor degree up to `f.natDegree` and every coefficient index up
to that degree.

The compiled runtime uses the value-equal closed form below, registered through
`@[csimp]`, which computes the loop-invariant
{name}`Hex.ZPoly.coeffL2NormBound` once instead of recomputing the whole bignum
coefficient norm inside every one of the `O(deg^2)` `mignotteCoeffBound` terms.
-/
@[expose]
noncomputable def defaultFactorCoeffBound (f : ZPoly) : Nat :=
  let degreeBound := f.natDegree
  (List.range (degreeBound + 1)).foldl
    (fun acc k =>
      (List.range (k + 1)).foldl
        (fun acc j => max acc (mignotteCoeffBound f k j))
        acc)
    0

/-- The floor square root of zero is zero. -/
@[simp, grind =] theorem floorSqrt_zero : floorSqrt 0 = 0 := HexArith.Nat.floorSqrt_zero

/-- The floor square root has square at most its argument. -/
theorem floorSqrt_sq_le (n : Nat) : floorSqrt n * floorSqrt n ≤ n :=
  HexArith.Nat.floorSqrt_sq_le n

/-- The ceiling square root of zero is zero. -/
@[simp, grind =] theorem ceilSqrt_zero : ceilSqrt 0 = 0 := HexArith.Nat.ceilSqrt_zero

/-- The ceiling square root has square at least its argument. -/
theorem le_ceilSqrt_sq (n : Nat) : n ≤ (ceilSqrt n) ^ 2 :=
  HexArith.Nat.le_ceilSqrt_sq n

/-- Restates `coeffNormSq f` as the explicit `foldl` summing `(f.coeff i).natAbs ^ 2`
over the stored coefficient indices `i < f.size`. -/
theorem coeffNormSq_eq_sum (f : ZPoly) :
    coeffNormSq f =
      (List.range f.size).foldl (fun acc i => acc + (f.coeff i).natAbs ^ 2) 0 := rfl

/-- `coeffL2NormBound f` equals the ceiling square root of the squared coefficient
norm `coeffNormSq f`. -/
theorem coeffL2NormBound_eq_ceilSqrt_coeffNormSq (f : ZPoly) :
    coeffL2NormBound f = ceilSqrt (coeffNormSq f) := rfl

/-- The executable Euclidean-norm bound has square at most twice the exact
squared coefficient norm. -/
theorem coeffL2NormBound_sq_le_two_mul_coeffNormSq (f : ZPoly) :
    (coeffL2NormBound f) ^ 2 ≤ 2 * coeffNormSq f := by
  unfold coeffL2NormBound ceilSqrt HexArith.Nat.ceilSqrt
  change (if floorSqrt (coeffNormSq f) * floorSqrt (coeffNormSq f) = coeffNormSq f
    then floorSqrt (coeffNormSq f) else floorSqrt (coeffNormSq f) + 1) ^ 2 ≤
      2 * coeffNormSq f
  let r := floorSqrt (coeffNormSq f)
  have hr_sq : r * r ≤ coeffNormSq f := by
    dsimp [r]
    exact floorSqrt_sq_le (coeffNormSq f)
  by_cases hsq : r * r = coeffNormSq f
  · rw [ite_eq_left hsq]
    rw [Nat.pow_two]
    have hsq_floor :
        floorSqrt (coeffNormSq f) * floorSqrt (coeffNormSq f) = coeffNormSq f := by
      simpa [r] using hsq
    omega
  · rw [ite_eq_right hsq]
    rw [Nat.pow_two]
    have hr_lt : r * r < coeffNormSq f := Nat.lt_of_le_of_ne hr_sq hsq
    have hsucc_le : r * r + 1 ≤ coeffNormSq f := by omega
    have htwo_r : 2 * r ≤ r * r + 1 := by
      rcases r with _ | _ | r
      · simp
      · simp
      · have htwo_le : 2 ≤ r + 2 := by omega
        have hmul := Nat.mul_le_mul_right (r + 2) htwo_le
        exact Nat.le_trans hmul (Nat.le_succ _)
    have hmain : r * r + 2 * r + 1 ≤ 2 * coeffNormSq f := by omega
    have hsquare : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by grind
    simpa [r, hsquare] using hmain

/-- `mignotteCoeffBound f k j` equals the product `binom k j * coeffL2NormBound f`
of the binomial coefficient and the conservative coefficient-norm bound. -/
theorem mignotteCoeffBound_eq (f : ZPoly) (k j : Nat) :
    mignotteCoeffBound f k j = Nat.binom k j * coeffL2NormBound f := rfl

/-- Restates `defaultFactorCoeffBound f` as the nested `foldl` taking the maximum of
`mignotteCoeffBound f k j` over factor degrees `k` up to `f.natDegree` and
coefficient indices `j` up to `k`. -/
theorem defaultFactorCoeffBound_eq (f : ZPoly) :
    defaultFactorCoeffBound f =
      let degreeBound := f.natDegree
      (List.range (degreeBound + 1)).foldl
        (fun acc k =>
          (List.range (k + 1)).foldl
            (fun acc j => max acc (mignotteCoeffBound f k j))
            acc)
        0 := rfl

/-- The zero polynomial has no stored coefficients, so the empty `foldl`
defining `coeffNormSq` normalizes `coeffNormSq 0` to `0`. -/
@[simp, grind =] theorem coeffNormSq_zero : coeffNormSq (0 : ZPoly) = 0 := by
  rfl

/-- Base case of the coefficient-norm bound: `coeffNormSq 0 = 0` and
`ceilSqrt 0 = 0`, so `coeffL2NormBound 0` normalizes to `0`. -/
@[simp, grind =] theorem coeffL2NormBound_zero : coeffL2NormBound (0 : ZPoly) = 0 := by
  simp [coeffL2NormBound]

/-- Base case of the Mignotte coefficient bound: the conservative norm factor
`coeffL2NormBound 0 = 0` annihilates the product, so `mignotteCoeffBound 0 k j`
normalizes to `0` for every degree `k` and index `j`. -/
@[simp, grind =] theorem mignotteCoeffBound_zero (k j : Nat) :
    mignotteCoeffBound (0 : ZPoly) k j = 0 := by
  simp [mignotteCoeffBound]

/-- Base case of the default factor coefficient bound: every entry of the nested
maximum is `mignotteCoeffBound 0 k j = 0`, so `defaultFactorCoeffBound 0`
normalizes to `0`. -/
@[simp, grind =] theorem defaultFactorCoeffBound_zero :
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
  exact hfold (List.range ((0 : ZPoly).natDegree + 1)) 0

/-- The executable Mignotte coefficient bound `mignotteCoeffBound f k j` vanishes when
the coefficient index `j` exceeds the factor degree `k`. -/
theorem mignotteCoeffBound_eq_zero_of_lt (f : ZPoly) (k j : Nat) (h : k < j) :
    mignotteCoeffBound f k j = 0 := by
  simp [mignotteCoeffBound, Nat.binom_eq_zero_of_lt h]

/-- The inner `max`-fold over `j ∈ range (k+1)` dominates each
`mignotteCoeffBound f k j` at an in-range index, by `le_foldl_max_of_mem`. -/
private theorem mignotteCoeffBound_le_degree_innerFold
    (f : ZPoly) (k : Nat) {j init : Nat} (hj : j ≤ k) :
    mignotteCoeffBound f k j ≤
      (List.range (k + 1)).foldl
        (fun acc j => max acc (mignotteCoeffBound f k j))
        init := by
  exact List.le_foldl_max_of_mem (List.range (k + 1))
    (fun j => mignotteCoeffBound f k j)
    (List.mem_range.mpr (Nat.lt_succ_of_le hj))

/-- The outer degree `max`-fold (each step running the inner `j`-fold) only
increases (or preserves) its accumulator, so the initial value bounds the
result. -/
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
        (List.le_foldl_max_self (List.range (k + 1))
          (fun j => mignotteCoeffBound f k j) init)
        (ih ((List.range (k + 1)).foldl
          (fun acc j => max acc (mignotteCoeffBound f k j)) init))

/-- For any degree `k ∈ ks` and in-range index `j ≤ k`, `mignotteCoeffBound f k j`
is bounded by the full nested degree/index `max`-fold, combining the inner-fold
and outer-fold monotonicity lemmas. -/
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
    (f : ZPoly) {k j : Nat} (hk : k ≤ f.natDegree) (hj : j ≤ k) :
    mignotteCoeffBound f k j ≤ defaultFactorCoeffBound f := by
  unfold defaultFactorCoeffBound
  exact mignotteCoeffBound_le_defaultFactorCoeffBound_fold f
    (List.range (f.natDegree + 1))
    (List.mem_range.mpr (Nat.lt_succ_of_le hk)) hj

/-- The conservative coefficient-norm bound `coeffL2NormBound f` is at most the default
uniform factor coefficient bound `defaultFactorCoeffBound f`. -/
theorem coeffL2NormBound_le_defaultFactorCoeffBound (f : ZPoly) :
    coeffL2NormBound f ≤ defaultFactorCoeffBound f := by
  simpa [mignotteCoeffBound] using
    (mignotteCoeffBound_le_defaultFactorCoeffBound f
      (k := 0) (j := 0) (Nat.zero_le _) (Nat.zero_le _))

/-- A maximizing natural-number `foldl` is bounded above by any value `B` that
dominates the seed and every `g x` at a member index. -/
private theorem foldl_max_le_of_forall {α : Type} (g : α → Nat) (B : Nat) :
    ∀ (xs : List α) (init : Nat), init ≤ B → (∀ x ∈ xs, g x ≤ B) →
      xs.foldl (fun acc x => max acc (g x)) init ≤ B := by
  intro xs
  induction xs with
  | nil => intro init hinit _; exact hinit
  | cons x xs ih =>
      intro init hinit hall
      simp only [List.foldl_cons]
      exact ih (max init (g x))
        (Nat.max_le.mpr ⟨hinit, hall x (List.mem_cons.mpr (Or.inl rfl))⟩)
        (fun y hy => hall y (List.mem_cons.mpr (Or.inr hy)))

/-- Upper-bound companion of `mignotteCoeffBound_le_defaultFactorCoeffBound`: if
every executable Mignotte coefficient bound within the ambient degree range is at
most `B`, then so is the default uniform factor coefficient bound. -/
theorem defaultFactorCoeffBound_le (f : ZPoly) {B : Nat}
    (h : ∀ k, k ≤ f.natDegree → ∀ j, j ≤ k → mignotteCoeffBound f k j ≤ B) :
    defaultFactorCoeffBound f ≤ B := by
  unfold defaultFactorCoeffBound
  have outer : ∀ (ks : List Nat) (init : Nat), init ≤ B →
      (∀ k ∈ ks, ∀ j, j ≤ k → mignotteCoeffBound f k j ≤ B) →
      ks.foldl
        (fun acc k =>
          (List.range (k + 1)).foldl
            (fun acc j => max acc (mignotteCoeffBound f k j)) acc)
        init ≤ B := by
    intro ks
    induction ks with
    | nil => intro init hinit _; exact hinit
    | cons k ks ih =>
        intro init hinit hall
        simp only [List.foldl_cons]
        refine ih _ ?_ (fun k' hk' j hj => hall k' (List.mem_cons.mpr (Or.inr hk')) j hj)
        exact foldl_max_le_of_forall (fun j => mignotteCoeffBound f k j) B
          (List.range (k + 1)) init hinit
          (fun j hj => hall k (List.mem_cons.mpr (Or.inl rfl)) j
            (Nat.lt_succ_iff.mp (List.mem_range.mp hj)))
  exact outer (List.range (f.natDegree + 1)) 0 (Nat.zero_le _)
    (fun k hk j hj => h k (Nat.lt_succ_iff.mp (List.mem_range.mp hk)) j hj)

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
    (List.le_foldl_add_of_mem (List.range f.size)
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

Consequently, `f ≠ 0` gives `B ≠ 0`; together with `p ≥ 2`, it also gives the
precision-modulus lower bound required by coefficient reconstruction.
-/
theorem defaultFactorCoeffBound_pos_of_ne_zero {f : ZPoly} (hf : f ≠ 0) :
    0 < defaultFactorCoeffBound f :=
  Nat.lt_of_lt_of_le (coeffL2NormBound_pos_of_ne_zero hf)
    (coeffL2NormBound_le_defaultFactorCoeffBound f)

/-!
# Closed-form runtime implementation of `defaultFactorCoeffBound`

The specification maxes `binom k j * coeffL2NormBound f` over the whole
`j ≤ k ≤ degree f` rectangle, recomputing the loop-invariant bignum norm
`coeffL2NormBound f` inside every one of the `O(deg^2)` terms. Because
`binom k j` peaks at the central binomial `binom n (n / 2)` (`n = degree f`),
the entire double max collapses to `binom n (n / 2) * coeffL2NormBound f`; one
norm, one binomial. The correspondence to the Mathlib-free Pascal `Hex.Nat.choose`
supplies the monotonicity needed to prove the collapse; the compiled runtime
then runs the closed form via a `@[csimp]` swap.
-/

/-- The binomial coefficient over the factor rectangle `j ≤ k ≤ n` is dominated
by the central binomial of the top row: `binom k j ≤ binom n (n / 2)`. This is the
monotonicity that collapses the `defaultFactorCoeffBound` double max. -/
theorem binom_le_central {n k j : Nat} (hjk : j ≤ k) (hkn : k ≤ n) :
    Nat.binom k j ≤ Nat.binom n (n / 2) := by
  rw [Nat.binom_eq_choose, Nat.binom_eq_choose]
  -- reduce `j` to the left-half index `j' = min j (k - j)`
  have hbjk : Hex.Nat.choose k j = Hex.Nat.choose k (min j (k - j)) := by
    rcases Nat.le_total j (k - j) with hle | hle
    · rw [Nat.min_eq_left hle]
    · rw [Nat.min_eq_right hle]; exact (Hex.Nat.choose_symm hjk).symm
  have h2j' : 2 * min j (k - j) ≤ k := by
    rcases Nat.le_total j (k - j) with hle | hle
    · rw [Nat.min_eq_left hle]; omega
    · rw [Nat.min_eq_right hle]; omega
  rw [hbjk]
  exact Nat.le_trans
    (Hex.Nat.choose_le_center k (k / 2) (min j (k - j)) (Nat.sub_le _ _) h2j')
    (Hex.Nat.centralChoose_mono hkn)

/-- Runtime implementation of `defaultFactorCoeffBound`: the closed-form central
binomial times the single loop-invariant norm. -/
@[expose]
def defaultFactorCoeffBoundImpl (f : ZPoly) : Nat :=
  let n := f.natDegree
  Nat.binom n (n / 2) * coeffL2NormBound f

/-- Register the value-equal closed form `defaultFactorCoeffBoundImpl` as the
compiled implementation of `defaultFactorCoeffBound`. The `@[csimp]` swap is
backed by the proof, so the runtime one-norm/one-binomial evaluation is verified
equal to the `O(deg^2)` specification. -/
@[csimp]
theorem defaultFactorCoeffBound_eq_impl :
    @defaultFactorCoeffBound = @defaultFactorCoeffBoundImpl := by
  funext f
  show defaultFactorCoeffBound f = defaultFactorCoeffBoundImpl f
  apply Nat.le_antisymm
  · refine defaultFactorCoeffBound_le f ?_
    intro k hk j hj
    rw [mignotteCoeffBound_eq]
    exact Nat.mul_le_mul_right (coeffL2NormBound f) (binom_le_central hj hk)
  · have hcentral :
        mignotteCoeffBound f (f.natDegree) (f.natDegree / 2)
          ≤ defaultFactorCoeffBound f :=
      mignotteCoeffBound_le_defaultFactorCoeffBound f (Nat.le_refl _)
        (Nat.div_le_self _ 2)
    rw [mignotteCoeffBound_eq] at hcentral
    exact hcentral

end ZPoly
end Hex
