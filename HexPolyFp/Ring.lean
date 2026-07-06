/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Prime
public import HexPoly.Euclid
public import Init.Data.List.Lemmas
public import Init.Data.List.Perm
public import HexPolyFp.Field
import all HexPolyFp.Field

public section
set_option backward.proofsInPublic true

/-!
Core `FpPoly` definitions (constructors, evaluation), the additive
structure, schoolbook multiplication, and the commutative-ring axioms.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-- Polynomial irreducibility over `F_p` phrased as the absence of nontrivial
factorizations inside the executable dense-polynomial model. -/
@[expose]
def Irreducible (f : FpPoly p) : Prop :=
  f ≠ 0 ∧
    ∀ a b : FpPoly p, a * b = f → a.degree? = some 0 ∨ b.degree? = some 0

/-- Build an `FpPoly` from raw coefficients, trimming trailing zero residues. -/
@[expose]
def ofCoeffs (coeffs : Array (ZMod64 p)) : FpPoly p :=
  DensePoly.ofCoeffs coeffs

/-- Constant polynomial in `F_p[x]`. -/
@[expose]
def C (c : ZMod64 p) : FpPoly p :=
  DensePoly.C c

/-- The polynomial indeterminate `X`. -/
@[expose]
def X : FpPoly p :=
  DensePoly.monomial 1 (1 : ZMod64 p)

/-- Reduction modulo a monic polynomial over `F_p[x]`. -/
@[expose]
def modByMonic (f g : FpPoly p) (hmonic : DensePoly.Monic f) : FpPoly p :=
  DensePoly.modByMonic g f hmonic

private theorem zmod_eq_of_toNat_eq {a b : ZMod64 p} (h : a.toNat = b.toNat) : a = b := by
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  simpa [ZMod64.toNat_eq_val] using h

private theorem zmod_add_zero (a : ZMod64 p) : a + 0 = a := by
  grind

private theorem zmod_zero_add (a : ZMod64 p) : 0 + a = a := by
  grind

private theorem zmod_add_zero_zero :
    (Zero.zero : ZMod64 p) + (Zero.zero : ZMod64 p) = (Zero.zero : ZMod64 p) :=
  zmod_add_zero Zero.zero

private theorem zmod_mul_zero (a : ZMod64 p) : a * 0 = 0 := by
  grind

private theorem zmod_zero_mul (a : ZMod64 p) : 0 * a = 0 :=
  Lean.Grind.Semiring.zero_mul a

private theorem zmod_one_mul (a : ZMod64 p) : 1 * a = a := by
  grind

private theorem zmod_mul_one (a : ZMod64 p) : a * 1 = a := by
  grind

private theorem coeff_one (n : Nat) :
    (1 : FpPoly p).coeff n = if n = 0 then (1 : ZMod64 p) else 0 := by
  change (DensePoly.C (1 : ZMod64 p)).coeff n = if n = 0 then (1 : ZMod64 p) else 0
  exact DensePoly.coeff_C (1 : ZMod64 p) n

/-- The zero polynomial evaluates to zero at every point. -/
@[grind =] theorem eval_zero (x : ZMod64 p) :
    DensePoly.eval (0 : FpPoly p) x = 0 := by
  exact DensePoly.eval_zero x

/-- A constant polynomial evaluates to its constant at every point. This is
the base case from which the evaluation map's homomorphism laws are built. -/
@[simp, grind =]
theorem eval_C (c x : ZMod64 p) :
    DensePoly.eval (FpPoly.C c) x = c := by
  unfold FpPoly.C
  exact DensePoly.eval_C c x (zmod_zero_mul x) (zmod_zero_add c)

/-- The variable `X` evaluates to the evaluation point. The companion base
case to `eval_C` for reasoning about the evaluation map. -/
@[simp, grind =]
theorem eval_X [ZMod64.PrimeModulus p] (x : ZMod64 p) :
    DensePoly.eval (FpPoly.X : FpPoly p) x = x := by
  unfold FpPoly.X DensePoly.eval DensePoly.toList DensePoly.toArray DensePoly.monomial
  have h1 : (1 : ZMod64 p) ≠ (Zero.zero : ZMod64 p) := by
    intro h
    have h2 : 2 ≤ p := (ZMod64.PrimeModulus.prime (p := p)).two_le
    have htoNat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat :=
      congrArg ZMod64.toNat h
    rw [show ((1 : ZMod64 p).toNat) = 1 % p from ZMod64.toNat_one,
        show ((0 : ZMod64 p).toNat) = 0 from ZMod64.toNat_zero,
        Nat.mod_eq_of_lt (by omega : 1 < p)] at htoNat
    exact absurd htoNat (by omega)
  rw [dif_neg h1]
  change (((0 : ZMod64 p) * x + 1) * x + 0 = x)
  rw [zmod_zero_mul, zmod_zero_add, zmod_one_mul, zmod_add_zero]

/-- Evaluating a monomial gives the coefficient times the corresponding power. -/
@[simp, grind =]
theorem eval_monomial (n : Nat) (c x : ZMod64 p) :
    DensePoly.eval (DensePoly.monomial n c : FpPoly p) x = c * x ^ n :=
  DensePoly.eval_monomial_semiring n c x

/-- Coefficients of the constant polynomial wrapper are constant at degree zero and zero elsewhere. -/
@[simp, grind =] theorem coeff_C (c : ZMod64 p) (n : Nat) :
    (FpPoly.C c).coeff n = if n = 0 then c else 0 := by
  unfold FpPoly.C
  exact DensePoly.coeff_C c n

/-- The degree-zero coefficient of the indeterminate wrapper is zero. -/
@[grind =] theorem coeff_X_zero :
    ((FpPoly.X : FpPoly p)).coeff 0 = 0 := by
  unfold FpPoly.X
  exact DensePoly.coeff_monomial 1 (1 : ZMod64 p) 0

/-- The degree-one coefficient of the indeterminate wrapper is one. -/
@[grind =] theorem coeff_X_one :
    ((FpPoly.X : FpPoly p)).coeff 1 = 1 := by
  unfold FpPoly.X
  exact DensePoly.coeff_monomial 1 (1 : ZMod64 p) 1

/-- Coefficients of the indeterminate wrapper are one at degree one and zero elsewhere. -/
@[simp, grind =] theorem coeff_X (n : Nat) :
    ((FpPoly.X : FpPoly p)).coeff n = if n = 1 then 1 else 0 := by
  unfold FpPoly.X
  exact DensePoly.coeff_monomial 1 (1 : ZMod64 p) n

/-- `evalCoeffPowerSumFrom coeffs base x` is the power sum `Σ coeffᵢ * x^(base+i)`
of a coefficient list starting at exponent `base`. -/
private def evalCoeffPowerSumFrom :
    List (ZMod64 p) → Nat → ZMod64 p → ZMod64 p
  | [], _, _ => 0
  | coeff :: coeffs, base, x =>
      coeff * x ^ base + evalCoeffPowerSumFrom coeffs (base + 1) x

/-- `evalScalarCoeffList coeffs x` is the Horner-form evaluation
`c₀ + x * (c₁ + x * (⋯))` of a coefficient list. -/
private def evalScalarCoeffList :
    List (ZMod64 p) → ZMod64 p → ZMod64 p
  | [], _ => 0
  | coeff :: coeffs, x => coeff + x * evalScalarCoeffList coeffs x

/-- Multiplying an `evalCoeffPowerSumFrom` value by `x` shifts its base exponent
up by one. -/
private theorem mul_evalCoeffPowerSumFrom_eq_succ
    (x : ZMod64 p) :
    ∀ coeffs base,
      x * evalCoeffPowerSumFrom coeffs base x =
        evalCoeffPowerSumFrom coeffs (base + 1) x
  | [], _ => by
      simp [evalCoeffPowerSumFrom, Lean.Grind.Semiring.mul_zero]
  | coeff :: coeffs, base => by
      simp only [evalCoeffPowerSumFrom]
      rw [Lean.Grind.Semiring.left_distrib, mul_evalCoeffPowerSumFrom_eq_succ x coeffs (base + 1),
        ← Lean.Grind.Semiring.mul_assoc x coeff (x ^ base),
        Lean.Grind.CommSemiring.mul_comm x coeff, Lean.Grind.Semiring.mul_assoc coeff x (x ^ base),
        Lean.Grind.CommSemiring.mul_comm x (x ^ base),
        ← Lean.Grind.Semiring.mul_assoc coeff (x ^ base) x, Lean.Grind.Semiring.pow_succ x base,
        Lean.Grind.Semiring.mul_assoc coeff (x ^ base) x]

/-- The Horner evaluation of a coefficient list equals its power sum based at
exponent zero. -/
private theorem evalScalarCoeffList_eq_powerSumFrom_zero
    (x : ZMod64 p) :
    ∀ coeffs,
      evalScalarCoeffList coeffs x = evalCoeffPowerSumFrom coeffs 0 x
  | [] => by
      simp [evalScalarCoeffList, evalCoeffPowerSumFrom]
  | coeff :: coeffs => by
      simp only [evalScalarCoeffList, evalCoeffPowerSumFrom]
      rw [evalScalarCoeffList_eq_powerSumFrom_zero x coeffs,
        mul_evalCoeffPowerSumFrom_eq_succ x coeffs 0]
      grind

/-- The generic low-to-high Horner walk equals `evalScalarCoeffList`; the two
recursions differ only by the commutations `acc * x = x * acc` and
`acc + c = c + acc`. -/
private theorem evalCoeffList_eq_evalScalarCoeffList
    (x : ZMod64 p) :
    ∀ coeffs,
      DensePoly.evalCoeffList coeffs x = evalScalarCoeffList coeffs x
  | [] => rfl
  | coeff :: coeffs => by
      show DensePoly.evalCoeffList coeffs x * x + coeff =
        coeff + x * evalScalarCoeffList coeffs x
      rw [evalCoeffList_eq_evalScalarCoeffList x coeffs, Lean.Grind.CommSemiring.mul_comm,
        Lean.Grind.Semiring.add_comm]

/-- `DensePoly.eval f x` equals the power sum of `f`'s coefficient list based at
exponent zero. -/
private theorem eval_eq_coeff_power_sum (f : FpPoly p) (x : ZMod64 p) :
    DensePoly.eval f x = evalCoeffPowerSumFrom f.toArray.toList 0 x := by
  show DensePoly.evalCoeffList f.toArray.toList x = _
  rw [evalCoeffList_eq_evalScalarCoeffList x f.toArray.toList]
  exact evalScalarCoeffList_eq_powerSumFrom_zero x f.toArray.toList

/-- Indexing `f`'s coefficient list with default zero recovers `f.coeff n`. -/
private theorem eval_coeff_list_getD_eq_coeff (f : FpPoly p) (n : Nat) :
    f.toArray.toList.getD n (0 : ZMod64 p) = f.coeff n := by
  unfold DensePoly.toArray DensePoly.coeff
  rw [Array.getD_eq_getD_getElem?]
  change f.coeffs.toList[n]?.getD (0 : ZMod64 p) =
    f.coeffs[n]?.getD (Zero.zero : ZMod64 p)
  rw [Array.getElem?_toList]
  rfl

/-- Indexing the `range`-mapped coefficient list returns `coeff n` inside the
range and zero outside it. -/
private theorem list_getD_map_range_zmod (bound n : Nat) (coeff : Nat → ZMod64 p) :
    ((List.range bound).map coeff).getD n (0 : ZMod64 p) =
      if n < bound then coeff n else 0 := by
  by_cases hn : n < bound
  · simp [hn, List.getD]
  · simp [hn, List.getD]

/-- Two coefficient lists of equal length that agree at every default-zero index
are equal. -/
private theorem list_eq_of_length_eq_of_getD_eq
    {xs ys : List (ZMod64 p)}
    (hlen : xs.length = ys.length)
    (hget : ∀ i, i < xs.length → xs.getD i 0 = ys.getD i 0) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hhead : x = y := by
            have h := hget 0 (by simp)
            simpa using h
          have hlen_tail : xs.length = ys.length := Nat.succ.inj hlen
          have htail : xs = ys := by
            apply ih hlen_tail
            intro i hi
            have h := hget (i + 1) (by simp [hi])
            simpa using h
          rw [hhead, htail]

/-- `f`'s coefficient array, viewed as a list, equals `range f.size` mapped
through `f.coeff`. -/
private theorem toArray_toList_eq_coeff_range (f : FpPoly p) :
    f.toArray.toList = (List.range f.size).map (fun i => f.coeff i) := by
  apply list_eq_of_length_eq_of_getD_eq
  · simp [DensePoly.toArray, DensePoly.size]
  · intro i hi
    have hi_size : i < f.size := by
      simpa [DensePoly.toArray, DensePoly.size] using hi
    rw [eval_coeff_list_getD_eq_coeff, list_getD_map_range_zmod]
    simp [hi_size]

/-- `evalCoeffPowerSumUpTo coeff n base x` is the power sum
`Σ coeff(base+i) * x^(base+i)` over the first `n` exponents from `base`, taking the
coefficients from a function rather than a list. -/
private def evalCoeffPowerSumUpTo
    (coeff : Nat → ZMod64 p) :
    Nat → Nat → ZMod64 p → ZMod64 p
  | 0, _, _ => 0
  | n + 1, base, x =>
      coeff base * x ^ base + evalCoeffPowerSumUpTo coeff n (base + 1) x

/-- The list-based power sum over a `range`-mapped coefficient function equals the
function-based `evalCoeffPowerSumUpTo`. -/
private theorem evalCoeffPowerSumFrom_range_eq_upTo
    (coeff : Nat → ZMod64 p) (x : ZMod64 p) :
    ∀ n base,
      evalCoeffPowerSumFrom ((List.range n).map (fun i => coeff (base + i))) base x =
        evalCoeffPowerSumUpTo coeff n base x
  | 0, base => by
      simp [evalCoeffPowerSumFrom, evalCoeffPowerSumUpTo]
  | n + 1, base => by
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      simp only [evalCoeffPowerSumFrom, evalCoeffPowerSumUpTo]
      congr 1
      simpa [Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using evalCoeffPowerSumFrom_range_eq_upTo coeff x n (base + 1)

/-- `DensePoly.eval f x` equals the function-based power sum over `f`'s
coefficients up to `f.size`. -/
private theorem eval_eq_coeff_power_sum_upTo_size (f : FpPoly p)
    (x : ZMod64 p) :
    DensePoly.eval f x = evalCoeffPowerSumUpTo (fun i => f.coeff i) f.size 0 x := by
  rw [eval_eq_coeff_power_sum, toArray_toList_eq_coeff_range]
  simpa using evalCoeffPowerSumFrom_range_eq_upTo (fun i => f.coeff i) x f.size 0

/-- Extending the power sum by one more term leaves it unchanged when the next
coefficient is zero. -/
private theorem evalCoeffPowerSumUpTo_succ_of_next_zero
    (coeff : Nat → ZMod64 p) (x : ZMod64 p) :
    ∀ n base,
      coeff (base + n) = 0 →
        evalCoeffPowerSumUpTo coeff n base x =
          evalCoeffPowerSumUpTo coeff (n + 1) base x
  | 0, base, hzero => by
      have hz : coeff base = 0 := by simpa using hzero
      rw [evalCoeffPowerSumUpTo, evalCoeffPowerSumUpTo, hz, evalCoeffPowerSumUpTo,
        Lean.Grind.Semiring.add_zero]
      exact (Lean.Grind.Semiring.zero_mul (x ^ base)).symm
  | n + 1, base, hzero => by
      simp only [evalCoeffPowerSumUpTo]
      rw [evalCoeffPowerSumUpTo_succ_of_next_zero coeff x n (base + 1) (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hzero)]
      simp only [evalCoeffPowerSumUpTo]

/-- Extending the upper bound of the power sum by any amount leaves it unchanged
when all coefficients past the bound vanish, for an arbitrary starting base. -/
private theorem evalCoeffPowerSumUpTo_le_extend_base
    (coeff : Nat → ZMod64 p) (x : ZMod64 p)
    (hzero : ∀ i, base + bound ≤ i → coeff i = 0) :
    ∀ extra,
      evalCoeffPowerSumUpTo coeff bound base x =
        evalCoeffPowerSumUpTo coeff (bound + extra) base x
  | 0 => by
      simp
  | extra + 1 => by
      rw [evalCoeffPowerSumUpTo_le_extend_base coeff x hzero extra, Nat.add_succ]
      exact evalCoeffPowerSumUpTo_succ_of_next_zero
        coeff x (bound + extra) base (hzero (base + (bound + extra)) (by omega))

/-- Extending the upper bound of the power sum based at zero leaves it unchanged
when all coefficients past the bound vanish. -/
private theorem evalCoeffPowerSumUpTo_le_extend
    (coeff : Nat → ZMod64 p) (x : ZMod64 p)
    (hzero : ∀ i, bound ≤ i → coeff i = 0) :
    ∀ extra,
      evalCoeffPowerSumUpTo coeff bound 0 x =
        evalCoeffPowerSumUpTo coeff (bound + extra) 0 x := by
  intro extra
  exact evalCoeffPowerSumUpTo_le_extend_base
    coeff x (base := 0) (bound := bound) (by simpa using hzero) extra

/-- `DensePoly.eval f x` equals the power sum of `f`'s coefficients up to any
bound at least `f.size`. -/
private theorem eval_eq_coeff_power_sum_upTo_bound (f : FpPoly p)
    (x : ZMod64 p) {bound : Nat} (hbound : f.size ≤ bound) :
    DensePoly.eval f x = evalCoeffPowerSumUpTo (fun i => f.coeff i) bound 0 x := by
  rw [eval_eq_coeff_power_sum_upTo_size]
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hbound
  exact evalCoeffPowerSumUpTo_le_extend
    (fun i => f.coeff i) x
    (fun i hi => DensePoly.coeff_eq_zero_of_size_le f hi) extra

/-- The power sum of a coefficientwise sum is the sum of the two power sums. -/
private theorem evalCoeffPowerSumUpTo_add
    (f h : FpPoly p) (x : ZMod64 p) :
    ∀ n base,
      evalCoeffPowerSumUpTo (fun i => f.coeff i + h.coeff i) n base x =
        evalCoeffPowerSumUpTo (fun i => f.coeff i) n base x +
          evalCoeffPowerSumUpTo (fun i => h.coeff i) n base x
  | 0, _ => by
      simp [evalCoeffPowerSumUpTo]
  | n + 1, base => by
      simp only [evalCoeffPowerSumUpTo]
      rw [evalCoeffPowerSumUpTo_add f h x n (base + 1)]
      grind

/-- The power sum of a coefficientwise difference is the difference of the two
power sums. -/
private theorem evalCoeffPowerSumUpTo_sub
    (f h : FpPoly p) (x : ZMod64 p) :
    ∀ n base,
      evalCoeffPowerSumUpTo (fun i => f.coeff i - h.coeff i) n base x =
        evalCoeffPowerSumUpTo (fun i => f.coeff i) n base x -
          evalCoeffPowerSumUpTo (fun i => h.coeff i) n base x
  | 0, _ => by
      simp [evalCoeffPowerSumUpTo]
      grind
  | n + 1, base => by
      simp only [evalCoeffPowerSumUpTo]
      rw [evalCoeffPowerSumUpTo_sub f h x n (base + 1)]
      grind

/-- Scaling every coefficient by a constant scales the power sum by that
constant. -/
private theorem evalCoeffPowerSumUpTo_const_mul
    (c : ZMod64 p) (coeff : Nat → ZMod64 p) (x : ZMod64 p) :
    ∀ n base,
      evalCoeffPowerSumUpTo (fun i => c * coeff i) n base x =
        c * evalCoeffPowerSumUpTo coeff n base x
  | 0, _ => by
      simp [evalCoeffPowerSumUpTo]
  | n + 1, base => by
      simp only [evalCoeffPowerSumUpTo]
      rw [evalCoeffPowerSumUpTo_const_mul c coeff x n (base + 1)]
      grind

/-- Multiplying a shifted-coefficient power sum by `x^shift` rebases it to start
at exponent `shift + base`. -/
private theorem evalCoeffPowerSumUpTo_rebase_mul
    (coeff : Nat → ZMod64 p) (x : ZMod64 p) (shift : Nat) :
    ∀ n base,
      x ^ shift *
          evalCoeffPowerSumUpTo (fun i => coeff (shift + i)) n base x =
        evalCoeffPowerSumUpTo coeff n (shift + base) x
  | 0, base => by
      simp [evalCoeffPowerSumUpTo]
  | n + 1, base => by
      simp only [evalCoeffPowerSumUpTo]
      rw [Lean.Grind.Semiring.left_distrib,
        evalCoeffPowerSumUpTo_rebase_mul coeff x shift n (base + 1)]
      have hpow :
          x ^ shift * x ^ base = x ^ (shift + base) := by
        exact (Lean.Grind.Semiring.pow_add x shift base).symm
      have hterm :
          x ^ shift * (coeff (shift + base) * x ^ base) =
            coeff (shift + base) * x ^ (shift + base) := by
        rw [← Lean.Grind.Semiring.mul_assoc,
          Lean.Grind.CommSemiring.mul_comm (x ^ shift) (coeff (shift + base)),
          Lean.Grind.Semiring.mul_assoc, hpow]
      rw [hterm]
      grind

/-- Prepending `shift` zero coefficients multiplies the power sum by `x^shift`. -/
private theorem evalCoeffPowerSumUpTo_zero_prefix_shift
    (coeff : Nat → ZMod64 p) (x : ZMod64 p) :
    ∀ shift n,
      evalCoeffPowerSumUpTo
          (fun k => if k < shift then 0 else coeff (k - shift))
          (shift + n) 0 x =
        x ^ shift * evalCoeffPowerSumUpTo coeff n 0 x
  | 0, n => by
      simp only [Nat.zero_add]
      rw [Lean.Grind.Semiring.pow_zero, Lean.Grind.Semiring.one_mul]
      rfl
  | shift + 1, n => by
      rw [Nat.succ_add]
      simp only [evalCoeffPowerSumUpTo]
      have hhead :
          (if 0 < shift + 1 then 0 else coeff (0 - (shift + 1))) *
              x ^ 0 = (0 : ZMod64 p) := by
        grind
      rw [hhead, zmod_zero_add]
      have htail :
          evalCoeffPowerSumUpTo
              (fun k => if k < shift + 1 then 0 else coeff (k - (shift + 1)))
              (shift + n) 1 x =
            x *
              evalCoeffPowerSumUpTo
                (fun k => if k < shift then 0 else coeff (k - shift))
                (shift + n) 0 x := by
        rw [← evalCoeffPowerSumUpTo_rebase_mul
          (fun k => if k < shift + 1 then 0 else coeff (k - (shift + 1)))
          x 1 (shift + n) 0]
        have hx_one : x ^ 1 = x := by
          rw [Lean.Grind.Semiring.pow_succ x 0, Lean.Grind.Semiring.pow_zero]
          grind
        rw [hx_one]
        have hfun :
            (fun i => if 1 + i < shift + 1 then 0 else coeff (1 + i - (shift + 1))) =
              (fun k => if k < shift then 0 else coeff (k - shift)) := by
          funext k
          by_cases hk : k < shift
          · have hk' : 1 + k < shift + 1 := by omega
            simp [hk, hk']
          · have hk' : ¬ 1 + k < shift + 1 := by omega
            have hsub : 1 + k - (shift + 1) = k - shift := by omega
            simp [hk, hk', hsub]
        rw [hfun]
      rw [htail, evalCoeffPowerSumUpTo_zero_prefix_shift coeff x shift n,
        Lean.Grind.Semiring.pow_succ x shift]
      grind

/-- A polynomial's size is at most `bound` when all coefficients from `bound`
onward vanish. -/
private theorem size_le_of_coeff_eq_zero_from (f : FpPoly p) (bound : Nat)
    (hzero : ∀ i, bound ≤ i → f.coeff i = 0) :
    f.size ≤ bound := by
  by_cases hle : f.size ≤ bound
  · exact hle
  · have hgt : bound < f.size := Nat.lt_of_not_ge hle
    have hpos : 0 < f.size := by omega
    have htop_zero : f.coeff (f.size - 1) = 0 := hzero (f.size - 1) (by omega)
    exact False.elim (DensePoly.coeff_last_ne_zero_of_pos_size f hpos htop_zero)

/-- Evaluating the monomial row `c · Xⁱ · f` at `x` multiplies the value of
`f` by `c * xⁱ`. This isolates one term of a product so that `eval_mul` and
related multiplicative laws can be assembled row by row. -/
theorem eval_shift_scale_row (i : Nat) (c : ZMod64 p) (f : FpPoly p)
    (x : ZMod64 p) :
    DensePoly.eval (DensePoly.shift i (DensePoly.scale c f)) x =
      (c * x ^ i) * DensePoly.eval f x := by
  rw [eval_eq_coeff_power_sum_upTo_bound
    (DensePoly.shift i (DensePoly.scale c f)) x (bound := i + f.size)]
  · rw [eval_eq_coeff_power_sum_upTo_size f x]
    have hcoeff :
        (fun k => (DensePoly.shift i (DensePoly.scale c f)).coeff k) =
          (fun k => if k < i then 0 else c * f.coeff (k - i)) := by
      funext k
      have hzero : c * (0 : ZMod64 p) = 0 := by grind
      rw [DensePoly.coeff_shift_scale i c f k hzero]
      rfl
    rw [hcoeff]
    rw [evalCoeffPowerSumUpTo_zero_prefix_shift
      (fun k => c * f.coeff k) x i f.size]
    rw [evalCoeffPowerSumUpTo_const_mul c (fun k => f.coeff k) x f.size 0]
    grind
  · apply size_le_of_coeff_eq_zero_from
    intro k hk
    have hzero : c * (0 : ZMod64 p) = 0 := by grind
    rw [DensePoly.coeff_shift_scale i c f k hzero]
    by_cases hki : k < i
    · simp [hki]
      rfl
    · have hf : f.size ≤ k - i := by omega
      simp [hki, DensePoly.coeff_eq_zero_of_size_le f hf]
      exact hzero

/-- Evaluation is additive: the value of a sum is the sum of the values.
One half of the statement that evaluation at a point is a ring homomorphism. -/
@[simp, grind =]
theorem eval_add (f h : FpPoly p) (x : ZMod64 p) :
    DensePoly.eval (f + h) x = DensePoly.eval f x + DensePoly.eval h x := by
  let bound := max f.size h.size
  rw [eval_eq_coeff_power_sum_upTo_bound (f + h) x (bound := bound)]
  · rw [eval_eq_coeff_power_sum_upTo_bound f x (bound := bound)
      (Nat.le_max_left f.size h.size)]
    rw [eval_eq_coeff_power_sum_upTo_bound h x (bound := bound)
      (Nat.le_max_right f.size h.size)]
    have hcoeff :
        (fun i => (f + h).coeff i) =
          (fun i => f.coeff i + h.coeff i) := by
      funext i
      rw [DensePoly.coeff_add_semiring]
    rw [hcoeff]
    exact evalCoeffPowerSumUpTo_add f h x bound 0
  · change (f + h).size ≤ max f.size h.size
    apply size_le_of_coeff_eq_zero_from
    intro i hi
    rw [DensePoly.coeff_add_semiring]
    rw [DensePoly.coeff_eq_zero_of_size_le f
        (Nat.le_trans (Nat.le_max_left f.size h.size) hi),
      DensePoly.coeff_eq_zero_of_size_le h
        (Nat.le_trans (Nat.le_max_right f.size h.size) hi)]
    exact zmod_add_zero_zero

/-- Evaluation respects subtraction. Lets callers push an evaluation through
a difference of polynomials, for example when checking that two polynomials
agree at a point. -/
@[simp, grind =]
theorem eval_sub (f h : FpPoly p) (x : ZMod64 p) :
    DensePoly.eval (f - h) x = DensePoly.eval f x - DensePoly.eval h x := by
  let bound := max f.size h.size
  rw [eval_eq_coeff_power_sum_upTo_bound (f - h) x (bound := bound)]
  · rw [eval_eq_coeff_power_sum_upTo_bound f x (bound := bound)
      (Nat.le_max_left f.size h.size)]
    rw [eval_eq_coeff_power_sum_upTo_bound h x (bound := bound)
      (Nat.le_max_right f.size h.size)]
    have hcoeff :
        (fun i => (f - h).coeff i) =
          (fun i => f.coeff i - h.coeff i) := by
      funext i
      rw [DensePoly.coeff_sub_ring]
    rw [hcoeff]
    exact evalCoeffPowerSumUpTo_sub f h x bound 0
  · change (f - h).size ≤ max f.size h.size
    apply size_le_of_coeff_eq_zero_from
    intro i hi
    rw [DensePoly.coeff_sub_ring]
    rw [DensePoly.coeff_eq_zero_of_size_le f
        (Nat.le_trans (Nat.le_max_left f.size h.size) hi),
      DensePoly.coeff_eq_zero_of_size_le h
        (Nat.le_trans (Nat.le_max_right f.size h.size) hi)]
    grind

/-- Evaluation respects additive inverses. -/
@[simp, grind =] theorem eval_neg (f : FpPoly p) (x : ZMod64 p) :
    DensePoly.eval (-f) x = -(DensePoly.eval f x) := by
  change DensePoly.eval (DensePoly.neg f) x = -(DensePoly.eval f x)
  unfold DensePoly.neg
  rw [eval_sub, eval_zero]
  exact DensePoly.ZeroSubNegLaw.zero_sub_eq_neg (DensePoly.eval f x)

/-- `0` is a right identity for addition. Part of the commutative-ring
structure on `FpPoly p`. -/
@[simp, grind =] theorem add_zero (f : FpPoly p) :
    f + 0 = f := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add_semiring, DensePoly.coeff_zero]
  grind

/-- `0` is a left identity for addition. Part of the commutative-ring
structure on `FpPoly p`. -/
@[simp, grind =] theorem zero_add (f : FpPoly p) :
    0 + f = f := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add_semiring, DensePoly.coeff_zero]
  grind

/-- Polynomial addition is commutative. Part of the commutative-ring
structure on `FpPoly p` that downstream algebra relies on. -/
theorem add_comm (f g : FpPoly p) :
    f + g = g + f := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add_semiring, DensePoly.coeff_add_semiring]
  grind

/-- Polynomial addition is associative, letting callers regroup sums freely.
Part of the commutative-ring structure on `FpPoly p`. -/
theorem add_assoc (f g h : FpPoly p) :
    f + g + h = f + (g + h) := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add_semiring, DensePoly.coeff_add_semiring, DensePoly.coeff_add_semiring,
    DensePoly.coeff_add_semiring]
  grind

/-- Negating `0` gives `0`. -/
@[simp, grind =] theorem neg_zero :
    -(0 : FpPoly p) = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_neg_ring, DensePoly.coeff_zero]
  grind

/-- The negation is a left additive inverse: `-f + f = 0`. -/
@[simp, grind =] theorem add_left_neg (f : FpPoly p) :
    -f + f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add_semiring, DensePoly.coeff_neg_ring, DensePoly.coeff_zero]
  grind

/-- The negation is a right additive inverse: `f + -f = 0`. -/
@[simp, grind =] theorem add_right_neg (f : FpPoly p) :
    f + -f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add_semiring, DensePoly.coeff_neg_ring, DensePoly.coeff_zero]
  grind

/-- Subtracting `0` leaves a polynomial unchanged. -/
@[simp, grind =] theorem sub_zero (f : FpPoly p) :
    f - 0 = f := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_sub_ring, DensePoly.coeff_zero]
  grind

/-- Subtracting a polynomial from `0` yields its negation. -/
@[simp, grind =] theorem zero_sub (f : FpPoly p) :
    0 - f = -f := by
  rfl

/-- A polynomial minus itself is `0`. -/
@[simp, grind =] theorem sub_self (f : FpPoly p) :
    f - f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_sub_ring, DensePoly.coeff_zero]
  grind

/-- Subtraction unfolds to adding the negation. Rewrites subtraction in terms
of the additive operations, so results proved for `+` transfer to `-`. -/
theorem sub_eq_add_neg (f g : FpPoly p) :
    f - g = f + -g := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add_semiring, DensePoly.coeff_sub_ring, DensePoly.coeff_neg_ring]
  grind

example (f : FpPoly p) :
    (f + 0) - f = 0 := by
  simp

/-- `0` is a left absorbing element for multiplication. -/
@[simp, grind =] theorem zero_mul (f : FpPoly p) :
    0 * f = 0 := by
  rfl

/-- `0` is a right absorbing element for multiplication. -/
@[simp, grind =] theorem mul_zero (f : FpPoly p) :
    f * 0 = 0 := by
  exact (DensePoly.mul_comm_poly f 0).trans (DensePoly.zero_mul f)

/-- Coefficient `k` of the partial fold rebuilding `f` from its first `n`
monomials via `shift`/`scale` of `1`: it is `f.coeff k` below the cutoff `n`
and `0` at or above it. -/
private theorem coeff_mul_one_fold (f : FpPoly p) (n k : Nat) :
    ((List.range n).foldl
        (fun acc i => acc + DensePoly.shift i (DensePoly.scale (f.coeff i) (1 : FpPoly p)))
        (0 : FpPoly p)).coeff k =
      if k < n then f.coeff k else 0 := by
  induction n with
  | zero =>
      exact DensePoly.coeff_zero k
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [DensePoly.coeff_add_semiring, ih, DensePoly.coeff_shift_scale]
      · rw [coeff_one]
        by_cases hk : k < n
        · have hks : k < n + 1 := Nat.lt_trans hk (Nat.lt_succ_self n)
          simp [hk, hks]
          exact zmod_add_zero (f.coeff k)
        · by_cases hkn : k = n
          · subst k
            simp
          · have hks : ¬ k < n + 1 := by omega
            have hsub : k - n ≠ 0 := by omega
            simp [hk, hks, hsub]
      · exact zmod_mul_zero (f.coeff n)

/-- `1` is a left identity for multiplication. -/
@[simp, grind =] theorem one_mul (f : FpPoly p) :
    1 * f = f := by
  exact (DensePoly.mul_comm_poly (1 : FpPoly p) f).trans (DensePoly.mul_one_right_poly f)

/-- `1` is a right identity for multiplication. -/
@[simp, grind =] theorem mul_one (f : FpPoly p) :
    f * 1 = f := by
  exact DensePoly.mul_one_right_poly f

/-! ### Schoolbook coefficient helpers (proof-facing Hensel scaffolding)

`mulCoeffTerm` and `mulCoeffSum` are kept public only because
`HexHensel/Linear.lean` reasons about the per-coefficient diagonal
contribution of `FpPoly` multiplication when establishing the linear
Hensel lift congruence. They are not part of the ordinary `FpPoly`
multiplication API — callers who only need a characterisation of
`(f * g).coeff n` should use the public `coeff_mul` lemma below, which
gives the same value without committing to the schoolbook fold shape.

The private cluster of lemmas that follows these two definitions
(`coeff_mul_fold`, `foldl_mulCoeffStep_*`, `mulCoeffTerm_*`,
`fold_mulCoeff_*`, `mulCoeffSum_eq_bound`, etc.) is proof plumbing for
the multiplication characterisations and is intentionally not exported. -/

/-- The `i`th schoolbook contribution to coefficient `n` of `f * g`.
Proof-facing Hensel scaffolding: ordinary `FpPoly` multiplication callers
should use `coeff_mul`, not this definition. -/
@[expose]
def mulCoeffTerm (f g : FpPoly p) (n i : Nat) : ZMod64 p :=
  if n < i then 0 else f.coeff i * g.coeff (n - i)

/-- The executable schoolbook coefficient sum matching `FpPoly`
multiplication. Proof-facing Hensel scaffolding: ordinary `FpPoly`
multiplication callers should use `coeff_mul`, not this definition. -/
@[expose]
def mulCoeffSum (f g : FpPoly p) (n : Nat) : ZMod64 p :=
  (List.range f.size).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0

/-- The `n`-th coefficient of the `shift`/`scale` product fold equals the
`mulCoeffTerm` fold over the same indices, started from `acc.coeff n`. -/
private theorem coeff_mul_fold (xs : List Nat) (acc f g : FpPoly p) (n : Nat) :
    (xs.foldl
        (fun acc i => acc + DensePoly.shift i (DensePoly.scale (f.coeff i) g))
        acc).coeff n =
      xs.foldl (fun coeff i => coeff + mulCoeffTerm f g n i) (acc.coeff n) := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      have hzero : f.coeff i * (0 : ZMod64 p) = 0 := by grind
      rw [DensePoly.coeff_add_semiring,
        DensePoly.coeff_shift_scale i (f.coeff i) g n hzero]
      rfl

/-- The inner `mulCoeffStep` fold over `range m` adds exactly the diagonal term
`f.coeff i * g.coeff (n - i)` when `i ≤ n` and `n - i < m`, and otherwise leaves
the accumulator unchanged. -/
private theorem foldl_mulCoeffStep_select_fp
    (f g : FpPoly p) (n i m : Nat) (acc : ZMod64 p) :
    (List.range m).foldl (DensePoly.mulCoeffStep f g n i) acc =
      acc + (if n < i then 0
        else if n - i < m then f.coeff i * g.coeff (n - i) else 0) := by
  induction m generalizing acc with
  | zero =>
      simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      unfold DensePoly.mulCoeffStep
      by_cases hlt : n < i
      · have hne : i + m ≠ n := by omega
        simp [hlt, hne]
      · by_cases hm : n - i < m
        · have hne : i + m ≠ n := by omega
          simp [hlt, hm, hne]
          grind
        · by_cases heq : i + m = n
          · have hsub : n - i = m := by omega
            simp [hlt, heq, hsub]
          · have hm' : ¬ n - i < m + 1 := by omega
            simp [hlt, hm, hm', heq]

/-- Rewrites the outer fold of inner `mulCoeffStep` folds (each over
`range g.size`) into the fold that adds the selected diagonal term directly. -/
private theorem foldl_mulCoeffStep_outer_fp
    (f g : FpPoly p) (n : Nat) (xs : List Nat) (acc : ZMod64 p) :
    xs.foldl
        (fun acc i =>
          (List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) acc)
        acc =
      xs.foldl
        (fun acc i =>
          acc + (if n < i then 0
            else if n - i < g.size then f.coeff i * g.coeff (n - i) else 0))
        acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [foldl_mulCoeffStep_select_fp]
      exact ih _

/-- The nested `mulCoeffStep` fold equals the fold accumulating
`mulCoeffTerm f g n i`, identifying the executable convolution with the
schoolbook term. -/
private theorem foldl_mulCoeffStep_outer_eq_mulCoeffTerm
    (f g : FpPoly p) (n : Nat) (xs : List Nat) (acc : ZMod64 p) :
    xs.foldl
        (fun acc i =>
          (List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) acc)
        acc =
      xs.foldl (fun acc i => acc + mulCoeffTerm f g n i) acc := by
  rw [foldl_mulCoeffStep_outer_fp]
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      unfold mulCoeffTerm
      by_cases hlt : n < i
      · simp [hlt]
      · by_cases hbound : n - i < g.size
        · simp [hlt, hbound]
        · have hcoeff : g.coeff (n - i) = 0 :=
            DensePoly.coeff_eq_zero_of_size_le g (Nat.le_of_not_gt hbound)
          simp [hlt, hbound, hcoeff]

/-- The `n`-th coefficient of a product is the convolution sum `mulCoeffSum`.
This is the coefficient-level specification of the executable multiplication,
the entry point for proving every higher multiplicative law. -/
theorem coeff_mul (f g : FpPoly p) (n : Nat) :
    (f * g).coeff n = mulCoeffSum f g n := by
  rw [DensePoly.coeff_mul]
  unfold DensePoly.mulCoeffSum mulCoeffSum
  exact foldl_mulCoeffStep_outer_eq_mulCoeffTerm f g n (List.range f.size) 0

/-- `mulCoeffTerm f g n i` vanishes once the index `i` reaches `f.size`, since
`f.coeff i` is then `0`. -/
private theorem mulCoeffTerm_eq_zero_of_size_le
    (f g : FpPoly p) (n i : Nat) (hi : f.size ≤ i) :
    mulCoeffTerm f g n i = 0 := by
  unfold mulCoeffTerm
  by_cases hn : n < i
  · simp [hn]
  · have hcoeff : f.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le f hi
    simp [hn, hcoeff]

/-- Extending the `mulCoeffTerm` fold by `d` indices past `f.size` leaves the
sum unchanged, as the extra terms vanish. -/
private theorem fold_mulCoeff_extend (f g : FpPoly p) (n d : Nat) :
    (List.range (f.size + d)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 =
      (List.range f.size).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hterm : mulCoeffTerm f g n (f.size + d) = 0 :=
        mulCoeffTerm_eq_zero_of_size_le f g n (f.size + d) (by omega)
      simp [hterm]

/-- `mulCoeffSum f g n` equals the `mulCoeffTerm` fold over `range m` for any
bound `m` at least `f.size`. -/
private theorem mulCoeffSum_eq_bound
    (f g : FpPoly p) (n m : Nat) (hm : f.size ≤ m) :
    mulCoeffSum f g n =
      (List.range m).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
  unfold mulCoeffSum
  have hm' : f.size + (m - f.size) = m := by omega
  rw [← hm', fold_mulCoeff_extend]

/-- `(f * g).coeff n` equals the `mulCoeffTerm` fold over `range m` for any
bound `m` at least `f.size`. -/
private theorem coeff_mul_of_size_le
    (f g : FpPoly p) (n m : Nat) (hm : f.size ≤ m) :
    (f * g).coeff n =
      (List.range m).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
  rw [coeff_mul, mulCoeffSum_eq_bound f g n m hm]

/-- `mulCoeffTerm f g n i` vanishes when the target degree `n` is below the
index `i`. -/
private theorem mulCoeffTerm_eq_zero_of_degree_lt
    (f g : FpPoly p) (n i : Nat) (hi : n < i) :
    mulCoeffTerm f g n i = 0 := by
  simp [mulCoeffTerm, hi]

/-- Extending the `mulCoeffTerm` fold by `d` indices past `n + 1` leaves the sum
unchanged, since terms with index above `n` vanish. -/
private theorem fold_mulCoeff_truncate_degree
    (f g : FpPoly p) (n d : Nat) :
    (List.range (n + 1 + d)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 =
      (List.range (n + 1)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hterm : mulCoeffTerm f g n (n + 1 + d) = 0 :=
        mulCoeffTerm_eq_zero_of_degree_lt f g n (n + 1 + d) (by omega)
      simp [hterm]

/-- `mulCoeffSum f g n` equals the `mulCoeffTerm` fold truncated to
`range (n + 1)`, since terms beyond degree `n` vanish. -/
private theorem mulCoeffSum_eq_degree_bound
    (f g : FpPoly p) (n : Nat) :
    mulCoeffSum f g n =
      (List.range (n + 1)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
  unfold mulCoeffSum
  by_cases hsize : f.size ≤ n + 1
  · exact mulCoeffSum_eq_bound f g n (n + 1) hsize
  · have hle : n + 1 ≤ f.size := Nat.le_of_not_ge hsize
    have hsize' : n + 1 + (f.size - (n + 1)) = f.size := by omega
    rw [← hsize']
    exact fold_mulCoeff_truncate_degree f g n (f.size - (n + 1))

/-- Left-folding addition over `xs` from `a + b` equals folding from `a` and
adding `b` afterwards, so a summand may be pulled out past the fold; used by
`fold_add_reverse` to peel the element exposed when the list is reversed. -/
private theorem fold_add_right
    (xs : List (ZMod64 p)) (a b : ZMod64 p) :
    xs.foldl (fun acc x => acc + x) (a + b) =
      xs.foldl (fun acc x => acc + x) a + b := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hacc : a + b + x = (a + x) + b := by grind
      rw [hacc]
      exact ih (a + x)

/-- Reversing `xs` before a left-fold of addition leaves the running sum
unchanged, since addition is commutative and associative; lets the
commutativity proof rewrite the `mulCoeffTerm` sum into reversed index order. -/
private theorem fold_add_reverse
    (xs : List (ZMod64 p)) (a : ZMod64 p) :
    xs.reverse.foldl (fun acc x => acc + x) a =
      xs.foldl (fun acc x => acc + x) a := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.reverse_cons, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, fold_add_right xs a x]

/-- `(List.range (n + 1)).reverse` equals `List.range (n + 1)` mapped by
`fun i => n - i`, recasting the reversed summation order as the index
substitution `i ↦ n - i` that the reindexing lemmas consume. -/
private theorem range_succ_reverse_eq_map_sub (n : Nat) :
    (List.range (n + 1)).reverse = (List.range (n + 1)).map (fun i => n - i) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    simp [List.length_reverse] at hleft hright
    rw [List.getElem_reverse]
    simp [List.getElem_map, List.getElem_range]

/-- The reindexed product term `mulCoeffTerm f g n (n - i)` equals
`mulCoeffTerm g f n i`, the pointwise factor-swap identity that underlies
commutativity of the degree-`n` coefficient. -/
private theorem mulCoeffTerm_comm_reindex
    (f g : FpPoly p) (n i : Nat) (hi : i < n + 1) :
    mulCoeffTerm f g n (n - i) = mulCoeffTerm g f n i := by
  have hile : i ≤ n := by omega
  have hleft : ¬ n < n - i := by omega
  have hright : ¬ n < i := by omega
  simp [mulCoeffTerm, hleft, hright, Nat.sub_sub_self hile]
  grind

/-- Over any index list whose entries stay below `n + 1`, folding the
reindexed `f, g` terms `mulCoeffTerm f g n (n - i)` matches folding the
swapped `g, f` terms, lifting `mulCoeffTerm_comm_reindex` from a single index
to the whole fold. -/
private theorem fold_mulCoeff_comm_reindex_list
    (f g : FpPoly p) (n : Nat) (xs : List Nat)
    (hxs : ∀ i, i ∈ xs → i < n + 1) (acc : ZMod64 p) :
    xs.foldl (fun acc i => acc + mulCoeffTerm f g n (n - i)) acc =
      xs.foldl (fun acc i => acc + mulCoeffTerm g f n i) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hi : i < n + 1 := hxs i (by simp)
      rw [mulCoeffTerm_comm_reindex f g n i hi]
      exact ih (by
        intro j hj
        exact hxs j (by simp [hj])) (acc + mulCoeffTerm g f n i)

/-- The full degree-`n` coefficient sum over `List.range (n + 1)` is invariant
under swapping `f` and `g`, combining the reverse, reindex, and pointwise-swap
lemmas into the per-coefficient identity that `mul_comm` consumes. -/
private theorem fold_mulCoeff_comm
    (f g : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 =
      (List.range (n + 1)).foldl (fun acc i => acc + mulCoeffTerm g f n i) 0 := by
  have hrev :
      (List.range (n + 1)).reverse.foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 =
        (List.range (n + 1)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
    simpa [List.foldl_map, ← List.map_reverse] using
      fold_add_reverse (p := p)
        ((List.range (n + 1)).map (fun i => mulCoeffTerm f g n i)) 0
  rw [← hrev, range_succ_reverse_eq_map_sub, List.foldl_map]
  exact fold_mulCoeff_comm_reindex_list f g n (List.range (n + 1)) (by
    intro i hi
    exact List.mem_range.mp hi) 0

/-- Polynomial multiplication is commutative. Part of the commutative-ring
structure on `FpPoly p`, and lets callers swap factors to match a lemma's
expected orientation. -/
theorem mul_comm (f g : FpPoly p) :
    f * g = g * f := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_mul, coeff_mul, mulCoeffSum_eq_degree_bound f g n, mulCoeffSum_eq_degree_bound g f n]
  exact fold_mulCoeff_comm f g n

private theorem mulCoeffTerm_left_distrib (f g h : FpPoly p) (n i : Nat) :
    mulCoeffTerm f (g + h) n i =
      mulCoeffTerm f g n i + mulCoeffTerm f h n i := by
  unfold mulCoeffTerm
  by_cases hi : n < i
  · simp [hi]
  · rw [DensePoly.coeff_add_semiring]
    simp [hi]
    grind

private theorem mulCoeffTerm_right_distrib (f g h : FpPoly p) (n i : Nat) :
    mulCoeffTerm (f + g) h n i =
      mulCoeffTerm f h n i + mulCoeffTerm g h n i := by
  unfold mulCoeffTerm
  by_cases hi : n < i
  · simp [hi]
  · rw [DensePoly.coeff_add_semiring]
    simp [hi]
    grind

private theorem fold_distrib_acc
    (xs : List Nat) (a b : ZMod64 p)
    (term term₁ term₂ : Nat → ZMod64 p)
    (hterm : ∀ i, term i = term₁ i + term₂ i) :
    xs.foldl (fun acc i => acc + term i) (a + b) =
      xs.foldl (fun acc i => acc + term₁ i) a +
        xs.foldl (fun acc i => acc + term₂ i) b := by
  induction xs generalizing a b with
  | nil =>
      rfl
  | cons i xs ih =>
    simp only [List.foldl_cons]
    rw [hterm i]
    have hacc :
        a + b + (term₁ i + term₂ i) =
          (a + term₁ i) + (b + term₂ i) := by
      grind
    rw [hacc]
    exact ih (a + term₁ i) (b + term₂ i)

private theorem fold_mul_right
    (xs : List Nat) (term : Nat → ZMod64 p) (c : ZMod64 p) :
    xs.foldl (fun acc i => acc + term i) 0 * c =
      xs.foldl (fun acc i => acc + term i * c) 0 := by
  induction xs with
  | nil =>
      grind
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hfold :
          xs.foldl (fun acc j => acc + term j) (0 + term i) =
            xs.foldl (fun acc j => acc + term j) 0 + term i := by
        simpa [List.foldl_map] using
          fold_add_right (p := p) (xs.map term) 0 (term i)
      have hfold' :
          xs.foldl (fun acc j => acc + term j * c) (0 + term i * c) =
            xs.foldl (fun acc j => acc + term j * c) 0 + term i * c := by
        simpa [List.foldl_map] using
          fold_add_right (p := p) (xs.map (fun j => term j * c)) 0 (term i * c)
      calc
        xs.foldl (fun acc j => acc + term j) (0 + term i) * c
            = (xs.foldl (fun acc j => acc + term j) 0 + term i) * c := by
                rw [hfold]
        _ = xs.foldl (fun acc j => acc + term j) 0 * c + term i * c := by
                grind
        _ = xs.foldl (fun acc j => acc + term j * c) 0 + term i * c := by
                rw [ih]
        _ = xs.foldl (fun acc j => acc + term j * c) (0 + term i * c) := by
                rw [hfold']

private theorem fold_mul_left
    (xs : List Nat) (term : Nat → ZMod64 p) (c : ZMod64 p) :
    c * xs.foldl (fun acc i => acc + term i) 0 =
      xs.foldl (fun acc i => acc + c * term i) 0 := by
  induction xs with
  | nil =>
      grind
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hfold :
          xs.foldl (fun acc j => acc + term j) (0 + term i) =
            xs.foldl (fun acc j => acc + term j) 0 + term i := by
        simpa [List.foldl_map] using
          fold_add_right (p := p) (xs.map term) 0 (term i)
      have hfold' :
          xs.foldl (fun acc j => acc + c * term j) (0 + c * term i) =
            xs.foldl (fun acc j => acc + c * term j) 0 + c * term i := by
        simpa [List.foldl_map] using
          fold_add_right (p := p) (xs.map (fun j => c * term j)) 0 (c * term i)
      calc
        c * xs.foldl (fun acc j => acc + term j) (0 + term i)
            = c * (xs.foldl (fun acc j => acc + term j) 0 + term i) := by
                rw [hfold]
        _ = c * xs.foldl (fun acc j => acc + term j) 0 + c * term i := by
                grind
        _ = xs.foldl (fun acc j => acc + c * term j) 0 + c * term i := by
                rw [ih]
        _ = xs.foldl (fun acc j => acc + c * term j) (0 + c * term i) := by
                rw [hfold']

private theorem mulCoeffTerm_mul_left_expand
    (f g h : FpPoly p) (n i : Nat) (hi : ¬ n < i) :
    mulCoeffTerm (f * g) h n i =
      (List.range (i + 1)).foldl
        (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0 := by
  unfold mulCoeffTerm
  simp [hi]
  rw [coeff_mul, mulCoeffSum_eq_degree_bound f g i]
  exact fold_mul_right (p := p) (List.range (i + 1))
    (fun j => mulCoeffTerm f g i j) (h.coeff (n - i))

private theorem mulCoeffTerm_mul_right_expand
    (f g h : FpPoly p) (n i : Nat) (hi : ¬ n < i) :
    mulCoeffTerm f (g * h) n i =
      (List.range (n - i + 1)).foldl
        (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0 := by
  unfold mulCoeffTerm
  simp [hi]
  rw [coeff_mul, mulCoeffSum_eq_degree_bound g h (n - i)]
  exact fold_mul_left (p := p) (List.range (n - i + 1))
    (fun j => mulCoeffTerm g h (n - i) j) (f.coeff i)

/-- `leftAssocTriples` enumerates the left-associated triples `((j, i - j), n - i)`
used to flatten the degree-`n` coefficient sum for `FpPoly` multiplication
associativity. -/
private def leftAssocTriples (n : Nat) : List ((Nat × Nat) × Nat) :=
  (List.range (n + 1)).flatMap fun i =>
    (List.range (i + 1)).map fun j => ((j, i - j), n - i)

/-- `rightAssocTriples` enumerates the right-associated triples `((i, j), n - i - j)`
used to flatten the same degree-`n` coefficient sum for `FpPoly` multiplication
associativity. -/
private def rightAssocTriples (n : Nat) : List ((Nat × Nat) × Nat) :=
  (List.range (n + 1)).flatMap fun i =>
    (List.range (n - i + 1)).map fun j => ((i, j), n - i - j)

/-- `nodup_map_of_injective` keeps a mapped list duplicate-free when the map is
injective on the source list, supporting duplicate-free triple enumerations for the
associativity reindexing. -/
private theorem nodup_map_of_injective
    {α β : Type} {xs : List α} {f : α → β}
    (hxs : xs.Nodup)
    (hinj : ∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b) :
    (xs.map f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [List.nodup_cons] at hxs ⊢
      constructor
      · intro hx
        rcases List.mem_map.mp hx with ⟨y, hy, hxy⟩
        have hxy' : x = y := hinj x (by simp) y (by simp [hy]) hxy.symm
        exact hxs.1 (by simpa [hxy'] using hy)
      · exact ih hxs.2 (by
          intro a ha b hb hab
          exact hinj a (by simp [ha]) b (by simp [hb]) hab)

/-- `nodup_flatMap_of_disjoint` keeps a flattened list duplicate-free when each row is
duplicate-free and different rows are disjoint, supporting the triangular triple
enumerations used in associativity reindexing. -/
private theorem nodup_flatMap_of_disjoint
    {α β : Type} {xs : List α} {f : α → List β}
    (hxs : xs.Nodup)
    (hrow : ∀ x, x ∈ xs → (f x).Nodup)
    (hdisj :
      ∀ x, x ∈ xs → ∀ y, y ∈ xs → x ≠ y →
        ∀ z, z ∈ f x → z ∈ f y → False) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨hrow x (by simp), ?_, ?_⟩
      · exact ih hxs.2
          (by intro y hy; exact hrow y (by simp [hy]))
          (by
            intro y hy z hz hyz t hty htz
            exact hdisj y (by simp [hy]) z (by simp [hz]) hyz t hty htz)
      · intro a ha b hb hab
        rcases List.mem_flatMap.mp hb with ⟨y, hy, hby⟩
        exact hdisj x (by simp) y (by simp [hy]) (by
          intro hxy
          exact hxs.1 (hxy ▸ hy)) a ha (hab ▸ hby)

/-- `leftAssocTriples_nodup` proves the left-associated triple enumeration has no
duplicates, so its coefficient fold can be compared by membership during associativity
reindexing. -/
private theorem leftAssocTriples_nodup (n : Nat) :
    (leftAssocTriples n).Nodup := by
  unfold leftAssocTriples
  apply nodup_flatMap_of_disjoint List.nodup_range
  · intro i hi
    apply nodup_map_of_injective List.nodup_range
    intro a ha b hb hab
    injection hab with hfst _
    exact Prod.ext_iff.mp hfst |>.1
  · intro i hi k hk hik z hzi hzk
    rcases List.mem_map.mp hzi with ⟨a, ha, rfl⟩
    rcases List.mem_map.mp hzk with ⟨b, hb, hEq⟩
    injection hEq with hpair hlast
    injection hpair with hfirst hsecond
    have hi' : i < n + 1 := List.mem_range.mp hi
    have hk' : k < n + 1 := List.mem_range.mp hk
    omega

/-- `rightAssocTriples_nodup` proves the right-associated triple enumeration has no
duplicates, so its coefficient fold can be compared by membership during associativity
reindexing. -/
private theorem rightAssocTriples_nodup (n : Nat) :
    (rightAssocTriples n).Nodup := by
  unfold rightAssocTriples
  apply nodup_flatMap_of_disjoint List.nodup_range
  · intro i hi
    apply nodup_map_of_injective List.nodup_range
    intro a ha b hb hab
    injection hab with hfst _
    exact Prod.ext_iff.mp hfst |>.2
  · intro i hi k hk hik z hzi hzk
    rcases List.mem_map.mp hzi with ⟨a, ha, rfl⟩
    rcases List.mem_map.mp hzk with ⟨b, hb, hEq⟩
    injection hEq with hpair _
    exact hik (Prod.ext_iff.mp hpair |>.1).symm

/-- `leftAssocTriples_mem_iff` characterizes membership in the left-associated triple
list by the equation `abc.1.1 + abc.1.2 + abc.2 = n`, exposing the index condition
used for associativity reindexing. -/
private theorem leftAssocTriples_mem_iff (n : Nat) (abc : (Nat × Nat) × Nat) :
    abc ∈ leftAssocTriples n ↔ abc.1.1 + abc.1.2 + abc.2 = n := by
  rcases abc with ⟨⟨a, b⟩, c⟩
  simp [leftAssocTriples]
  constructor
  · intro h
    omega
  · intro h
    refine ⟨a + b, ?_, a, ?_, ?_⟩ <;> omega

/-- `rightAssocTriples_mem_iff` characterizes membership in the right-associated triple
list by the equation `abc.1.1 + abc.1.2 + abc.2 = n`, matching the index condition
used for associativity reindexing. -/
private theorem rightAssocTriples_mem_iff (n : Nat) (abc : (Nat × Nat) × Nat) :
    abc ∈ rightAssocTriples n ↔ abc.1.1 + abc.1.2 + abc.2 = n := by
  rcases abc with ⟨⟨a, b⟩, c⟩
  simp [rightAssocTriples]
  constructor
  · intro h
    omega
  · intro h
    refine ⟨a, ?_, b, ?_, ?_⟩ <;> omega

/-- `leftAssocTriples_perm_rightAssocTriples` proves the left- and right-associated
triple enumerations are permutations, giving the combinatorial core of the
associativity reindexing. -/
private theorem leftAssocTriples_perm_rightAssocTriples (n : Nat) :
    List.Perm (leftAssocTriples n) (rightAssocTriples n) := by
  rw [List.perm_iff_count]
  intro abc
  rw [(leftAssocTriples_nodup n).count, (rightAssocTriples_nodup n).count]
  simp [leftAssocTriples_mem_iff, rightAssocTriples_mem_iff]

/-- `fold_add_perm` proves additive left folds over `ZMod64 p` are invariant under list
permutation, allowing the permuted triple enumerations to carry the same coefficient
sum. -/
private theorem fold_add_perm {xs ys : List (ZMod64 p)}
    (h : List.Perm xs ys) (acc : ZMod64 p) :
    xs.foldl (fun acc x => acc + x) acc =
      ys.foldl (fun acc x => acc + x) acc := by
  induction h generalizing acc with
  | nil =>
      rfl
  | cons x _ ih =>
      simp only [List.foldl_cons]
      exact ih (acc + x)
  | swap x y _ =>
      simp only [List.foldl_cons]
      have hxy : acc + x + y = acc + y + x := by grind
      rw [hxy]
  | trans _ _ ih₁ ih₂ =>
      exact Eq.trans (ih₁ acc) (ih₂ acc)

/-- `fold_add_acc` splits the starting accumulator out of an additive left fold, letting
flattened coefficient sums be normalized to a zero accumulator for associativity
reindexing. -/
private theorem fold_add_acc
    (xs : List (ZMod64 p)) (acc : ZMod64 p) :
    xs.foldl (fun acc x => acc + x) acc =
      acc + xs.foldl (fun acc x => acc + x) 0 := by
  have h := fold_add_right (p := p) xs 0 acc
  simp only [zmod_zero_add] at h
  rw [h]
  grind

/-- `fold_flatMap_map_add` rewrites an additive fold over a `flatMap` of mapped rows as
nested row folds, connecting flattened triple sums with the triangular coefficient
folds. -/
private theorem fold_flatMap_map_add
    {α β : Type} (xs : List α) (row : α → List β)
    (term : α → β → ZMod64 p) (acc : ZMod64 p) :
    (xs.flatMap fun x => (row x).map (term x)).foldl
        (fun acc x => acc + x) acc =
      xs.foldl
        (fun acc x =>
          acc + (row x).foldl (fun acc y => acc + term x y) 0) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.flatMap_cons, List.foldl_append, fold_add_acc (p := p) ((row x).map (term x)) acc,
        ih]
      simp [List.foldl_map]

/-- `fold_triangular_assoc_reindex` reindexes the triangular coefficient double-fold
between left- and right-associated orderings, supplying the fold identity used in
`FpPoly` multiplication associativity. -/
private theorem fold_triangular_assoc_reindex
    (n : Nat) (term : Nat → Nat → Nat → ZMod64 p) :
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + term j (i - j) (n - i)) 0) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + term i j (n - i - j)) 0) 0 := by
  have hperm :
      List.Perm
        ((leftAssocTriples n).map (fun abc => term abc.1.1 abc.1.2 abc.2))
        ((rightAssocTriples n).map (fun abc => term abc.1.1 abc.1.2 abc.2)) :=
    (leftAssocTriples_perm_rightAssocTriples n).map _
  have hfold := fold_add_perm (p := p) hperm 0
  rw [← fold_flatMap_map_add (p := p) (List.range (n + 1))
    (fun i => List.range (i + 1))
    (fun i j => term j (i - j) (n - i)) 0]
  rw [← fold_flatMap_map_add (p := p) (List.range (n + 1))
    (fun i => List.range (n - i + 1))
    (fun i j => term i j (n - i - j)) 0]
  simpa [leftAssocTriples, rightAssocTriples, List.map_flatMap, Function.comp_def] using hfold

private theorem fold_add_congr
    (xs : List Nat) {term₁ term₂ : Nat → ZMod64 p}
    (hterm : ∀ i, i ∈ xs → term₁ i = term₂ i) (acc : ZMod64 p) :
    xs.foldl (fun acc i => acc + term₁ i) acc =
      xs.foldl (fun acc i => acc + term₂ i) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [hterm i (by simp)]
      exact ih (by
        intro j hj
        exact hterm j (by simp [hj])) (acc + term₂ i)

private theorem fold_add_zero_terms_acc
    (xs : List Nat) (term : Nat → ZMod64 p)
    (hterm : ∀ i, i ∈ xs → term i = 0) (acc : ZMod64 p) :
    xs.foldl (fun acc i => acc + term i) acc = acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [hterm i (by simp), zmod_add_zero]
      exact ih (by
        intro j hj
        exact hterm j (by simp [hj])) acc

private theorem fold_add_zero_terms
    (xs : List Nat) (term : Nat → ZMod64 p)
    (hterm : ∀ i, i ∈ xs → term i = 0) :
    xs.foldl (fun acc i => acc + term i) 0 = 0 := by
  exact fold_add_zero_terms_acc xs term hterm 0

private theorem fold_add_single_range
    (n t : Nat) (a : ZMod64 p) (ht : t < n + 1) :
    (List.range (n + 1)).foldl
        (fun acc i => acc + if i = t then a else 0) 0 = a := by
  induction n with
  | zero =>
      have ht0 : t = 0 := by omega
      simp [ht0]
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hlast : t = n + 1
      · subst t
        have hzero :
            (List.range (n + 1)).foldl
                (fun acc i => acc + if i = n + 1 then a else 0) 0 = 0 := by
          apply fold_add_zero_terms
          intro i hi
          have hi' : i < n + 1 := List.mem_range.mp hi
          have hne : i ≠ n + 1 := by omega
          rw [if_neg hne]
        rw [hzero, if_pos rfl]
        exact zmod_zero_add a
      · have ht' : t < n + 1 := by omega
        rw [ih ht']
        have hne : n + 1 ≠ t := by omega
        rw [if_neg hne]
        exact zmod_add_zero a

/-- Multiplying `f` by the scaled monomial `c · Xⁱ` shifts each coefficient up
by `i` and scales it by `c`. Gives a closed form for the coefficients produced
when a polynomial is multiplied by a single monomial term. -/
theorem coeff_mul_shift_scale_one
    (f : FpPoly p) (c : ZMod64 p) (i n : Nat) :
    (f * DensePoly.shift i (DensePoly.scale c (1 : FpPoly p))).coeff n =
      if i ≤ n then f.coeff (n - i) * c else 0 := by
  rw [coeff_mul, mulCoeffSum_eq_degree_bound f
    (DensePoly.shift i (DensePoly.scale c (1 : FpPoly p))) n]
  by_cases hin : i ≤ n
  · calc
      (List.range (n + 1)).foldl
          (fun acc j =>
            acc + mulCoeffTerm f
              (DensePoly.shift i (DensePoly.scale c (1 : FpPoly p))) n j) 0
          =
        (List.range (n + 1)).foldl
          (fun acc j => acc + if j = n - i then f.coeff (n - i) * c else 0) 0 := by
            apply fold_add_congr
            intro j hj
            have hjn : j < n + 1 := List.mem_range.mp hj
            unfold mulCoeffTerm
            by_cases hnj : n < j
            · have hne : j ≠ n - i := by omega
              rw [if_pos hnj, if_neg hne]
            · simp [hnj, -DensePoly.coeff_shift]
              have hzero : c * (0 : ZMod64 p) = 0 := by grind
              rw [DensePoly.coeff_shift_scale i c (1 : FpPoly p) (n - j) hzero]
              by_cases hlt : n - j < i
              · have hne : j ≠ n - i := by
                  intro hji
                  subst j
                  have hnot : ¬ n - (n - i) < i := by
                    rw [Nat.sub_sub_self hin]
                    omega
                  exact hnot hlt
                rw [if_neg hne]
                simp [hlt]
                exact zmod_mul_zero (f.coeff j)
              · by_cases hji : j = n - i
                · subst j
                  rw [if_pos rfl]
                  simp [hlt]
                  rw [coeff_one]
                  have hsub : n - (n - i) - i = 0 := by
                    rw [Nat.sub_sub_self hin]
                    simp
                  simp [hsub]
                · rw [if_neg hji]
                  simp [hlt]
                  rw [coeff_one]
                  have hsub : n - j - i ≠ 0 := by omega
                  simp [hsub]
      _ = f.coeff (n - i) * c := by
            exact fold_add_single_range n (n - i) (f.coeff (n - i) * c) (by omega)
      _ = if i ≤ n then f.coeff (n - i) * c else 0 := by
            rw [if_pos hin]
  · have hzero :
        (List.range (n + 1)).foldl
            (fun acc j =>
              acc + mulCoeffTerm f
                (DensePoly.shift i (DensePoly.scale c (1 : FpPoly p))) n j) 0 = 0 := by
      apply fold_add_zero_terms
      intro j hj
      have hjn : j < n + 1 := List.mem_range.mp hj
      unfold mulCoeffTerm
      by_cases hnj : n < j
      · simp [hnj]
      · simp [hnj, -DensePoly.coeff_shift]
        have hzero : c * (0 : ZMod64 p) = 0 := by grind
        rw [DensePoly.coeff_shift_scale i c (1 : FpPoly p) (n - j) hzero]
        have hlt : n - j < i := by omega
        simp [hlt]
        exact zmod_mul_zero (f.coeff j)
    rw [hzero, if_neg hin]

/-- Expands the degree-`n` coefficient of `(f * g) * h` into a left-associated
triple fold: the outer sum over `i` pairs the `i`-th coefficient of `f * g`
(itself an inner fold over `j`) with `h.coeff (n - i)`. First step of the
associativity proof, putting `(f * g) * h` into a nested-fold form. -/
private theorem fold_mulCoeff_assoc_left_expand
    (f g h : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i => acc + mulCoeffTerm (f * g) h n i) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0) 0 := by
  apply fold_add_congr
  intro i hi
  exact mulCoeffTerm_mul_left_expand f g h n i (by
    have hi' : i < n + 1 := List.mem_range.mp hi
    omega)

/-- Expands the degree-`n` coefficient of `f * (g * h)` into a right-associated
triple fold: the outer sum over `i` pairs `f.coeff i` with the `(n - i)`-th
coefficient of `g * h` (itself an inner fold over `j`). Mirror of
`fold_mulCoeff_assoc_left_expand` for the other parenthesization. -/
private theorem fold_mulCoeff_assoc_right_expand
    (f g h : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i => acc + mulCoeffTerm f (g * h) n i) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0) 0 := by
  apply fold_add_congr
  intro i hi
  exact mulCoeffTerm_mul_right_expand f g h n i (by
    have hi' : i < n + 1 := List.mem_range.mp hi
    omega)

/-- Rewrites the left-associated triple fold into the common coefficient-indexed
canonical form, replacing each `mulCoeffTerm f g i j` by the explicit product
`f.coeff j * g.coeff (i - j)`. Normalizes `(f * g) * h` so it can be compared to
the right-associated side via reindexing. -/
private theorem fold_mulCoeff_assoc_left_normalize
    (f g h : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + (f.coeff j * g.coeff (i - j)) * h.coeff (n - i)) 0) 0 := by
  apply fold_add_congr
  intro i _hi
  apply fold_add_congr
  intro j hj
  have hji : ¬ i < j := by
    have hj' : j < i + 1 := List.mem_range.mp hj
    omega
  simp [mulCoeffTerm, hji]

/-- Rewrites the right-associated triple fold into the same coefficient-indexed
canonical form, replacing each `mulCoeffTerm g h (n - i) j` by the explicit
product `g.coeff j * h.coeff (n - i - j)`. Counterpart of
`fold_mulCoeff_assoc_left_normalize` for `f * (g * h)`. -/
private theorem fold_mulCoeff_assoc_right_normalize
    (f g h : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + (f.coeff i * g.coeff j) * h.coeff (n - i - j)) 0) 0 := by
  apply fold_add_congr
  intro i _hi
  apply fold_add_congr
  intro j hj
  have hji : ¬ n - i < j := by
    have hj' : j < n - i + 1 := List.mem_range.mp hj
    omega
  simp [mulCoeffTerm, hji]
  grind

/-- The pivotal associativity lemma: the left- and right-associated triple folds
are equal. It normalizes both sides into canonical form (via the two
`*_normalize` lemmas) and identifies them as a reindexing of one another over
the triangle of index triples `(i, j, n - i - j)` (`fold_triangular_assoc_reindex`).
This permutation equality is what makes `FpPoly` multiplication associative. -/
private theorem mulCoeff_assoc_reindex
    (f g h : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0) 0 := by
  calc
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0) 0
        = (List.range (n + 1)).foldl
            (fun acc i =>
              acc +
                (List.range (i + 1)).foldl
                  (fun acc j => acc + (f.coeff j * g.coeff (i - j)) * h.coeff (n - i)) 0) 0 := by
            exact fold_mulCoeff_assoc_left_normalize f g h n
    _ = (List.range (n + 1)).foldl
            (fun acc i =>
              acc +
                (List.range (n - i + 1)).foldl
                  (fun acc j => acc + (f.coeff i * g.coeff j) * h.coeff (n - i - j)) 0) 0 := by
            exact fold_triangular_assoc_reindex n
              (fun a b c => (f.coeff a * g.coeff b) * h.coeff c)
    _ = (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0) 0 := by
            exact (fold_mulCoeff_assoc_right_normalize f g h n).symm

private theorem fold_left_distrib (xs : List Nat) (f g h : FpPoly p) (n : Nat) :
    xs.foldl (fun acc i => acc + mulCoeffTerm f (g + h) n i) 0 =
      xs.foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 +
        xs.foldl (fun acc i => acc + mulCoeffTerm f h n i) 0 := by
  simpa [show (0 : ZMod64 p) + 0 = 0 by grind] using
    fold_distrib_acc (p := p) xs 0 0
      (fun i => mulCoeffTerm f (g + h) n i)
      (fun i => mulCoeffTerm f g n i)
      (fun i => mulCoeffTerm f h n i)
      (mulCoeffTerm_left_distrib f g h n)

private theorem fold_right_distrib (xs : List Nat) (f g h : FpPoly p) (n : Nat) :
    xs.foldl (fun acc i => acc + mulCoeffTerm (f + g) h n i) 0 =
      xs.foldl (fun acc i => acc + mulCoeffTerm f h n i) 0 +
        xs.foldl (fun acc i => acc + mulCoeffTerm g h n i) 0 := by
  simpa [show (0 : ZMod64 p) + 0 = 0 by grind] using
    fold_distrib_acc (p := p) xs 0 0
      (fun i => mulCoeffTerm (f + g) h n i)
      (fun i => mulCoeffTerm f h n i)
      (fun i => mulCoeffTerm g h n i)
      (mulCoeffTerm_right_distrib f g h n)

/-- Multiplication distributes over addition on the left. Part of the
commutative-ring structure on `FpPoly p`. -/
theorem left_distrib (f g h : FpPoly p) :
    f * (g + h) = f * g + f * h := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_add_semiring]
  simp [coeff_mul, mulCoeffSum, fold_left_distrib]

/-- Multiplication distributes over addition on the right. Part of the
commutative-ring structure on `FpPoly p`. -/
theorem right_distrib (f g h : FpPoly p) :
    (f + g) * h = f * h + g * h := by
  apply DensePoly.ext_coeff
  intro n
  let m := max (max (f + g).size f.size) g.size
  rw [DensePoly.coeff_add_semiring, coeff_mul_of_size_le (f + g) h n m (by dsimp [m]; omega),
    coeff_mul_of_size_le f h n m (by dsimp [m]; omega),
    coeff_mul_of_size_le g h n m (by dsimp [m]; omega)]
  exact fold_right_distrib (List.range m) f g h n

/-- Polynomial multiplication is associative, letting callers regroup products
freely. Part of the commutative-ring structure on `FpPoly p`. -/
theorem mul_assoc (f g h : FpPoly p) :
    (f * g) * h = f * (g * h) := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_mul, coeff_mul, mulCoeffSum_eq_degree_bound (f * g) h n,
    mulCoeffSum_eq_degree_bound f (g * h) n]
  calc
    (List.range (n + 1)).foldl
        (fun acc i => acc + mulCoeffTerm (f * g) h n i) 0
        = (List.range (n + 1)).foldl
            (fun acc i =>
              acc +
                (List.range (i + 1)).foldl
                  (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0) 0 := by
            exact fold_mulCoeff_assoc_left_expand f g h n
    _ = (List.range (n + 1)).foldl
            (fun acc i =>
              acc +
                (List.range (n - i + 1)).foldl
                  (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0) 0 := by
            exact mulCoeff_assoc_reindex f g h n
    _ = (List.range (n + 1)).foldl
        (fun acc i => acc + mulCoeffTerm f (g * h) n i) 0 := by
            exact (fold_mulCoeff_assoc_right_expand f g h n).symm

/-- `FpPoly p` is a multiplicative monoid for `Std`, so the shared
`List.foldl_mul_*` algebra and core's `List.foldl_assoc` apply to fold-products
of `FpPoly`. -/
instance instAssociativeMul {p : Nat} [ZMod64.Bounds p] :
    Std.Associative (· * · : FpPoly p → FpPoly p → FpPoly p) :=
  ⟨mul_assoc⟩

instance instLawfulIdentityMul {p : Nat} [ZMod64.Bounds p] :
    Std.LawfulIdentity (· * · : FpPoly p → FpPoly p → FpPoly p) 1 where
  left_id := one_mul
  right_id := mul_one

end FpPoly
end Hex
