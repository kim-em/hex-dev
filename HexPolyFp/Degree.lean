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
public import HexPolyFp.Ring
import all HexPolyFp.Field
import all HexPolyFp.Ring

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
Scalar scaling, degree and leading-coefficient lemmas, size/divisibility/
gcd arithmetic, monomial multiplication, and `linearPow` for `FpPoly`.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]
/-- Scalar scaling distributes over polynomial addition. Lets callers move a
scalar across a sum, for example when normalizing a linear combination. -/
theorem scale_add (c : ZMod64 p) (f g : FpPoly p) :
    DensePoly.scale c (f + g) =
      DensePoly.scale c f + DensePoly.scale c g := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : c * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero, DensePoly.coeff_add_semiring, DensePoly.coeff_add_semiring,
    DensePoly.coeff_scale _ _ _ hzero, DensePoly.coeff_scale _ _ _ hzero]
  grind

/-- Scaling a product equals scaling its left factor. With `mul_comm` this lets
a scalar be absorbed into either factor of a product. -/
theorem scale_mul_left (c : ZMod64 p) (f g : FpPoly p) :
    DensePoly.scale c (f * g) =
      DensePoly.scale c f * g := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : c * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero, coeff_mul, coeff_mul,
    mulCoeffSum_eq_degree_bound (DensePoly.scale c f) g n, mulCoeffSum_eq_degree_bound f g n,
    fold_mul_left]
  apply fold_add_congr
  intro i _hi
  unfold mulCoeffTerm
  by_cases hn : n < i
  · simp [hn]
  · simp [hn]
    rw [DensePoly.coeff_scale _ _ _ hzero]
    grind

/-- Scaling the unit polynomial by `c` yields the constant polynomial `C c`.
Identifies the scalar action on `1` with the constant embedding. -/
theorem scale_one_poly (c : ZMod64 p) :
    DensePoly.scale c (1 : FpPoly p) = DensePoly.C c := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : c * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero]
  change c * (DensePoly.C (1 : ZMod64 p)).coeff n = (DensePoly.C c).coeff n
  rw [DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => grind
  | succ n => exact hzero

/-- Multiplying by a constant polynomial coincides with scalar scaling. Lets
callers convert between the `C c * f` and `scale c f` representations so the
scale-specific lemmas apply to constant multiplications. -/
theorem C_mul_eq_scale (c : ZMod64 p) (f : FpPoly p) :
    DensePoly.C c * f = DensePoly.scale c f := by
  have hscale := scale_mul_left c (1 : FpPoly p) f
  rw [one_mul, scale_one_poly] at hscale
  exact hscale.symm

/-- Evaluating `C c * f` at `x` multiplies the value of `f` by the scalar `c`.
The constant-multiplication special case of `eval_mul`. -/
@[grind =]
theorem eval_C_mul (c : ZMod64 p) (f : FpPoly p) (x : ZMod64 p) :
    DensePoly.eval (DensePoly.C c * f) x = c * DensePoly.eval f x := by
  rw [C_mul_eq_scale, eval_eq_coeff_power_sum_upTo_bound (DensePoly.scale c f) x (bound := f.size)]
  · rw [eval_eq_coeff_power_sum_upTo_size f x]
    have hcoeff :
        (fun i => (DensePoly.scale c f).coeff i) =
          (fun i => c * f.coeff i) := by
      funext i
      have hzero : c * (0 : ZMod64 p) = 0 := by grind
      rw [DensePoly.coeff_scale _ _ _ hzero]
    rw [hcoeff]
    exact evalCoeffPowerSumUpTo_const_mul c (fun i => f.coeff i) x f.size 0
  · apply size_le_of_coeff_eq_zero_from
    intro i hi
    have hzero : c * (0 : ZMod64 p) = 0 := by grind
    rw [DensePoly.coeff_scale _ _ _ hzero, DensePoly.coeff_eq_zero_of_size_le f hi]
    exact hzero

/-- Evaluating the constant polynomial `1` at any point gives `1`. -/
@[simp, grind =] theorem eval_one (x : ZMod64 p) :
    DensePoly.eval (1 : FpPoly p) x = 1 := by
  change DensePoly.eval (FpPoly.C (1 : ZMod64 p)) x = 1
  exact eval_C 1 x

private theorem fold_eval_shift_scale_rows
    (xs : List Nat) (acc : FpPoly p) (f h : FpPoly p) (x : ZMod64 p) :
    DensePoly.eval
        (xs.foldl
          (fun acc i => acc + DensePoly.shift i (DensePoly.scale (f.coeff i) h))
          acc) x =
      xs.foldl
        (fun acc i => acc + (f.coeff i * x ^ i) * DensePoly.eval h x)
        (DensePoly.eval acc x) := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + DensePoly.shift i (DensePoly.scale (f.coeff i) h)), eval_add,
        eval_shift_scale_row]

private theorem fold_shift_scale_one_eq_self (f : FpPoly p) :
    (List.range f.size).foldl
        (fun acc i => acc + DensePoly.shift i (DensePoly.scale (f.coeff i) (1 : FpPoly p)))
        (0 : FpPoly p) = f := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_mul_one_fold]
  by_cases hn : n < f.size
  · simp [hn]
  · have hzero : f.coeff n = 0 :=
      DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hn)
    simp [hn, hzero]

private theorem mul_eq_fold_shift_scale_rows (f h : FpPoly p) :
    f * h =
      (List.range f.size).foldl
        (fun acc i => acc + DensePoly.shift i (DensePoly.scale (f.coeff i) h))
        (0 : FpPoly p) := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_mul, coeff_mul_fold]
  unfold mulCoeffSum
  rw [DensePoly.coeff_zero]
  rfl

/-- Evaluation is multiplicative: the value of a product is the product of the
values. Together with `eval_add` this is the ring-homomorphism property of
evaluation, used wherever a root or factorization is checked pointwise. -/
@[simp, grind =]
theorem eval_mul (f h : FpPoly p) (x : ZMod64 p) :
    DensePoly.eval (f * h) x = DensePoly.eval f x * DensePoly.eval h x := by
  rw [mul_eq_fold_shift_scale_rows, fold_eval_shift_scale_rows, DensePoly.eval_zero]
  have hf :
      DensePoly.eval f x =
        (List.range f.size).foldl
          (fun acc i => acc + (f.coeff i * x ^ i) * DensePoly.eval (1 : FpPoly p) x)
          (DensePoly.eval (0 : FpPoly p) x) := by
    rw [← fold_eval_shift_scale_rows
      (List.range f.size) (0 : FpPoly p) f (1 : FpPoly p) x]
    rw [fold_shift_scale_one_eq_self]
  rw [hf, DensePoly.eval_zero, eval_one]
  have hone :
      (List.range f.size).foldl
          (fun acc i => acc + (f.coeff i * x ^ i) * (1 : ZMod64 p)) 0 =
        (List.range f.size).foldl
          (fun acc i => acc + f.coeff i * x ^ i) 0 := by
    apply fold_add_congr
    intro i _hi
    grind
  calc
    (List.range f.size).foldl
        (fun acc i => acc + (f.coeff i * x ^ i) * DensePoly.eval h x) 0
        =
      (List.range f.size).foldl
          (fun acc i => acc + f.coeff i * x ^ i) 0 * DensePoly.eval h x := by
        exact (fold_mul_right (p := p) (List.range f.size)
          (fun i => f.coeff i * x ^ i) (DensePoly.eval h x)).symm
    _ =
      (List.range f.size).foldl
          (fun acc i => acc + (f.coeff i * x ^ i) * (1 : ZMod64 p)) 0 *
        DensePoly.eval h x := by
        rw [hone]

/-- Two successive scalings compose into a single scaling by the product of the
scalars. Lets callers collapse a chain of scalar adjustments into one. -/
theorem scale_scale (c d : ZMod64 p) (f : FpPoly p) :
    DensePoly.scale c (DensePoly.scale d f) = DensePoly.scale (c * d) f := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_c : c * (0 : ZMod64 p) = 0 := by grind
  have hzero_d : d * (0 : ZMod64 p) = 0 := by grind
  have hzero_cd : (c * d) * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero_c, DensePoly.coeff_scale _ _ _ hzero_d,
    DensePoly.coeff_scale _ _ _ hzero_cd]
  grind

/-- Scaling by `1` leaves the polynomial unchanged. The identity law of the
scalar action, needed to recognize a trivial scaling as a no-op. -/
theorem scale_one_left (f : FpPoly p) :
    DensePoly.scale (1 : ZMod64 p) f = f := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : (1 : ZMod64 p) * 0 = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero]
  grind

private theorem zmod64_one_ne_zero [ZMod64.PrimeModulus p] :
    (1 : ZMod64 p) ≠ (0 : ZMod64 p) := by
  intro h
  have h2 : 2 ≤ p := (ZMod64.PrimeModulus.prime (p := p)).two_le
  have htoNat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat :=
    congrArg ZMod64.toNat h
  rw [show ((1 : ZMod64 p).toNat) = 1 % p from ZMod64.toNat_one,
      show ((0 : ZMod64 p).toNat) = 0 from ZMod64.toNat_zero,
      Nat.mod_eq_of_lt (by omega : 1 < p)] at htoNat
  exact absurd htoNat (by omega)

/-- Scaling never increases the coefficient-array size. The unconditional size
bound, valid even when `c = 0` collapses leading coefficients to zero. -/
theorem scale_size_le (c : ZMod64 p) (f : FpPoly p) :
    (DensePoly.scale c f).size ≤ f.size := by
  by_cases hle : (DensePoly.scale c f).size ≤ f.size
  · exact hle
  · exfalso
    let i := (DensePoly.scale c f).size - 1
    have hscale_pos : 0 < (DensePoly.scale c f).size := by omega
    have htop_ne :
        (DensePoly.scale c f).coeff i ≠ (0 : ZMod64 p) :=
      DensePoly.coeff_last_ne_zero_of_pos_size (DensePoly.scale c f) hscale_pos
    have hfi : f.size ≤ i := by
      dsimp [i]
      omega
    have hzero_c : c * (0 : ZMod64 p) = 0 := by grind
    rw [DensePoly.coeff_scale _ _ _ hzero_c] at htop_ne
    rw [DensePoly.coeff_eq_zero_of_size_le f hfi] at htop_ne
    exact htop_ne hzero_c

/-- Scaling by a nonzero scalar preserves the coefficient-array size: over a
field the top coefficient cannot be cancelled. Callers use this to know that
a unit scaling preserves degree. -/
theorem scale_size_eq_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) (f : FpPoly p) :
    (DensePoly.scale c f).size = f.size := by
  apply Nat.le_antisymm
  · exact scale_size_le c f
  · by_cases hfsize : f.size = 0
    · omega
    · let i := f.size - 1
      have hf_pos : 0 < f.size := Nat.pos_of_ne_zero hfsize
      have hf_top : f.coeff i ≠ (0 : ZMod64 p) :=
        DensePoly.coeff_last_ne_zero_of_pos_size f hf_pos
      have hprod_ne : c * f.coeff i ≠ (0 : ZMod64 p) := by
        intro hprod
        rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero
            (ZMod64.PrimeModulus.prime (p := p)) hprod with hcz | hfz
        · exact hc hcz
        · exact hf_top hfz
      have hzero_c : c * (0 : ZMod64 p) = 0 := by grind
      have hcoeff :
          (DensePoly.scale c f).coeff i ≠ (0 : ZMod64 p) := by
        rw [DensePoly.coeff_scale _ _ _ hzero_c]
        exact hprod_ne
      by_cases hle : f.size ≤ (DensePoly.scale c f).size
      · exact hle
      · exfalso
        have hle' : (DensePoly.scale c f).size ≤ i := by
          dsimp [i]
          omega
        exact hcoeff (DensePoly.coeff_eq_zero_of_size_le (DensePoly.scale c f) hle')

/-- Scaling by a nonzero scalar preserves the optional degree. The degree-level
counterpart of `scale_size_eq_of_ne_zero`, used when reasoning in terms of
`degree?` rather than `size`. -/
theorem scale_degree?_eq_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) (f : FpPoly p) :
    (DensePoly.scale c f).degree? = f.degree? := by
  have hsize := scale_size_eq_of_ne_zero (p := p) hc f
  unfold DensePoly.degree?
  rw [hsize]

/-- Nonzero scaling preserves the degree in the `degree?.getD 0` form callers
commonly carry, sparing them an `Option` unfolding at each use site. -/
theorem scale_degree?_getD_eq_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) (f : FpPoly p) :
    (DensePoly.scale c f).degree?.getD 0 = f.degree?.getD 0 := by
  rw [scale_degree?_eq_of_ne_zero (p := p) hc f]

/-- For a nonempty polynomial the leading coefficient is the coefficient at the
top index `size - 1`. Gives callers a concrete index for the leading
coefficient when they need to compute or rewrite it. -/
theorem leadingCoeff_eq_coeff_pred
    (f : FpPoly p) (hpos : 0 < f.size) :
    DensePoly.leadingCoeff f = f.coeff (f.size - 1) := by
  simp [DensePoly.leadingCoeff, DensePoly.coeff, DensePoly.size]

/-- A polynomial of positive degree has a nonzero leading coefficient. The
nondegeneracy fact that justifies inverting the leading coefficient during
monic normalization. -/
theorem leadingCoeff_ne_zero_of_pos_degree
    (f : FpPoly p) (hpos : 0 < f.degree?.getD 0) :
    DensePoly.leadingCoeff f ≠ 0 := by
  have hfsize : 0 < f.size := by
    by_cases h : 0 < f.size
    · exact h
    · exfalso
      have hsize : f.size = 0 := by omega
      simp [DensePoly.degree?, hsize] at hpos
  rw [leadingCoeff_eq_coeff_pred f hfsize]
  exact DensePoly.coeff_last_ne_zero_of_pos_size f hfsize

/-- For a nonzero scalar and a positive-degree polynomial the leading
coefficient scales by `c`. Lets callers track how the leading coefficient moves
under a unit scaling, the key step in computing a monic-normalizing scalar. -/
theorem leadingCoeff_scale_of_ne_zero_of_pos_degree [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) (f : FpPoly p)
    (hpos : 0 < f.degree?.getD 0) :
    DensePoly.leadingCoeff (DensePoly.scale c f) =
      c * DensePoly.leadingCoeff f := by
  have hfpos : 0 < f.size := by
    by_cases h : 0 < f.size
    · exact h
    · exfalso
      have hsize : f.size = 0 := by omega
      simp [DensePoly.degree?, hsize] at hpos
  have hs : (DensePoly.scale c f).size = f.size :=
    scale_size_eq_of_ne_zero (p := p) hc f
  have hscale_pos : 0 < (DensePoly.scale c f).size := by omega
  have hscale_zero : c * (0 : ZMod64 p) = 0 := by grind
  rw [leadingCoeff_eq_coeff_pred (DensePoly.scale c f) hscale_pos,
    leadingCoeff_eq_coeff_pred f hfpos, show (DensePoly.scale c f).size - 1 = f.size - 1 by omega,
    DensePoly.coeff_scale _ _ _ hscale_zero]

/-- The same leading-coefficient scaling law as
`leadingCoeff_scale_of_ne_zero_of_pos_degree`, stated from the weaker nonempty
hypothesis `f.size ≠ 0` so it applies to constants as well as higher-degree
polynomials. -/
theorem leadingCoeff_scale_of_ne_zero_of_nonzero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) (f : FpPoly p)
    (hfsize : f.size ≠ 0) :
    DensePoly.leadingCoeff (DensePoly.scale c f) =
      c * DensePoly.leadingCoeff f := by
  have hfpos : 0 < f.size := Nat.pos_of_ne_zero hfsize
  have hscale_size : (DensePoly.scale c f).size = f.size :=
    scale_size_eq_of_ne_zero (p := p) hc f
  have hscale_pos : 0 < (DensePoly.scale c f).size := by omega
  have hscale_zero : c * (0 : ZMod64 p) = 0 := by grind
  rw [leadingCoeff_eq_coeff_pred (DensePoly.scale c f) hscale_pos,
    leadingCoeff_eq_coeff_pred f hfpos, show (DensePoly.scale c f).size - 1 = f.size - 1 by omega,
    DensePoly.coeff_scale _ _ _ hscale_zero]

/-- Scaling a positive-degree polynomial by the inverse of its leading
coefficient produces a monic polynomial. This is the monic-normalization step
that puts a polynomial into the canonical leading-`1` form. -/
theorem scale_inv_leadingCoeff_monic [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hpos : 0 < f.degree?.getD 0) :
    DensePoly.Monic (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f) := by
  have hlead_ne := leadingCoeff_ne_zero_of_pos_degree f hpos
  have hinv_ne : (DensePoly.leadingCoeff f)⁻¹ ≠ (0 : ZMod64 p) := by
    intro hinv
    change ZMod64.inv (DensePoly.leadingCoeff f) = (0 : ZMod64 p) at hinv
    have hone := ZMod64.inv_mul_eq_one_of_prime
      (ZMod64.PrimeModulus.prime (p := p)) hlead_ne
    rw [hinv] at hone
    have hzero : (0 : ZMod64 p) * DensePoly.leadingCoeff f = 0 := by grind
    rw [hzero] at hone
    exact zmod64_one_ne_zero hone.symm
  unfold DensePoly.Monic
  rw [leadingCoeff_scale_of_ne_zero_of_pos_degree (p := p) hinv_ne f hpos]
  exact ZMod64.inv_mul_eq_one_of_prime
    (ZMod64.PrimeModulus.prime (p := p)) hlead_ne

/-- Scaling by a nonzero (hence unit) scalar preserves irreducibility in both
directions. Lets callers normalize a polynomial to monic form without changing
whether it is irreducible. -/
theorem irreducible_scale_iff_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) (f : FpPoly p) :
    FpPoly.Irreducible (DensePoly.scale c f) ↔ FpPoly.Irreducible f := by
  constructor
  · intro hcf
    have hcinv : c⁻¹ ≠ (0 : ZMod64 p) := by
      intro hinv
      change ZMod64.inv c = (0 : ZMod64 p) at hinv
      have hone := ZMod64.inv_mul_eq_one_of_prime
        (ZMod64.PrimeModulus.prime (p := p)) hc
      rw [hinv] at hone
      have hzero : (0 : ZMod64 p) * c = 0 := by grind
      rw [hzero] at hone
      exact zmod64_one_ne_zero hone.symm
    have hscale_back : DensePoly.scale c⁻¹ (DensePoly.scale c f) = f := by
      rw [scale_scale]
      have hmul : c⁻¹ * c = (1 : ZMod64 p) :=
        ZMod64.inv_mul_eq_one_of_prime (ZMod64.PrimeModulus.prime (p := p)) hc
      rw [hmul]
      exact scale_one_left f
    constructor
    · intro hfzero
      apply hcf.1
      rw [hfzero]
      apply DensePoly.ext_coeff
      intro n
      have hzero : c * (0 : ZMod64 p) = 0 := by grind
      rw [DensePoly.coeff_scale _ _ _ hzero, DensePoly.coeff_zero]
      exact hzero
    · intro a b hab
      have hab' : DensePoly.scale c (a * b) = DensePoly.scale c f := by
        rw [hab]
      rw [scale_mul_left] at hab'
      rcases hcf.2 (DensePoly.scale c a) b hab' with ha | hb
      · left
        rwa [scale_degree?_eq_of_ne_zero (p := p) hc a] at ha
      · right
        exact hb
  · intro hf
    constructor
    · intro hcfzero
      apply hf.1
      have hback : DensePoly.scale c⁻¹ (DensePoly.scale c f) = f := by
        rw [scale_scale]
        have hmul : c⁻¹ * c = (1 : ZMod64 p) :=
          ZMod64.inv_mul_eq_one_of_prime (ZMod64.PrimeModulus.prime (p := p)) hc
        rw [hmul]
        exact scale_one_left f
      rw [hcfzero] at hback
      have hzero : DensePoly.scale c⁻¹ (0 : FpPoly p) = 0 := by
        apply DensePoly.ext_coeff
        intro n
        have hz : c⁻¹ * (0 : ZMod64 p) = 0 := by grind
        rw [DensePoly.coeff_scale _ _ _ hz, DensePoly.coeff_zero]
        exact hz
      rw [hzero] at hback
      exact hback.symm
    · intro a b hab
      have hab_scaled : DensePoly.scale c⁻¹ (a * b) = f := by
        rw [hab, scale_scale]
        have hmul : c⁻¹ * c = (1 : ZMod64 p) :=
          ZMod64.inv_mul_eq_one_of_prime (ZMod64.PrimeModulus.prime (p := p)) hc
        rw [hmul]
        exact scale_one_left f
      rw [scale_mul_left] at hab_scaled
      rcases hf.2 (DensePoly.scale c⁻¹ a) b hab_scaled with ha | hb
      · left
        have hcinv : c⁻¹ ≠ (0 : ZMod64 p) := by
          intro hinv
          change ZMod64.inv c = (0 : ZMod64 p) at hinv
          have hone := ZMod64.inv_mul_eq_one_of_prime
            (ZMod64.PrimeModulus.prime (p := p)) hc
          rw [hinv] at hone
          have hzero : (0 : ZMod64 p) * c = 0 := by grind
          rw [hzero] at hone
          exact zmod64_one_ne_zero hone.symm
        rwa [scale_degree?_eq_of_ne_zero (p := p) hcinv a] at ha
      · right
        exact hb

/-- Forward direction of `irreducible_scale_iff_of_ne_zero`: a nonzero scaling
of an irreducible polynomial is irreducible. The convenient form when the
hypothesis is irreducibility of the unscaled polynomial. -/
theorem irreducible_scale_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) {f : FpPoly p}
    (hf : FpPoly.Irreducible f) :
    FpPoly.Irreducible (DensePoly.scale c f) :=
  (irreducible_scale_iff_of_ne_zero (p := p) hc f).2 hf

/-- Reverse direction of `irreducible_scale_iff_of_ne_zero`: if a nonzero
scaling is irreducible then so is the unscaled polynomial. Lets callers
transfer irreducibility back from a normalized representative. -/
theorem irreducible_of_scale_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) {f : FpPoly p}
    (hf : FpPoly.Irreducible (DensePoly.scale c f)) :
    FpPoly.Irreducible f :=
  (irreducible_scale_iff_of_ne_zero (p := p) hc f).1 hf

/-- Divisibility is preserved when both sides are scaled by the same scalar.
Holds for any `c`, so callers can scale a divisibility relation without a
nonzero hypothesis. -/
theorem dvd_scale_of_dvd {c : ZMod64 p} {f g : FpPoly p}
    (hfg : f ∣ g) : DensePoly.scale c f ∣ DensePoly.scale c g := by
  rcases hfg with ⟨q, hq⟩
  exact ⟨q, by rw [← scale_mul_left, hq]⟩

/-- Converse of `dvd_scale_of_dvd` for a nonzero scalar: a divisibility between
equally scaled polynomials reflects back to the originals. Lets callers strip a
common unit scaling from both sides of a divisibility. -/
theorem dvd_of_scale_dvd [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) {f g : FpPoly p}
    (hfg : DensePoly.scale c f ∣ DensePoly.scale c g) : f ∣ g := by
  rcases hfg with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have hscaled : DensePoly.scale c⁻¹ (DensePoly.scale c g) =
      DensePoly.scale c⁻¹ (DensePoly.scale c f * q) := by
    rw [hq]
  rw [scale_scale] at hscaled
  rw [scale_mul_left, scale_scale] at hscaled
  have hmul : c⁻¹ * c = (1 : ZMod64 p) :=
    ZMod64.inv_mul_eq_one_of_prime (ZMod64.PrimeModulus.prime (p := p)) hc
  rw [hmul, scale_one_left, scale_one_left] at hscaled
  exact hscaled

/-- A nonzero scaling of `f` divides `f` itself: scaling by a unit produces an
associate. Lets callers treat a unit-scaled polynomial and the original as
mutually divisible. -/
theorem dvd_scale_self_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) (f : FpPoly p) :
    DensePoly.scale c f ∣ f := by
  refine ⟨DensePoly.C c⁻¹, ?_⟩
  rw [mul_comm, C_mul_eq_scale, scale_scale]
  have hmul : c⁻¹ * c = (1 : ZMod64 p) :=
    ZMod64.inv_mul_eq_one_of_prime (ZMod64.PrimeModulus.prime (p := p)) hc
  rw [hmul, scale_one_left]

private theorem mulCoeffTerm_eq_zero_above_top
    (f g : FpPoly p) {n i : Nat} (hi : i < f.size)
    (hbound : f.size - 1 + (g.size - 1) < n) :
    mulCoeffTerm f g n i = 0 := by
  unfold mulCoeffTerm
  have hni : ¬ n < i := by omega
  have h_gi : g.size ≤ n - i := by omega
  have hg_zero : g.coeff (n - i) = 0 :=
    DensePoly.coeff_eq_zero_of_size_le g h_gi
  simp [hni, hg_zero]

private theorem coeff_mul_eq_zero_above_top
    (f g : FpPoly p) {n : Nat}
    (hbound : f.size - 1 + (g.size - 1) < n) :
    (f * g).coeff n = 0 := by
  rw [coeff_mul]
  unfold mulCoeffSum
  have hfold : ∀ (xs : List Nat) (acc : ZMod64 p),
      (∀ j ∈ xs, j < f.size) →
      xs.foldl (fun acc i => acc + mulCoeffTerm f g n i) acc = acc := by
    intro xs
    induction xs with
    | nil => intro acc _; rfl
    | cons j xs ih =>
        intro acc hxs
        have hj : j < f.size := hxs j (by simp)
        simp only [List.foldl_cons]
        have hzero : mulCoeffTerm f g n j = 0 :=
          mulCoeffTerm_eq_zero_above_top f g hj hbound
        rw [hzero]
        have hadd : acc + (0 : ZMod64 p) = acc := zmod_add_zero acc
        rw [hadd]
        exact ih acc (fun k hk => hxs k (by simp [hk]))
  exact hfold (List.range f.size) 0 (fun j hj => List.mem_range.mp hj)

/--
Over a prime modulus, the degree of a product of nonzero polynomials in
`FpPoly p` equals the sum of the degrees. This is the no-zero-divisors
identity expressed at the level of `degree?.getD 0`.
-/
theorem degree?_mul_eq_add_degree?
    [ZMod64.PrimeModulus p] (a b : FpPoly p)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).degree?.getD 0 = a.degree?.getD 0 + b.degree?.getD 0 := by
  have ha_size_pos : 0 < a.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply ha
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le a (by omega)
  have hb_size_pos : 0 < b.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply hb
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le b (by omega)
  have ha_lead_ne : a.coeff (a.size - 1) ≠ 0 :=
    DensePoly.coeff_last_ne_zero_of_pos_size a ha_size_pos
  have hb_lead_ne : b.coeff (b.size - 1) ≠ 0 :=
    DensePoly.coeff_last_ne_zero_of_pos_size b hb_size_pos
  have hp_prime : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime
  have hprod_ne : a.coeff (a.size - 1) * b.coeff (b.size - 1) ≠ 0 := by
    intro hprod
    rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp_prime hprod with hh | hh
    · exact ha_lead_ne hh
    · exact hb_lead_ne hh
  have htop_ne : (a * b).coeff (a.size - 1 + (b.size - 1)) ≠ 0 := by
    rw [ZMod64.coeff_mul_at_top a b ha_size_pos hb_size_pos]
    exact hprod_ne
  have hab_size_lower : a.size - 1 + (b.size - 1) < (a * b).size := by
    rcases Nat.lt_or_ge (a.size - 1 + (b.size - 1)) (a * b).size with h | hle
    · exact h
    · exact False.elim (htop_ne (DensePoly.coeff_eq_zero_of_size_le _ hle))
  have hab_size_upper : (a * b).size ≤ a.size + b.size - 1 := by
    rcases Nat.lt_or_ge (a.size + b.size - 1) (a * b).size with hgt | hle
    · exfalso
      have hab_size_pos : 0 < (a * b).size := by omega
      have hbound : a.size - 1 + (b.size - 1) < (a * b).size - 1 := by omega
      have htop_zero : (a * b).coeff ((a * b).size - 1) = 0 :=
        coeff_mul_eq_zero_above_top a b hbound
      exact DensePoly.coeff_last_ne_zero_of_pos_size (a * b) hab_size_pos htop_zero
    · exact hle
  have hab_size : (a * b).size = a.size + b.size - 1 := by omega
  have hab_size_ne_zero : (a * b).size ≠ 0 := by omega
  have ha_size_ne_zero : a.size ≠ 0 := Nat.pos_iff_ne_zero.mp ha_size_pos
  have hb_size_ne_zero : b.size ≠ 0 := Nat.pos_iff_ne_zero.mp hb_size_pos
  have hab_deg : (a * b).degree? = some ((a * b).size - 1) := by
    unfold DensePoly.degree?
    simp [hab_size_ne_zero]
  have ha_deg : a.degree? = some (a.size - 1) := by
    unfold DensePoly.degree?
    simp [ha_size_ne_zero]
  have hb_deg : b.degree? = some (b.size - 1) := by
    unfold DensePoly.degree?
    simp [hb_size_ne_zero]
  rw [hab_deg, ha_deg, hb_deg]
  simp
  omega

/-- An `FpPoly p` polynomial is nonzero exactly when its stored coefficient array is nonempty. -/
theorem size_pos_of_ne_zero {f : FpPoly p} (hf : f ≠ 0) : 0 < f.size := by
  apply Nat.pos_of_ne_zero
  intro hsize
  apply hf
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_zero]
  exact DensePoly.coeff_eq_zero_of_size_le f (by omega)

/--
Over a prime modulus, the executable size of a product of two nonzero polynomials in
`FpPoly p` is the sum of their sizes minus one. This is the no-zero-divisors identity at
the level of `DensePoly.size`.
-/
theorem size_mul_eq_add_sub_one
    [ZMod64.PrimeModulus p] (a b : FpPoly p)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).size = a.size + b.size - 1 := by
  have ha_size_pos : 0 < a.size := size_pos_of_ne_zero ha
  have hb_size_pos : 0 < b.size := size_pos_of_ne_zero hb
  have ha_lead_ne : a.coeff (a.size - 1) ≠ 0 :=
    DensePoly.coeff_last_ne_zero_of_pos_size a ha_size_pos
  have hb_lead_ne : b.coeff (b.size - 1) ≠ 0 :=
    DensePoly.coeff_last_ne_zero_of_pos_size b hb_size_pos
  have hp_prime : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime
  have hprod_ne : a.coeff (a.size - 1) * b.coeff (b.size - 1) ≠ 0 := by
    intro hprod
    rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp_prime hprod with hh | hh
    · exact ha_lead_ne hh
    · exact hb_lead_ne hh
  have htop_ne : (a * b).coeff (a.size - 1 + (b.size - 1)) ≠ 0 := by
    rw [ZMod64.coeff_mul_at_top a b ha_size_pos hb_size_pos]
    exact hprod_ne
  have hab_size_lower : a.size - 1 + (b.size - 1) < (a * b).size := by
    rcases Nat.lt_or_ge (a.size - 1 + (b.size - 1)) (a * b).size with h | hle
    · exact h
    · exact False.elim (htop_ne (DensePoly.coeff_eq_zero_of_size_le _ hle))
  have hab_size_upper : (a * b).size ≤ a.size + b.size - 1 := by
    rcases Nat.lt_or_ge (a.size + b.size - 1) (a * b).size with hgt | hle
    · exfalso
      have hab_size_pos : 0 < (a * b).size := by omega
      have hbound : a.size - 1 + (b.size - 1) < (a * b).size - 1 := by omega
      have htop_zero : (a * b).coeff ((a * b).size - 1) = 0 :=
        coeff_mul_eq_zero_above_top a b hbound
      exact DensePoly.coeff_last_ne_zero_of_pos_size (a * b) hab_size_pos htop_zero
    · exact hle
  omega

/--
Over a prime modulus, multiplying two nonzero polynomials in `FpPoly p` gives a nonzero
polynomial: prime-field polynomials form an integral domain.
-/
theorem mul_ne_zero_of_ne_zero
    [ZMod64.PrimeModulus p] {a b : FpPoly p}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  intro hmul
  have ha_size_pos : 0 < a.size := size_pos_of_ne_zero ha
  have hb_size_pos : 0 < b.size := size_pos_of_ne_zero hb
  have hsize := size_mul_eq_add_sub_one a b ha hb
  have habsize : (a * b).size = 0 := by rw [hmul]; rfl
  omega

/-- Leading coefficient of a product equals the product of leading coefficients
on nonzero `FpPoly p` factors: the top-coefficient lemma `coeff_mul_at_top` plus
the size identity `size_mul_eq_add_sub_one` give this directly. -/
theorem leadingCoeff_mul
    [ZMod64.PrimeModulus p] (a b : FpPoly p)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    DensePoly.leadingCoeff (a * b)
      = DensePoly.leadingCoeff a * DensePoly.leadingCoeff b := by
  have ha_pos : 0 < a.size := size_pos_of_ne_zero ha
  have hb_pos : 0 < b.size := size_pos_of_ne_zero hb
  have hab_ne : a * b ≠ 0 := mul_ne_zero_of_ne_zero ha hb
  have hab_pos : 0 < (a * b).size := size_pos_of_ne_zero hab_ne
  have hsize := size_mul_eq_add_sub_one a b ha hb
  have hindex : (a * b).size - 1 = a.size - 1 + (b.size - 1) := by omega
  rw [DensePoly.leadingCoeff_eq_coeff_last (a * b) hab_pos, hindex,
    DensePoly.leadingCoeff_eq_coeff_last a ha_pos, DensePoly.leadingCoeff_eq_coeff_last b hb_pos]
  exact ZMod64.coeff_mul_at_top a b ha_pos hb_pos

/-- Right cancellation for multiplication by a nonzero `FpPoly p` polynomial. -/
theorem mul_right_cancel_of_ne_zero
    [ZMod64.PrimeModulus p] {a b c : FpPoly p}
    (hc : c ≠ 0) (h : a * c = b * c) :
    a = b := by
  apply Classical.byContradiction
  intro hab
  have hsub_ne : a - b ≠ 0 := by
    intro hsub
    apply hab
    apply DensePoly.ext_coeff
    intro n
    have hcoeff := congrArg (fun s : FpPoly p => s.coeff n) hsub
    change (a - b).coeff n = (0 : FpPoly p).coeff n at hcoeff
    rw [DensePoly.coeff_sub_ring, DensePoly.coeff_zero] at hcoeff
    grind
  have hmul_ne : (a - b) * c ≠ 0 := mul_ne_zero_of_ne_zero hsub_ne hc
  apply hmul_ne
  rw [sub_eq_add_neg, right_distrib]
  have hneg : (-(b : FpPoly p)) * c = -(b * c) := by
    show (0 - b) * c = 0 - b * c
    exact DensePoly.neg_mul_right_poly b c
  rw [hneg, h, add_right_neg]

/--
Over a prime modulus, divisibility implies a size bound: if `a ∣ b` and `b ≠ 0`, then
`a.size ≤ b.size`. The standard polynomial fact that a divisor has degree at most the
degree of the dividend, expressed at the level of `DensePoly.size`.
-/
theorem size_le_of_dvd_of_ne_zero
    [ZMod64.PrimeModulus p] {a b : FpPoly p}
    (hab : a ∣ b) (hb : b ≠ 0) :
    a.size ≤ b.size := by
  rcases hab with ⟨c, hc⟩
  have ha_ne : a ≠ 0 := by
    intro ha
    apply hb
    rw [hc, ha, zero_mul]
  have hc_ne : c ≠ 0 := by
    intro hc_zero
    apply hb
    rw [hc, hc_zero, mul_zero]
  have ha_size_pos : 0 < a.size := size_pos_of_ne_zero ha_ne
  have hc_size_pos : 0 < c.size := size_pos_of_ne_zero hc_ne
  have hsize := size_mul_eq_add_sub_one a c ha_ne hc_ne
  rw [hc, hsize]
  omega

/--
Over a prime modulus, when `d` divides a nonzero polynomial `c`, the executable sizes
satisfy `(c / d).size + d.size = c.size + 1`. This is degree-additivity for exact
division translated to the `size` indexing.
-/
theorem size_div_add_size_eq_size_add_one_of_dvd
    [ZMod64.PrimeModulus p] {c d : FpPoly p}
    (hdc : d ∣ c) (hc : c ≠ 0) :
    (c / d).size + d.size = c.size + 1 := by
  have hd_ne : d ≠ 0 := by
    intro hd
    rcases hdc with ⟨e, he⟩
    apply hc
    rw [he, hd, zero_mul]
  have hmod : c % d = 0 := DensePoly.mod_eq_zero_of_dvd c d hdc
  have hrec : (c / d) * d + (c % d) = c := DensePoly.div_mul_add_mod c d
  have hquot_mul : (c / d) * d = c := by
    rw [hmod] at hrec
    rwa [add_zero ((c / d) * d)] at hrec
  have hquot_ne : c / d ≠ 0 := by
    intro hquot
    apply hc
    rw [← hquot_mul, hquot, zero_mul]
  have hsize_mul := size_mul_eq_add_sub_one (c / d) d hquot_ne hd_ne
  have hd_size_pos : 0 < d.size := size_pos_of_ne_zero hd_ne
  have hquot_size_pos : 0 < (c / d).size := size_pos_of_ne_zero hquot_ne
  have hc_size : ((c / d) * d).size = c.size := by rw [hquot_mul]
  rw [hsize_mul] at hc_size
  omega

/--
Specialised quotient-size strict decrease: if `gcd c w` is nonconstant (size ≥ 2) and
`c ≠ 0`, then `c / gcd c w` has strictly smaller size than `c`. This is the size-strict
descent step that powers Yun-style square-free decomposition termination.
-/
theorem size_div_lt_of_size_gcd_pos
    [ZMod64.PrimeModulus p] (c w : FpPoly p)
    (hgcd_pos : 1 < (DensePoly.gcd c w).size)
    (hc : c.isZero = false) :
    (c / DensePoly.gcd c w).size < c.size := by
  have hc_ne : c ≠ 0 := by
    intro hzero
    rw [hzero] at hc
    exact (Bool.eq_not_self _).mp hc.symm
  have hgcd_dvd : DensePoly.gcd c w ∣ c := DensePoly.gcd_dvd_left c w
  have hsize := size_div_add_size_eq_size_add_one_of_dvd hgcd_dvd hc_ne
  omega

/-- A monic finite-field polynomial that divides the unit polynomial is the unit polynomial. -/
theorem eq_one_of_monic_dvd_one
    [ZMod64.PrimeModulus p] {g : FpPoly p}
    (hmonic : DensePoly.Monic g) (hdiv : g ∣ 1) :
    g = 1 := by
  rcases hdiv with ⟨u, hu⟩
  have hone_ne : (1 : FpPoly p) ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) h
    change (1 : FpPoly p).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
    rw [coeff_one, DensePoly.coeff_zero] at hcoeff
    exact zmod64_one_ne_zero hcoeff
  have hg_ne : g ≠ 0 := by
    intro hg
    apply hone_ne
    rw [hu, hg, zero_mul]
  have hu_ne : u ≠ 0 := by
    intro hu_zero
    apply hone_ne
    rw [hu, hu_zero, mul_zero]
  have hdeg_mul := degree?_mul_eq_add_degree? g u hg_ne hu_ne
  have hdeg_one : (1 : FpPoly p).degree?.getD 0 = 0 := by
    exact DensePoly.degree?_C_getD (1 : ZMod64 p)
  have hdeg_eq :
      (g * u).degree?.getD 0 = (1 : FpPoly p).degree?.getD 0 :=
    congrArg (fun f : FpPoly p => f.degree?.getD 0) hu.symm
  have hg_degree_zero : g.degree?.getD 0 = 0 := by
    rw [hdeg_mul, hdeg_one] at hdeg_eq
    omega
  have hg_size_pos : 0 < g.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply hg_ne
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le g (by omega)
  have hg_degree_size : g.degree?.getD 0 = g.size - 1 := by
    unfold DensePoly.degree?
    have hsize_ne : g.size ≠ 0 := Nat.pos_iff_ne_zero.mp hg_size_pos
    simp [hsize_ne]
  have hg_size_one : g.size = 1 := by
    omega
  have hg_coeff_zero : g.coeff 0 = 1 := by
    have hlead := leadingCoeff_eq_coeff_pred g hg_size_pos
    rw [hg_size_one] at hlead
    change DensePoly.leadingCoeff g = g.coeff 0 at hlead
    unfold DensePoly.Monic at hmonic
    rw [hlead] at hmonic
    exact hmonic
  apply DensePoly.ext_coeff
  intro n
  by_cases hn : n = 0
  · subst n
    rw [hg_coeff_zero, coeff_one]
    simp
  · have hsize_le : g.size ≤ n := by omega
    rw [DensePoly.coeff_eq_zero_of_size_le g hsize_le, coeff_one]
    simp [hn]
    rfl

/--
Turn the executable gcd into the equality `gcd a b = 1` once the gcd is known
monic and every common divisor of `a` and `b` divides `1`.
-/
theorem gcd_eq_one_of_monic_of_common_dvd_one
    [ZMod64.PrimeModulus p] (a b : FpPoly p)
    (hmonic : DensePoly.Monic (DensePoly.gcd a b))
    (hcommon :
      ∀ d : FpPoly p, d ∣ a → d ∣ b → d ∣ (1 : FpPoly p)) :
    DensePoly.gcd a b = 1 := by
  apply eq_one_of_monic_dvd_one hmonic
  exact hcommon (DensePoly.gcd a b)
    (DensePoly.gcd_dvd_left a b)
    (DensePoly.gcd_dvd_right a b)

/--
Bezout-style coprime cancellation for `FpPoly p`. If `g ∣ c * h` and every
common divisor of `c` and `g` divides the unit polynomial `1`, then `g ∣ h`.

The proof uses the extended Euclidean algorithm `DensePoly.xgcd`: from the
Bezout identity `r.left * c + r.right * g = DensePoly.gcd c g` and the fact
that `DensePoly.gcd c g ∣ 1` (via the coprime hypothesis), one concludes that
`g` divides `h`.
-/
theorem dvd_of_dvd_mul_of_common_dvd_one
    [ZMod64.PrimeModulus p]
    {g c h : FpPoly p}
    (hdvd : g ∣ c * h)
    (hcoprime : ∀ d : FpPoly p, d ∣ c → d ∣ g → d ∣ (1 : FpPoly p)) :
    g ∣ h := by
  -- The gcd of `(c, g)` divides `c`, `g`, hence `1` by hypothesis.
  have hDc : DensePoly.gcd c g ∣ c := DensePoly.gcd_dvd_left c g
  have hDg : DensePoly.gcd c g ∣ g := DensePoly.gcd_dvd_right c g
  have hD1 : DensePoly.gcd c g ∣ (1 : FpPoly p) :=
    hcoprime (DensePoly.gcd c g) hDc hDg
  rcases hD1 with ⟨e, he⟩
  -- Extract the Bezout coefficients as free variables (not let-bindings).
  obtain ⟨s, t, hbez⟩ :
      ∃ s t : FpPoly p, s * c + t * g = DensePoly.gcd c g :=
    ⟨(DensePoly.xgcd c g).left, (DensePoly.xgcd c g).right,
     DensePoly.xgcd_gcd_eq_gcd c g ▸ DensePoly.xgcd_bezout c g⟩
  -- `g` divides each summand of `(s * c + t * g) * h`.
  have hg_left : g ∣ s * c * h := by
    have h_assoc : s * c * h = s * (c * h) := DensePoly.mul_assoc_poly s c h
    exact h_assoc ▸ DensePoly.dvd_mul_left_poly s hdvd
  have hg_right : g ∣ t * g * h := by
    have h_rearrange : t * g * h = (t * h) * g := by
      calc t * g * h
          = t * (g * h) := DensePoly.mul_assoc_poly _ _ _
        _ = t * (h * g) := congrArg (fun x => t * x) (DensePoly.mul_comm_poly g h)
        _ = (t * h) * g := (DensePoly.mul_assoc_poly _ _ _).symm
    exact h_rearrange ▸ DensePoly.dvd_mul_left_poly (t * h) (DensePoly.dvd_refl_poly g)
  -- Combine to get `g ∣ DensePoly.gcd c g * h`.
  have hbez_h :
      s * c * h + t * g * h = DensePoly.gcd c g * h := by
    calc s * c * h + t * g * h
        = (s * c + t * g) * h :=
          (DensePoly.mul_add_left_poly (s * c) (t * g) h).symm
      _ = DensePoly.gcd c g * h := congrArg (fun x => x * h) hbez
  have hg_Dh : g ∣ DensePoly.gcd c g * h :=
    hbez_h ▸ DensePoly.dvd_add_poly hg_left hg_right
  -- Use `DensePoly.gcd c g ∣ 1` to conclude `g ∣ h`.
  have hh_eq : h = e * (DensePoly.gcd c g * h) := by
    calc h
        = h * 1 := (DensePoly.mul_one_right_poly h).symm
      _ = h * (DensePoly.gcd c g * e) :=
          congrArg (fun x => h * x) he
      _ = (h * DensePoly.gcd c g) * e :=
          (DensePoly.mul_assoc_poly h (DensePoly.gcd c g) e).symm
      _ = (DensePoly.gcd c g * h) * e :=
          congrArg (fun x => x * e) (DensePoly.mul_comm_poly h (DensePoly.gcd c g))
      _ = e * (DensePoly.gcd c g * h) :=
          DensePoly.mul_comm_poly (DensePoly.gcd c g * h) e
  exact hh_eq ▸ DensePoly.dvd_mul_left_poly e hg_Dh

/-! ### Monomial multiplication and geometric-series divisibility

These lemmas support the `xPowSubX` divisibility chain in
`HexBerlekamp/RabinSoundness.lean`. -/

private theorem mulCoeffTerm_monomial_eq_zero_of_ne
    (k : Nat) (c : ZMod64 p) (g : FpPoly p) (n i : Nat) (hi : i ≠ k) :
    mulCoeffTerm (DensePoly.monomial k c : FpPoly p) g n i = 0 := by
  unfold mulCoeffTerm
  by_cases hni : n < i
  · simp [hni]
  · have hcoeff : (DensePoly.monomial k c : FpPoly p).coeff i = 0 := by
      rw [DensePoly.coeff_monomial]
      simp [hi]
      rfl
    simp [hni, hcoeff]

private theorem mulCoeffTerm_monomial_self_le
    (k : Nat) (c : ZMod64 p) (g : FpPoly p) (n : Nat) (hk : ¬ n < k) :
    mulCoeffTerm (DensePoly.monomial k c : FpPoly p) g n k = c * g.coeff (n - k) := by
  unfold mulCoeffTerm
  rw [DensePoly.coeff_monomial]
  simp [hk]

private theorem mulCoeffTerm_monomial_self_lt
    (k : Nat) (c : ZMod64 p) (g : FpPoly p) (n : Nat) (hk : n < k) :
    mulCoeffTerm (DensePoly.monomial k c : FpPoly p) g n k = 0 := by
  unfold mulCoeffTerm
  simp [hk]

private theorem fold_mulCoeffTerm_monomial_eq
    (k : Nat) (c : ZMod64 p) (g : FpPoly p) (n : Nat) :
    ∀ (m : Nat) (acc : ZMod64 p),
      (List.range m).foldl
          (fun acc i =>
            acc + mulCoeffTerm (DensePoly.monomial k c : FpPoly p) g n i) acc =
        acc + (if k < m ∧ ¬ n < k then c * g.coeff (n - k) else 0) := by
  intro m
  induction m with
  | zero =>
      intro acc
      simp
  | succ m ih =>
      intro acc
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      by_cases hkm : k < m
      · -- k < m, so the new index m is not k.
        have hm_ne : m ≠ k := by omega
        rw [mulCoeffTerm_monomial_eq_zero_of_ne k c g n m hm_ne, zmod_add_zero]
        have hkm' : k < m + 1 := by omega
        by_cases hkn : ¬ n < k
        · simp [hkm, hkn, hkm']
        · simp [hkm, hkn, hkm']
      · -- ¬ k < m
        by_cases hkm_eq : k = m
        · subst hkm_eq
          -- index m = k in the new step
          by_cases hkn : ¬ n < k
          · rw [mulCoeffTerm_monomial_self_le k c g n hkn]
            simp [hkn]
          · rw [mulCoeffTerm_monomial_self_lt k c g n (by omega)]
            simp [hkn]
        · -- ¬ k < m and k ≠ m. So k > m, in particular k ≥ m + 1.
          have hkm' : ¬ k < m + 1 := by omega
          have hm_ne : m ≠ k := fun h => hkm_eq h.symm
          rw [mulCoeffTerm_monomial_eq_zero_of_ne k c g n m hm_ne, zmod_add_zero]
          simp [hkm, hkm']

/-- Coefficient of `monomial k c * g` at degree `n`: zero below `k`, `c · g[n-k]`
above. -/
theorem coeff_monomial_mul (k : Nat) (c : ZMod64 p) (g : FpPoly p) (n : Nat) :
    ((DensePoly.monomial k c : FpPoly p) * g).coeff n =
      if n < k then 0 else c * g.coeff (n - k) := by
  rw [coeff_mul, mulCoeffSum_eq_degree_bound, fold_mulCoeffTerm_monomial_eq k c g n (n + 1) 0,
    zmod_zero_add]
  by_cases hnk : n < k
  · simp [hnk]
  · have hkn : k < n + 1 := by omega
    simp [hnk, hkn]

/-- Synthetic-division quotient coefficients: for a coefficient list `cs`
(constant term first) and scalar `α`, entry `n` is the Horner value
`evalScalarCoeffList (cs.drop (n+1)) α`, so the list holds the coefficients of
the divided difference `(f - f(α)) / (X - α)`. -/
private def scalarDividedDifferenceCoeffs :
    List (ZMod64 p) → ZMod64 p → List (ZMod64 p)
  | [], _ => []
  | [_], _ => []
  | _ :: c :: cs, α =>
      evalScalarCoeffList (c :: cs) α :: scalarDividedDifferenceCoeffs (c :: cs) α

/-- Routine bridge: the `Zero.zero` literal coincides with `0` in `ZMod64 p`. -/
private theorem zmod_Zero_zero_eq_zero :
    (Zero.zero : ZMod64 p) = (0 : ZMod64 p) := by
  apply zmod_eq_of_toNat_eq
  change (Zero.zero : ZMod64 p).toNat = 0
  exact ZMod64.toNat_zero

/-- Entry `n` of the divided-difference quotient list (default `0`) is the
Horner value `evalScalarCoeffList (cs.drop (n+1)) α`; characterises
`scalarDividedDifferenceCoeffs` entrywise. -/
private theorem scalarDividedDifferenceCoeffs_getD
    (cs : List (ZMod64 p)) (α : ZMod64 p) (n : Nat) :
    (scalarDividedDifferenceCoeffs cs α).getD n (0 : ZMod64 p) =
      evalScalarCoeffList (cs.drop (n + 1)) α := by
  induction cs generalizing n with
  | nil =>
      simp [scalarDividedDifferenceCoeffs, evalScalarCoeffList]
  | cons c cs ih =>
      cases cs with
      | nil =>
          cases n <;> simp [scalarDividedDifferenceCoeffs, evalScalarCoeffList]
      | cons d ds =>
          cases n with
          | zero =>
              simp [scalarDividedDifferenceCoeffs]
          | succ n =>
              simpa [scalarDividedDifferenceCoeffs, Nat.succ_eq_add_one, Nat.add_assoc]
                using ih (n := n)

/-- One Horner step on a suffix: evaluating `cs.drop n` peels off the leading
coefficient `cs[n]` plus `α` times the evaluation of `cs.drop (n+1)`. -/
private theorem evalScalarCoeffList_drop_eq_getD_add
    (cs : List (ZMod64 p)) (α : ZMod64 p) (n : Nat) :
    evalScalarCoeffList (cs.drop n) α =
      cs.getD n (0 : ZMod64 p) +
        α * evalScalarCoeffList (cs.drop (n + 1)) α := by
  induction cs generalizing n with
  | nil =>
      simp [evalScalarCoeffList]
  | cons c cs ih =>
      cases n with
      | zero =>
          rfl
      | succ n =>
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using ih (n := n)

/-- Routine round-trip: rebuilding a polynomial from its own coefficient array
recovers it. -/
private theorem ofCoeffs_toArray_fp (f : FpPoly p) :
    (DensePoly.ofCoeffs f.toArray : FpPoly p) = f := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_ofCoeffs]
  rfl

/-- `getElem?`/`getD` restatement of `scalarDividedDifferenceCoeffs_getD`, the
form used when reading quotient coefficients out of `ofCoeffs` arrays. -/
private theorem scalarDividedDifferenceCoeffs_getElem?_getD
    (cs : List (ZMod64 p)) (α : ZMod64 p) (n : Nat) :
    (scalarDividedDifferenceCoeffs cs α)[n]?.getD (0 : ZMod64 p) =
      evalScalarCoeffList (cs.drop (n + 1)) α := by
  simpa [List.getD] using scalarDividedDifferenceCoeffs_getD cs α n

/-- Routine: the constant polynomial `C 0` is the zero polynomial in `FpPoly p`. -/
private theorem C_zero_fp :
    FpPoly.C (0 : ZMod64 p) = (0 : FpPoly p) := by
  apply DensePoly.ext_coeff
  intro n
  unfold FpPoly.C
  rw [DensePoly.coeff_C, DensePoly.coeff_zero]
  cases n <;> rfl

/-- Coefficient `n` of the linear factor times the quotient,
`((X - C α) · q).coeff n`, expanded via Horner suffixes: it equals
`(evalScalarCoeffList (cs.drop n) α for n ≠ 0, else 0) - α · evalScalarCoeffList (cs.drop (n+1)) α`.
The product-coefficient half of the factorization identity. -/
private theorem scalar_linear_factor_mul_dividedDifference_coeff
    (cs : List (ZMod64 p)) (α : ZMod64 p) (n : Nat) :
    let q : FpPoly p :=
      DensePoly.ofCoeffs (scalarDividedDifferenceCoeffs cs α).toArray
    ((FpPoly.X - FpPoly.C α) * q).coeff n =
      (if n = 0 then 0 else evalScalarCoeffList (cs.drop n) α) -
        α * evalScalarCoeffList (cs.drop (n + 1)) α := by
  intro q
  have hzero_mul : α * (0 : ZMod64 p) = 0 := by grind
  have hneg_mul : (-(FpPoly.C α) : FpPoly p) * q = -(FpPoly.C α * q) := by
    show (0 - FpPoly.C α) * q = 0 - FpPoly.C α * q
    exact DensePoly.neg_mul_right_poly (FpPoly.C α) q
  rw [sub_eq_add_neg, right_distrib, DensePoly.coeff_add_semiring, hneg_mul,
    DensePoly.coeff_neg_ring]
  have hCmul : FpPoly.C α * q = DensePoly.scale α q := C_mul_eq_scale α q
  rw [hCmul, DensePoly.coeff_scale _ _ _ hzero_mul,
    show FpPoly.X = (DensePoly.monomial 1 (1 : ZMod64 p) : FpPoly p) from rfl, coeff_monomial_mul,
    DensePoly.coeff_ofCoeffs_list, DensePoly.coeff_ofCoeffs_list, zmod_Zero_zero_eq_zero]
  cases n with
  | zero =>
      simp
      rw [scalarDividedDifferenceCoeffs_getElem?_getD cs α 0,
        show cs.drop 1 = cs.tail by cases cs <;> rfl]
      grind
  | succ n =>
      simp
      rw [scalarDividedDifferenceCoeffs_getElem?_getD cs α n,
        scalarDividedDifferenceCoeffs_getElem?_getD cs α (n + 1)]
      grind

/-- Capstone factorization (Ruffini / Horner remainder identity): the polynomial
built from coefficients `cs` splits as `C (eval cs α) + (X - C α) · q`, where `q`
is the divided-difference quotient `scalarDividedDifferenceCoeffs cs α`. Combines
the constant-term Horner unfolding with
`scalar_linear_factor_mul_dividedDifference_coeff` coefficientwise. -/
private theorem ofCoeffs_eq_C_eval_add_linear_mul_dividedDifference
    (cs : List (ZMod64 p)) (α : ZMod64 p) :
    (DensePoly.ofCoeffs cs.toArray : FpPoly p) =
      FpPoly.C (evalScalarCoeffList cs α) +
        (FpPoly.X - FpPoly.C α) *
          (DensePoly.ofCoeffs (scalarDividedDifferenceCoeffs cs α).toArray : FpPoly p) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_add_semiring, DensePoly.coeff_ofCoeffs_list, zmod_Zero_zero_eq_zero]
  rw [show (FpPoly.C (evalScalarCoeffList cs α)).coeff n =
      if n = 0 then evalScalarCoeffList cs α else (Zero.zero : ZMod64 p) by
    unfold FpPoly.C
    rw [DensePoly.coeff_C]]
  rw [zmod_Zero_zero_eq_zero, scalar_linear_factor_mul_dividedDifference_coeff cs α n]
  cases n with
  | zero =>
      have hdrop := evalScalarCoeffList_drop_eq_getD_add cs α 0
      simp at hdrop ⊢
      grind
  | succ n =>
      have hdrop := evalScalarCoeffList_drop_eq_getD_add cs α (n + 1)
      simp at hdrop ⊢
      grind

/-- If `c` is a scalar root of `f`, then the linear factor `X - C c` divides `f`. -/
theorem X_sub_C_dvd_of_eval_eq_zero
    (f : FpPoly p) (c : ZMod64 p)
    (hroot : DensePoly.eval f c = 0) :
    (FpPoly.X - FpPoly.C c) ∣ f := by
  let q : FpPoly p :=
    DensePoly.ofCoeffs (scalarDividedDifferenceCoeffs f.toArray.toList c).toArray
  refine ⟨q, ?_⟩
  have hcoeffs :=
    ofCoeffs_eq_C_eval_add_linear_mul_dividedDifference
      (p := p) f.toArray.toList c
  rw [eval_eq_coeff_power_sum] at hroot
  have hroot_scalar : evalScalarCoeffList f.toArray.toList c = 0 := by
    rw [evalScalarCoeffList_eq_powerSumFrom_zero, hroot]
  rw [← ofCoeffs_toArray_fp f, hcoeffs, hroot_scalar, C_zero_fp]
  change (0 : FpPoly p) +
      (FpPoly.X - FpPoly.C c) * q = (FpPoly.X - FpPoly.C c) * q
  exact zero_add ((FpPoly.X - FpPoly.C c) * q)

/-- Multiplying two monic monomials adds their exponents. -/
theorem monomial_mul_monomial (m n : Nat) :
    (DensePoly.monomial m (1 : ZMod64 p)) *
        (DensePoly.monomial n (1 : ZMod64 p)) =
      DensePoly.monomial (m + n) (1 : ZMod64 p) := by
  apply DensePoly.ext_coeff
  intro i
  rw [coeff_monomial_mul, DensePoly.coeff_monomial, DensePoly.coeff_monomial]
  by_cases him : i < m
  · simp [him]
    have hne : i ≠ m + n := by omega
    simp [hne]
    rfl
  · simp [him]
    by_cases hi : i = m + n
    · have hi' : i - m = n := by omega
      simp [hi]
    · simp [hi]
      have hi' : i - m ≠ n := by omega
      simp [hi']

/-- The constant `1` polynomial agrees with the zero-degree monic monomial. -/
theorem monomial_zero_one_eq_one :
    (DensePoly.monomial 0 (1 : ZMod64 p) : FpPoly p) = 1 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_monomial, coeff_one]
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi]
    rfl

/-- Linear polynomial exponentiation by repeated right-multiplication.
This is the building block for the geometric-series identity used by
the `xPowSubX` divisibility chain. -/
@[expose]
def linearPow (f : FpPoly p) : Nat → FpPoly p
  | 0 => 1
  | n + 1 => linearPow f n * f

/-- The zeroth power is the multiplicative identity `1`. Base case pairing
with `linearPow_succ`. -/
@[simp, grind =] theorem linearPow_zero (f : FpPoly p) : linearPow f 0 = 1 := rfl

/-- Successor exponents append one right multiplication by the base. -/
@[simp, grind =] theorem linearPow_succ (f : FpPoly p) (n : Nat) :
    linearPow f (n + 1) = linearPow f n * f := rfl

/-- Successor exponents may also be read as one left multiplication by the base. -/
theorem linearPow_succ_left (f : FpPoly p) (n : Nat) :
    linearPow f (n + 1) = f * linearPow f n := by
  induction n with
  | zero =>
      change (1 : FpPoly p) * f = f * 1
      rw [one_mul, mul_one]
  | succ n ih =>
      calc linearPow f ((n + 1) + 1)
          = linearPow f (n + 1) * f := rfl
        _ = (f * linearPow f n) * f := by rw [ih]
        _ = f * (linearPow f n * f) := mul_assoc f (linearPow f n) f
        _ = f * linearPow f (n + 1) := rfl

/-- The first `linearPow` of a polynomial is the polynomial itself. -/
@[grind =] theorem linearPow_one (f : FpPoly p) :
    linearPow f 1 = f := by
  grind

/-- `linearPow` turns exponent addition into polynomial multiplication. -/
theorem linearPow_add (f : FpPoly p) (m n : Nat) :
    linearPow f (m + n) = linearPow f m * linearPow f n := by
  induction n with
  | zero =>
      change linearPow f m = linearPow f m * 1
      rw [mul_one]
  | succ n ih =>
      calc linearPow f (m + (n + 1))
          = linearPow f ((m + n) + 1) := by rw [Nat.add_succ]
        _ = linearPow f (m + n) * f := rfl
        _ = (linearPow f m * linearPow f n) * f := by rw [ih]
        _ = linearPow f m * (linearPow f n * f) := mul_assoc _ _ _
        _ = linearPow f m * linearPow f (n + 1) := rfl

/-- Iterated `linearPow` multiplies exponents. -/
theorem linearPow_iterate_mul (f : FpPoly p) (m : Nat) :
    ∀ n, linearPow (linearPow f m) n = linearPow f (m * n)
  | 0 => by
      simp [Nat.mul_zero]
  | n + 1 => by
      rw [linearPow_succ, linearPow_iterate_mul f m n, Nat.mul_succ,
        linearPow_add]

/-- Scalar evaluation distributes over `linearPow`: `eval (f^n) x = (eval f x)^n`. -/
theorem eval_linearPow (f : FpPoly p) (n : Nat) (x : ZMod64 p) :
    DensePoly.eval (linearPow f n) x = (DensePoly.eval f x) ^ n := by
  induction n with
  | zero =>
      rw [linearPow_zero, Lean.Grind.Semiring.pow_zero]
      exact eval_one x
  | succ n ih =>
      rw [linearPow_succ, eval_mul, ih, Lean.Grind.Semiring.pow_succ]

/-- `linearPow (monomial k 1) n = monomial (k * n) 1`. -/
theorem linearPow_monomial (k n : Nat) :
    linearPow (DensePoly.monomial k (1 : ZMod64 p)) n =
      DensePoly.monomial (k * n) (1 : ZMod64 p) := by
  induction n with
  | zero =>
      show (1 : FpPoly p) = DensePoly.monomial (k * 0) 1
      rw [Nat.mul_zero]
      exact monomial_zero_one_eq_one.symm
  | succ n ih =>
      rw [linearPow_succ, ih]
      have h := monomial_mul_monomial (p := p) (k * n) k
      have heq : k * n + k = k * (n + 1) := (Nat.mul_succ k n).symm
      rw [heq] at h
      exact h

/-- `linearPow (monomial 1 1) n = monomial n 1`. -/
theorem linearPow_monomial_one (n : Nat) :
    linearPow (DensePoly.monomial 1 (1 : ZMod64 p)) n =
      DensePoly.monomial n (1 : ZMod64 p) := by
  have h := linearPow_monomial (p := p) 1 n
  rw [Nat.one_mul] at h
  exact h

/-- `linearPow X n` is the degree-`n` monomial. -/
theorem linearPow_X (n : Nat) :
    linearPow (FpPoly.X : FpPoly p) n =
      DensePoly.monomial n (1 : ZMod64 p) := by
  exact linearPow_monomial_one (p := p) n

private theorem C_mul_C (a b : ZMod64 p) :
    FpPoly.C a * FpPoly.C b = FpPoly.C (a * b) := by
  unfold FpPoly.C
  rw [C_mul_eq_scale]
  apply DensePoly.ext_coeff
  intro n
  have hzero : a * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero, DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => rfl
  | succ n => rfl

/-- `linearPow` of a constant polynomial stays constant. -/
theorem linearPow_C (c : ZMod64 p) (n : Nat) :
    linearPow (FpPoly.C c) n = FpPoly.C (c ^ n) := by
  induction n with
  | zero =>
      rw [linearPow_zero, Lean.Grind.Semiring.pow_zero]
      rfl
  | succ n ih =>
      rw [linearPow_succ, ih, Lean.Grind.Semiring.pow_succ, C_mul_C]

/-- The polynomial-level subtraction-multiplication identity: `(P - 1) * Y = P * Y - Y`. -/
private theorem sub_one_mul_eq (P Y : FpPoly p) :
    (P - 1) * Y = P * Y - Y := by
  rw [sub_eq_add_neg, right_distrib]
  have hneg : (-(1 : FpPoly p)) * Y = -Y := by
    show (0 - (1 : FpPoly p)) * Y = 0 - Y
    have h := DensePoly.neg_mul_right_poly (1 : FpPoly p) Y
    have h1 : (1 : FpPoly p) * Y = Y := one_mul Y
    calc (0 - (1 : FpPoly p)) * Y = 0 - 1 * Y := h
      _ = 0 - Y := by rw [h1]
  rw [hneg, ← sub_eq_add_neg]

/-- Geometric-series divisibility: `Y - 1 ∣ Y^j - 1`. -/
theorem sub_one_dvd_linearPow_sub_one (Y : FpPoly p) (j : Nat) :
    (Y - 1) ∣ (linearPow Y j - 1) := by
  induction j with
  | zero =>
      change (Y - 1) ∣ (1 - 1 : FpPoly p)
      exact ⟨0, by rw [sub_self, mul_zero]⟩
  | succ j ih =>
      obtain ⟨q, hq⟩ := ih
      refine ⟨q * Y + 1, ?_⟩
      -- Need: linearPow Y (j + 1) - 1 = (Y - 1) * (q * Y + 1)
      rw [linearPow_succ, left_distrib, mul_one,
        show (Y - 1) * (q * Y) = ((Y - 1) * q) * Y from (mul_assoc _ _ _).symm, ← hq,
        sub_one_mul_eq]
      -- goal: linearPow Y j * Y - 1 = linearPow Y j * Y - Y + (Y - 1)
      -- A - 1 = A - Y + Y - 1, regroup at coefficient level.
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_sub_ring, DensePoly.coeff_add_semiring, DensePoly.coeff_sub_ring,
        DensePoly.coeff_sub_ring]
      grind

/-- Geometric-series divisibility for monomials: when `k ∣ l`,
`(monomial k 1 - 1) ∣ (monomial l 1 - 1)`. -/
theorem monomial_sub_one_dvd_of_dvd
    {k l : Nat} (hdvd : k ∣ l) :
    ((DensePoly.monomial k (1 : ZMod64 p) - 1) : FpPoly p) ∣
      (DensePoly.monomial l (1 : ZMod64 p) - 1 : FpPoly p) := by
  obtain ⟨j, rfl⟩ := hdvd
  rw [show (DensePoly.monomial (k * j) (1 : ZMod64 p) : FpPoly p) =
        linearPow (DensePoly.monomial k (1 : ZMod64 p)) j from
        (linearPow_monomial k j).symm]
  exact sub_one_dvd_linearPow_sub_one _ j


end FpPoly
end Hex
