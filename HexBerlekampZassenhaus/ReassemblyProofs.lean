/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexArith.Nat.Prime
public meta import HexBerlekamp.Factor
public meta import HexBerlekamp.Irreducibility
public meta import HexHensel.Basic
public meta import HexHensel.Multifactor
public meta import HexHensel.QuadraticMultifactor
public meta import HexMatrix.Basic
public meta import HexPolyZ.Mignotte
public meta import HexLLL.Basic
public import HexArith.Nat.Prime
public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexHensel.Multifactor
public import HexHensel.QuadraticMultifactor
public import HexLLL.Basic
-- Needed so `decide`/`rfl` over `DensePoly`/`Array` equality reduces in the
-- kernel: the core `Array.instDecidableEq` delegates its nonempty case to the
-- non-`@[expose]` `Array.instDecidableEqImpl`, which is otherwise opaque under
-- the module system. Drop once that impl is exposed upstream (lean4).
import all Init.Data.Array.DecidableEq

public import HexBerlekampZassenhaus.ChoosePrimeData
public meta import HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData

public section
set_option backward.proofsInPublic true

/-!
This module collects the BHKS bounds and reassembly-correctness theorems.
-/
namespace Hex

namespace ZPoly

/--
`PrimeChoiceData`-shaped wrapper around
`Hex.ZPoly.quadraticMultifactorLiftInvariant_of_factorsModP`.

Given monic `core`, an admissible `1 ≤ B`, and the minimal modular boundary
facts about `primeData.factorsModP` -- per-factor monicness, product
congruence modulo `primeData.p`, sequential split coprimality, and a
nonempty witness -- this produces the recursive quadratic multifactor lift
invariant on the lifted modular factors that `henselLiftData` consumes.

The Mathlib-free downstream theorem
`HexBerlekampZassenhausMathlib.henselLiftData_liftedFactor_monic` already
feeds this invariant into `Hex.ZPoly.multifactorLiftQuadratic_each_monic`.
-/
theorem QuadraticMultifactorLiftInvariant_of_choosePrimeData
    (core : ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hp_prime : Nat.Prime primeData.p)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B)
    (hcore_monic : DensePoly.Monic core)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map FpPoly.liftToZ))
        core primeData.p)
    (hcoprime :
      letI := primeData.bounds
      QuadraticMultifactorCoprimeSplits primeData.p
        primeData.factorsModP.toList)
    (hnonempty : primeData.factorsModP.toList ≠ []) :
    letI := primeData.bounds
    QuadraticMultifactorLiftInvariant primeData.p B core
      (primeData.factorsModP.map FpPoly.liftToZ).toList := by
  letI := primeData.bounds
  haveI : ZMod64.PrimeModulus primeData.p :=
    ZMod64.primeModulusOfPrime hp_prime
  have hfactors_monic_list :
      ∀ g ∈ primeData.factorsModP.toList, DensePoly.Monic g := by
    intro g hg
    exact hfactors_monic g (by simpa using hg)
  have hproduct_mod_p_list :
      ZPoly.congr
        (Array.polyProduct
          ((primeData.factorsModP.toList.map FpPoly.liftToZ).toArray))
        core primeData.p := by
    have hmap_eq :
        (primeData.factorsModP.toList.map FpPoly.liftToZ).toArray
          = primeData.factorsModP.map FpPoly.liftToZ := by
      rw [← Array.toList_map]
    rw [hmap_eq]; exact hproduct_mod_p
  have hkey :=
    Hex.ZPoly.quadraticMultifactorLiftInvariant_of_factorsModP
      primeData.p B core primeData.factorsModP.toList
      hp hB hcore_monic hfactors_monic_list hproduct_mod_p_list
      hcoprime hnonempty
  have hmap_list :
      (primeData.factorsModP.map FpPoly.liftToZ).toList
        = primeData.factorsModP.toList.map FpPoly.liftToZ := by simp
  rw [hmap_list]
  exact hkey

end ZPoly

/--
Integer upper bound for the BHKS fast-recombination precision schedule.

This is the conservative all-integer cap from the `hex-berlekamp-zassenhaus`
SPEC: `1 + n * 4^(n^2) * (sumSquared + 1)^n * log2(sumSquared + 1)^n`, where
`n` is the executable degree bound and `sumSquared` is the squared coefficient
norm.
-/
def bhksBound (f : ZPoly) : Nat :=
  let n := f.degree?.getD 0
  let sumSquared := ZPoly.coeffNormSq f
  1 + n * 4 ^ (n * n) * (sumSquared + 1) ^ n * (Nat.log2 (sumSquared + 1)) ^ n

/-- Integer coefficient bound `B_j` used by the BHKS all-coefficients CLD lattice. -/
@[expose]
def bhksCoeffBound (f : ZPoly) (j : Nat) : Nat :=
  let n := f.degree?.getD 0
  Nat.choose (n - 1) j * n * ZPoly.coeffL2NormBound f

def ceilLogPAux (p target : Nat) : Nat → Nat → Nat → Nat
  | 0, ell, _ => ell
  | fuel + 1, ell, power =>
      if target ≤ power then
        ell
      else
        ceilLogPAux p target fuel (ell + 1) (power * p)

/--
Small executable `ceil_log_p` helper.

For `1 < p`, `ceilLogP p target` searches for the least visible exponent
whose `p`-power is at least `target`. The degenerate `p ≤ 1` case returns
zero because the BHKS fast path is only used with admissible primes.
-/
@[expose]
def ceilLogP (p target : Nat) : Nat :=
  if p ≤ 1 then
    0
  else
    ceilLogPAux p target (target + 1) 0 1

/-- Per-coordinate BHKS precision threshold `ell_j := ceil_log_p (2 * B_j + 1)`. -/
@[expose]
def bhksCoeffCutThreshold (p : Nat) (f : ZPoly) (j : Nat) : Nat :=
  ceilLogP p (2 * bhksCoeffBound f j + 1)

/--
Hensel precision exponent for a Mignotte coefficient bound.

For the Mignotte criterion `p^a > 2·B`, returns the smallest exponent
`a` with `p^a ≥ 2·B + 1` (equivalently `p^a > 2·B`). The two quantities
are different — `B` is a magnitude on integer coefficients, `a` is the
small exponent on the Hensel modulus `p^a` — and must not be conflated.
See SPEC/Libraries/hex-berlekamp-zassenhaus.md §"Slow path".
-/
@[expose]
def precisionForCoeffBound (B p : Nat) : Nat :=
  ceilLogP p (2 * B + 1)

private theorem ceilLogPAux_ge_ell (p target : Nat) :
    ∀ (fuel ell power : Nat),
      ell ≤ ceilLogPAux p target fuel ell power := by
  intro fuel
  induction fuel with
  | zero =>
    intro ell power
    simp [ceilLogPAux]
  | succ fuel ih =>
    intro ell power
    unfold ceilLogPAux
    split
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ ell) (ih (ell + 1) (power * p))

private theorem ceilLogPAux_pow_bound (p : Nat) :
    ∀ (fuel target ell power : Nat),
      target ≤ power * p ^ fuel →
      target ≤ power * p ^ (ceilLogPAux p target fuel ell power - ell) := by
  intro fuel
  induction fuel with
  | zero =>
    intro target ell power h
    simp only [ceilLogPAux, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    simpa [Nat.pow_zero, Nat.mul_one] using h
  | succ fuel ih =>
    intro target ell power h
    unfold ceilLogPAux
    split
    · rename_i h_le
      simpa [Nat.sub_self, Nat.pow_zero, Nat.mul_one] using h_le
    · have h_step : target ≤ (power * p) * p ^ fuel := by
        have hrw : power * p ^ (fuel + 1) = (power * p) * p ^ fuel := by
          rw [Nat.pow_succ, Nat.mul_comm (p ^ fuel) p, ← Nat.mul_assoc]
        rw [hrw] at h
        exact h
      have ih_app := ih target (ell + 1) (power * p) h_step
      have hge : ell + 1 ≤ ceilLogPAux p target fuel (ell + 1) (power * p) :=
        ceilLogPAux_ge_ell p target fuel (ell + 1) (power * p)
      have hk :
          ceilLogPAux p target fuel (ell + 1) (power * p) - ell =
            (ceilLogPAux p target fuel (ell + 1) (power * p) - (ell + 1)) + 1 := by
        omega
      rw [hk, Nat.pow_succ]
      have hrw2 :
          power *
              (p ^ (ceilLogPAux p target fuel (ell + 1) (power * p) - (ell + 1)) *
                p) =
            (power * p) *
              p ^ (ceilLogPAux p target fuel (ell + 1) (power * p) - (ell + 1)) := by
        rw [Nat.mul_comm (p ^ _) p, ← Nat.mul_assoc]
      rw [hrw2]
      exact ih_app

/--
Correctness of `ceilLogP`: when `2 ≤ p`, the returned exponent satisfies
`target ≤ p ^ ceilLogP p target`.

This is the small spec consumed by `precisionForCoeffBound_spec` below; the
strict-inequality Mignotte side condition `2 * B < p ^ precisionForCoeffBound B p`
follows by chaining this with the target `target = 2 * B + 1`.
-/
theorem le_pow_ceilLogP {p : Nat} (hp : 2 ≤ p) (target : Nat) :
    target ≤ p ^ ceilLogP p target := by
  unfold ceilLogP
  rw [if_neg (by omega : ¬ p ≤ 1)]
  have hlt2 : target < 2 ^ target := Nat.lt_two_pow_self
  have hle2 : (2 : Nat) ^ target ≤ 2 ^ (target + 1) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
  have hpow_p : (2 : Nat) ^ (target + 1) ≤ p ^ (target + 1) :=
    Nat.pow_le_pow_left hp (target + 1)
  have h_init : target ≤ 1 * p ^ (target + 1) := by
    rw [Nat.one_mul]; omega
  have h_spec := ceilLogPAux_pow_bound p (target + 1) target 0 1 h_init
  simpa [Nat.sub_zero, Nat.one_mul] using h_spec

private theorem ceilLogPAux_le (p : Nat) (hp : 2 ≤ p) (target a : Nat)
    (hta : target ≤ p ^ a) :
    ∀ (fuel ell : Nat), ell ≤ a →
      ceilLogPAux p target fuel ell (p ^ ell) ≤ a := by
  intro fuel
  induction fuel with
  | zero =>
    intro ell hell
    simpa [ceilLogPAux] using hell
  | succ fuel ih =>
    intro ell hell
    unfold ceilLogPAux
    split
    · exact hell
    · rename_i hgt
      have hella : ell < a := by
        rcases Nat.lt_or_ge ell a with h | h
        · exact h
        · have hpow_le : p ^ a ≤ p ^ ell := Nat.pow_le_pow_right (by omega) h
          omega
      have hpow : p ^ ell * p = p ^ (ell + 1) := by rw [Nat.pow_succ]
      rw [hpow]
      exact ih (ell + 1) (by omega)

/--
Minimality of `ceilLogP`: when `2 ≤ p` and `target ≤ p ^ a`, the least exponent
returned by `ceilLogP` is at most `a`.

This is the upper-bound companion to `le_pow_ceilLogP`.  Together they pin
`ceilLogP p target` between the least admissible exponent and any witness `a`,
which the BHKS period rows need to know the cut threshold `ℓ_j` does not exceed
the ambient Hensel precision `a` (`ℓ_j ≤ a`, so the diagonal exponent `a − ℓ_j`
is a genuine subtraction).
-/
theorem ceilLogP_le_of_le_pow {p : Nat} (hp : 2 ≤ p) (target a : Nat)
    (h : target ≤ p ^ a) :
    ceilLogP p target ≤ a := by
  unfold ceilLogP
  rw [if_neg (by omega : ¬ p ≤ 1)]
  have := ceilLogPAux_le p hp target a h (target + 1) 0 (Nat.zero_le a)
  simpa using this

/--
The executable Mignotte precision exponent satisfies the Mignotte side
condition `2 * B < p ^ precisionForCoeffBound B p` whenever the modulus is at
least `2`.

This is the reusable spec consumed by `ForwardRecoveryInputs` constructors that
need to discharge the `mignotte_precision` field at the actual executable
precision returned by `henselLiftData f (precisionForCoeffBound B p)`.
-/
theorem precisionForCoeffBound_spec {p : Nat} (hp : 2 ≤ p) (B : Nat) :
    2 * B < p ^ precisionForCoeffBound B p := by
  unfold precisionForCoeffBound
  have h := le_pow_ceilLogP hp (2 * B + 1)
  omega

/-- Enumerate every way to partition a list of polynomials into a `(selected,
unselected)` pair while preserving the original order in each component.  Used
by the exhaustive recombination search to drive the slow path. -/
@[expose]
def subsetSplits : List ZPoly → List (List ZPoly × List ZPoly)
  | [] => [([], [])]
  | factor :: factors =>
      let rest := subsetSplits factors
      rest.map (fun split => (split.1, factor :: split.2)) ++
        rest.map (fun split => (factor :: split.1, split.2))

/-- Variant of `subsetSplits` that forces the first element of the input list
into the `selected` component.  This is what the recombination search actually
iterates over, since the head of the remaining local factors must end up in
some recovered factor and tracking that explicitly avoids enumerating the same
subset twice through different traversal orders. -/
@[expose]
def subsetSplitsWithFirst : List ZPoly → List (List ZPoly × List ZPoly)
  | [] => []
  | factor :: factors =>
      (subsetSplits factors).map fun split => (factor :: split.1, split.2)

/-- Return the first `some` produced by applying `f` to elements of `xs` in
order, or `none` if every application is `none`. -/
def firstSome {α β : Type} : List α → (α → Option β) → Option β
  | [], _ => none
  | x :: xs, f =>
      match f x with
      | some y => some y
      | none => firstSome xs f

private theorem polyProduct_contentFactorArray (content : Int) :
    Array.polyProduct (contentFactorArray content) =
      if content = 1 then 1 else DensePoly.C content := by
  unfold contentFactorArray
  by_cases hcontent : content = 1
  · simp [hcontent, ZPoly.polyProduct_empty]
  · simp [hcontent, Array.polyProduct]

private theorem polyProduct_repeatedPartFactorArray (repeatedPart : ZPoly) :
    Array.polyProduct (repeatedPartFactorArray repeatedPart) =
      if repeatedPart = 1 then 1 else repeatedPart := by
  unfold repeatedPartFactorArray
  by_cases hrepeated : repeatedPart = 1
  · simp [hrepeated, ZPoly.polyProduct_empty]
  · simp [hrepeated, Array.polyProduct]

private theorem polyProduct_replicate_X_zero :
    Array.polyProduct ((List.replicate 0 ZPoly.X).toArray) = 1 := by
  rfl

private theorem polyProduct_replicate_X_succ (power : Nat) :
    Array.polyProduct ((List.replicate (power + 1) ZPoly.X).toArray) =
      ZPoly.X * Array.polyProduct ((List.replicate power ZPoly.X).toArray) := by
  simpa [List.replicate] using ZPoly.polyProduct_cons_toArray ZPoly.X (List.replicate power ZPoly.X)

private theorem polyProduct_xPowerFactorArray_zero :
    Array.polyProduct (xPowerFactorArray 0) = 1 := by
  simp [xPowerFactorArray]

private theorem polyProduct_xPowerFactorArray_succ (power : Nat) :
    Array.polyProduct (xPowerFactorArray (power + 1)) =
      ZPoly.X * Array.polyProduct (xPowerFactorArray power) := by
  simpa [xPowerFactorArray] using polyProduct_replicate_X_succ power

private theorem shift_zero (f : ZPoly) :
    DensePoly.shift 0 f = f := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_shift]
  simp

private theorem ofCoeffs_toArray (f : ZPoly) :
    DensePoly.ofCoeffs f.toArray = f := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_ofCoeffs]
  rfl

private theorem shift_shift_one (power : Nat) (f : ZPoly) :
    DensePoly.shift 1 (DensePoly.shift power f) = DensePoly.shift (power + 1) f := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_shift (power + 1) f n, DensePoly.coeff_shift 1 (DensePoly.shift power f) n]
  cases n with
  | zero =>
      simp
  | succ n =>
      have hsub_one : n + 1 - 1 = n := by omega
      rw [hsub_one, DensePoly.coeff_shift power f n]
      by_cases hn : n < power
      · have hsucc : n + 1 < power + 1 := by omega
        simp [hn, hsucc]
      · have hsucc : ¬ n + 1 < power + 1 := by omega
        simp [hn, hsucc, Nat.succ_sub_succ_eq_sub]

private theorem X_mul_shift (power : Nat) (f : ZPoly) :
    ZPoly.X * DensePoly.shift power f = DensePoly.shift (power + 1) f := by
  unfold ZPoly.X
  rw [DensePoly.monomial_one_mul_poly_eq_shift]
  exact shift_shift_one power f

private theorem polyProduct_xPowerFactorArray_mul (power : Nat) (f : ZPoly) :
    Array.polyProduct (xPowerFactorArray power) * f = DensePoly.shift power f := by
  induction power with
  | zero =>
      rw [polyProduct_xPowerFactorArray_zero, ZPoly.one_mul_zpoly, shift_zero]
  | succ power ih =>
      rw [polyProduct_xPowerFactorArray_succ, DensePoly.mul_assoc_poly (S := Int), ih]
      exact X_mul_shift power f

private theorem splitInitialZeros_reassembles (coeffs : List Int) :
    let split := ZPoly.splitInitialZeros coeffs
    DensePoly.shift split.1 (DensePoly.ofCoeffs split.2.toArray) =
      DensePoly.ofCoeffs coeffs.toArray := by
  induction coeffs with
  | nil =>
      rfl
  | cons coeff coeffs ih =>
      unfold ZPoly.splitInitialZeros
      by_cases hcoeff : coeff = 0
      · simp [hcoeff]
        cases split : ZPoly.splitInitialZeros coeffs with
        | mk power core =>
            have hcore :
                DensePoly.shift power (DensePoly.ofCoeffs core.toArray) =
                  DensePoly.ofCoeffs coeffs.toArray := by
              simpa [split] using ih
            simp
            apply DensePoly.ext_coeff
            intro n
            cases n with
            | zero =>
                rw [DensePoly.coeff_shift (power + 1) (DensePoly.ofCoeffs core.toArray) 0,
                  DensePoly.coeff_ofCoeffs_list (0 :: coeffs) 0]
                simp
                rfl
            | succ n =>
                have hcoeff_n := congrArg (fun p : ZPoly => p.coeff n) hcore
                change (DensePoly.shift power (DensePoly.ofCoeffs core.toArray)).coeff n =
                  (DensePoly.ofCoeffs coeffs.toArray).coeff n at hcoeff_n
                rw [DensePoly.coeff_shift power (DensePoly.ofCoeffs core.toArray) n] at hcoeff_n
                rw [DensePoly.coeff_ofCoeffs_list coeffs n] at hcoeff_n
                rw [DensePoly.coeff_shift (power + 1) (DensePoly.ofCoeffs core.toArray) (n + 1),
                  DensePoly.coeff_ofCoeffs_list (0 :: coeffs) (n + 1)]
                by_cases hn : n < power
                · have hsucc : n + 1 < power + 1 := by omega
                  simpa [hsucc, hn] using hcoeff_n
                · have hsucc : ¬ n + 1 < power + 1 := by omega
                  have hvalue :
                      (DensePoly.ofCoeffs core.toArray).coeff (n - power) =
                        coeffs.getD n 0 := by
                    have key := hcoeff_n; rw [if_neg hn] at key; exact key
                  simp only [hsucc, Nat.succ_sub_succ_eq_sub, if_false, List.getD_cons_succ]
                  exact hvalue
      · simp [hcoeff]

private theorem extractXPower_product (f : ZPoly) :
    let xData := ZPoly.extractXPower f
    Array.polyProduct (xPowerFactorArray xData.power ++ #[xData.core]) = f := by
  unfold ZPoly.extractXPower
  generalize hsplit : ZPoly.splitInitialZeros f.toArray.toList = split
  cases split with
  | mk power core =>
      simp only
      rw [ZPoly.polyProduct_append, ZPoly.polyProduct_singleton, polyProduct_xPowerFactorArray_mul]
      have hreassemble := splitInitialZeros_reassembles f.toArray.toList
      rw [hsplit] at hreassemble
      rw [← ofCoeffs_toArray f]
      simpa [DensePoly.toArray] using hreassemble

private theorem polyProduct_polynomialNormalizationPrefixFactors
    (d : FactorNormalizationData) :
    Array.polyProduct (polynomialNormalizationPrefixFactors d) =
      Array.polyProduct (xPowerFactorArray d.xPower) *
        Array.polyProduct (repeatedPartFactorArray d.repeatedPart) := by
  unfold polynomialNormalizationPrefixFactors
  rw [ZPoly.polyProduct_append]

private theorem polyPow_zero_lemma (g : ZPoly) :
    Factorization.polyPow g 0 = (1 : ZPoly) := rfl

private theorem polyPow_succ_lemma (g : ZPoly) (n : Nat) :
    Factorization.polyPow g (n + 1) = Factorization.polyPow g n * g := rfl

private theorem polyProduct_replicate_toArray (q : ZPoly) (m : Nat) :
    Array.polyProduct (List.replicate m q).toArray = Factorization.polyPow q m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [List.replicate_succ, ZPoly.polyProduct_cons_toArray, ih, polyPow_succ_lemma,
        DensePoly.mul_comm_poly (S := Int)]

private theorem consumeExactPower_invariant
    (target candidate : ZPoly) (fuel : Nat) :
    Factorization.polyPow candidate (consumeExactPower target candidate fuel).2 *
        (consumeExactPower target candidate fuel).1 = target := by
  induction fuel generalizing target with
  | zero =>
      show Factorization.polyPow candidate 0 * target = target
      rw [polyPow_zero_lemma, ZPoly.one_mul_zpoly]
  | succ fuel ih =>
      unfold consumeExactPower
      cases hex : exactQuotient? target candidate with
      | none =>
          simp only
          rw [polyPow_zero_lemma, ZPoly.one_mul_zpoly]
      | some quot =>
          have hquot : quot * candidate = target := exactQuotient?_product hex
          have hih := ih quot
          simp only
          rw [polyPow_succ_lemma, DensePoly.mul_assoc_poly (S := Int)]
          rw [DensePoly.mul_comm_poly (S := Int) candidate
            (consumeExactPower quot candidate fuel).1]
          rw [← DensePoly.mul_assoc_poly (S := Int), hih]
          exact hquot

private theorem expandRepeatedPartFactorsAux_invariant
    (coreFactors : List ZPoly) (rp : ZPoly) (fuel : Nat) :
    Array.polyProduct (expandRepeatedPartFactorsAux coreFactors rp fuel).1 *
        (expandRepeatedPartFactorsAux coreFactors rp fuel).2 = rp := by
  induction coreFactors generalizing rp with
  | nil =>
      show Array.polyProduct #[] * rp = rp
      rw [ZPoly.polyProduct_empty, ZPoly.one_mul_zpoly]
  | cons q qs ih =>
      unfold expandRepeatedPartFactorsAux
      have hcep := consumeExactPower_invariant rp q fuel
      have hih := ih (consumeExactPower rp q fuel).1
      simp only
      rw [ZPoly.polyProduct_append, polyProduct_replicate_toArray,
        DensePoly.mul_assoc_poly (S := Int), hih]
      exact hcep

private theorem expandRepeatedPartFactorArray_invariant
    (rp : ZPoly) (coreFactors : Array ZPoly) :
    Array.polyProduct (expandRepeatedPartFactorArray rp coreFactors).1 *
        (expandRepeatedPartFactorArray rp coreFactors).2 = rp := by
  unfold expandRepeatedPartFactorArray
  exact expandRepeatedPartFactorsAux_invariant _ _ _

private theorem expandRepeatedPartFactorsAux_mem
    (coreFactors : List ZPoly) (rp : ZPoly) (fuel : Nat) (factor : ZPoly)
    (hmem : factor ∈ (expandRepeatedPartFactorsAux coreFactors rp fuel).1.toList) :
    factor ∈ coreFactors := by
  induction coreFactors generalizing rp with
  | nil =>
      simp [expandRepeatedPartFactorsAux] at hmem
  | cons q qs ih =>
      unfold expandRepeatedPartFactorsAux at hmem
      simp only at hmem
      rw [Array.toList_append] at hmem
      rcases List.mem_append.mp hmem with hreplicate | hrest
      · have hreplicate_list :
            factor ∈ List.replicate (consumeExactPower rp q fuel).2 q := by
          simpa using hreplicate
        rw [List.eq_of_mem_replicate hreplicate_list]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem q (ih _ hrest)

private theorem expandRepeatedPartFactorArray_mem
    (rp : ZPoly) (coreFactors : Array ZPoly) (factor : ZPoly)
    (hmem : factor ∈ (expandRepeatedPartFactorArray rp coreFactors).1.toList) :
    factor ∈ coreFactors.toList := by
  unfold expandRepeatedPartFactorArray at hmem
  exact expandRepeatedPartFactorsAux_mem _ _ _ _ hmem

private theorem reassemblePolynomialFactors_mem
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) (factor : ZPoly)
    (hmem : factor ∈ (reassemblePolynomialFactors d coreFactors).toList) :
    factor ∈ (polynomialNormalizationPrefixFactors d).toList ∨
      factor ∈ coreFactors.toList := by
  unfold reassemblePolynomialFactors at hmem
  generalize hexp : expandRepeatedPartFactorArray d.repeatedPart coreFactors = exp at hmem
  cases exp with
  | mk expanded residual =>
      simp only at hmem
      by_cases hres : residual = 1
      · rw [if_pos hres] at hmem
        rw [Array.toList_append, Array.toList_append] at hmem
        rcases List.mem_append.mp hmem with hxe | hcf
        · rcases List.mem_append.mp hxe with hx | hexp_mem
          · left
            unfold polynomialNormalizationPrefixFactors
            rw [Array.toList_append]
            exact List.mem_append.mpr (Or.inl hx)
          · right
            have hexp_mem' : factor ∈
                (expandRepeatedPartFactorArray d.repeatedPart coreFactors).1.toList := by
              rw [hexp]
              exact hexp_mem
            exact expandRepeatedPartFactorArray_mem _ _ _ hexp_mem'
        · right
          exact hcf
      · rw [if_neg hres] at hmem
        rw [Array.toList_append] at hmem
        rcases List.mem_append.mp hmem with hprefix | hcf
        · exact Or.inl hprefix
        · exact Or.inr hcf

/-- Public wrapper for the reassembly membership split used by downstream
factor-output classifiers. -/
theorem reassemblePolynomialFactors_mem_normalization_or_core
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) (factor : ZPoly)
    (hmem : factor ∈ (reassemblePolynomialFactors d coreFactors).toList) :
    factor ∈ (polynomialNormalizationPrefixFactors d).toList ∨
      factor ∈ coreFactors.toList :=
  reassemblePolynomialFactors_mem d coreFactors factor hmem

/--
The repeated-part expansion fully consumed the normalization residual, so
`reassemblePolynomialFactors` uses its expanded branch rather than the
non-decomposed repeated-part fallback.
-/
@[expose]
def reassemblyExpansionComplete
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) : Prop :=
  (expandRepeatedPartFactorArray d.repeatedPart coreFactors).2 = 1

/--
Sharp membership split for the complete-expansion branch of reassembly.

When the repeated part has been completely expanded by the supplied core
factors, a reassembled raw factor is either an extracted `X`-power factor or one
of the supplied core factors. In particular, it cannot be the non-decomposed
`repeatedPartFactorArray` fallback.
-/
theorem reassemblePolynomialFactors_mem_xPower_or_core_of_expansionComplete
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) (factor : ZPoly)
    (hcomplete : reassemblyExpansionComplete d coreFactors)
    (hmem : factor ∈ (reassemblePolynomialFactors d coreFactors).toList) :
    factor ∈ (xPowerFactorArray d.xPower).toList ∨
      factor ∈ coreFactors.toList := by
  unfold reassemblyExpansionComplete at hcomplete
  unfold reassemblePolynomialFactors at hmem
  generalize hexp : expandRepeatedPartFactorArray d.repeatedPart coreFactors = exp at hmem hcomplete
  cases exp with
  | mk expanded residual =>
      simp only at hmem hcomplete
      rw [if_pos hcomplete] at hmem
      rw [Array.toList_append, Array.toList_append] at hmem
      rcases List.mem_append.mp hmem with hxe | hcore
      · rcases List.mem_append.mp hxe with hx | hexp_mem
        · exact Or.inl hx
        · right
          have hexp_mem' :
              factor ∈ (expandRepeatedPartFactorArray d.repeatedPart coreFactors).1.toList := by
            rw [hexp]
            exact hexp_mem
          exact expandRepeatedPartFactorArray_mem _ _ _ hexp_mem'
      · exact Or.inr hcore

private theorem polyProduct_repeatedPartFactorArray_eq (repeatedPart : ZPoly) :
    Array.polyProduct (repeatedPartFactorArray repeatedPart) = repeatedPart := by
  rw [polyProduct_repeatedPartFactorArray]
  split <;> simp_all

private theorem polyProduct_reassemblePolynomialFactors
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) :
    Array.polyProduct (reassemblePolynomialFactors d coreFactors) =
      DensePoly.shift d.xPower d.repeatedPart * Array.polyProduct coreFactors := by
  unfold reassemblePolynomialFactors
  have hinv := expandRepeatedPartFactorArray_invariant d.repeatedPart coreFactors
  generalize hexp : expandRepeatedPartFactorArray d.repeatedPart coreFactors = exp at hinv
  cases exp with
  | mk expanded residual =>
      simp only at hinv ⊢
      by_cases hres : residual = 1
      · rw [if_pos hres]
        rw [hres] at hinv
        rw [DensePoly.mul_one_right_poly (S := Int)] at hinv
        rw [ZPoly.polyProduct_append, ZPoly.polyProduct_append, polyProduct_xPowerFactorArray_mul,
          hinv]
      · rw [if_neg hres]
        rw [ZPoly.polyProduct_append, polyProduct_polynomialNormalizationPrefixFactors,
          polyProduct_xPowerFactorArray_mul, polyProduct_repeatedPartFactorArray_eq]

private theorem polyProduct_normalizationPrefixFactors (d : FactorNormalizationData) :
    Array.polyProduct (normalizationPrefixFactors d) =
      Array.polyProduct (contentFactorArray d.content) *
        (Array.polyProduct (xPowerFactorArray d.xPower) *
          Array.polyProduct (repeatedPartFactorArray d.repeatedPart)) := by
  unfold normalizationPrefixFactors
  rw [ZPoly.polyProduct_append, ZPoly.polyProduct_append, DensePoly.mul_assoc_poly (S := Int)]

private theorem polyPow_zero (g : ZPoly) :
    Factorization.polyPow g 0 = (1 : ZPoly) := rfl

private theorem polyPow_succ (g : ZPoly) (n : Nat) :
    Factorization.polyPow g (n + 1) = Factorization.polyPow g n * g := rfl

private theorem polyPow_one (g : ZPoly) :
    Factorization.polyPow g 1 = g := by
  rw [polyPow_succ, polyPow_zero, ZPoly.one_mul_zpoly]

private def multListProduct (mults : List (ZPoly × Nat)) : ZPoly :=
  mults.foldl (fun acc m => acc * Factorization.polyPow m.1 m.2) 1

private theorem multListProduct_nil :
    multListProduct [] = 1 := rfl

private theorem multListFoldl_eq_mul_foldl_one (acc : ZPoly) (mults : List (ZPoly × Nat)) :
    mults.foldl (fun acc m => acc * Factorization.polyPow m.1 m.2) acc =
      acc * mults.foldl (fun acc m => acc * Factorization.polyPow m.1 m.2) 1 := by
  induction mults generalizing acc with
  | nil =>
      simpa using (DensePoly.mul_one_right_poly (S := Int) acc).symm
  | cons m ms ih =>
      simp only [List.foldl_cons]
      rw [ZPoly.one_mul_zpoly]
      calc
        ms.foldl (fun acc m => acc * Factorization.polyPow m.1 m.2)
            (acc * Factorization.polyPow m.1 m.2) =
              (acc * Factorization.polyPow m.1 m.2) *
                ms.foldl (fun acc m => acc * Factorization.polyPow m.1 m.2) 1 :=
            ih (acc * Factorization.polyPow m.1 m.2)
        _ = acc * (Factorization.polyPow m.1 m.2 *
              ms.foldl (fun acc m => acc * Factorization.polyPow m.1 m.2) 1) := by
              rw [DensePoly.mul_assoc_poly (S := Int)]
        _ = acc * ms.foldl (fun acc m => acc * Factorization.polyPow m.1 m.2)
              (Factorization.polyPow m.1 m.2) := by
              rw [ih (Factorization.polyPow m.1 m.2)]

private theorem multListProduct_cons (m : ZPoly × Nat) (ms : List (ZPoly × Nat)) :
    multListProduct (m :: ms) =
      Factorization.polyPow m.1 m.2 * multListProduct ms := by
  simp only [multListProduct, List.foldl_cons]
  rw [ZPoly.one_mul_zpoly]
  exact multListFoldl_eq_mul_foldl_one (Factorization.polyPow m.1 m.2) ms

private theorem multListProduct_singleton (m : ZPoly × Nat) :
    multListProduct [m] = Factorization.polyPow m.1 m.2 := by
  rw [multListProduct_cons, multListProduct_nil, DensePoly.mul_one_right_poly]

private theorem multListProduct_append (xs ys : List (ZPoly × Nat)) :
    multListProduct (xs ++ ys) = multListProduct xs * multListProduct ys := by
  induction xs with
  | nil =>
      rw [List.nil_append, multListProduct_nil, ZPoly.one_mul_zpoly]
  | cons m ms ih =>
      rw [List.cons_append, multListProduct_cons, multListProduct_cons, ih,
        DensePoly.mul_assoc_poly (S := Int)]

private theorem multListProduct_reverse (mults : List (ZPoly × Nat)) :
    multListProduct mults.reverse = multListProduct mults := by
  induction mults with
  | nil => rfl
  | cons m ms ih =>
      rw [List.reverse_cons, multListProduct_append, multListProduct_singleton,
        ih, multListProduct_cons]
      exact DensePoly.mul_comm_poly (S := Int) _ _

private theorem multListProduct_bumpFactorMultiplicity
    (g : ZPoly) (mults : List (ZPoly × Nat)) :
    multListProduct (bumpFactorMultiplicity g mults) = g * multListProduct mults := by
  induction mults with
  | nil =>
      rw [bumpFactorMultiplicity, multListProduct_singleton, multListProduct_nil, polyPow_one,
        DensePoly.mul_one_right_poly]
  | cons entry entries ih =>
      unfold bumpFactorMultiplicity
      by_cases heq : entry.1 = g
      · simp only [heq, if_true]
        rw [multListProduct_cons]
        show Factorization.polyPow g (entry.2 + 1) * multListProduct entries =
          g * multListProduct (entry :: entries)
        rw [polyPow_succ, multListProduct_cons, heq]
        rw [DensePoly.mul_comm_poly (S := Int)
              (Factorization.polyPow g entry.2) g]
        rw [DensePoly.mul_assoc_poly (S := Int)]
      · simp only [heq, if_false]
        rw [multListProduct_cons, multListProduct_cons, ih, ← DensePoly.mul_assoc_poly (S := Int)]
        rw [DensePoly.mul_comm_poly (S := Int)
              (Factorization.polyPow entry.1 entry.2) g]
        rw [DensePoly.mul_assoc_poly (S := Int)]

private def collectFactorStep
    (acc : List (ZPoly × Nat)) (f : ZPoly) : List (ZPoly × Nat) :=
  let f := normalizeFactorSign f
  if shouldRecordPolynomialFactor f then
    bumpFactorMultiplicity f acc
  else
    acc

private theorem collectFactorMultiplicities_eq_foldl (factors : Array ZPoly) :
    collectFactorMultiplicities factors =
      (factors.toList.foldl collectFactorStep []).reverse.toArray := rfl

private def filteredNormalizedFactors (factors : List ZPoly) : List ZPoly :=
  factors.filterMap fun f =>
    let f := normalizeFactorSign f
    if shouldRecordPolynomialFactor f then some f else none

private theorem filteredNormalizedFactors_nil :
    filteredNormalizedFactors [] = [] := rfl

private theorem filteredNormalizedFactors_cons_keep
    {f : ZPoly} (fs : List ZPoly)
    (hkeep : shouldRecordPolynomialFactor (normalizeFactorSign f) = true) :
    filteredNormalizedFactors (f :: fs) =
      normalizeFactorSign f :: filteredNormalizedFactors fs := by
  unfold filteredNormalizedFactors
  simp [hkeep]

private theorem filteredNormalizedFactors_cons_drop
    {f : ZPoly} (fs : List ZPoly)
    (hdrop : shouldRecordPolynomialFactor (normalizeFactorSign f) = false) :
    filteredNormalizedFactors (f :: fs) = filteredNormalizedFactors fs := by
  unfold filteredNormalizedFactors
  simp [hdrop]

private theorem shouldRecordPolynomialFactor_eq_true_of_ne
    {f : ZPoly}
    (hzero : f ≠ 0)
    (hone : f ≠ 1)
    (hneg_one : f ≠ DensePoly.C (-1 : Int)) :
    shouldRecordPolynomialFactor f = true := by
  unfold shouldRecordPolynomialFactor
  simp [hzero, hone, hneg_one]

theorem normalizeFactorSign_ne_zero_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0) :
    normalizeFactorSign f ≠ 0 := by
  unfold normalizeFactorSign
  by_cases hlead : DensePoly.leadingCoeff f < 0
  · rw [if_pos hlead]
    intro hzero
    apply hf
    apply DensePoly.ext_coeff
    intro n
    have hcoeff := congrArg (fun p : ZPoly => p.coeff n) hzero
    change (DensePoly.scale (-1 : Int) f).coeff n = (0 : ZPoly).coeff n at hcoeff
    rw [DensePoly.coeff_scale (R := Int) (-1 : Int) f n
      (Int.mul_zero (-1 : Int))] at hcoeff
    rw [DensePoly.coeff_zero] at hcoeff
    rw [DensePoly.coeff_zero]
    omega
  · rw [if_neg hlead]
    exact hf

private theorem filteredNormalizedFactors_eq_map_normalizeFactorSign_of_no_units
    (factors : List ZPoly)
    (h_no_zero : ∀ factor ∈ factors, factor ≠ 0)
    (h_no_unit :
      ∀ factor ∈ factors,
        normalizeFactorSign factor ≠ 1 ∧
          normalizeFactorSign factor ≠ DensePoly.C (-1 : Int)) :
    filteredNormalizedFactors factors = factors.map normalizeFactorSign := by
  induction factors with
  | nil => rfl
  | cons factor factors ih =>
      have hkeep :
          shouldRecordPolynomialFactor (normalizeFactorSign factor) = true :=
        shouldRecordPolynomialFactor_eq_true_of_ne
          (normalizeFactorSign_ne_zero_of_ne_zero factor
            (h_no_zero factor (by simp)))
          (h_no_unit factor (by simp)).1
          (h_no_unit factor (by simp)).2
      rw [filteredNormalizedFactors_cons_keep factors hkeep]
      rw [ih
        (fun factor hmem => h_no_zero factor (by simp [hmem]))
        (fun factor hmem => h_no_unit factor (by simp [hmem]))]
      simp

private theorem polyProduct_filteredNormalizedFactors_eq_of_normalized_product
    (factors : Array ZPoly)
    (h_no_zero : ∀ factor ∈ factors.toList, factor ≠ 0)
    (h_no_unit :
      ∀ factor ∈ factors.toList,
        normalizeFactorSign factor ≠ 1 ∧
          normalizeFactorSign factor ≠ DensePoly.C (-1 : Int))
    (hnormalized_product :
      Array.polyProduct (factors.toList.map normalizeFactorSign).toArray =
        Array.polyProduct factors) :
    Array.polyProduct (filteredNormalizedFactors factors.toList).toArray =
      Array.polyProduct factors := by
  rw [filteredNormalizedFactors_eq_map_normalizeFactorSign_of_no_units
    factors.toList h_no_zero h_no_unit]
  exact hnormalized_product

private theorem filteredNormalizedFactors_eq_self_of_all_recorded_normalized
    (factors : List ZPoly)
    (hnormalized :
      ∀ factor ∈ factors, normalizeFactorSign factor = factor)
    (hrecorded :
      ∀ factor ∈ factors, shouldRecordPolynomialFactor factor = true) :
    filteredNormalizedFactors factors = factors := by
  induction factors with
  | nil => rfl
  | cons factor factors ih =>
      have hfactor_normalized :
          normalizeFactorSign factor = factor :=
        hnormalized factor (by simp)
      have hfactor_recorded :
          shouldRecordPolynomialFactor factor = true :=
        hrecorded factor (by simp)
      have hkeep :
          shouldRecordPolynomialFactor (normalizeFactorSign factor) = true := by
        rw [hfactor_normalized]
        exact hfactor_recorded
      rw [filteredNormalizedFactors_cons_keep factors hkeep, hfactor_normalized]
      rw [ih
        (fun factor hmem => hnormalized factor (by simp [hmem]))
        (fun factor hmem => hrecorded factor (by simp [hmem]))]

private theorem polyProduct_filteredNormalizedFactors_eq_self_of_all_recorded_normalized
    (factors : Array ZPoly)
    (hnormalized :
      ∀ factor ∈ factors.toList, normalizeFactorSign factor = factor)
    (hrecorded :
      ∀ factor ∈ factors.toList, shouldRecordPolynomialFactor factor = true) :
    Array.polyProduct (filteredNormalizedFactors factors.toList).toArray =
      Array.polyProduct factors := by
  rw [filteredNormalizedFactors_eq_self_of_all_recorded_normalized
    factors.toList hnormalized hrecorded]

private theorem multListProduct_collectAux
    (acc : List (ZPoly × Nat)) (factors : List ZPoly) :
    multListProduct (factors.foldl collectFactorStep acc) =
      multListProduct acc *
        Array.polyProduct (filteredNormalizedFactors factors).toArray := by
  induction factors generalizing acc with
  | nil =>
      rw [filteredNormalizedFactors_nil, List.foldl_nil]
      show multListProduct acc = _
      simp [Array.polyProduct]
      rw [DensePoly.mul_one_right_poly]
  | cons f fs ih =>
      rw [List.foldl_cons]
      by_cases hrec :
          shouldRecordPolynomialFactor (normalizeFactorSign f) = true
      · rw [filteredNormalizedFactors_cons_keep fs hrec]
        rw [show collectFactorStep acc f =
              bumpFactorMultiplicity (normalizeFactorSign f) acc from by
              unfold collectFactorStep
              simp [hrec]]
        rw [ih (bumpFactorMultiplicity (normalizeFactorSign f) acc),
          multListProduct_bumpFactorMultiplicity, ZPoly.polyProduct_cons_toArray]
        rw [DensePoly.mul_comm_poly (S := Int) (normalizeFactorSign f)
              (multListProduct acc)]
        rw [DensePoly.mul_assoc_poly (S := Int)]
      · have hdrop : shouldRecordPolynomialFactor (normalizeFactorSign f) = false := by
          cases hcase :
              shouldRecordPolynomialFactor (normalizeFactorSign f) with
          | true => exact (hrec hcase).elim
          | false => rfl
        rw [filteredNormalizedFactors_cons_drop fs hdrop]
        rw [show collectFactorStep acc f = acc from by
              unfold collectFactorStep
              simp [hdrop]]
        exact ih acc

private theorem multListProduct_collectFactorMultiplicities
    (factors : Array ZPoly) :
    multListProduct (collectFactorMultiplicities factors).toList =
      Array.polyProduct (filteredNormalizedFactors factors.toList).toArray := by
  rw [collectFactorMultiplicities_eq_foldl]
  show multListProduct (factors.toList.foldl collectFactorStep []).reverse = _
  rw [multListProduct_reverse]
  have hcol := multListProduct_collectAux [] factors.toList
  rw [multListProduct_nil, ZPoly.one_mul_zpoly] at hcol
  exact hcol

private theorem bumpFactorMultiplicity_mem_normalized_or_old
    (g : ZPoly) (acc : List (ZPoly × Nat)) (entry : ZPoly × Nat)
    (hmem : entry ∈ bumpFactorMultiplicity g acc) :
    entry.1 = g ∨ entry ∈ acc := by
  induction acc with
  | nil =>
      simp [bumpFactorMultiplicity] at hmem
      left
      rw [hmem]
  | cons head tail ih =>
      unfold bumpFactorMultiplicity at hmem
      by_cases heq : head.1 = g
      · simp [heq] at hmem
        rcases hmem with hentry | htail
        · left
          rw [hentry]
        · right
          exact List.mem_cons_of_mem head htail
      · simp [heq] at hmem
        rcases hmem with hhead | htail
        · right
          rw [hhead]
          simp
        · rcases ih htail with hnorm | hold
          · left
            exact hnorm
          · right
            exact List.mem_cons_of_mem head hold

private theorem collectFactorStep_mem_normalized_or_old
    (acc : List (ZPoly × Nat)) (factor : ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ collectFactorStep acc factor) :
    entry.1 = normalizeFactorSign factor ∨ entry ∈ acc := by
  unfold collectFactorStep at hmem
  by_cases hrec : shouldRecordPolynomialFactor (normalizeFactorSign factor) = true
  · simp [hrec] at hmem
    exact bumpFactorMultiplicity_mem_normalized_or_old
      (normalizeFactorSign factor) acc entry hmem
  · simp [hrec] at hmem
    exact Or.inr hmem

private theorem foldl_collectFactorStep_mem_normalized_or_old
    (factors : List ZPoly) (acc : List (ZPoly × Nat)) (entry : ZPoly × Nat)
    (hmem : entry ∈ factors.foldl collectFactorStep acc) :
    entry ∈ acc ∨ ∃ factor ∈ factors, entry.1 = normalizeFactorSign factor := by
  induction factors generalizing acc with
  | nil =>
      simp at hmem
      exact Or.inl hmem
  | cons factor factors ih =>
      simp only [List.foldl_cons] at hmem
      rcases ih (collectFactorStep acc factor) hmem with hstep | htail
      · rcases collectFactorStep_mem_normalized_or_old acc factor entry hstep with hnorm | hold
        · right
          exact ⟨factor, by simp, hnorm⟩
        · left
          exact hold
      · rcases htail with ⟨raw, hraw, hnorm⟩
        right
        exact ⟨raw, by simp [hraw], hnorm⟩

private theorem bumpFactorMultiplicity_entries_positive
    (g : ZPoly) (acc : List (ZPoly × Nat))
    (hpos : ∀ entry ∈ acc, 0 < entry.2) :
    ∀ entry ∈ bumpFactorMultiplicity g acc, 0 < entry.2 := by
  induction acc with
  | nil =>
      intro entry hmem
      simp [bumpFactorMultiplicity] at hmem
      rw [hmem]
      simp
  | cons head tail ih =>
      intro entry hmem
      unfold bumpFactorMultiplicity at hmem
      by_cases heq : head.1 = g
      · simp [heq] at hmem
        rcases hmem with hentry | htail
        · rw [hentry]
          simp
        · exact hpos entry (by simp [htail])
      · simp [heq] at hmem
        rcases hmem with hentry | htail
        · rw [hentry]
          exact hpos head (by simp)
        · exact ih (fun entry hentry => hpos entry (by simp [hentry])) entry htail

private theorem collectFactorStep_entries_positive
    (acc : List (ZPoly × Nat)) (factor : ZPoly)
    (hpos : ∀ entry ∈ acc, 0 < entry.2) :
    ∀ entry ∈ collectFactorStep acc factor, 0 < entry.2 := by
  unfold collectFactorStep
  by_cases hrec : shouldRecordPolynomialFactor (normalizeFactorSign factor) = true
  · intro entry hmem
    simp [hrec] at hmem
    exact
      bumpFactorMultiplicity_entries_positive
        (normalizeFactorSign factor) acc hpos entry hmem
  · intro entry hmem
    simp [hrec] at hmem
    exact hpos entry hmem

private theorem foldl_collectFactorStep_entries_positive
    (factors : List ZPoly) (acc : List (ZPoly × Nat))
    (hpos : ∀ entry ∈ acc, 0 < entry.2) :
    ∀ entry ∈ factors.foldl collectFactorStep acc, 0 < entry.2 := by
  induction factors generalizing acc with
  | nil =>
      simpa using hpos
  | cons factor factors ih =>
      simp only [List.foldl_cons]
      exact ih (collectFactorStep acc factor)
        (collectFactorStep_entries_positive acc factor hpos)

private theorem bumpFactorMultiplicity_entries_recorded
    (g : ZPoly) (acc : List (ZPoly × Nat))
    (hrec : shouldRecordPolynomialFactor g = true)
    (hacc : ∀ entry ∈ acc, shouldRecordPolynomialFactor entry.1 = true) :
    ∀ entry ∈ bumpFactorMultiplicity g acc,
      shouldRecordPolynomialFactor entry.1 = true := by
  intro entry hmem
  rcases bumpFactorMultiplicity_mem_normalized_or_old g acc entry hmem with hnorm | hold
  · rw [hnorm]
    exact hrec
  · exact hacc entry hold

private theorem collectFactorStep_entries_recorded
    (acc : List (ZPoly × Nat)) (factor : ZPoly)
    (hacc : ∀ entry ∈ acc, shouldRecordPolynomialFactor entry.1 = true) :
    ∀ entry ∈ collectFactorStep acc factor,
      shouldRecordPolynomialFactor entry.1 = true := by
  unfold collectFactorStep
  by_cases hrec : shouldRecordPolynomialFactor (normalizeFactorSign factor) = true
  · intro entry hmem
    simp [hrec] at hmem
    exact bumpFactorMultiplicity_entries_recorded
      (normalizeFactorSign factor) acc hrec hacc entry hmem
  · intro entry hmem
    simp [hrec] at hmem
    exact hacc entry hmem

private theorem foldl_collectFactorStep_entries_recorded
    (factors : List ZPoly) (acc : List (ZPoly × Nat))
    (hacc : ∀ entry ∈ acc, shouldRecordPolynomialFactor entry.1 = true) :
    ∀ entry ∈ factors.foldl collectFactorStep acc,
      shouldRecordPolynomialFactor entry.1 = true := by
  induction factors generalizing acc with
  | nil =>
      simpa using hacc
  | cons factor factors ih =>
      simp only [List.foldl_cons]
      exact ih (collectFactorStep acc factor)
        (collectFactorStep_entries_recorded acc factor hacc)

private theorem bumpFactorMultiplicity_pairwise_first
    (g : ZPoly) (acc : List (ZPoly × Nat))
    (hpair : List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1) acc) :
    List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1)
      (bumpFactorMultiplicity g acc) := by
  induction acc with
  | nil =>
      simp [bumpFactorMultiplicity]
  | cons head tail ih =>
      unfold bumpFactorMultiplicity
      by_cases heq : head.1 = g
      · cases hpair with
        | cons hhead htail =>
            simp [heq]
            constructor
            · intro a m hmem
              simpa [heq] using hhead (a, m) hmem
            · exact htail
      · cases hpair with
        | cons hhead htail =>
            simp [heq]
            constructor
            · intro a m hmem hfirst
              rcases bumpFactorMultiplicity_mem_normalized_or_old g tail (a, m) hmem with
                hnorm | hold
              · exact heq (hfirst.trans hnorm)
              · exact hhead (a, m) hold hfirst
            · exact ih htail

private theorem collectFactorStep_pairwise_first
    (acc : List (ZPoly × Nat)) (factor : ZPoly)
    (hpair : List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1) acc) :
    List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1)
      (collectFactorStep acc factor) := by
  unfold collectFactorStep
  by_cases hrec : shouldRecordPolynomialFactor (normalizeFactorSign factor) = true
  · simp [hrec]
    exact bumpFactorMultiplicity_pairwise_first
      (normalizeFactorSign factor) acc hpair
  · simp [hrec]
    exact hpair

private theorem foldl_collectFactorStep_pairwise_first
    (factors : List ZPoly) (acc : List (ZPoly × Nat))
    (hpair : List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1) acc) :
    List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1)
      (factors.foldl collectFactorStep acc) := by
  induction factors generalizing acc with
  | nil =>
      simpa using hpair
  | cons factor factors ih =>
      simp only [List.foldl_cons]
      exact ih (collectFactorStep acc factor)
        (collectFactorStep_pairwise_first acc factor hpair)

/-- Every collected `(factor, multiplicity)` entry comes from some raw factor
after sign normalization. This is the theorem-level wrapper for the
`collectFactorMultiplicities` step. -/
theorem collectFactorMultiplicities_entry_mem_normalized_raw
    (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (collectFactorMultiplicities factors).toList) :
    ∃ raw ∈ factors.toList, entry.1 = normalizeFactorSign raw := by
  rw [collectFactorMultiplicities_eq_foldl] at hmem
  have hmem_fold : entry ∈ factors.toList.foldl collectFactorStep [] := by
    simpa using hmem
  rcases foldl_collectFactorStep_mem_normalized_or_old factors.toList [] entry hmem_fold with
    hold | hraw
  · simp at hold
  · exact hraw

/-- Every collected factorization entry has positive multiplicity. -/
theorem collectFactorMultiplicities_entry_multiplicity_pos
    (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (collectFactorMultiplicities factors).toList) :
    0 < entry.2 := by
  rw [collectFactorMultiplicities_eq_foldl] at hmem
  have hmem_fold : entry ∈ factors.toList.foldl collectFactorStep [] := by
    simpa using hmem
  exact
    foldl_collectFactorStep_entries_positive factors.toList []
      (by simp) entry hmem_fold

/-- Every collected factorization entry passed the recorded-factor filter. -/
theorem collectFactorMultiplicities_entry_shouldRecord
    (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (collectFactorMultiplicities factors).toList) :
    shouldRecordPolynomialFactor entry.1 = true := by
  rw [collectFactorMultiplicities_eq_foldl] at hmem
  have hmem_fold : entry ∈ factors.toList.foldl collectFactorStep [] := by
    simpa using hmem
  exact
    foldl_collectFactorStep_entries_recorded factors.toList []
      (by simp) entry hmem_fold

/-- The collector emits no duplicate polynomial keys. -/
theorem collectFactorMultiplicities_pairwise_first
    (factors : Array ZPoly) :
    List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1)
      (collectFactorMultiplicities factors).toList := by
  rw [collectFactorMultiplicities_eq_foldl]
  have hpair :
      List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1)
        (factors.toList.foldl collectFactorStep []) :=
    foldl_collectFactorStep_pairwise_first factors.toList [] (by simp)
  rw [List.pairwise_reverse]
  exact hpair.imp (fun hne h => hne h.symm)

/-- Membership in a `Factorization` built from a raw factor array descends to
membership in that raw array, up to sign normalization. -/
theorem factorizationOfFactors_entry_mem_normalized_raw
    (f : ZPoly) (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factorizationOfFactors f factors).factors.toList) :
    ∃ raw ∈ factors.toList, entry.1 = normalizeFactorSign raw := by
  unfold factorizationOfFactors at hmem
  exact collectFactorMultiplicities_entry_mem_normalized_raw factors entry hmem

/-- Entries in a `Factorization` built from raw factors have positive multiplicity. -/
theorem factorizationOfFactors_entry_multiplicity_pos
    (f : ZPoly) (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factorizationOfFactors f factors).factors.toList) :
    0 < entry.2 := by
  unfold factorizationOfFactors at hmem
  exact collectFactorMultiplicities_entry_multiplicity_pos factors entry hmem

/-- A `Factorization` built from raw factors has no duplicate polynomial keys. -/
theorem factorizationOfFactors_pairwise_first
    (f : ZPoly) (factors : Array ZPoly) :
    List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1)
      (factorizationOfFactors f factors).factors.toList := by
  unfold factorizationOfFactors
  exact collectFactorMultiplicities_pairwise_first factors

private theorem factorizationOfFactors_product
    (f : ZPoly) (factors : Array ZPoly) :
    Factorization.product (factorizationOfFactors f factors) =
      DensePoly.C (signedContentScalar f) *
        Array.polyProduct (filteredNormalizedFactors factors.toList).toArray := by
  show
    (collectFactorMultiplicities factors).foldl
        (fun acc m => acc * Factorization.polyPow m.1 m.2)
        (DensePoly.C (signedContentScalar f)) =
      _
  rw [← Array.foldl_toList, multListFoldl_eq_mul_foldl_one]
  show
    DensePoly.C (signedContentScalar f) *
        multListProduct (collectFactorMultiplicities factors).toList =
      _
  rw [multListProduct_collectFactorMultiplicities]

private theorem factorizationOfFactors_product_of_filtered_product
    (f : ZPoly) (factors : Array ZPoly)
    (hraw : DensePoly.C (signedContentScalar f) *
      Array.polyProduct factors = f)
    (hfiltered :
      Array.polyProduct (filteredNormalizedFactors factors.toList).toArray =
        Array.polyProduct factors) :
    Factorization.product (factorizationOfFactors f factors) = f := by
  rw [factorizationOfFactors_product, hfiltered]
  exact hraw

private theorem factorizationOfFactors_product_of_raw_product_of_all_recorded_normalized
    (f : ZPoly) (factors : Array ZPoly)
    (hraw : DensePoly.C (signedContentScalar f) *
      Array.polyProduct factors = f)
    (hnormalized :
      ∀ factor ∈ factors.toList, normalizeFactorSign factor = factor)
    (hrecorded :
      ∀ factor ∈ factors.toList, shouldRecordPolynomialFactor factor = true) :
    Factorization.product (factorizationOfFactors f factors) = f :=
  factorizationOfFactors_product_of_filtered_product f factors hraw
    (polyProduct_filteredNormalizedFactors_eq_self_of_all_recorded_normalized
      factors hnormalized hrecorded)

private theorem signedContentScalar_zero :
    signedContentScalar 0 = 0 := by
  unfold signedContentScalar
  simp

private theorem factorizationOfFactors_product_of_zero (factors : Array ZPoly) :
    Factorization.product (factorizationOfFactors 0 factors) = 0 := by
  rw [factorizationOfFactors_product, signedContentScalar_zero]
  change DensePoly.C (0 : Int) *
      Array.polyProduct (filteredNormalizedFactors factors.toList).toArray = 0
  rw [show (DensePoly.C (0 : Int) : ZPoly) = (0 : ZPoly) from rfl]
  exact DensePoly.zero_mul
    (Array.polyProduct (filteredNormalizedFactors factors.toList).toArray)

private theorem leadingCoeff_X :
    DensePoly.leadingCoeff ZPoly.X = (1 : Int) := by
  rfl

private theorem X_ne_zero : ZPoly.X ≠ (0 : ZPoly) := by
  decide

private theorem X_ne_one : ZPoly.X ≠ (1 : ZPoly) := by
  decide

private theorem X_ne_C_neg_one : ZPoly.X ≠ DensePoly.C (-1 : Int) := by
  decide

private theorem normalizeFactorSign_X :
    normalizeFactorSign ZPoly.X = ZPoly.X := by
  unfold normalizeFactorSign
  rw [leadingCoeff_X]
  simp

private theorem shouldRecordPolynomialFactor_X :
    shouldRecordPolynomialFactor ZPoly.X = true := by
  unfold shouldRecordPolynomialFactor
  simp [X_ne_zero, X_ne_one, X_ne_C_neg_one]

/-- The sign-normalisation of `1` is `1`.  Exposed publicly so Mathlib-side
per-branch umbrellas (in particular the fast-path constant arm, where the
singleton square-free core collapses to `1`) can normalise the unit core
without re-deriving the leading-coefficient computation inline. -/
theorem normalizeFactorSign_one :
    normalizeFactorSign (1 : ZPoly) = 1 := by
  unfold normalizeFactorSign
  have hnot : ¬ DensePoly.leadingCoeff (1 : ZPoly) < 0 := by
    change ¬ DensePoly.leadingCoeff (DensePoly.C (1 : Int)) < 0
    simp [DensePoly.leadingCoeff,
      DensePoly.coeffs_C_of_ne_zero (by decide : (1 : Int) ≠ 0)]
  rw [if_neg hnot]

/-- The `shouldRecordPolynomialFactor` filter rejects the unit `1`.  Exposed
publicly so Mathlib-side per-branch umbrellas can contradict
`factorize_entry_shouldRecord` directly when an entry collapses to a
unit (in particular the fast-path constant arm, where the singleton
square-free core is `1`). -/
theorem shouldRecordPolynomialFactor_one :
    shouldRecordPolynomialFactor (1 : ZPoly) = false := by
  unfold shouldRecordPolynomialFactor
  simp

private theorem mem_xPowerFactorArray_eq_X (power : Nat) (factor : ZPoly)
    (h : factor ∈ (xPowerFactorArray power).toList) :
    factor = ZPoly.X := by
  unfold xPowerFactorArray at h
  simp [List.mem_replicate] at h
  exact h.2

private theorem xPowerFactorArray_normalizeFactorSign
    (power : Nat) (factor : ZPoly)
    (h : factor ∈ (xPowerFactorArray power).toList) :
    normalizeFactorSign factor = factor := by
  rw [mem_xPowerFactorArray_eq_X power factor h]
  exact normalizeFactorSign_X

private theorem xPowerFactorArray_shouldRecord
    (power : Nat) (factor : ZPoly)
    (h : factor ∈ (xPowerFactorArray power).toList) :
    shouldRecordPolynomialFactor factor = true := by
  rw [mem_xPowerFactorArray_eq_X power factor h]
  exact shouldRecordPolynomialFactor_X

private theorem mem_repeatedPartFactorArray_eq (rep : ZPoly) (factor : ZPoly)
    (h : factor ∈ (repeatedPartFactorArray rep).toList) :
    factor = rep := by
  unfold repeatedPartFactorArray at h
  by_cases hone : rep = 1
  · simp [hone] at h
  · simp [hone] at h
    exact h

private theorem mem_repeatedPartFactorArray_ne_one
    (rep : ZPoly) (factor : ZPoly)
    (h : factor ∈ (repeatedPartFactorArray rep).toList) :
    rep ≠ 1 := by
  unfold repeatedPartFactorArray at h
  by_cases hone : rep = 1
  · simp [hone] at h
  · exact hone

theorem normalizeFactorSign_eq_self_of_leadingCoeff_nonneg (g : ZPoly)
    (h : 0 ≤ DensePoly.leadingCoeff g) :
    normalizeFactorSign g = g := by
  unfold normalizeFactorSign
  have hnot : ¬ DensePoly.leadingCoeff g < 0 := by omega
  rw [if_neg hnot]

theorem normalizeFactorSign_leadingCoeff_nonneg (g : ZPoly) :
    0 ≤ DensePoly.leadingCoeff (normalizeFactorSign g) := by
  unfold normalizeFactorSign
  by_cases hlead : DensePoly.leadingCoeff g < 0
  · rw [if_pos hlead]
    have hg_ne : g ≠ 0 := by
      intro hzero
      rw [hzero] at hlead
      rw [DensePoly.leadingCoeff_zero] at hlead
      omega
    rw [ZPoly.leadingCoeff_scale_of_nonzero (-1 : Int) g (by decide)]
    omega
  · rw [if_neg hlead]
    omega

theorem normalizeFactorSign_idem (g : ZPoly) :
    normalizeFactorSign (normalizeFactorSign g) = normalizeFactorSign g :=
  normalizeFactorSign_eq_self_of_leadingCoeff_nonneg
    (normalizeFactorSign g) (normalizeFactorSign_leadingCoeff_nonneg g)

/-- Sign normalisation preserves primitivity: the `if_neg` branch is the
identity, and the `if_pos` branch scales by `-1`, which preserves content
by `DensePoly.content_scale_neg_one`. -/
theorem normalizeFactorSign_primitive (f : ZPoly)
    (h : ZPoly.Primitive f) :
    ZPoly.Primitive (normalizeFactorSign f) := by
  unfold normalizeFactorSign
  by_cases hlead : DensePoly.leadingCoeff f < 0
  · rw [if_pos hlead]
    show ZPoly.content (DensePoly.scale (-1 : Int) f) = 1
    rw [show ZPoly.content (DensePoly.scale (-1 : Int) f)
          = DensePoly.content (DensePoly.scale (-1 : Int) f) from rfl,
        DensePoly.content_scale_neg_one f]
    exact h
  · rw [if_neg hlead]
    exact h

/-- Collected factor entries are fixed points of `normalizeFactorSign`. -/
theorem collectFactorMultiplicities_entry_normalizeFactorSign_id
    (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (collectFactorMultiplicities factors).toList) :
    normalizeFactorSign entry.1 = entry.1 := by
  rcases collectFactorMultiplicities_entry_mem_normalized_raw factors entry hmem with
    ⟨raw, _hraw_mem, hraw⟩
  rw [hraw]
  exact normalizeFactorSign_idem raw

/-- Collected factor entries have positive leading coefficient. -/
theorem collectFactorMultiplicities_entry_leadingCoeff_pos
    (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (collectFactorMultiplicities factors).toList) :
    0 < DensePoly.leadingCoeff entry.1 := by
  have hnorm :=
    collectFactorMultiplicities_entry_normalizeFactorSign_id factors entry hmem
  have hnonneg : 0 ≤ DensePoly.leadingCoeff entry.1 := by
    have h := normalizeFactorSign_leadingCoeff_nonneg entry.1
    rwa [hnorm] at h
  have hrecord :=
    collectFactorMultiplicities_entry_shouldRecord factors entry hmem
  have hne : entry.1 ≠ 0 := by
    unfold shouldRecordPolynomialFactor at hrecord
    simp at hrecord
    exact hrecord.1.1
  have hlead_ne : DensePoly.leadingCoeff entry.1 ≠ 0 :=
    ZPoly.leadingCoeff_ne_zero_of_ne_zero entry.1 hne
  omega

/-- Entries in a `Factorization` built from raw factors are fixed points of
`normalizeFactorSign`. -/
theorem factorizationOfFactors_entry_normalizeFactorSign_id
    (f : ZPoly) (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factorizationOfFactors f factors).factors.toList) :
    normalizeFactorSign entry.1 = entry.1 := by
  unfold factorizationOfFactors at hmem
  exact collectFactorMultiplicities_entry_normalizeFactorSign_id factors entry hmem

/-- Entries in a `Factorization` built from raw factors have positive leading
coefficient. -/
theorem factorizationOfFactors_entry_leadingCoeff_pos
    (f : ZPoly) (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factorizationOfFactors f factors).factors.toList) :
    0 < DensePoly.leadingCoeff entry.1 := by
  unfold factorizationOfFactors at hmem
  exact collectFactorMultiplicities_entry_leadingCoeff_pos factors entry hmem

private theorem rat_scale_scale (u v : Rat) (p : DensePoly Rat) :
    DensePoly.scale u (DensePoly.scale v p) = DensePoly.scale (u * v) p := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Rat) u (DensePoly.scale v p) n (Rat.mul_zero u),
    DensePoly.coeff_scale (R := Rat) v p n (Rat.mul_zero v),
    DensePoly.coeff_scale (R := Rat) (u * v) p n (Rat.mul_zero (u * v)), Rat.mul_assoc]

private theorem int_scale_scale (u v : Int) (p : ZPoly) :
    DensePoly.scale u (DensePoly.scale v p) = DensePoly.scale (u * v) p := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Int) u (DensePoly.scale v p) n (Int.mul_zero u),
    DensePoly.coeff_scale (R := Int) v p n (Int.mul_zero v),
    DensePoly.coeff_scale (R := Int) (u * v) p n (Int.mul_zero (u * v)), Int.mul_assoc]

private theorem shift_scale_int (k : Nat) (c : Int) (p : ZPoly) :
    DensePoly.shift k (DensePoly.scale c p) =
      DensePoly.scale c (DensePoly.shift k p) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_shift, DensePoly.coeff_scale (R := Int) c (DensePoly.shift k p) n
    (Int.mul_zero c)]
  rw [DensePoly.coeff_shift]
  by_cases hn : n < k
  · rw [if_pos hn]
    rw [if_pos hn]
    change (0 : Int) = c * 0
    rw [Int.mul_zero]
  · rw [if_neg hn]
    rw [if_neg hn, DensePoly.coeff_scale (R := Int) c p (n - k) (Int.mul_zero c)]

private theorem toRatPoly_mul_product (f g : ZPoly) :
    ZPoly.toRatPoly (f * g) = ZPoly.toRatPoly f * ZPoly.toRatPoly g := by
  exact ZPoly.toRatPoly_mul f g

private theorem primitiveSquareFreeDecomposition_reassembles_xfree_over_rat
    (xFree : ZPoly) :
    let sqData := ZPoly.primitiveSquareFreeDecomposition xFree
    ∃ unit : Rat,
      ZPoly.toRatPoly xFree =
        DensePoly.scale unit (ZPoly.toRatPoly (sqData.squareFreeCore * sqData.repeatedPart)) := by
  simp only
  rcases ZPoly.primitiveSquareFreeDecomposition_reassembly_over_rat xFree with
    ⟨unit, hunit⟩
  refine ⟨(ZPoly.content xFree : Rat) * unit, ?_⟩
  have hprimitive :
      (ZPoly.primitiveSquareFreeDecomposition xFree).primitive =
        ZPoly.primitivePart xFree :=
    ZPoly.primitiveSquareFreeDecomposition_primitive xFree
  rw [hprimitive] at hunit
  have hcontent :
      ZPoly.toRatPoly xFree =
        DensePoly.scale (ZPoly.content xFree : Rat)
          (ZPoly.toRatPoly (ZPoly.primitivePart xFree)) := by
    rw [← ZPoly.toRatPoly_scale_int, ZPoly.content_mul_primitivePart]
  rw [hcontent, hunit, rat_scale_scale, toRatPoly_mul_product]

/-- Converse to `exactQuotient?_product`: if `candidate` is monic with positive
degree and `quotient * candidate = target`, then `exactQuotient? target candidate`
returns `some quotient`. -/
theorem exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree
    {target candidate quotient : ZPoly}
    (hmonic : DensePoly.Monic candidate)
    (hdegree : 0 < candidate.degree?.getD 0)
    (hmul : quotient * candidate = target) :
    exactQuotient? target candidate = some quotient := by
  have hcandidate_ne : candidate ≠ 0 := by
    intro hzero
    have hdeg : candidate.degree?.getD 0 = 0 := by
      rw [hzero]
      simp [DensePoly.degree?]
    omega
  have hcandidate_ne_one : candidate ≠ 1 := by
    intro hone
    have hdeg : candidate.degree?.getD 0 = 0 := by
      rw [hone]
      change (DensePoly.C (1 : Int)).degree?.getD 0 = 0
      exact DensePoly.degree?_C_getD 1
    omega
  have hsize_pos : 0 < candidate.size := by
    rcases Nat.lt_or_ge 0 candidate.size with h | h
    · exact h
    · exfalso
      apply hcandidate_ne
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le candidate (by omega)
  have hisZero_false : candidate.isZero = false := by
    unfold DensePoly.isZero
    have hne : candidate.coeffs ≠ #[] := by
      intro hempty
      have : candidate.size = 0 := by
        change candidate.coeffs.size = 0
        rw [hempty]
        rfl
      omega
    simpa using hne
  have hdivMod_eq : DensePoly.divMod target candidate = (quotient, 0) :=
    ZPoly.divMod_eq_of_monic_mul_eq target candidate quotient hmonic hdegree hmul
  unfold exactQuotient?
  rw [hisZero_false]
  simp only [Bool.false_or, decide_eq_true_eq]
  rw [if_neg hcandidate_ne_one, hdivMod_eq]
  simp [hmul]

/--
Non-monic packaging companion for `exactQuotient?_product`.

For non-monic integer polynomials, an exact product equation alone does not
identify the executable quotient: `DensePoly.divMod` performs coefficient
division in `ℤ`, so downstream proofs must also supply the concrete
`divMod` result.  This lemma records the remaining wrapper logic of
`exactQuotient?`: a recorded non-unit candidate with zero executable
remainder and the checked product equation is accepted with the witnessed
quotient.
-/
theorem exactQuotient?_eq_some_of_divMod_eq_of_shouldRecord
    {target candidate quotient : ZPoly}
    (hrecord : shouldRecordPolynomialFactor candidate = true)
    (hdivMod : DensePoly.divMod target candidate = (quotient, 0))
    (hmul : quotient * candidate = target) :
    exactQuotient? target candidate = some quotient := by
  have hrecord_props :
      (candidate ≠ 0 ∧ candidate ≠ 1) ∧
        candidate ≠ DensePoly.C (-1 : Int) := by
    simpa [shouldRecordPolynomialFactor] using hrecord
  have hcandidate_ne : candidate ≠ 0 := by
    exact hrecord_props.1.1
  have hcandidate_ne_one : candidate ≠ 1 := by
    exact hrecord_props.1.2
  have hsize_pos : 0 < candidate.size := by
    rcases Nat.lt_or_ge 0 candidate.size with h | h
    · exact h
    · exfalso
      apply hcandidate_ne
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le candidate (by omega)
  have hisZero_false : candidate.isZero = false := by
    unfold DensePoly.isZero
    have hne : candidate.coeffs ≠ #[] := by
      intro hempty
      have : candidate.size = 0 := by
        change candidate.coeffs.size = 0
        rw [hempty]
        rfl
      omega
    simpa using hne
  unfold exactQuotient?
  rw [hisZero_false]
  simp only [Bool.false_or, decide_eq_true_eq]
  rw [if_neg hcandidate_ne_one, hdivMod]
  simp [hmul]

end Hex
