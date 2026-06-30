/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBasic
import HexBerlekamp.Factor
import HexBerlekamp.Irreducibility
import HexBerlekamp.RabinSoundness

/-!
Executable distinct-degree factorization surface for `hex-berlekamp`.

For a monic square-free input `f`, the executable loop computes the successive
gcds with `X^(p^d) - X mod f`.  Each non-unit gcd is recorded as the degree-`d`
bucket, and removed from the residual polynomial before the next degree is
tested.
-/
namespace Hex

namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p]

/-- One distinct-degree bucket: the product of factors of the recorded degree. -/
structure DegreeBucket (p : Nat) [ZMod64.Bounds p] where
  degree : Nat
  factor : FpPoly p

/--
Public result of executable distinct-degree factorization.  `residual` is kept
explicit so downstream callers can inspect any part not separated by the
bounded executable pass.
-/
structure DistinctDegreeFactorization (p : Nat) [ZMod64.Bounds p] where
  input : FpPoly p
  buckets : List (DegreeBucket p)
  residual : FpPoly p

/-- Extract the polynomial factors recorded in distinct-degree buckets. -/
def degreeBucketFactors (buckets : List (DegreeBucket p)) : List (FpPoly p) :=
  buckets.map DegreeBucket.factor

/-- `degreeBucketFactors` of the empty bucket list is the empty factor list.
Definitional rewrite (`by rfl`) characterising `degreeBucketFactors`. -/
@[simp, grind =] theorem degreeBucketFactors_nil :
    degreeBucketFactors ([] : List (DegreeBucket p)) = [] := by
  rfl

/-- `degreeBucketFactors` distributes over `::`, pulling the head bucket's
`.factor` to the front of the recovered factor list. Definitional rewrite
(`by rfl`) characterising `degreeBucketFactors`. -/
@[simp, grind =] theorem degreeBucketFactors_cons
    (bucket : DegreeBucket p) (buckets : List (DegreeBucket p)) :
    degreeBucketFactors (bucket :: buckets) =
      bucket.factor :: degreeBucketFactors buckets := by
  rfl

/-- `degreeBucketFactors` distributes over `++`: the factors of a concatenated
bucket list are the concatenation of each part's factors. -/
@[simp, grind =] theorem degreeBucketFactors_append
    (buckets₁ buckets₂ : List (DegreeBucket p)) :
    degreeBucketFactors (buckets₁ ++ buckets₂) =
      degreeBucketFactors buckets₁ ++ degreeBucketFactors buckets₂ := by
  simp [degreeBucketFactors]

/-- Multiply the polynomial factors recorded in distinct-degree buckets. -/
def degreeBucketProduct (buckets : List (DegreeBucket p)) : FpPoly p :=
  factorProduct (degreeBucketFactors buckets)

/-- The product over the empty bucket list is `1`. Definitional rewrite
(`by rfl`) characterising `degreeBucketProduct`. -/
@[simp, grind =] theorem degreeBucketProduct_nil :
    degreeBucketProduct ([] : List (DegreeBucket p)) = 1 := by
  rfl

/-- Product represented by a distinct-degree factorization result. -/
def DistinctDegreeFactorization.product (result : DistinctDegreeFactorization p) :
    FpPoly p :=
  degreeBucketProduct result.buckets * result.residual

/-- Unfold `DistinctDegreeFactorization.product` to the product of the bucket
factors times the residual. Definitional rewrite (`by rfl`) characterising
`DistinctDegreeFactorization.product`. -/
@[simp, grind =] theorem DistinctDegreeFactorization.product_eq
    (result : DistinctDegreeFactorization p) :
    result.product = degreeBucketProduct result.buckets * result.residual := by
  rfl

/-- The degree-`d` gcd candidate against the current residual polynomial. -/
def distinctDegreeCandidate
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (residual : FpPoly p) (d : Nat) : FpPoly p :=
  DensePoly.gcd residual (frobeniusDiffMod f hmonic d)

/-- One executable DDF step, returning an optional newly found bucket. -/
def distinctDegreeStep
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (residual : FpPoly p) (d : Nat) :
    Option (DegreeBucket p) × FpPoly p :=
  let candidate := distinctDegreeCandidate f hmonic residual d
  if isUnitPolynomial candidate then
    (none, residual)
  else
    (some { degree := d, factor := candidate }, residual / candidate)

/-- Append an optional bucket while preserving the existing bucket order. -/
private def appendBucket? (buckets : List (DegreeBucket p)) :
    Option (DegreeBucket p) → List (DegreeBucket p)
  | none => buckets
  | some bucket => buckets ++ [bucket]

/-- Finalize one degree extraction, absorbing scalar-unit residuals into the
recorded bucket so strict conformance fixtures end with residual `1`. -/
private def finishDegreePower (d : Nat) (residual acc : FpPoly p) :
    Option (DegreeBucket p) × FpPoly p :=
  if isUnitPolynomial acc then
    (none, residual)
  else if isUnitPolynomial residual then
    (some { degree := d, factor := acc * residual }, 1)
  else
    (some { degree := d, factor := acc }, residual)

/--
Repeat one degree test against the current residual, multiplying every
non-unit gcd into the same degree bucket before the outer loop advances.

For square-free inputs this records at most one factor.  For repeated-factor
inputs it preserves FLINT-style bucket multiplicities: if a degree-`d`
irreducible factor appears several times, every copy is stripped while the
same Frobenius difference is active.
-/
private def distinctDegreePowerLoop (d : Nat) (diff : FpPoly p) :
    Nat → FpPoly p → FpPoly p → Option (DegreeBucket p) × FpPoly p
  | 0, residual, acc =>
      finishDegreePower d residual acc
  | fuel + 1, residual, acc =>
      if residual.isZero then
        finishDegreePower d residual acc
      else
        let candidate := DensePoly.gcd residual diff
        if isUnitPolynomial candidate then
          finishDegreePower d residual acc
        else
          distinctDegreePowerLoop d diff fuel (residual / candidate) (acc * candidate)

/--
Fuel-bounded distinct-degree loop that maintains `currentFrob = X^(p^d) mod f`
iteratively across degrees. Each step computes the next Frobenius power as
`currentFrob^p mod f`, costing `O(log p)` polynomial multiplications rather
than the `O(d)` of `powModMonic X f hmonic (p^d)` from scratch.
-/
private def distinctDegreeLoop
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (xMod : FpPoly p) :
    Nat → Nat → FpPoly p → FpPoly p → List (DegreeBucket p) →
        List (DegreeBucket p) × FpPoly p
  | 0, _, _, residual, buckets => (buckets, residual)
  | fuel + 1, d, currentFrob, residual, buckets =>
      if residual.isZero then
        (buckets, residual)
      else
        let diff := currentFrob - xMod
        let (newBucket, newResidual) :=
          distinctDegreePowerLoop d diff (residual.size + 1) residual 1
        let nextFrob := FpPoly.powModMonic currentFrob f hmonic p
        distinctDegreeLoop f hmonic xMod fuel (d + 1) nextFrob newResidual
          (appendBucket? buckets newBucket)

/--
Compute the distinct-degree factorization surface of a monic polynomial over
`F_p`.
-/
def distinctDegreeFactor
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    DistinctDegreeFactorization p :=
  let xMod := FpPoly.modByMonic f FpPoly.X hmonic
  let frobX := FpPoly.frobeniusXMod f hmonic
  let result := distinctDegreeLoop f hmonic xMod (basisSize f + 1) 1 frobX f []
  { input := f
    buckets := result.1
    residual := result.2 }

/--
Predicate used by the SPEC-facing bucket invariant theorem: the recorded
factor divides the corresponding `X^(p^d) - X mod f`. The unnormalised
executable `DensePoly.gcd` does not return `bucket.factor` literally on the
left of `gcd bucket.factor (frobeniusDiffMod ...) = bucket.factor` (e.g.
`gcd X (2*X) = 2*X` over `F_3`), so the morally-correct invariant is the
divisibility statement that `gcd_dvd_right` already supplies.
-/
def DegreeBucket.matchesFrobeniusDegree
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (bucket : DegreeBucket p) : Prop :=
  bucket.factor ∣ frobeniusDiffMod f hmonic bucket.degree

/-- Restate `DegreeBucket.matchesFrobeniusDegree` as the divisibility
`bucket.factor ∣ frobeniusDiffMod f hmonic bucket.degree`, the morally-correct
bucket invariant. Definitional rewrite (`by rfl`). -/
theorem DegreeBucket.matchesFrobeniusDegree_iff
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (bucket : DegreeBucket p) :
    bucket.matchesFrobeniusDegree f hmonic ↔
      bucket.factor ∣ frobeniusDiffMod f hmonic bucket.degree := by
  rfl

/-- The degree-`d` candidate unfolds to `DensePoly.gcd residual
(frobeniusDiffMod f hmonic d)`. Definitional rewrite (`by rfl`) characterising
`distinctDegreeCandidate`. -/
theorem distinctDegreeCandidate_spec
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (residual : FpPoly p) (d : Nat) :
    distinctDegreeCandidate f hmonic residual d =
      DensePoly.gcd residual (frobeniusDiffMod f hmonic d) := by
  rfl

/-- `1 * a = a`: left identity for `FpPoly` multiplication, from commutativity
and the right unit law. -/
private theorem one_mul_poly
    [ZMod64.PrimeModulus p]
    (a : FpPoly p) :
    (1 : FpPoly p) * a = a :=
  (DensePoly.mul_comm_poly (1 : FpPoly p) a).trans (DensePoly.mul_one_right_poly a)

/-- `factorProduct` of a cons is the head times the `factorProduct` of the
tail. -/
private theorem factorProduct_cons_eq
    [ZMod64.PrimeModulus p]
    (x : FpPoly p) (xs : List (FpPoly p)) :
    factorProduct (x :: xs) = x * factorProduct xs := by
  show xs.foldl (fun acc factor => acc * factor) (1 * x)
    = x * xs.foldl (fun acc factor => acc * factor) 1
  rw [one_mul_poly x]
  exact List.foldl_mul_eq_mul_foldl xs id x

/-- `factorProduct` distributes over list append. -/
private theorem factorProduct_append
    [ZMod64.PrimeModulus p]
    (xs ys : List (FpPoly p)) :
    factorProduct (xs ++ ys) = factorProduct xs * factorProduct ys := by
  induction xs with
  | nil =>
      simp [factorProduct]
  | cons x xs ih =>
      rw [List.cons_append, factorProduct_cons_eq, factorProduct_cons_eq, ih]
      exact (DensePoly.mul_assoc_poly x (factorProduct xs) (factorProduct ys)).symm

/-- Bucket products distribute over list append in stored bucket order. -/
theorem degreeBucketProduct_append
    [ZMod64.PrimeModulus p]
    (buckets₁ buckets₂ : List (DegreeBucket p)) :
    degreeBucketProduct (buckets₁ ++ buckets₂) =
      degreeBucketProduct buckets₁ * degreeBucketProduct buckets₂ := by
  simp [degreeBucketProduct, degreeBucketFactors_append, factorProduct_append]

/-- The product of a singleton bucket list is its recorded factor. -/
@[simp, grind =] theorem degreeBucketProduct_singleton
    [ZMod64.PrimeModulus p]
    (bucket : DegreeBucket p) :
    degreeBucketProduct [bucket] = bucket.factor := by
  simp [degreeBucketProduct, degreeBucketFactors, factorProduct]

/-- Pull the first bucket factor out of a bucket product. -/
@[simp, grind =] theorem degreeBucketProduct_cons
    [ZMod64.PrimeModulus p]
    (bucket : DegreeBucket p) (buckets : List (DegreeBucket p)) :
    degreeBucketProduct (bucket :: buckets) =
      bucket.factor * degreeBucketProduct buckets := by
  rw [show bucket :: buckets = [bucket] ++ buckets from rfl,
    degreeBucketProduct_append, degreeBucketProduct_singleton]

/-- Appending no bucket (`none`) leaves the bucket product unchanged. -/
private theorem degreeBucketProduct_appendBucket?_none
    (buckets : List (DegreeBucket p)) :
    degreeBucketProduct (appendBucket? buckets none) = degreeBucketProduct buckets := by
  rfl

/-- Appending `some bucket` multiplies the bucket product on the right by that
bucket's recorded factor. -/
private theorem degreeBucketProduct_appendBucket?_some
    [ZMod64.PrimeModulus p]
    (buckets : List (DegreeBucket p)) (bucket : DegreeBucket p) :
    degreeBucketProduct (appendBucket? buckets (some bucket)) =
      degreeBucketProduct buckets * bucket.factor := by
  rw [appendBucket?, degreeBucketProduct_append, degreeBucketProduct_singleton]

/-- The factor contributed by an optional bucket: `1` for `none`, the recorded
factor for `some bucket`. -/
private def optionalBucketProduct : Option (DegreeBucket p) → FpPoly p
  | none => 1
  | some bucket => bucket.factor

/-- Appending an optional bucket multiplies the bucket product on the right by
`optionalBucketProduct`, unifying the `none` and `some` cases. -/
private theorem degreeBucketProduct_appendBucket?
    [ZMod64.PrimeModulus p]
    (buckets : List (DegreeBucket p)) (bucket? : Option (DegreeBucket p)) :
    degreeBucketProduct (appendBucket? buckets bucket?) =
      degreeBucketProduct buckets * optionalBucketProduct bucket? := by
  cases bucket? with
  | none =>
      rw [degreeBucketProduct_appendBucket?_none]
      exact (DensePoly.mul_one_right_poly (degreeBucketProduct buckets)).symm
  | some bucket =>
      exact degreeBucketProduct_appendBucket?_some buckets bucket

/-- `gcd residual diff * (residual / gcd residual diff) = residual`: the gcd
divides `residual`, so multiplying the quotient back recovers it. -/
private theorem gcd_mul_div_eq
    [ZMod64.PrimeModulus p]
    (residual diff : FpPoly p) :
    DensePoly.gcd residual diff * (residual / DensePoly.gcd residual diff) = residual := by
  have hspec := DensePoly.div_mul_add_mod residual (DensePoly.gcd residual diff)
  have hmod :
      residual % DensePoly.gcd residual diff = 0 := by
    exact DensePoly.mod_eq_zero_of_dvd residual
      (DensePoly.gcd residual diff)
      (DensePoly.gcd_dvd_left residual diff)
  rw [hmod] at hspec
  exact (DensePoly.mul_comm_poly (DensePoly.gcd residual diff)
      (residual / DensePoly.gcd residual diff)).trans
    ((DensePoly.add_zero_poly
      ((residual / DensePoly.gcd residual diff) *
        DensePoly.gcd residual diff)).symm.trans hspec)

/-- The degree-`d` candidate divides `residual`: candidate times
`residual / candidate` recovers `residual`. -/
private theorem distinctDegreeCandidate_mul_div_eq
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (residual : FpPoly p) (d : Nat) :
    distinctDegreeCandidate f hmonic residual d *
        (residual / distinctDegreeCandidate f hmonic residual d) = residual := by
  rw [distinctDegreeCandidate_spec]
  exact gcd_mul_div_eq residual (frobeniusDiffMod f hmonic d)

/-- A product with a non-unit right factor is non-unit, since any divisor of a
unit is a unit. -/
private theorem isUnitPolynomial_mul_eq_false_of_right
    [ZMod64.PrimeModulus p]
    (a b : FpPoly p) (hb : isUnitPolynomial b = false) :
    isUnitPolynomial (a * b) = false := by
  cases hprod : isUnitPolynomial (a * b) with
  | false => rfl
  | true =>
      have hbUnit : isUnitPolynomial b = true :=
        isUnitPolynomial_of_dvd_isUnitPolynomial
          (g := b) (h := a * b) ⟨a, DensePoly.mul_comm_poly a b⟩ hprod
      rw [hbUnit] at hb
      simp at hb

/-- `finishDegreePower` preserves the running product when `acc` is non-unit:
the emitted bucket factor times the returned residual equals `acc * residual`. -/
private theorem finishDegreePower_product_nonunit
    [ZMod64.PrimeModulus p]
    (d : Nat) (residual acc : FpPoly p)
    (hacc : isUnitPolynomial acc = false) :
    let result := finishDegreePower (p := p) d residual acc
    optionalBucketProduct result.1 * result.2 = acc * residual := by
  unfold finishDegreePower
  rw [hacc]
  cases isUnitPolynomial residual <;> simp [optionalBucketProduct]

/-- `1 ≠ 0` in `ZMod64 p` for a prime modulus, since `p ≥ 2` makes
`1 % p = 1`. -/
private theorem zmod_one_ne_zero_local
    [ZMod64.PrimeModulus p] :
    (1 : ZMod64 p) ≠ 0 := by
  intro h
  have htoNat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat :=
    congrArg ZMod64.toNat h
  rw [show ((1 : ZMod64 p).toNat) = 1 % p from ZMod64.toNat_one,
      show ((0 : ZMod64 p).toNat) = 0 from ZMod64.toNat_zero,
      Nat.mod_eq_of_lt (by
        have h2 : 2 ≤ p := (ZMod64.PrimeModulus.prime (p := p)).two_le
        omega : 1 < p)] at htoNat
  exact absurd htoNat (by omega)

/-- The constant polynomial `1` is a unit (degree `0`). -/
private theorem isUnitPolynomial_one
    [ZMod64.PrimeModulus p] :
    isUnitPolynomial (1 : FpPoly p) = true := by
  unfold isUnitPolynomial
  change (match DensePoly.degree? (DensePoly.C (1 : ZMod64 p)) with
    | some 0 => true
    | _ => false) = true
  have hcoeffs : (DensePoly.C (1 : ZMod64 p)).coeffs = #[(1 : ZMod64 p)] :=
    DensePoly.coeffs_C_of_ne_zero zmod_one_ne_zero_local
  simp [DensePoly.degree?, DensePoly.size, hcoeffs]

/-- `finishDegreePower` from unit accumulator `1` preserves `residual`: the
emitted bucket factor times the returned residual equals `residual`. -/
private theorem finishDegreePower_product_one
    [ZMod64.PrimeModulus p]
    (d : Nat) (residual : FpPoly p) :
    let result := finishDegreePower (p := p) d residual 1
    optionalBucketProduct result.1 * result.2 = residual := by
  unfold finishDegreePower
  rw [isUnitPolynomial_one]
  simp [optionalBucketProduct]

/-- `distinctDegreePowerLoop` preserves the running product `acc * residual` for
non-unit `acc` across all fuel steps. -/
private theorem distinctDegreePowerLoop_product_nonunit
    [ZMod64.PrimeModulus p]
    (d : Nat) (diff : FpPoly p) (fuel : Nat) (residual acc : FpPoly p)
    (hacc : isUnitPolynomial acc = false) :
    let result := distinctDegreePowerLoop (p := p) d diff fuel residual acc
    optionalBucketProduct result.1 * result.2 = acc * residual := by
  induction fuel generalizing residual acc with
  | zero =>
      exact finishDegreePower_product_nonunit d residual acc hacc
  | succ fuel ih =>
      unfold distinctDegreePowerLoop
      by_cases hzero : residual.isZero
      · simp [hzero, finishDegreePower_product_nonunit d residual acc hacc]
      · simp [hzero]
        cases hcand : isUnitPolynomial (DensePoly.gcd residual diff) with
        | true =>
          simp [finishDegreePower_product_nonunit d residual acc hacc]
        | false =>
          have hcandFalse : isUnitPolynomial (DensePoly.gcd residual diff) = false := hcand
          simp
          have hmul :
              isUnitPolynomial (acc * DensePoly.gcd residual diff) = false :=
            isUnitPolynomial_mul_eq_false_of_right acc (DensePoly.gcd residual diff) hcandFalse
          have hrec := ih (residual / DensePoly.gcd residual diff)
            (acc * DensePoly.gcd residual diff) hmul
          calc
            optionalBucketProduct
                  (distinctDegreePowerLoop d diff fuel
                    (residual / DensePoly.gcd residual diff)
                    (acc * DensePoly.gcd residual diff)).1 *
                (distinctDegreePowerLoop d diff fuel
                    (residual / DensePoly.gcd residual diff)
                    (acc * DensePoly.gcd residual diff)).2
                = (acc * DensePoly.gcd residual diff) *
                    (residual / DensePoly.gcd residual diff) := hrec
            _ = acc * residual := by
              calc
                (acc * DensePoly.gcd residual diff) *
                    (residual / DensePoly.gcd residual diff)
                    = acc * (DensePoly.gcd residual diff *
                        (residual / DensePoly.gcd residual diff)) := by
                      exact DensePoly.mul_assoc_poly acc (DensePoly.gcd residual diff)
                        (residual / DensePoly.gcd residual diff)
                _ = acc * residual := by
                      exact congrArg (fun x => acc * x) (gcd_mul_div_eq residual diff)

/-- `distinctDegreePowerLoop` from unit accumulator `1` preserves `residual`
across all fuel steps. -/
private theorem distinctDegreePowerLoop_product_one
    [ZMod64.PrimeModulus p]
    (d : Nat) (diff : FpPoly p) (fuel : Nat) (residual : FpPoly p) :
    let result := distinctDegreePowerLoop (p := p) d diff fuel residual 1
    optionalBucketProduct result.1 * result.2 = residual := by
  induction fuel generalizing residual with
  | zero =>
      exact finishDegreePower_product_one d residual
  | succ fuel ih =>
      unfold distinctDegreePowerLoop
      by_cases hzero : residual.isZero
      · simp [hzero, finishDegreePower_product_one d residual]
      · simp [hzero]
        cases hcand : isUnitPolynomial (DensePoly.gcd residual diff) with
        | true =>
          simp [finishDegreePower_product_one d residual]
        | false =>
          have hcandFalse : isUnitPolynomial (DensePoly.gcd residual diff) = false := hcand
          simp
          have hrec := distinctDegreePowerLoop_product_nonunit d diff fuel
            (residual / DensePoly.gcd residual diff)
            (DensePoly.gcd residual diff)
          calc
            optionalBucketProduct
                  (distinctDegreePowerLoop d diff fuel
                    (residual / DensePoly.gcd residual diff)
                    (DensePoly.gcd residual diff)).1 *
                (distinctDegreePowerLoop d diff fuel
                    (residual / DensePoly.gcd residual diff)
                    (DensePoly.gcd residual diff)).2
                = DensePoly.gcd residual diff *
                    (residual / DensePoly.gcd residual diff) := hrec hcandFalse
            _ = residual := by
              exact gcd_mul_div_eq residual diff

/-- `distinctDegreeLoop` preserves the global product
`degreeBucketProduct buckets * residual`: the accumulated bucket product times
the final residual equals the starting product. -/
private theorem distinctDegreeLoop_product_eq
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (xMod : FpPoly p)
    (fuel d : Nat) (currentFrob residual : FpPoly p)
    (buckets : List (DegreeBucket p)) :
    let result := distinctDegreeLoop f hmonic xMod fuel d currentFrob residual buckets
    degreeBucketProduct result.1 * result.2 =
      degreeBucketProduct buckets * residual := by
  induction fuel generalizing d currentFrob residual buckets with
  | zero => rfl
  | succ fuel ih =>
      unfold distinctDegreeLoop
      by_cases hzero : residual.isZero
      · simp [hzero]
      · simp [hzero]
        let powerResult :=
          distinctDegreePowerLoop d (currentFrob - xMod) (residual.size + 1) residual 1
        have hpower :
            optionalBucketProduct powerResult.1 * powerResult.2 = residual :=
          distinctDegreePowerLoop_product_one d (currentFrob - xMod)
            (residual.size + 1) residual
        have hstep :
            degreeBucketProduct (appendBucket? buckets powerResult.1) * powerResult.2 =
              degreeBucketProduct buckets * residual := by
          rw [degreeBucketProduct_appendBucket?]
          calc
            (degreeBucketProduct buckets * optionalBucketProduct powerResult.1) *
                powerResult.2
                = degreeBucketProduct buckets *
                    (optionalBucketProduct powerResult.1 * powerResult.2) := by
                  exact DensePoly.mul_assoc_poly
                    (degreeBucketProduct buckets) (optionalBucketProduct powerResult.1)
                    powerResult.2
            _ = degreeBucketProduct buckets * residual := by
                  rw [hpower]
        have htail := ih (d + 1) (FpPoly.powModMonic currentFrob f hmonic p)
          powerResult.2 (appendBucket? buckets powerResult.1)
        exact htail.trans hstep

/-- One `distinctDegreeLoop` step advances the cached Frobenius state from
`frobeniusXPowMod f hmonic d` to degree `d + 1`. -/
private theorem distinctDegreeLoop_frobenius_state_step
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (d : Nat) (currentFrob : FpPoly p)
    (hstate : currentFrob = FpPoly.frobeniusXPowMod f hmonic d) :
    FpPoly.powModMonic currentFrob f hmonic p =
      FpPoly.frobeniusXPowMod f hmonic (d + 1) := by
  rw [hstate]
  exact (FpPoly.frobeniusXPowMod_succ f hmonic d).symm

/-- Any bucket emitted by `finishDegreePower` at degree `d` records degree
`d`. -/
private theorem finishDegreePower_bucket_degree
    (d : Nat) (residual acc : FpPoly p) :
    ∀ bucket : DegreeBucket p,
      (finishDegreePower (p := p) d residual acc).1 = some bucket →
        bucket.degree = d := by
  intro bucket hbucket
  unfold finishDegreePower at hbucket
  cases hacc : isUnitPolynomial acc <;> simp [hacc] at hbucket
  cases hres : isUnitPolynomial residual <;> simp [hres] at hbucket
  · cases hbucket
    rfl
  · cases hbucket
    rfl

/-- Any bucket emitted by `distinctDegreePowerLoop` at degree `d` records degree
`d`. -/
private theorem distinctDegreePowerLoop_bucket_degree
    (d : Nat) (diff : FpPoly p) (fuel : Nat) (residual acc : FpPoly p) :
    ∀ bucket : DegreeBucket p,
      (distinctDegreePowerLoop (p := p) d diff fuel residual acc).1 = some bucket →
        bucket.degree = d := by
  induction fuel generalizing residual acc with
  | zero =>
      exact finishDegreePower_bucket_degree d residual acc
  | succ fuel ih =>
      intro bucket hbucket
      unfold distinctDegreePowerLoop at hbucket
      by_cases hzero : residual.isZero
      · simp [hzero] at hbucket
        exact finishDegreePower_bucket_degree d residual acc bucket hbucket
      · simp [hzero] at hbucket
        cases hcand : isUnitPolynomial (DensePoly.gcd residual diff) with
        | true =>
            simp [hcand] at hbucket
            exact finishDegreePower_bucket_degree d residual acc bucket hbucket
        | false =>
            simp [hcand] at hbucket
            exact ih (residual / DensePoly.gcd residual diff)
              (acc * DensePoly.gcd residual diff) bucket hbucket

/-!
### Same-degree extraction divisibility

`finishDegreePower` and `distinctDegreePowerLoop` both emit at most one bucket
recording the accumulated product of repeated same-degree gcds against the
fixed Frobenius difference `diff`.  After the first iteration the bucket
factor is no longer literally `gcd residual diff`, so divisibility by `diff`
needs more than `DensePoly.gcd_dvd_right`: it follows from a step-preserved
invariant on `(residual, acc)` whose construction (the square-free /
multiplicity content) is delegated to the caller.

`finishDegreePower_bucket_dvd_diff` covers all three exit cases of
`finishDegreePower` — including the scalar-unit residual case where the
emitted factor is `acc * residual`.

`distinctDegreePowerLoop_bucket_dvd_diff` threads an abstract
step-preserving predicate `P : FpPoly → FpPoly → Prop` through induction
on the fuel.  Concrete instantiations (e.g. "`acc ∣ diff` together with a
square-free residual coprime to `acc`") feed the divisibility, the unit
finish case, and the gcd-extraction step into the three hypotheses
`hP_acc_dvd`, `hP_finish_unit`, and `hP_step`.
-/

private theorem finishDegreePower_bucket_dvd_diff
    (d : Nat) (diff residual acc : FpPoly p)
    (hacc : acc ∣ diff)
    (hunit : isUnitPolynomial residual = true → acc * residual ∣ diff) :
    ∀ bucket : DegreeBucket p,
      (finishDegreePower (p := p) d residual acc).1 = some bucket →
        bucket.factor ∣ diff := by
  intro bucket hbucket
  unfold finishDegreePower at hbucket
  cases hacc_unit : isUnitPolynomial acc <;> simp [hacc_unit] at hbucket
  cases hres_unit : isUnitPolynomial residual <;> simp [hres_unit] at hbucket
  · cases hbucket
    exact hacc
  · cases hbucket
    exact hunit hres_unit

/-- `distinctDegreePowerLoop_bucket_dvd_diff`: under an invariant `P` carried
from the accumulator through the gcd-extraction step, every bucket the loop
emits has a factor dividing `diff`. -/
private theorem distinctDegreePowerLoop_bucket_dvd_diff
    (d : Nat) (diff : FpPoly p)
    (P : FpPoly p → FpPoly p → Prop)
    (hP_acc_dvd : ∀ r a, P r a → a ∣ diff)
    (hP_finish_unit : ∀ r a, P r a → isUnitPolynomial r = true → a * r ∣ diff)
    (hP_step : ∀ r a, P r a →
        isUnitPolynomial (DensePoly.gcd r diff) = false →
        P (r / DensePoly.gcd r diff) (a * DensePoly.gcd r diff)) :
    ∀ (fuel : Nat) (residual acc : FpPoly p), P residual acc →
      ∀ bucket : DegreeBucket p,
        (distinctDegreePowerLoop (p := p) d diff fuel residual acc).1 = some bucket →
          bucket.factor ∣ diff := by
  intro fuel
  induction fuel with
  | zero =>
      intro residual acc hP bucket hbucket
      exact finishDegreePower_bucket_dvd_diff d diff residual acc
        (hP_acc_dvd residual acc hP)
        (fun hu => hP_finish_unit residual acc hP hu) bucket hbucket
  | succ fuel ih =>
      intro residual acc hP bucket hbucket
      unfold distinctDegreePowerLoop at hbucket
      by_cases hzero : residual.isZero
      · simp [hzero] at hbucket
        exact finishDegreePower_bucket_dvd_diff d diff residual acc
          (hP_acc_dvd residual acc hP)
          (fun hu => hP_finish_unit residual acc hP hu) bucket hbucket
      · simp [hzero] at hbucket
        cases hcand : isUnitPolynomial (DensePoly.gcd residual diff) with
        | true =>
            simp [hcand] at hbucket
            exact finishDegreePower_bucket_dvd_diff d diff residual acc
              (hP_acc_dvd residual acc hP)
              (fun hu => hP_finish_unit residual acc hP hu) bucket hbucket
        | false =>
            simp [hcand] at hbucket
            exact ih (residual / DensePoly.gcd residual diff)
              (acc * DensePoly.gcd residual diff)
              (hP_step residual acc hP hcand) bucket hbucket

/-- `unitPolynomial_dvd_any`: a unit (degree-zero, nonzero) polynomial divides
any polynomial. -/
private theorem unitPolynomial_dvd_any
    [ZMod64.PrimeModulus p]
    {u target : FpPoly p} (hu : isUnitPolynomial u = true) :
    u ∣ target := by
  have hu_degree : ¬ 0 < u.degree?.getD 0 := by
    intro hpos
    unfold isUnitPolynomial at hu
    cases hdeg : u.degree? with
    | none =>
        rw [hdeg] at hu
        simp at hu
    | some k =>
        rw [hdeg] at hu
        cases k with
        | zero =>
            rw [hdeg] at hpos
            simp at hpos
        | succ _ => simp at hu
  have hu_deg : u.degree? = some 0 := by
    unfold isUnitPolynomial at hu
    cases hdeg : u.degree? with
    | none =>
        rw [hdeg] at hu
        simp at hu
    | some k =>
        rw [hdeg] at hu
        cases k with
        | zero => rfl
        | succ _ => simp at hu
  have hu_size_ne_zero : u.size ≠ 0 := by
    intro hsize
    unfold DensePoly.degree? at hu_deg
    simp [hsize] at hu_deg
  have hu_size : u.size = 1 := by
    unfold DensePoly.degree? at hu_deg
    simp [hu_size_ne_zero] at hu_deg
    omega
  have hmod : target % u = 0 := by
    show (DensePoly.divMod target u).2 = 0
    apply DensePoly.divMod_remainder_eq_zero_of_degree_zero_core
    · exact hu_size
    · intro a
      have hpos : 0 < u.size := by omega
      have hidx : u.coeffs.size - 1 < u.coeffs.size := by
        simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hpos
      have hlead_eq : u.leadingCoeff = u.coeff (u.size - 1) := by
        unfold DensePoly.leadingCoeff DensePoly.coeff
        change u.coeffs.back?.getD (0 : ZMod64 p) =
          u.coeffs.getD (u.coeffs.size - 1) (Zero.zero : ZMod64 p)
        rw [Array.back?_eq_getElem?, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_getElem hidx]
        rfl
      have hlead_ne : u.leadingCoeff ≠ (Zero.zero : ZMod64 p) := by
        rw [hlead_eq]
        exact DensePoly.coeff_last_ne_zero_of_pos_size u hpos
      have hinv : ZMod64.inv u.leadingCoeff * u.leadingCoeff = (1 : ZMod64 p) :=
        ZMod64.inv_mul_eq_one_of_prime (ZMod64.PrimeModulus.prime (p := p)) hlead_ne
      have hmul : (a / u.leadingCoeff) * u.leadingCoeff = a := by
        change (ZMod64.mul a (ZMod64.inv u.leadingCoeff)) * u.leadingCoeff = a
        calc
          (ZMod64.mul a (ZMod64.inv u.leadingCoeff)) * u.leadingCoeff
              = a * (ZMod64.inv u.leadingCoeff * u.leadingCoeff) := by
                  exact Lean.Grind.Semiring.mul_assoc a (ZMod64.inv u.leadingCoeff)
                    u.leadingCoeff
          _ = a * (1 : ZMod64 p) := by rw [hinv]
          _ = a := Lean.Grind.Semiring.mul_one a
      change a - (a / u.leadingCoeff) * u.leadingCoeff = (Zero.zero : ZMod64 p)
      rw [hmul]
      change ZMod64.sub a a = (Zero.zero : ZMod64 p)
      apply ZMod64.ext
      apply UInt64.toNat_inj.mp
      change (ZMod64.sub a a).toNat = (Zero.zero : ZMod64 p).toNat
      rw [ZMod64.toNat_sub]
      have hsum : a.toNat + (p - a.toNat) = p := by
        have ha : a.toNat < p := a.toNat_lt
        omega
      rw [hsum, Nat.mod_self]
      exact ZMod64.toNat_zero.symm
  refine ⟨target / u, ?_⟩
  have hspec := DensePoly.div_mul_add_mod target u
  rw [hmod] at hspec
  exact ((DensePoly.mul_comm_poly u (target / u)).trans
    ((DensePoly.add_zero_poly ((target / u) * u)).symm.trans hspec)).symm

/-- `one_dvd_poly`: the constant `1` divides any polynomial. -/
private theorem one_dvd_poly
    [ZMod64.PrimeModulus p]
    (target : FpPoly p) :
    (1 : FpPoly p) ∣ target := by
  exact unitPolynomial_dvd_any (u := (1 : FpPoly p)) (target := target)
    isUnitPolynomial_one

/-- `mul_right_unit_dvd_of_dvd`: multiplying a divisor on the right by a unit
preserves divisibility. -/
private theorem mul_right_unit_dvd_of_dvd
    [ZMod64.PrimeModulus p]
    {a u target : FpPoly p}
    (ha : a ∣ target) (hu : isUnitPolynomial u = true) :
    a * u ∣ target := by
  rcases ha with ⟨q, hq⟩
  rcases unitPolynomial_dvd_any (u := u) (target := q) hu with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc target
      = a * q := hq
    _ = a * (u * k) := by rw [hk]
    _ = (a * u) * k := (DensePoly.mul_assoc_poly a u k).symm

/-- `dvd_trans_poly`: divisibility of `FpPoly` is transitive. -/
private theorem dvd_trans_poly
    {a b c : FpPoly p} (hab : a ∣ b) (hbc : b ∣ c) :
    a ∣ c := by
  rcases hab with ⟨x, hx⟩
  rcases hbc with ⟨y, hy⟩
  refine ⟨x * y, ?_⟩
  calc c
      = b * y := hy
    _ = (a * x) * y := by rw [hx]
    _ = a * (x * y) := DensePoly.mul_assoc_poly a x y

/-- `isUnitPolynomial_gcd_quotient_of_squareFree_divisor`: when `f` is square-free
and `r` divides `f`, the gcd of the gcd-quotient `r / gcd r d` with `d` is a
unit, so no factor is extracted twice. -/
private theorem isUnitPolynomial_gcd_quotient_of_squareFree_divisor
    [ZMod64.PrimeModulus p]
    {f r d : FpPoly p}
    (hsf : DensePoly.gcd f (DensePoly.derivative f) = 1)
    (hrf : r ∣ f) :
    isUnitPolynomial (DensePoly.gcd (r / DensePoly.gcd r d) d) = true := by
  have hc_dvd_r : DensePoly.gcd r d ∣ r := DensePoly.gcd_dvd_left r d
  have hr_eq : r = DensePoly.gcd r d * (r / DensePoly.gcd r d) := by
    have hmod : r % DensePoly.gcd r d = 0 :=
      DensePoly.mod_eq_zero_of_dvd r (DensePoly.gcd r d) hc_dvd_r
    have hspec := DensePoly.div_mul_add_mod r (DensePoly.gcd r d)
    rw [hmod] at hspec
    exact (hspec.symm.trans
      (DensePoly.add_zero_poly ((r / DensePoly.gcd r d) * DensePoly.gcd r d))).trans
      (DensePoly.mul_comm_poly (r / DensePoly.gcd r d) (DensePoly.gcd r d))
  have hg_dvd_quot :
      DensePoly.gcd (r / DensePoly.gcd r d) d ∣ r / DensePoly.gcd r d :=
    DensePoly.gcd_dvd_left _ _
  have hg_dvd_d :
      DensePoly.gcd (r / DensePoly.gcd r d) d ∣ d :=
    DensePoly.gcd_dvd_right _ _
  have hg_dvd_r :
      DensePoly.gcd (r / DensePoly.gcd r d) d ∣ r := by
    rcases hg_dvd_quot with ⟨a, ha⟩
    refine ⟨DensePoly.gcd r d * a, ?_⟩
    calc r
        = DensePoly.gcd r d * (r / DensePoly.gcd r d) := hr_eq
      _ = DensePoly.gcd r d *
            (DensePoly.gcd (r / DensePoly.gcd r d) d * a) := by
          exact congrArg (DensePoly.gcd r d * ·) ha
      _ = DensePoly.gcd (r / DensePoly.gcd r d) d *
            (DensePoly.gcd r d * a) := by
          calc DensePoly.gcd r d *
                  (DensePoly.gcd (r / DensePoly.gcd r d) d * a)
              = (DensePoly.gcd r d *
                  DensePoly.gcd (r / DensePoly.gcd r d) d) * a :=
                    (DensePoly.mul_assoc_poly _ _ _).symm
            _ = (DensePoly.gcd (r / DensePoly.gcd r d) d *
                  DensePoly.gcd r d) * a := by
                    exact congrArg (· * a) (DensePoly.mul_comm_poly _ _)
            _ = DensePoly.gcd (r / DensePoly.gcd r d) d *
                  (DensePoly.gcd r d * a) :=
                    DensePoly.mul_assoc_poly _ _ _
  have hg_dvd_c :
      DensePoly.gcd (r / DensePoly.gcd r d) d ∣ DensePoly.gcd r d :=
    DensePoly.dvd_gcd _ r d hg_dvd_r hg_dvd_d
  have hg2_dvd_r :
      DensePoly.gcd (r / DensePoly.gcd r d) d *
        DensePoly.gcd (r / DensePoly.gcd r d) d ∣ r := by
    rcases hg_dvd_c with ⟨e, he⟩
    rcases hg_dvd_quot with ⟨a, ha⟩
    refine ⟨e * a, ?_⟩
    let g := DensePoly.gcd (r / DensePoly.gcd r d) d
    have hpair : (DensePoly.gcd r d, r / DensePoly.gcd r d) = (g * e, g * a) :=
      Prod.ext he ha
    calc r
        = DensePoly.gcd r d * (r / DensePoly.gcd r d) := hr_eq
      _ = (g * e) * (g * a) := by
          exact congrArg (fun (xy : FpPoly p × FpPoly p) => xy.1 * xy.2) hpair
      _ = (g * g) * (e * a) := by
          calc (g * e) * (g * a)
              = g * (e * (g * a)) := DensePoly.mul_assoc_poly g e (g * a)
            _ = g * ((e * g) * a) := by
                exact congrArg (g * ·) (DensePoly.mul_assoc_poly e g a).symm
            _ = g * ((g * e) * a) := by
                exact congrArg (fun x => g * (x * a)) (DensePoly.mul_comm_poly e g)
            _ = g * (g * (e * a)) := by
                exact congrArg (g * ·) (DensePoly.mul_assoc_poly g e a)
            _ = (g * g) * (e * a) := (DensePoly.mul_assoc_poly g g (e * a)).symm
  exact isUnitPolynomial_of_squareFree_of_squared_dvd
    (squareFree_common_of_gcd_eq_one hsf)
    (dvd_trans_poly hg2_dvd_r hrf)

/-- `distinctDegreePowerLoop_bucket_dvd_diff_of_squareFree_divisor`: for a
square-free `f` with `residual ∣ f`, every bucket the loop emits has a factor
dividing `diff`. -/
private theorem distinctDegreePowerLoop_bucket_dvd_diff_of_squareFree_divisor
    [ZMod64.PrimeModulus p]
    (f : FpPoly p)
    (hsf : DensePoly.gcd f (DensePoly.derivative f) = 1)
    (d : Nat) (diff residual : FpPoly p)
    (hresidual : residual ∣ f) :
    ∀ bucket : DegreeBucket p,
      (distinctDegreePowerLoop (p := p) d diff (residual.size + 1) residual 1).1 =
        some bucket →
        bucket.factor ∣ diff := by
  let P : FpPoly p → FpPoly p → Prop :=
    fun r a =>
      (a = 1 ∧ r = residual) ∨
        (a ∣ diff ∧ isUnitPolynomial (DensePoly.gcd r diff) = true)
  apply distinctDegreePowerLoop_bucket_dvd_diff d diff P
  · intro r a hP
    rcases hP with hinit | hdone
    · rcases hinit with ⟨ha, _hr⟩
      rw [ha]
      exact one_dvd_poly diff
    · exact hdone.1
  · intro r a hP hunit
    rcases hP with hinit | hdone
    · rcases hinit with ⟨ha, _hr⟩
      rw [ha]
      exact unitPolynomial_dvd_any (u := (1 : FpPoly p) * r) (target := diff) (by
        rw [one_mul_poly r]
        exact hunit)
    · exact mul_right_unit_dvd_of_dvd hdone.1 hunit
  · intro r a hP hg_nonunit
    rcases hP with hinit | hdone
    · rcases hinit with ⟨ha, hr⟩
      right
      constructor
      · rw [ha, one_mul_poly]
        exact DensePoly.gcd_dvd_right r diff
      · rw [hr]
        simpa [one_mul_poly] using
          isUnitPolynomial_gcd_quotient_of_squareFree_divisor
            (f := f) (r := residual) (d := diff) hsf hresidual
    · rw [hdone.2] at hg_nonunit
      simp at hg_nonunit
  · left
    exact ⟨rfl, rfl⟩

/-- `distinctDegreePowerLoop_residual_dvd`: the residual returned by the loop
divides the residual it started from. -/
private theorem distinctDegreePowerLoop_residual_dvd
    [ZMod64.PrimeModulus p]
    (d : Nat) (diff : FpPoly p) (fuel : Nat) (residual : FpPoly p) :
    (distinctDegreePowerLoop (p := p) d diff fuel residual 1).2 ∣ residual := by
  have hproduct := distinctDegreePowerLoop_product_one d diff fuel residual
  refine ⟨optionalBucketProduct
      (distinctDegreePowerLoop (p := p) d diff fuel residual 1).1, ?_⟩
  exact ((DensePoly.mul_comm_poly
      (distinctDegreePowerLoop (p := p) d diff fuel residual 1).2
      (optionalBucketProduct
        (distinctDegreePowerLoop (p := p) d diff fuel residual 1).1)).trans
    hproduct).symm

private theorem appendBucket?_positive_degrees
    (buckets : List (DegreeBucket p)) (bucket? : Option (DegreeBucket p))
    (d : Nat)
    (hprev : ∀ bucket ∈ buckets, 0 < bucket.degree)
    (hnew : ∀ bucket : DegreeBucket p, bucket? = some bucket → bucket.degree = d)
    (hd : 0 < d) :
    ∀ bucket ∈ appendBucket? buckets bucket?, 0 < bucket.degree := by
  intro bucket hmem
  cases hbucket : bucket? with
  | none =>
      simp [appendBucket?, hbucket] at hmem
      exact hprev bucket hmem
  | some newBucket =>
      simp [appendBucket?, hbucket] at hmem
      rcases hmem with hmem | hmem
      · exact hprev bucket hmem
      · rcases hmem with rfl
        have hdeg : bucket.degree = d := hnew bucket (by simp [hbucket])
        rw [hdeg]
        exact hd

private theorem appendBucket?_matches
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (buckets : List (DegreeBucket p)) (bucket? : Option (DegreeBucket p))
    (hprev : ∀ bucket ∈ buckets, bucket.matchesFrobeniusDegree f hmonic)
    (hnew : ∀ bucket : DegreeBucket p, bucket? = some bucket →
      bucket.matchesFrobeniusDegree f hmonic) :
    ∀ bucket ∈ appendBucket? buckets bucket?,
      bucket.matchesFrobeniusDegree f hmonic := by
  intro bucket hmem
  cases hbucket : bucket? with
  | none =>
      simp [appendBucket?, hbucket] at hmem
      exact hprev bucket hmem
  | some newBucket =>
      simp [appendBucket?, hbucket] at hmem
      rcases hmem with hmem | hmem
      · exact hprev bucket hmem
      · rcases hmem with rfl
        exact hnew bucket (by simp [hbucket])

private theorem distinctDegreeLoop_bucket_positive_degrees
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (xMod : FpPoly p)
    (fuel d : Nat) (currentFrob residual : FpPoly p)
    (buckets : List (DegreeBucket p))
    (hd : 0 < d)
    (hprev : ∀ bucket ∈ buckets, 0 < bucket.degree) :
    ∀ bucket ∈ (distinctDegreeLoop f hmonic xMod fuel d currentFrob residual buckets).1,
      0 < bucket.degree := by
  induction fuel generalizing d currentFrob residual buckets with
  | zero =>
      intro bucket hmem
      exact hprev bucket hmem
  | succ fuel ih =>
      intro bucket hmem
      unfold distinctDegreeLoop at hmem
      by_cases hzero : residual.isZero
      · simp [hzero] at hmem
        exact hprev bucket hmem
      · simp [hzero] at hmem
        let powerResult :=
          distinctDegreePowerLoop d (currentFrob - xMod) (residual.size + 1) residual 1
        have happend :
            ∀ bucket ∈ appendBucket? buckets powerResult.1, 0 < bucket.degree := by
          apply appendBucket?_positive_degrees buckets powerResult.1 d hprev
          · intro newBucket hnew
            exact distinctDegreePowerLoop_bucket_degree d (currentFrob - xMod)
              (residual.size + 1) residual 1 newBucket hnew
          · exact hd
        exact ih (d + 1) (FpPoly.powModMonic currentFrob f hmonic p) powerResult.2
          (appendBucket? buckets powerResult.1) (by omega) happend bucket hmem

private theorem distinctDegreeFactor_bucket_positive_degrees
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    ∀ bucket ∈ (distinctDegreeFactor f hmonic).buckets, 0 < bucket.degree := by
  unfold distinctDegreeFactor
  let xMod := FpPoly.modByMonic f FpPoly.X hmonic
  let frobX := FpPoly.frobeniusXMod f hmonic
  exact distinctDegreeLoop_bucket_positive_degrees f hmonic xMod
    (basisSize f + 1) 1 frobX f [] (by omega) (by simp)

private theorem distinctDegreeLoop_bucket_matches
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (xMod : FpPoly p)
    (hsquareFree : DensePoly.gcd f (DensePoly.derivative f) = 1)
    (fuel d : Nat) (currentFrob residual : FpPoly p)
    (buckets : List (DegreeBucket p))
    (hxMod : xMod = FpPoly.modByMonic f FpPoly.X hmonic)
    (hstate : currentFrob = FpPoly.frobeniusXPowMod f hmonic d)
    (hresidual : residual ∣ f)
    (hprev : ∀ bucket ∈ buckets, bucket.matchesFrobeniusDegree f hmonic) :
    ∀ bucket ∈ (distinctDegreeLoop f hmonic xMod fuel d currentFrob residual buckets).1,
      bucket.matchesFrobeniusDegree f hmonic := by
  induction fuel generalizing d currentFrob residual buckets with
  | zero =>
      intro bucket hmem
      exact hprev bucket hmem
  | succ fuel ih =>
      intro bucket hmem
      unfold distinctDegreeLoop at hmem
      by_cases hzero : residual.isZero
      · simp [hzero] at hmem
        exact hprev bucket hmem
      · simp [hzero] at hmem
        let powerResult :=
          distinctDegreePowerLoop d (currentFrob - xMod) (residual.size + 1) residual 1
        have hnew :
            ∀ bucket : DegreeBucket p, powerResult.1 = some bucket →
              bucket.matchesFrobeniusDegree f hmonic := by
          intro newBucket hbucket
          have hdeg : newBucket.degree = d :=
            distinctDegreePowerLoop_bucket_degree d (currentFrob - xMod)
              (residual.size + 1) residual 1 newBucket hbucket
          have hdvd : newBucket.factor ∣ currentFrob - xMod :=
            distinctDegreePowerLoop_bucket_dvd_diff_of_squareFree_divisor
              f hsquareFree d (currentFrob - xMod) residual hresidual
              newBucket hbucket
          unfold DegreeBucket.matchesFrobeniusDegree
          rw [hdeg, frobeniusDiffMod, ← hstate, ← hxMod]
          exact hdvd
        have happend :
            ∀ bucket ∈ appendBucket? buckets powerResult.1,
              bucket.matchesFrobeniusDegree f hmonic :=
          appendBucket?_matches f hmonic buckets powerResult.1 hprev hnew
        have hnext_state :
            FpPoly.powModMonic currentFrob f hmonic p =
              FpPoly.frobeniusXPowMod f hmonic (d + 1) :=
          distinctDegreeLoop_frobenius_state_step f hmonic d currentFrob hstate
        have hpower_residual :
            powerResult.2 ∣ residual :=
          distinctDegreePowerLoop_residual_dvd d (currentFrob - xMod)
            (residual.size + 1) residual
        have hnext_residual : powerResult.2 ∣ f :=
          dvd_trans_poly hpower_residual hresidual
        exact ih (d + 1) (FpPoly.powModMonic currentFrob f hmonic p)
          powerResult.2 (appendBucket? buckets powerResult.1) hnext_state
          hnext_residual happend bucket hmem

private theorem distinctDegreeFactor_bucket_matches
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hsquareFree : DensePoly.gcd f (DensePoly.derivative f) = 1) :
    ∀ bucket ∈ (distinctDegreeFactor f hmonic).buckets,
      bucket.matchesFrobeniusDegree f hmonic := by
  unfold distinctDegreeFactor
  let xMod := FpPoly.modByMonic f FpPoly.X hmonic
  let frobX := FpPoly.frobeniusXMod f hmonic
  exact distinctDegreeLoop_bucket_matches f hmonic xMod hsquareFree
    (basisSize f + 1) 1 frobX f [] rfl
    (FpPoly.frobeniusXMod_eq_frobeniusXPowMod_one f hmonic)
    (DensePoly.dvd_refl_poly f) (by simp)

/--
The executable distinct-degree factorization preserves the input polynomial as
the product of recorded degree buckets and the residual factor.
-/
theorem prod_distinctDegreeFactor
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (_hsquareFree : DensePoly.gcd f (DensePoly.derivative f) = 1) :
    (distinctDegreeFactor f hmonic).product = f := by
  unfold distinctDegreeFactor DistinctDegreeFactorization.product
  let xMod := FpPoly.modByMonic f FpPoly.X hmonic
  let frobX := FpPoly.frobeniusXMod f hmonic
  have hloop := distinctDegreeLoop_product_eq f hmonic xMod
    (basisSize f + 1) 1 frobX f []
  simpa [degreeBucketProduct, degreeBucketFactors, factorProduct] using hloop

/--
Every recorded bucket is associated with a positive degree and satisfies the
corresponding Frobenius-degree divisibility invariant.
-/
theorem distinctDegreeFactor_bucket_invariants
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hsquareFree : DensePoly.gcd f (DensePoly.derivative f) = 1) :
    ∀ bucket ∈ (distinctDegreeFactor f hmonic).buckets,
      0 < bucket.degree ∧ bucket.matchesFrobeniusDegree f hmonic := by
  intro bucket hmem
  exact ⟨distinctDegreeFactor_bucket_positive_degrees f hmonic bucket hmem,
    distinctDegreeFactor_bucket_matches f hmonic hsquareFree bucket hmem⟩

/--
Every bucket emitted by `distinctDegreeFactor` records a positive Frobenius
degree.
-/
theorem distinctDegreeFactor_bucket_degree_pos
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hsquareFree : DensePoly.gcd f (DensePoly.derivative f) = 1)
    {bucket : DegreeBucket p}
    (hmem : bucket ∈ (distinctDegreeFactor f hmonic).buckets) :
    0 < bucket.degree :=
  (distinctDegreeFactor_bucket_invariants f hmonic hsquareFree bucket hmem).1

/--
Every bucket emitted by `distinctDegreeFactor` divides its matching Frobenius
difference.
-/
theorem distinctDegreeFactor_bucket_matchesFrobeniusDegree
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hsquareFree : DensePoly.gcd f (DensePoly.derivative f) = 1)
    {bucket : DegreeBucket p}
    (hmem : bucket ∈ (distinctDegreeFactor f hmonic).buckets) :
    bucket.matchesFrobeniusDegree f hmonic :=
  (distinctDegreeFactor_bucket_invariants f hmonic hsquareFree bucket hmem).2

end Berlekamp

end Hex
