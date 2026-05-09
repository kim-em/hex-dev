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
explicit so downstream consumers can inspect any part not separated by the
bounded executable pass.
-/
structure DistinctDegreeFactorization (p : Nat) [ZMod64.Bounds p] where
  input : FpPoly p
  buckets : List (DegreeBucket p)
  residual : FpPoly p

/-- Extract the polynomial factors recorded in distinct-degree buckets. -/
def degreeBucketFactors (buckets : List (DegreeBucket p)) : List (FpPoly p) :=
  buckets.map DegreeBucket.factor

/-- Multiply the polynomial factors recorded in distinct-degree buckets. -/
def degreeBucketProduct (buckets : List (DegreeBucket p)) : FpPoly p :=
  factorProduct (degreeBucketFactors buckets)

/-- Product represented by a distinct-degree factorization result. -/
def DistinctDegreeFactorization.product (result : DistinctDegreeFactorization p) :
    FpPoly p :=
  degreeBucketProduct result.buckets * result.residual

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

theorem distinctDegreeCandidate_spec
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (residual : FpPoly p) (d : Nat) :
    distinctDegreeCandidate f hmonic residual d =
      DensePoly.gcd residual (frobeniusDiffMod f hmonic d) := by
  rfl

private theorem degreeBucketFactors_append
    (buckets₁ buckets₂ : List (DegreeBucket p)) :
    degreeBucketFactors (buckets₁ ++ buckets₂) =
      degreeBucketFactors buckets₁ ++ degreeBucketFactors buckets₂ := by
  simp [degreeBucketFactors]

private theorem one_mul_poly
    [ZMod64.PrimeModulus p]
    (a : FpPoly p) :
    (1 : FpPoly p) * a = a :=
  (DensePoly.mul_comm_poly (1 : FpPoly p) a).trans (DensePoly.mul_one_right_poly a)

private theorem foldl_mul_left_factor
    [ZMod64.PrimeModulus p]
    (z a : FpPoly p) (xs : List (FpPoly p)) :
    xs.foldl (fun acc factor => acc * factor) (z * a)
      = z * xs.foldl (fun acc factor => acc * factor) a := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    have hcong : List.foldl (fun acc factor : FpPoly p => acc * factor) ((z * a) * b) bs
        = List.foldl (fun acc factor => acc * factor) (z * (a * b)) bs := by
      congr 1
      exact DensePoly.mul_assoc_poly z a b
    have hih : List.foldl (fun acc factor : FpPoly p => acc * factor) (z * (a * b)) bs
        = z * List.foldl (fun acc factor => acc * factor) (a * b) bs := ih (a * b)
    show List.foldl (fun acc factor => acc * factor) (z * a * b) bs
        = z * List.foldl (fun acc factor => acc * factor) (a * b) bs
    exact hcong.trans hih

private theorem foldl_mul_eq_mul_foldl
    [ZMod64.PrimeModulus p]
    (z : FpPoly p) (xs : List (FpPoly p)) :
    xs.foldl (fun acc factor => acc * factor) z
      = z * xs.foldl (fun acc factor => acc * factor) 1 := by
  have h1 : xs.foldl (fun acc factor => acc * factor) z
      = xs.foldl (fun acc factor => acc * factor) (z * 1) := by
    congr 1
    exact (DensePoly.mul_one_right_poly z).symm
  exact h1.trans (foldl_mul_left_factor z 1 xs)

private theorem factorProduct_cons_eq
    [ZMod64.PrimeModulus p]
    (x : FpPoly p) (xs : List (FpPoly p)) :
    factorProduct (x :: xs) = x * factorProduct xs := by
  show xs.foldl (fun acc factor => acc * factor) (1 * x)
    = x * xs.foldl (fun acc factor => acc * factor) 1
  rw [one_mul_poly x]
  exact foldl_mul_eq_mul_foldl x xs

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

private theorem degreeBucketProduct_append
    [ZMod64.PrimeModulus p]
    (buckets₁ buckets₂ : List (DegreeBucket p)) :
    degreeBucketProduct (buckets₁ ++ buckets₂) =
      degreeBucketProduct buckets₁ * degreeBucketProduct buckets₂ := by
  simp [degreeBucketProduct, degreeBucketFactors_append, factorProduct_append]

private theorem degreeBucketProduct_singleton
    [ZMod64.PrimeModulus p]
    (bucket : DegreeBucket p) :
    degreeBucketProduct [bucket] = bucket.factor := by
  simp [degreeBucketProduct, degreeBucketFactors, factorProduct]

private theorem degreeBucketProduct_appendBucket?_none
    (buckets : List (DegreeBucket p)) :
    degreeBucketProduct (appendBucket? buckets none) = degreeBucketProduct buckets := by
  rfl

private theorem degreeBucketProduct_appendBucket?_some
    [ZMod64.PrimeModulus p]
    (buckets : List (DegreeBucket p)) (bucket : DegreeBucket p) :
    degreeBucketProduct (appendBucket? buckets (some bucket)) =
      degreeBucketProduct buckets * bucket.factor := by
  rw [appendBucket?]
  rw [degreeBucketProduct_append, degreeBucketProduct_singleton]

private def optionalBucketProduct : Option (DegreeBucket p) → FpPoly p
  | none => 1
  | some bucket => bucket.factor

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

private theorem distinctDegreeCandidate_mul_div_eq
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (residual : FpPoly p) (d : Nat) :
    distinctDegreeCandidate f hmonic residual d *
        (residual / distinctDegreeCandidate f hmonic residual d) = residual := by
  rw [distinctDegreeCandidate_spec]
  exact gcd_mul_div_eq residual (frobeniusDiffMod f hmonic d)

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

private theorem finishDegreePower_product_nonunit
    [ZMod64.PrimeModulus p]
    (d : Nat) (residual acc : FpPoly p)
    (hacc : isUnitPolynomial acc = false) :
    let result := finishDegreePower (p := p) d residual acc
    optionalBucketProduct result.1 * result.2 = acc * residual := by
  unfold finishDegreePower
  rw [hacc]
  cases isUnitPolynomial residual <;> simp [optionalBucketProduct]

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

private theorem finishDegreePower_product_one
    [ZMod64.PrimeModulus p]
    (d : Nat) (residual : FpPoly p) :
    let result := finishDegreePower (p := p) d residual 1
    optionalBucketProduct result.1 * result.2 = residual := by
  unfold finishDegreePower
  rw [isUnitPolynomial_one]
  simp [optionalBucketProduct]

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

private theorem distinctDegreeLoop_frobenius_state_step
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (d : Nat) (currentFrob : FpPoly p)
    (hstate : currentFrob = FpPoly.frobeniusXPowMod f hmonic d) :
    FpPoly.powModMonic currentFrob f hmonic p =
      FpPoly.frobeniusXPowMod f hmonic (d + 1) := by
  rw [hstate]
  exact (FpPoly.frobeniusXPowMod_succ f hmonic d).symm

private theorem frobeniusXMod_eq_frobeniusXPowMod_one
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    FpPoly.frobeniusXMod f hmonic =
      FpPoly.frobeniusXPowMod f hmonic 1 := by
  unfold FpPoly.frobeniusXMod FpPoly.frobeniusXPowMod
  rw [Nat.pow_one]

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
multiplicity content) is delegated to the consumer.

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
    (_hsquareFree : DensePoly.gcd f (DensePoly.derivative f) = 1) :
    ∀ bucket ∈ (distinctDegreeFactor f hmonic).buckets,
      0 < bucket.degree ∧ bucket.matchesFrobeniusDegree f hmonic := by
  sorry

end Berlekamp

end Hex
