import HexBerlekamp.Factor
import HexBerlekamp.Irreducibility

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

private theorem distinctDegreeCandidate_mul_div_eq
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (residual : FpPoly p) (d : Nat) :
    distinctDegreeCandidate f hmonic residual d *
        (residual / distinctDegreeCandidate f hmonic residual d) = residual := by
  have hspec := DensePoly.div_mul_add_mod residual
    (distinctDegreeCandidate f hmonic residual d)
  have hmod :
      residual % distinctDegreeCandidate f hmonic residual d = 0 := by
    rw [distinctDegreeCandidate_spec]
    exact DensePoly.mod_eq_zero_of_dvd residual
      (DensePoly.gcd residual (frobeniusDiffMod f hmonic d))
      (DensePoly.gcd_dvd_left residual (frobeniusDiffMod f hmonic d))
  rw [hmod] at hspec
  exact (DensePoly.mul_comm_poly (distinctDegreeCandidate f hmonic residual d)
      (residual / distinctDegreeCandidate f hmonic residual d)).trans
    ((DensePoly.add_zero_poly
      ((residual / distinctDegreeCandidate f hmonic residual d) *
        distinctDegreeCandidate f hmonic residual d)).symm.trans hspec)

/--
The executable distinct-degree factorization preserves the input polynomial as
the product of recorded degree buckets and the residual factor.
-/
theorem prod_distinctDegreeFactor
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (_hsquareFree : DensePoly.gcd f (DensePoly.derivative f) = 1) :
    (distinctDegreeFactor f hmonic).product = f := by
  sorry

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
