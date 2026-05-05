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
        let candidate := DensePoly.gcd residual diff
        let (newBucket, newResidual) :=
          if isUnitPolynomial candidate then
            (none, residual)
          else
            (some { degree := d, factor := candidate }, residual / candidate)
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

private theorem factorProduct_append (xs : List (FpPoly p)) (y : FpPoly p) :
    factorProduct (xs ++ [y]) = factorProduct xs * y := by
  unfold factorProduct
  rw [List.foldl_append]
  rfl

private theorem degreeBucketProduct_append_some
    (buckets : List (DegreeBucket p)) (bucket : DegreeBucket p) :
    degreeBucketProduct (buckets ++ [bucket]) =
      degreeBucketProduct buckets * bucket.factor := by
  unfold degreeBucketProduct degreeBucketFactors
  rw [List.map_append, List.map_cons, List.map_nil, factorProduct_append]

private theorem degreeBucketProduct_appendBucket?_some
    (buckets : List (DegreeBucket p)) (bucket : DegreeBucket p) :
    degreeBucketProduct (appendBucket? buckets (some bucket)) =
      degreeBucketProduct buckets * bucket.factor := by
  unfold appendBucket?
  exact degreeBucketProduct_append_some buckets bucket

private theorem degreeBucketProduct_appendBucket?_none
    (buckets : List (DegreeBucket p)) :
    degreeBucketProduct (appendBucket? buckets none) =
      degreeBucketProduct buckets := rfl

private theorem mul_div_eq_of_dvd
    [ZMod64.PrimeModulus p]
    {r s : FpPoly p} (h : r ∣ s) :
    r * (s / r) = s := by
  have hspec := DensePoly.div_mul_add_mod s r
  have hmod : s % r = 0 := DensePoly.mod_eq_zero_of_dvd s r h
  rw [hmod] at hspec
  exact (DensePoly.mul_comm_poly r (s / r)).trans
    ((DensePoly.add_zero_poly ((s / r) * r)).symm.trans hspec)

private theorem candidate_mul_div_residual
    [ZMod64.PrimeModulus p]
    (residual diff : FpPoly p) :
    DensePoly.gcd residual diff * (residual / DensePoly.gcd residual diff) = residual :=
  mul_div_eq_of_dvd (DensePoly.gcd_dvd_left residual diff)

private theorem distinctDegreeLoop_product_invariant
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (xMod : FpPoly p) :
    ∀ (fuel d : Nat) (currentFrob residual : FpPoly p)
        (buckets : List (DegreeBucket p)),
      degreeBucketProduct
          (distinctDegreeLoop f hmonic xMod fuel d currentFrob residual buckets).1 *
        (distinctDegreeLoop f hmonic xMod fuel d currentFrob residual buckets).2 =
        degreeBucketProduct buckets * residual := by
  intro fuel
  induction fuel with
  | zero =>
      intro d currentFrob residual buckets
      rfl
  | succ fuel ih =>
      intro d currentFrob residual buckets
      unfold distinctDegreeLoop
      cases hzero : residual.isZero
      · simp only [Bool.false_eq_true, if_false]
        cases hunit : isUnitPolynomial (DensePoly.gcd residual (currentFrob - xMod))
        · simp only [Bool.false_eq_true, if_false]
          let bucket : DegreeBucket p :=
            { degree := d
              factor := DensePoly.gcd residual (currentFrob - xMod) }
          rw [ih (d + 1) (FpPoly.powModMonic currentFrob f hmonic p)
              (residual / DensePoly.gcd residual (currentFrob - xMod))
              (appendBucket? buckets (some bucket)),
            degreeBucketProduct_appendBucket?_some,
            FpPoly.mul_assoc,
            candidate_mul_div_residual]
        · simp only [if_true]
          rw [ih (d + 1) (FpPoly.powModMonic currentFrob f hmonic p) residual
              (appendBucket? buckets none),
            degreeBucketProduct_appendBucket?_none]
      · simp only [if_true]

/--
The executable distinct-degree factorization preserves the input polynomial as
the product of recorded degree buckets and the residual factor.
-/
theorem prod_distinctDegreeFactor
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (_hsquareFree : DensePoly.gcd f (DensePoly.derivative f) = 1) :
    (distinctDegreeFactor f hmonic).product = f := by
  unfold DistinctDegreeFactorization.product distinctDegreeFactor
  exact (distinctDegreeLoop_product_invariant f hmonic
    (FpPoly.modByMonic f FpPoly.X hmonic) (basisSize f + 1) 1
    (FpPoly.frobeniusXMod f hmonic) f []).trans
    (by
      change degreeBucketProduct [] * f = f
      unfold degreeBucketProduct degreeBucketFactors factorProduct
      simp)

private theorem distinctDegreeLoop_bucket_invariants
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    ∀ (fuel d : Nat) (currentFrob residual : FpPoly p)
        (buckets : List (DegreeBucket p)),
      0 < d →
      currentFrob = FpPoly.frobeniusXPowMod f hmonic d →
      (∀ bucket ∈ buckets,
          0 < bucket.degree ∧ bucket.matchesFrobeniusDegree f hmonic) →
      ∀ bucket ∈
          (distinctDegreeLoop f hmonic
              (FpPoly.modByMonic f FpPoly.X hmonic) fuel d currentFrob residual
              buckets).1,
        0 < bucket.degree ∧ bucket.matchesFrobeniusDegree f hmonic := by
  intro fuel
  induction fuel with
  | zero =>
      intro d currentFrob residual buckets _ _ hbuckets bucket hbucket
      exact hbuckets bucket hbucket
  | succ fuel ih =>
      intro d currentFrob residual buckets hd hcurrent hbuckets bucket hbucket
      unfold distinctDegreeLoop at hbucket
      cases hzero : residual.isZero
      · simp only [hzero, Bool.false_eq_true, if_false] at hbucket
        have hd' : 0 < d + 1 := Nat.succ_pos _
        have hnext :
            FpPoly.powModMonic currentFrob f hmonic p =
              FpPoly.frobeniusXPowMod f hmonic (d + 1) := by
          rw [hcurrent, ← FpPoly.frobeniusXPowMod_succ]
        cases hunit : isUnitPolynomial
            (DensePoly.gcd residual
                (currentFrob - FpPoly.modByMonic f FpPoly.X hmonic))
        · simp only [hunit, Bool.false_eq_true, if_false] at hbucket
          have hnew :
              ∀ b ∈ appendBucket? buckets
                  (some { degree := d,
                          factor := DensePoly.gcd residual
                              (currentFrob -
                                  FpPoly.modByMonic f FpPoly.X hmonic) }),
                0 < b.degree ∧ b.matchesFrobeniusDegree f hmonic := by
            intro b hb
            simp only [appendBucket?, List.mem_append, List.mem_singleton] at hb
            rcases hb with hb | rfl
            · exact hbuckets b hb
            refine ⟨hd, ?_⟩
            show DensePoly.gcd residual
                  (currentFrob - FpPoly.modByMonic f FpPoly.X hmonic) ∣
                frobeniusDiffMod f hmonic d
            unfold frobeniusDiffMod
            rw [← hcurrent]
            exact DensePoly.gcd_dvd_right _ _
          exact ih (d + 1) _ _ _ hd' hnext hnew bucket hbucket
        · simp only [hunit, if_true] at hbucket
          exact ih (d + 1) _ _ _ hd' hnext (fun b hb => hbuckets b hb) bucket hbucket
      · simp only [hzero, if_true] at hbucket
        exact hbuckets bucket hbucket

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
  intro bucket hbucket
  unfold distinctDegreeFactor at hbucket
  apply distinctDegreeLoop_bucket_invariants f hmonic
      (basisSize f + 1) 1 (FpPoly.frobeniusXMod f hmonic) f [] Nat.one_pos
  · show FpPoly.frobeniusXMod f hmonic = FpPoly.frobeniusXPowMod f hmonic 1
    unfold FpPoly.frobeniusXMod FpPoly.frobeniusXPowMod
    rw [Nat.pow_one]
  · intro b hb
    cases hb
  · exact hbucket

end Berlekamp

end Hex
