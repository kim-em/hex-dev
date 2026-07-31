/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexArith.Nat.Prime
public meta import HexBerlekamp.Factor
public meta import HexBerlekamp.Irreducibility
public meta import HexHensel.ModularPolynomial
public meta import HexHensel.Multifactor
public meta import HexHensel.QuadraticMultifactor
public meta import HexMatrix.Basic
public meta import HexPolyZ.Mignotte
public meta import HexLLL
public import HexArith.Nat.Prime
public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexHensel.Multifactor
public import HexHensel.QuadraticMultifactor
public import HexLLL
-- Kernel-reducible `Array`/`Vector` equality; see `HexBasic.ArrayDecEq`.
-- Drop once leanprover/lean4#14270 lands and the toolchain is bumped past it.
public import HexBasic.ArrayDecEq

public import HexBerlekampZassenhaus.Recombination
public meta import HexBerlekampZassenhaus.Recombination
public import HexBerlekampZassenhaus.Classical.Factorization
public meta import HexBerlekampZassenhaus.Classical.Factorization
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.FactorizationData
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.FactorizationResult
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.BhksRecover
import all HexBerlekampZassenhaus.Recombination

open scoped Hex   -- kernel-reducible Array/Vector equality; see HexBasic.ArrayDecEq

public section
set_option backward.proofsInPublic true

/-!
Integer factorization by the classical, lattice, and trial methods, with the
`factorize_scalar` theorems.
-/
namespace Hex

/-- Method that produced a public factorization result. -/
inductive FactorMethod where
  /-- Constant-polynomial normalization. -/
  | constant
  /-- Direct extraction of integer roots from a quadratic. -/
  | quadratic
  /-- Exhaustive recombination of lifted modular factors. -/
  | classical
  /-- Lattice recombination using logarithmic derivatives. -/
  | lattice
  /-- Trial division by bounded candidate factors. -/
  | trial
deriving DecidableEq

namespace FactorMethod

/-- A short diagnostic name for a factorization method. -/
@[expose]
def name : FactorMethod → String
  | .constant => "constant"
  | .quadratic => "quadratic"
  | .classical => "classical"
  | .lattice => "lattice"
  | .trial => "trial"

end FactorMethod

/-- Trace derived from the same factorization result used by the untraced API. -/
structure DirectFactorTrace where
  /-- The method that produced the returned factorization. -/
  method : FactorMethod
  /-- The reason classical recombination declined, when it did. -/
  classicalDecline : Option DeclineReason := none
  /-- Measurements from the classical recombination attempt. -/
  classical : ClassicalStats := {}
deriving DecidableEq

/-- Result of normalization followed by classical recombination. A successful
prime plan is retained even when recombination declines, so lattice recombination
can consume the exact modular factorization already computed. -/
structure ClassicalRun (f : ZPoly) where
  /-- The factors when classical recombination succeeded. -/
  factors : Option (Array ZPoly)
  /-- The method and classical-search measurements. -/
  trace : DirectFactorTrace
  /-- The selected modular plan, retained for possible lattice recombination. -/
  modular :
    Option (DirectPrimePlan (SquareFreeInput.ofNormalized (normalizeForFactor f))) :=
      none

/-- Raw factors and trace produced by the total selector in one execution. -/
structure FactorRun where
  /-- The raw polynomial factors before multiplicities are collected. -/
  factors : Array ZPoly
  /-- The method and classical-search measurements. -/
  trace : DirectFactorTrace
deriving DecidableEq

theorem bhksRecoveryCoreWithBound_ne_none_of_recovery_on_schedule
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    {start fuel target : Nat} {factors : Array ZPoly}
    (hfloor : bhksRecoveryFloor core ≤ target)
    (hmem : target ∈ henselPrecisionSchedule B start fuel)
    (hrecover :
      bhksRecover? core (ZPoly.directLiftData core target primeData) = some factors) :
    bhksRecoveryCoreWithBound core B primeData start fuel ≠ none := by
  intro hnone
  have hsome :=
    bhksRecoveryCoreWithBound_isSome_of_recovery_on_schedule
      core B primeData hfloor hmem hrecover
  rw [hnone] at hsome
  simp at hsome

private def bhksRecoveryGuardPrimeData : PrimeChoiceData :=
  letI := bounds_five
  let c : SmallPrimeCandidate :=
    { p := 5, bounds := bounds_five, prime := prime_five }
  { p := 5
    fModP := ZPoly.modP 5 cldGuardF
    factorsModP := berlekampFactorsModP cldGuardF c }

#guard bhksRecoveryCoreWithBound cldGuardF 1 bhksRecoveryGuardPrimeData
    (initialHenselPrecision 1) (ZPoly.quadraticDoublingSteps 1 + 2) =
  none

-- With the CLD-adequacy acceptance gate, a coefficient bound below
-- `cldCoeffFloor cldGuardF = 32` cannot be accepted: the schedule reaches the
-- cap `B` while every success is still below the floor, so the loop reports
-- `none`.
#guard bhksRecoveryCoreWithBound cldGuardF 4 bhksRecoveryGuardPrimeData
    (initialHenselPrecision 4) (ZPoly.quadraticDoublingSteps 4 + 2) =
  none

-- At a bound that reaches the floor the first gated success is accepted: for
-- `cldGuardF` this is schedule index `k = 32` (lift precision `liftData.k = 3`,
-- modulus `5 ^ 3 = 125`), recovering the same factors.
#guard bhksRecoveryCoreWithBound cldGuardF 32 bhksRecoveryGuardPrimeData
    (initialHenselPrecision 32) (ZPoly.quadraticDoublingSteps 32 + 2) =
  some bhksGuardFactors

private def exhaustiveNonMonicQuadraticGuard : ZPoly :=
  DensePoly.ofCoeffs #[1, 0, 2]

#guard (ZPoly.toMonic exhaustiveNonMonicQuadraticGuard).monic =
  DensePoly.ofCoeffs #[2, 0, 1]

#guard quadraticIntegerRootFactors? exhaustiveNonMonicQuadraticGuard = none

/-- Run the sole direct-coordinate classical engine on a normalized polynomial. -/
@[expose]
def classicalCoreFactors (core : ZPoly) : ClassicalOutcome :=
  match factorDirectCore ⟨core⟩ with
  | outcome => outcome

/-- Normalize once, handle the cheap terminal cases, and otherwise plan and
execute the direct engine.  A successful modular plan remains attached to a
decline for the total selector. -/
@[expose]
def runClassical (f : ZPoly) : ClassicalRun f :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    { factors :=
        some (reassemblePolynomialFactors normalized
          #[normalized.squareFreeCore])
      trace := { method := .constant } }
  else
    match quadraticIntegerRootFactors? normalized.squareFreeCore with
    | some coreFactors =>
        { factors :=
            some (reassemblePolynomialFactors normalized coreFactors)
          trace := { method := .quadratic } }
    | none =>
        let core := SquareFreeInput.ofNormalized normalized
        match directPrimePlan? core with
        | none =>
            { factors := none
              trace :=
                { method := .classical
                  classicalDecline := some .noGoodPrime } }
        | some modular =>
            match factorDirectCoreOfPlan core modular with
            | .factored coreFactors stats =>
                { factors :=
                    some (reassemblePolynomialFactors normalized coreFactors)
                  trace := { method := .classical, classical := stats }
                  modular := some modular }
            | .declined reason stats =>
                { factors := none
                  trace :=
                    { method := .classical
                      classicalDecline := some reason
                      classical := stats }
                  modular := some modular }

/-- Raw factor array for the sole production classical method. -/
@[expose]
def factorClassicalFactors (f : ZPoly) : Option (Array ZPoly) :=
  (runClassical f).factors

/-- Factor via the direct-coordinate, size-ordered classical engine.  Returns
`none` only with a typed decline recorded by `runClassical`. -/
def factorClassical (f : ZPoly) : Option Factorization :=
  (factorClassicalFactors f).map (factorizationOfFactors f)

/-- Classical factorization and typed trace derived from one shared execution. -/
@[expose]
def factorClassicalTraced (f : ZPoly) :
    Option Factorization × DirectFactorTrace :=
  let run := runClassical f
  (run.factors.map (factorizationOfFactors f), run.trace)

-- (X-1)(X-2)(X-3): a reducible cubic (past the quadratic short-circuit) that the
-- size-ordered recombination must split into three linear factors.
private def classicalGuardCubic : ZPoly := DensePoly.ofCoeffs #[-6, 11, -6, 1]

#guard ((factorClassical classicalGuardCubic).map Factorization.product) = some classicalGuardCubic
#guard ((factorClassical classicalGuardCubic).map (·.factors.size)) = some 3
-- A higher-`r` reducible (six linear factors) is recovered by the same engine.
private def classicalGuardSextic : ZPoly := DensePoly.ofCoeffs #[720, -1764, 1624, -735, 175, -21, 1]
#guard ((factorClassical classicalGuardSextic).map (·.factors.size)) = some 6
#guard ((factorClassical exhaustiveNonMonicQuadraticGuard).map Factorization.product)
  = some exhaustiveNonMonicQuadraticGuard

-- the traced variant's result agrees with `factorClassical`, and reports the
-- classical method, no decline, and a small (size-ordered) candidate count.
#guard (factorClassicalTraced classicalGuardCubic).1 = factorClassical classicalGuardCubic
#guard (factorClassicalTraced classicalGuardCubic).2.method = .classical
#guard (factorClassicalTraced classicalGuardCubic).2.classicalDecline = none
#guard (factorClassicalTraced classicalGuardCubic).2.classical.candidatesTried ≤ 64

/-- Raw factor array produced by the integer trial-division slow path.

Handles the deg-0 square-free part and integer-root cases up front via the same
constant/quadratic-root short-circuits as the classical method; the residual
exhaustive branch selects to the standalone integer trial-division algorithm
(`exhaustiveIntegerTrialCoreFactorsWithBound`). This is the trial-division
method of the three-method `factorize` combinator. -/
@[expose]
def factorTrialFactorsWithBound (f : ZPoly) (B : Nat) : Array ZPoly :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    reassemblePolynomialFactors normalized #[normalized.squareFreeCore]
  else
    match quadraticIntegerRootFactors? normalized.squareFreeCore with
    | some coreFactors => reassemblePolynomialFactors normalized coreFactors
    | none =>
        let coreFactors :=
          exhaustiveIntegerTrialCoreFactorsWithBound normalized.squareFreeCore B
        reassemblePolynomialFactors normalized coreFactors

#guard factorTrialFactorsWithBound exhaustiveNonMonicQuadraticGuard 4 =
  #[exhaustiveNonMonicQuadraticGuard]

/-- Factor using exhaustive recombination with the supplied coefficient bound. -/
@[expose]
def factorTrialWithBound (f : ZPoly) (B : Nat) : Factorization :=
  factorizationOfFactors f (factorTrialFactorsWithBound f B)

/-- Characterise the bounded integer trial-division slow wrapper as the raw
factor array packed into the public `Factorization` representation. -/
theorem factorTrialWithBound_eq_factorizationOfFactors
    (f : ZPoly) (B : Nat) :
    factorTrialWithBound f B =
      factorizationOfFactors f (factorTrialFactorsWithBound f B) := rfl

/--
Factor using the integer trial-division path at the default Mignotte
coefficient bound. This is the trial-division method of the three-method
`factorize` combinator.
-/
@[expose]
def factorTrial (f : ZPoly) : Factorization :=
  factorTrialWithBound f (ZPoly.defaultFactorCoeffBound f)

/-- Trial factorization uses the default coefficient bound. -/
theorem factorTrial_eq (f : ZPoly) :
    factorTrial f =
      factorTrialWithBound f (ZPoly.defaultFactorCoeffBound f) := rfl

#guard factorTrial exhaustiveNonMonicQuadraticGuard =
  factorizationOfFactors exhaustiveNonMonicQuadraticGuard #[exhaustiveNonMonicQuadraticGuard]

/--
Precision cap used by the public fast path.

The cap is the larger of the BHKS separation threshold bound of the
primitive square-free part and the Mignotte coefficient bound of the input, so later
termination proofs can use the same precision for both lattice separation
and exact integer reconstruction.

The CLD lattice is built directly over `(normalizeForFactor f).squareFreeCore`.
The square-free part remains explicit because it can have a larger coefficient norm than
`f` (for
`f = (x¹⁸ - 1)(x¹⁹ - 1)` the square-free part `f / (x - 1)` has `coeffNormSq 36` against
`f`'s `4`).
-/
def latticePrecisionCap (f : ZPoly) : Nat :=
  let core := (normalizeForFactor f).squareFreeCore
  max (max (bhksBound core) (cldCoeffFloor core))
    (max (ZPoly.defaultFactorCoeffBound f)
      (ZPoly.defaultFactorCoeffBound core))

theorem bhksBound_squareFreeCore_le_latticePrecisionCap (f : ZPoly) :
    bhksBound (normalizeForFactor f).squareFreeCore ≤ latticePrecisionCap f := by
  unfold latticePrecisionCap
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)

/-- The cap clears the CLD column-adequacy floor of the primitive square-free part, so the
lattice method's cap-precision run is column-adequate by construction. -/
theorem cldCoeffFloor_squareFreeCore_le_latticePrecisionCap (f : ZPoly) :
    cldCoeffFloor (normalizeForFactor f).squareFreeCore ≤ latticePrecisionCap f := by
  unfold latticePrecisionCap
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

theorem defaultFactorCoeffBound_le_latticePrecisionCap (f : ZPoly) :
    ZPoly.defaultFactorCoeffBound f ≤ latticePrecisionCap f := by
  unfold latticePrecisionCap
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- The public precision cap clears the whole fast recovery acceptance floor, so
the conditional loop always has admissible precisions on its schedule. -/
theorem bhksRecoveryFloor_squareFreeCore_le_latticePrecisionCap (f : ZPoly) :
    bhksRecoveryFloor (normalizeForFactor f).squareFreeCore ≤ latticePrecisionCap f := by
  unfold bhksRecoveryFloor
  refine Nat.max_le.mpr ⟨cldCoeffFloor_squareFreeCore_le_latticePrecisionCap f,
    ?_⟩
  unfold latticePrecisionCap
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- The cap dominates the Mignotte bound of the primitive square-free part itself, needed
by the true-support nonemptiness argument at cap precision. -/
theorem defaultFactorCoeffBound_squareFreeCore_le_latticePrecisionCap (f : ZPoly) :
    ZPoly.defaultFactorCoeffBound (normalizeForFactor f).squareFreeCore ≤
      latticePrecisionCap f := by
  unfold latticePrecisionCap
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/--
At the public precision cap, the monic lift for the primitive square-free part clears
the BHKS separation threshold: `2 · bhksBound core < p ^ k`.  This is the
`hprec` obligation of the lattice method's cap-precision irreducibility
certification; it is what forces the cap's BHKS component to
be computed from the square-free part rather than from `f`.
-/
theorem two_mul_bhksBound_squareFreeCore_lt_pow_cap
    (f : ZPoly) (primeData : PrimeChoiceData) (hp : 2 ≤ primeData.p) :
    2 * bhksBound (normalizeForFactor f).squareFreeCore <
      primeData.p ^
        (ZPoly.directLiftData (normalizeForFactor f).squareFreeCore
          (latticePrecisionCap f) primeData).k := by
  have hk :
      (ZPoly.directLiftData (normalizeForFactor f).squareFreeCore
          (latticePrecisionCap f) primeData).k =
        precisionForCoeffBound (latticePrecisionCap f) primeData.p := by
    unfold ZPoly.directLiftData
    exact henselLiftData_k _ _ _
  rw [hk]
  have hle := bhksBound_squareFreeCore_le_latticePrecisionCap f
  have hspec := precisionForCoeffBound_spec hp (latticePrecisionCap f)
  omega

/-- Variant of `two_mul_bhksBound_squareFreeCore_lt_pow_cap` keyed on the
lattice method's prime-selection witness, matching the shape of the `hprec`
side goal at the `factorLatticeFactorsWithBound` call site. -/
theorem two_mul_bhksBound_squareFreeCore_lt_pow_cap_of_choosePrimeData
    (f : ZPoly) (primeData : PrimeChoiceData)
    (hchoose :
      choosePrimeData? (normalizeForFactor f).squareFreeCore = some primeData) :
    2 * bhksBound (normalizeForFactor f).squareFreeCore <
      primeData.p ^
        (ZPoly.directLiftData (normalizeForFactor f).squareFreeCore
          (latticePrecisionCap f) primeData).k :=
  two_mul_bhksBound_squareFreeCore_lt_pow_cap f primeData
    (choosePrimeData?_prime _ primeData hchoose).two_le

-- #8521 regression witness: normalization can increase the square-free core's
-- coefficient norm, so the cap must not rely on norm monotonicity.
#guard
  let f : ZPoly := DensePoly.ofCoeffs
    #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  ZPoly.coeffNormSq f < ZPoly.coeffNormSq (normalizeForFactor f).squareFreeCore

/-- The CLD recovery's equivalence-class partition at this precision is the single
all-ones class; the signature of an *irreducible* input (all lifted mod-`p`
factors form the one integer factor). At column-adequate precision
(`bhksRecoveryFloor core ≤ k`) this certifies irreducibility; the proven count
lower bound forces a reducible square-free part to exhibit ≥ 2 classes there
(`squareFreeCore_irreducible_of_bhksSingleAllOnes` in the Mathlib layer); while
below the floor it may instead mean the lattice has not separated the factors
yet, so callers must only trust it at `k ≥ bhksRecoveryFloor core`. (A cap-free
CLD path would treat this partition as `degenerate` and decline, which is why
such a path "misses" on Swinnerton-Dyer inputs; the lattice method uses this predicate, both
in `latticeCoreLoop`'s early stop and in the trailing cap check, to turn the
declined-but-certified case into a positive irreducibility verdict.) -/
@[expose]
def bhksSingleAllOnesPartition (f : ZPoly) (d : LiftData) : Bool :=
  let L := bhksLatticeBasis f d.p d.k d.liftedFactors
  if hrows : 1 ≤ L.factorCount + L.coeffWidth then
    let projected := bhksProjectedRows L hrows
    let indicators := bhksEquivalenceClassIndicators projected
    !indicators.isEmpty && !projected.projectedRows.isEmpty &&
      indicators.size == 1 && bhksIndicatorAllOnes projected.factorCount (indicators.getD 0 #[])
  else
    false

/-- The fused recovery step's all-ones flag equals `bhksSingleAllOnesPartition`:
both read the single-all-ones signature off the same CLD lattice / RREF indicator
partition, so the lattice method reads it off the one lattice build the classifier
already ran. -/
private theorem bhksRecoverClassifiedWithAllOnes_snd (f : ZPoly) (d : LiftData) :
    (bhksRecoverClassifiedWithAllOnes f d).2 = bhksSingleAllOnesPartition f d := by
  rw [bhksRecoverClassifiedWithAllOnes, bhksSingleAllOnesPartition]
  by_cases hrows :
      1 ≤ (bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount +
        (bhksLatticeBasis f d.p d.k d.liftedFactors).coeffWidth
  · simp only [dif_pos hrows]
  · simp only [dif_neg hrows]

/-- Lattice-method recombination loop: `bhksRecoveryLoop` plus certificate-backed
early termination. The split path is byte-identical to the fast loop;
below `floor` every step is skipped, and at/above `floor` a classified recovery
success is accepted immediately.  The single change is the `.degenerate` arm: at
`k ≥ floor` the loop re-examines the partition, and the single all-ones class is
accepted as a **sound** irreducibility certificate (`some #[core]`) instead of
advancing the schedule.  Soundness is not heuristic: at column-adequate precision
(`bhksRecoveryFloor core ≤ k`) the proven count lower bound forces a reducible square-free part
to exhibit ≥ 2 equivalence classes, so all-ones can only be reported for a
genuinely irreducible square-free part (`squareFreeCore_irreducible_of_bhksSingleAllOnes` in the
Mathlib layer consumes exactly the `⟨k, floor ≤ k, all-ones⟩` witness this loop
produces).  Without the early stop the loop grinds the doubling schedule to the
conservative BHKS cap on every irreducible input.

Private: only `latticeCoreWithBound` (which passes `bhksRecoveryThreshold core`) is
the semantically supported entry point; the bare `floor` parameter must not be
set independently. -/
private def latticeCoreLoop
    (core : ZPoly) (B floor : Nat) (primeData : PrimeChoiceData) :
    Nat → Nat → Option (Array ZPoly)
  | _k, 0 => none
  | k, fuel + 1 =>
      if k < floor then
        if k ≥ B then
          none
        else
          latticeCoreLoop core B floor primeData (nextHenselPrecision k B) fuel
      else
        -- Build the CLD lattice once per step and read both the classification
        -- and the single-all-ones certificate off it (#8543): the `.degenerate`
        -- arm below no longer re-runs `bhksSingleAllOnesPartition`, which would
        -- repeat Hensel lifting, the logarithmic-derivative lattice reduction,
        -- and support-indicator extraction.
        let step := bhksRecoverClassifiedWithAllOnes core (ZPoly.directLiftData core k primeData)
        match step.1 with
        | .success factors =>
          some factors
        | .candidateFailure =>
          if k ≥ B then
            none
          else
            latticeCoreLoop core B floor primeData (nextHenselPrecision k B) fuel
        | .productMismatch _ =>
          if k ≥ B then
            none
          else
            latticeCoreLoop core B floor primeData (nextHenselPrecision k B) fuel
        | .degenerate =>
          if step.2 then
            some #[core]
          else if k ≥ B then
            none
          else
            latticeCoreLoop core B floor primeData (nextHenselPrecision k B) fuel

/-- Lattice factorization loop entry: `bhksRecoveryCoreWithBound` with certificate-backed
early termination on the single all-ones partition. Computes the CLD
column-adequacy floor once (through the irreducible `bhksRecoveryThreshold`) and runs
`latticeCoreLoop`. -/
def latticeCoreWithBound
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) (k fuel : Nat) :
    Option (Array ZPoly) :=
  latticeCoreLoop core B (bhksRecoveryThreshold core) primeData k fuel

/-- Behavioural unfolding for the lattice-method loop: the fused-step body is
propositionally equal to the two-call form (`bhksRecoverClassified` for the
classification, `bhksSingleAllOnesPartition` for the certificate). The fused
step shares one lattice build across the classification and the all-ones flag;
`bhksRecoverClassifiedWithAllOnes_fst`/`_snd` identify its two projections. -/
private theorem latticeCoreLoop_unfold
    (core : ZPoly) (B floor : Nat) (primeData : PrimeChoiceData) (k fuel : Nat) :
    latticeCoreLoop core B floor primeData k (fuel + 1) =
      (if k < floor then
        if k ≥ B then
          none
        else
          latticeCoreLoop core B floor primeData (nextHenselPrecision k B) fuel
      else
        match bhksRecoverClassified core (ZPoly.directLiftData core k primeData) with
        | .success factors => some factors
        | .candidateFailure =>
          if k ≥ B then none
          else latticeCoreLoop core B floor primeData (nextHenselPrecision k B) fuel
        | .productMismatch _ =>
          if k ≥ B then none
          else latticeCoreLoop core B floor primeData (nextHenselPrecision k B) fuel
        | .degenerate =>
          if bhksSingleAllOnesPartition core (ZPoly.directLiftData core k primeData) then
            some #[core]
          else if k ≥ B then none
          else latticeCoreLoop core B floor primeData (nextHenselPrecision k B) fuel) := by
  rw [latticeCoreLoop]
  by_cases hfl : k < floor
  · rw [if_pos hfl, if_pos hfl]
  · rw [if_neg hfl, if_neg hfl]
    simp only [bhksRecoverClassifiedWithAllOnes_fst, bhksRecoverClassifiedWithAllOnes_snd]

/-- The certificate-aware lattice loop can only turn a fast-loop failure into
an additional success; if it returns `none`, the underlying BHKS recovery loop
also returns `none`. -/
private theorem latticeCoreLoop_none_imp_bhksRecoveryLoop_none
    (core : ZPoly) (B floor : Nat) (primeData : PrimeChoiceData) :
    ∀ fuel k,
      latticeCoreLoop core B floor primeData k fuel = none →
        bhksRecoveryLoop core B floor primeData k fuel = none := by
  intro fuel
  induction fuel with
  | zero =>
      intro k _
      simp [bhksRecoveryLoop]
  | succ fuel ih =>
      intro k hnone
      rw [latticeCoreLoop_unfold] at hnone
      rw [bhksRecoveryLoop]
      by_cases hfl : k < floor
      · rw [if_pos hfl] at hnone ⊢
        by_cases hk : k ≥ B
        · simp [hk]
        · rw [if_neg hk] at hnone ⊢
          exact ih _ hnone
      · rw [if_neg hfl] at hnone ⊢
        cases hclass :
            bhksRecoverClassified core
              (ZPoly.directLiftData core k primeData) with
        | success factors =>
            rw [hclass] at hnone
            simp at hnone
        | candidateFailure =>
            rw [hclass] at hnone
            by_cases hk : k ≥ B
            · simp [hk]
            · rw [if_neg hk] at hnone ⊢
              exact ih _ hnone
        | productMismatch candidates =>
            rw [hclass] at hnone
            by_cases hk : k ≥ B
            · simp [hk]
            · rw [if_neg hk] at hnone ⊢
              exact ih _ hnone
        | degenerate =>
            rw [hclass] at hnone
            by_cases hones :
                bhksSingleAllOnesPartition core
                  (ZPoly.directLiftData core k primeData) = true
            · rw [if_pos hones] at hnone
              simp at hnone
            · rw [if_neg hones] at hnone
              by_cases hk : k ≥ B
              · simp [hk]
              · rw [if_neg hk] at hnone ⊢
                exact ih _ hnone

/-- A successful fixed-precision recovery on the scheduled lattice path forces
the certificate-aware lattice recovery loop to return some result. -/
theorem latticeCoreWithBound_ne_none_of_recovery_on_schedule
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    {start fuel target : Nat} {factors : Array ZPoly}
    (hfloor : bhksRecoveryFloor core ≤ target)
    (hmem : target ∈ henselPrecisionSchedule B start fuel)
    (hrecover :
      bhksRecover? core (ZPoly.directLiftData core target primeData) =
        some factors) :
    latticeCoreWithBound core B primeData start fuel ≠ none := by
  intro hnone
  have hfast_none :
      bhksRecoveryCoreWithBound core B primeData start fuel = none := by
    change latticeCoreLoop core B (bhksRecoveryThreshold core)
      primeData start fuel = none at hnone
    change bhksRecoveryLoop core B (bhksRecoveryThreshold core)
      primeData start fuel = none
    rw [bhksRecoveryThreshold_eq] at hnone ⊢
    exact latticeCoreLoop_none_imp_bhksRecoveryLoop_none
      core B (bhksRecoveryFloor core) primeData fuel start hnone
  exact
    (bhksRecoveryCoreWithBound_ne_none_of_recovery_on_schedule
      core B primeData hfloor hmem hrecover) hfast_none

/-- Structural spec for the lattice-method loop: every success is either a fast-loop
success (the split path is untouched) or the certificate-backed early stop; the
singleton `#[core]` together with a concrete witness precision `k'` at/above the
column-adequacy floor whose partition is the single all-ones class. -/
private theorem latticeCoreLoop_some_spec
    (core : ZPoly) (B floor : Nat) (primeData : PrimeChoiceData) :
    ∀ fuel k cf,
      latticeCoreLoop core B floor primeData k fuel = some cf →
        bhksRecoveryLoop core B floor primeData k fuel = some cf ∨
          (cf = #[core] ∧ ∃ k', floor ≤ k' ∧
            bhksSingleAllOnesPartition core (ZPoly.directLiftData core k' primeData)
              = true) := by
  intro fuel
  induction fuel with
  | zero =>
      intro k cf h
      simp [latticeCoreLoop] at h
  | succ fuel ih =>
      intro k cf h
      rw [latticeCoreLoop_unfold] at h
      rw [bhksRecoveryLoop]
      by_cases hfl : k < floor
      · rw [if_pos hfl] at h ⊢
        by_cases hk : k ≥ B
        · simp [hk] at h
        · rw [if_neg hk] at h ⊢
          exact ih _ cf h
      · rw [if_neg hfl] at h ⊢
        cases hclass : bhksRecoverClassified core (ZPoly.directLiftData core k primeData) with
        | success factors =>
            rw [hclass] at h
            exact Or.inl h
        | candidateFailure =>
            rw [hclass] at h
            by_cases hk : k ≥ B
            · simp [hk] at h
            · rw [if_neg hk] at h ⊢
              exact ih _ cf h
        | productMismatch cands =>
            rw [hclass] at h
            by_cases hk : k ≥ B
            · simp [hk] at h
            · rw [if_neg hk] at h ⊢
              exact ih _ cf h
        | degenerate =>
            rw [hclass] at h
            by_cases hones :
                bhksSingleAllOnesPartition core (ZPoly.directLiftData core k primeData) = true
            · rw [if_pos hones] at h
              exact Or.inr ⟨(Option.some.inj h).symm,
                k, Nat.le_of_not_lt hfl, hones⟩
            · rw [if_neg hones] at h
              by_cases hk : k ≥ B
              · simp [hk] at h
              · rw [if_neg hk] at h ⊢
                exact ih _ cf h

/-- A successful `latticeCoreWithBound` call is either a
`bhksRecoveryCoreWithBound` success or the early irreducibility certificate; the
singleton `#[core]` with a witness precision `k'` clearing `bhksRecoveryFloor core`
whose partition is the single all-ones class.  The witness pair is exactly the
`hB_floor`/`hbhks` input of the Mathlib layer's
`squareFreeCore_irreducible_of_bhksSingleAllOnes`. -/
theorem latticeCoreWithBound_some_spec
    {core : ZPoly} {B : Nat} {primeData : PrimeChoiceData} {k fuel : Nat}
    {cf : Array ZPoly}
    (h : latticeCoreWithBound core B primeData k fuel = some cf) :
    bhksRecoveryCoreWithBound core B primeData k fuel = some cf ∨
      (cf = #[core] ∧ ∃ k', bhksRecoveryFloor core ≤ k' ∧
        bhksSingleAllOnesPartition core (ZPoly.directLiftData core k' primeData)
          = true) := by
  rw [latticeCoreWithBound, bhksRecoveryThreshold_eq] at h
  rcases latticeCoreLoop_some_spec core B (bhksRecoveryFloor core) primeData fuel k cf h with
    hfast | hcert
  · rw [bhksRecoveryCoreWithBound, bhksRecoveryThreshold_eq]
    exact Or.inl hfast
  · exact Or.inr hcert

/-- Large-`r` lattice factorization factorisation: the van Hoeij CLD recovery, plus
**irreducibility certification**. When the recovery splits `core`, use its
factors; when the loop's certificate-backed early stop fires (single all-ones
partition at column-adequate precision), `core` is irreducible
(`#[core]`); when the loop declines all the way to the cap, check the
cap-precision partition once more: the single all-ones class means `core` is
irreducible (`#[core]`), anything else is a genuine failure (`none`).

Both certification arms are conditional on the column-adequacy floor: the loop's
early stop only examines the partition at `k ≥ bhksRecoveryThreshold core`, and the
trailing cap check requires `bhksRecoveryThreshold core ≤ B`; below the floor the
all-ones partition may merely mean the lattice has not separated the factors
yet, so certifying there would be unsound.  The public `factorLattice` supplies
`latticePrecisionCap`, which clears the floor by construction. -/
@[expose]
def latticeCoreFactorsWithBound
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) : Option (Array ZPoly) :=
  if primeData.factorsModP.size ≤ 1 then
    some #[core]
  else
    match latticeCoreWithBound core B primeData
        (initialHenselPrecision B) (ZPoly.quadraticDoublingSteps B + 2) with
    | some coreFactors => some coreFactors
    | none =>
        if bhksRecoveryThreshold core ≤ B then
          if bhksSingleAllOnesPartition core (ZPoly.directLiftData core B primeData) then
            some #[core]
          else
            none
        else
          none

/-- Reassemble a lattice result from an existing direct prime plan.  The plan
is indexed by the normalized polynomial, so callers cannot reuse modular factors for
a different polynomial. -/
@[expose]
def factorLatticeFactorsWithPlan
    (normalized : FactorNormalizationData) (B : Nat)
    (modular : DirectPrimePlan (SquareFreeInput.ofNormalized normalized)) :
    Option (Array ZPoly) :=
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    some (reassemblePolynomialFactors normalized #[normalized.squareFreeCore])
  else if B = 0 then
    none
  else
    match quadraticIntegerRootFactors? normalized.squareFreeCore with
    | some coreFactors => some (reassemblePolynomialFactors normalized coreFactors)
    | none =>
        (latticeCoreFactorsWithBound normalized.squareFreeCore B modular.data).map
          fun coreFactors => reassemblePolynomialFactors normalized coreFactors

/-- Raw factor array for the large-`r` lattice method: the CLD lattice recovery,
certifying irreducibility at the cap so that Swinnerton-Dyer / high-`r`
irreducibles return `some #[f]` instead of `none`. -/
@[expose]
def factorLatticeFactorsWithBound (f : ZPoly) (B : Nat) : Option (Array ZPoly) :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    some (reassemblePolynomialFactors normalized #[normalized.squareFreeCore])
  else if B = 0 then
    none
  else
    match quadraticIntegerRootFactors? normalized.squareFreeCore with
    | some coreFactors => some (reassemblePolynomialFactors normalized coreFactors)
    | none =>
        match directPrimePlan? ⟨normalized.squareFreeCore⟩ with
        | none => none
        | some modular =>
            factorLatticeFactorsWithPlan normalized B modular

/-- The bounded lattice method represents the zero polynomial by its normalized zero factor. -/
theorem factorLatticeFactorsWithBound_zero (B : Nat) :
    factorLatticeFactorsWithBound 0 B =
      some (reassemblePolynomialFactors (normalizeForFactor 0)
        #[(normalizeForFactor 0).squareFreeCore]) := by
  have hprimitive : ZPoly.primitivePart (0 : ZPoly) = 0 := by
    apply DensePoly.primitivePart_eq_zero_of_content_eq_zero
    exact DensePoly.content_zero
  have hxcore : (ZPoly.extractXPower (0 : ZPoly)).core = 0 := by
    rfl
  have hsquare :
      (ZPoly.primitiveSquareFreeDecomposition (0 : ZPoly)).squareFreeCore = 0 := by
    unfold ZPoly.primitiveSquareFreeDecomposition
    rw [hprimitive]
    rfl
  have hnormalized : (normalizeForFactor (0 : ZPoly)).squareFreeCore = 0 := by
    simp only [normalizeForFactor, hprimitive]
    change
      (ZPoly.primitiveSquareFreeDecomposition
        (ZPoly.extractXPower (0 : ZPoly)).core).squareFreeCore = 0
    rw [hxcore, hsquare]
  unfold factorLatticeFactorsWithBound
  simp [hnormalized]

/-- Attempt lattice recombination with the supplied coefficient bound. -/
@[expose]
def factorLatticeWithBound (f : ZPoly) (B : Nat) : Option Factorization :=
  (factorLatticeFactorsWithBound f B).map (factorizationOfFactors f)

/-- Van Hoeij CLD lattice method (large-`r`) at the full BHKS precision cap.
Certifies irreducibility (unlike a cap-free CLD path), so it returns `some` on
Swinnerton-Dyer and cyclotomic high-`r` irreducibles. -/
@[expose]
def factorLattice (f : ZPoly) : Option Factorization :=
  factorLatticeWithBound f (latticePrecisionCap f)

-- Swinnerton-Dyer SD2 and Φ₁₅: irreducible over ℤ but split mod p; a cap-free
-- CLD path misses, `factorLattice` certifies them as single irreducible factors.
#guard ((factorLattice (DensePoly.ofCoeffs #[1, 0, -10, 0, 1])).map (·.factors.size)) = some 1
#guard ((factorLattice (DensePoly.ofCoeffs #[1, 0, -10, 0, 1])).map Factorization.product)
  = some (DensePoly.ofCoeffs #[1, 0, -10, 0, 1])
#guard ((factorLattice (DensePoly.ofCoeffs #[1, -1, 0, 1, -1, 1, 0, -1, 1])).map (·.factors.size)) = some 1
-- a reducible input the CLD splits directly still works
#guard ((factorLattice (DensePoly.ofCoeffs #[6, 0, -5, 0, 1])).map Factorization.product)
  = some (DensePoly.ofCoeffs #[6, 0, -5, 0, 1])

/-- Total integer-polynomial factorization with bounded fast paths.

The size-ordered classical method handles every input
within its subset budget; fast for reducibles (it peels factors) and bounded for
irreducibles (it exhausts subsets up to the budget, then
declines). The lattice method is correct but slower because it runs to the precision
cap, so the function runs the classical method first and falls back to the
lattice only when classical declines (budget exhausted, i.e. `r` too large), then
to trial division when no admissible prime exists. This dominates an up-front
`r`-estimate that could send a reducible high-`r` input to the slow lattice method.

Returns the chosen `Factorization` and a `DirectFactorTrace` whose `method`
records which method answered.  A classical decline retains its direct prime
plan, and the lattice fallback consumes that plan without repeating modular
factorization.

**Self-certifying.** Each non-backstop method's `Factorization` is accepted only
when it reconstructs the input (`Factorization.product φ = f`, decidable on
`ZPoly`); on the (corpus-never) miss it falls through to the proven
`factorTrial` backstop. This makes `Factorization.product (ZPoly.factorize f) = f`
provable unconditionally without yet proving the classical recombination loop
reconstructs (that, with per-factor irreducibility, is the separate re-proof
step). The classical method is correct on the whole conformance corpus, so the
guard always passes there and the emitted factor/trace values are unchanged.

The raw factors and trace are retained together so every public view observes
the same selection execution. -/
@[expose]
def runFactor (f : ZPoly) : FactorRun :=
  let run := runClassical f
  match run.factors with
  | some factors =>
      let φ := factorizationOfFactors f factors
      if Factorization.product φ = f then
        { factors, trace := run.trace }
      else
        { factors :=
            factorTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)
          trace := { run.trace with method := .trial } }
  | none =>
      match run.modular with
      | some modular =>
          match factorLatticeFactorsWithPlan
              (normalizeForFactor f) (latticePrecisionCap f) modular with
          | some factors =>
              let φ := factorizationOfFactors f factors
              if Factorization.product φ = f then
                { factors, trace := { run.trace with method := .lattice } }
              else
                { factors :=
                    factorTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)
                  trace := { run.trace with method := .trial } }
          | none =>
              { factors :=
                  factorTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)
                trace := { run.trace with method := .trial } }
      | none =>
          { factors :=
              factorTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)
            trace := { run.trace with method := .trial } }

/-- Factor an integer polynomial and return a trace of the selected method. -/
@[expose]
def factorTraced (f : ZPoly) : Factorization × DirectFactorTrace :=
  let run := runFactor f
  (factorizationOfFactors f run.factors, run.trace)

/--
The public total factorisation of a {name}`Hex.ZPoly`.

{name}`Hex.factorClassical` first tries a bounded subset search. If it declines,
{name}`Hex.factorLattice` tries CLD lattice recombination. An answer from either
optional method is accepted only when {name}`Hex.Factorization.product`
reconstructs `f`. If both methods decline, {name}`Hex.factorTrial` supplies the
total backstop. The trial method does not depend on {name}`Hex.choosePrimeData?`,
so this function still returns a factorisation when prime selection fails.

This definition lives in the {name}`Hex.ZPoly` namespace, so it can be called
with dot notation as `f.factorize`.
-/
@[expose]
def ZPoly.factorize (f : ZPoly) : Factorization :=
  (factorTraced f).1

/-- The irreducible factors of `f` with their multiplicities: the `factors`
field of the full factorisation `f.factorize`. -/
@[expose]
def ZPoly.factors (f : ZPoly) : Array (ZPoly × Nat) :=
  (ZPoly.factorize f).factors

-- classical answers the corpus, including small/medium-r Swinnerton-Dyer / cyclotomic
-- irreducibles, so no fallback is taken (the lattice/trial arms cover only the
-- budget-exceeding tail and the no-prime case).
#guard Factorization.product (ZPoly.factorize (DensePoly.ofCoeffs #[6, 0, -5, 0, 1]))
  = DensePoly.ofCoeffs #[6, 0, -5, 0, 1]                                      -- reducible
#guard (factorTraced (DensePoly.ofCoeffs #[6, 0, -5, 0, 1])).2.method = .classical
#guard Factorization.product (ZPoly.factorize (DensePoly.ofCoeffs #[1, 0, -10, 0, 1]))
  = DensePoly.ofCoeffs #[1, 0, -10, 0, 1]                                     -- SD2, irreducible
#guard ((ZPoly.factorize (DensePoly.ofCoeffs #[1, 0, -10, 0, 1])).factors.size) = 1
#guard (factorTraced (DensePoly.ofCoeffs #[1, 0, -10, 0, 1])).2.method = .classical
#guard (factorTraced (DensePoly.ofCoeffs #[1, 0, -10, 0, 1])).2.classicalDecline = none

/-- The CLD lattice method's `Factorization` is the raw lattice factor array packed
through `factorizationOfFactors f`. -/
theorem factorLattice_eq_map (f : ZPoly) :
    factorLattice f =
      (factorLatticeFactorsWithBound f (latticePrecisionCap f)).map
        (factorizationOfFactors f) := rfl

/-- Raw factor array produced by the same total-selection execution as
`ZPoly.factorize`. -/
@[expose]
def factorFactors (f : ZPoly) : Array ZPoly :=
  (runFactor f).factors

/-- The cost-based hybrid factorisation is the `factorizationOfFactors`-packed
form of its raw factor array `factorFactors`. Every method (classical /
lattice / trial) assembles via `factorizationOfFactors f`, so this correspondence lets
the structural `factorizationOfFactors_entry_*` lemmas apply to every entry
of the hybrid result. -/
theorem factorize_eq_factorizationOfFactors (f : ZPoly) :
    ZPoly.factorize f = factorizationOfFactors f (factorFactors f) := rfl

/-- A modular plan retained by the classical run is exactly the plan selected
for the normalized polynomial. -/
theorem runClassical_modular_eq_some
    (f : ZPoly)
    {modular : DirectPrimePlan
      (SquareFreeInput.ofNormalized (normalizeForFactor f))}
    (hmodular : (runClassical f).modular = some modular) :
  directPrimePlan? (SquareFreeInput.ofNormalized (normalizeForFactor f)) =
      some modular := by
  unfold runClassical at hmodular
  by_cases hdegree :
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · rw [if_pos hdegree] at hmodular
    simp at hmodular
  · rw [if_neg hdegree] at hmodular
    cases hquadratic :
        quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore with
    | some coreFactors =>
        simp [hquadratic] at hmodular
    | none =>
        simp only [hquadratic] at hmodular
        generalize hplan :
            directPrimePlan?
                (SquareFreeInput.ofNormalized (normalizeForFactor f)) = plan?
          at hmodular
        cases plan? with
        | none => simp at hmodular
        | some plan =>
            cases houtcome : factorDirectCoreOfPlan
                (SquareFreeInput.ofNormalized (normalizeForFactor f)) plan with
            | factored factors stats =>
                have heq : some plan = some modular := by
                  simpa only [houtcome] using hmodular
                cases Option.some.inj heq
                rfl
            | declined reason stats =>
                have heq : some plan = some modular := by
                  simpa only [houtcome] using hmodular
                cases Option.some.inj heq
                rfl

/-- Every raw factor of the cost-based hybrid comes from one of its three
selection branches: the classical method's certified output, the CLD lattice
method's certified output, or the `factorTrial` totality backstop. It
exposes the branch source (mirroring `factorize_entry_mem_raw_source` for the
raw hybrid array) without leaking the private `factorizationOfFactors` guard, so
the Mathlib-side irreducibility assembly can case-split over the branches. -/
theorem factorFactors_mem_source (f : ZPoly) {raw : ZPoly}
    (hmem : raw ∈ (factorFactors f).toList) :
    (∃ cf, factorClassicalFactors f =
        some cf ∧ raw ∈ cf.toList) ∨
      (∃ (modular : DirectPrimePlan
            (SquareFreeInput.ofNormalized (normalizeForFactor f)))
          (cf : Array ZPoly),
        directPrimePlan?
            (SquareFreeInput.ofNormalized (normalizeForFactor f)) = some modular ∧
          factorLatticeFactorsWithPlan
            (normalizeForFactor f) (latticePrecisionCap f) modular = some cf ∧
          raw ∈ cf.toList) ∨
      raw ∈ (factorTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)).toList := by
  simp only [factorFactors, runFactor] at hmem
  generalize hrun : runClassical f = run at hmem
  cases hcf : run.factors with
  | some cf =>
      simp only [hcf] at hmem
      by_cases hp : Factorization.product (factorizationOfFactors f cf) = f
      · rw [if_pos hp] at hmem
        exact Or.inl ⟨cf, by simp [factorClassicalFactors, hrun, hcf], hmem⟩
      · rw [if_neg hp] at hmem
        exact Or.inr (Or.inr hmem)
  | none =>
      simp only [hcf] at hmem
      cases hmod : run.modular with
      | none =>
          simp only [hmod] at hmem
          exact Or.inr (Or.inr hmem)
      | some modular =>
          simp only [hmod] at hmem
          cases hl : factorLatticeFactorsWithPlan
              (normalizeForFactor f) (latticePrecisionCap f) modular with
          | none =>
              simp only [hl] at hmem
              exact Or.inr (Or.inr hmem)
          | some cf =>
              simp only [hl] at hmem
              by_cases hp :
                  Factorization.product (factorizationOfFactors f cf) = f
              · rw [if_pos hp] at hmem
                exact Or.inr (Or.inl
                  ⟨modular, cf,
                    runClassical_modular_eq_some f
                      (by simpa [hrun] using hmod),
                    hl, hmem⟩)
              · rw [if_neg hp] at hmem
                exact Or.inr (Or.inr hmem)


private theorem content_ne_zero_of_zpoly_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    ZPoly.content f ≠ 0 := by
  intro hcontent
  apply hf
  have hreconstruct := ZPoly.content_mul_primitivePart f
  rw [hcontent] at hreconstruct
  have hzero : DensePoly.scale (0 : Int) (ZPoly.primitivePart f) = 0 := by
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_scale (R := Int) (0 : Int) (ZPoly.primitivePart f) n
      (Int.zero_mul 0)]
    rw [DensePoly.coeff_zero]
    exact Int.zero_mul _
  rw [hzero] at hreconstruct
  exact hreconstruct.symm

private theorem signedContentScalar_eq_zero_iff (f : ZPoly) :
    (if f = 0 then
        0
      else if DensePoly.leadingCoeff f < 0 then
        -ZPoly.content f
      else
        ZPoly.content f) = 0 ↔ f = 0 := by
  constructor
  · intro h
    by_cases hf : f = 0
    · exact hf
    have hcontent_ne := content_ne_zero_of_zpoly_ne_zero f hf
    rw [if_neg hf] at h
    by_cases hneg : DensePoly.leadingCoeff f < 0
    · rw [if_pos hneg] at h
      exact absurd (Int.neg_eq_zero.mp h) hcontent_ne
    · rw [if_neg hneg] at h
      exact absurd h hcontent_ne
  · intro hf
    simp [hf]

/-- Scalar contract for a factorization assembled from a raw factor array.
The public statement exposes the signed-content convention without exposing
the private helper used to compute it. -/
theorem factorizationOfFactors_scalar (f : ZPoly) (rawFactors : Array ZPoly) :
    (factorizationOfFactors f rawFactors).scalar =
      if f = 0 then
        0
      else if DensePoly.leadingCoeff f < 0 then
        -ZPoly.content f
      else
        ZPoly.content f := by
  rfl

@[simp, grind =] theorem factorizationOfFactors_scalar_zero (rawFactors : Array ZPoly) :
    (factorizationOfFactors 0 rawFactors).scalar = 0 := by
  simp [factorizationOfFactors_scalar]

theorem factorizationOfFactors_scalar_of_leadingCoeff_neg
    {f : ZPoly} (rawFactors : Array ZPoly)
    (hf : f ≠ 0) (hneg : DensePoly.leadingCoeff f < 0) :
    (factorizationOfFactors f rawFactors).scalar = -ZPoly.content f := by
  simp [factorizationOfFactors_scalar, hf, hneg]

theorem factorizationOfFactors_scalar_of_leadingCoeff_pos
    {f : ZPoly} (rawFactors : Array ZPoly)
    (hf : f ≠ 0) (hpos : 0 < DensePoly.leadingCoeff f) :
    (factorizationOfFactors f rawFactors).scalar = ZPoly.content f := by
  have hnot_neg : ¬ DensePoly.leadingCoeff f < 0 := by omega
  simp [factorizationOfFactors_scalar, hf, hnot_neg]

theorem factorizationOfFactors_scalar_eq_zero_iff
    (f : ZPoly) (rawFactors : Array ZPoly) :
    (factorizationOfFactors f rawFactors).scalar = 0 ↔ f = 0 := by
  rw [factorizationOfFactors_scalar]
  exact signedContentScalar_eq_zero_iff f

/-- Scalar contract for the default public factorization entry point. -/
theorem factorize_scalar (f : ZPoly) :
    (ZPoly.factorize f).scalar =
      if f = 0 then
        0
      else if DensePoly.leadingCoeff f < 0 then
        -ZPoly.content f
      else
        ZPoly.content f := by
  rw [factorize_eq_factorizationOfFactors]
  exact factorizationOfFactors_scalar f (factorFactors f)

@[simp, grind =] theorem factorize_scalar_zero :
    (ZPoly.factorize 0).scalar = 0 := by
  rw [factorize_eq_factorizationOfFactors]
  exact factorizationOfFactors_scalar_zero (factorFactors 0)

/-- The default factorization of `0` records no polynomial factors: the
primitive square-free part of `0` is the unit `1`, so every reassembled raw factor is
dropped by the `shouldRecordPolynomialFactor` filter. This lets
`factorize_irreducible_of_nonUnit` discharge the degenerate `f = 0` case
vacuously, without a nonzero hypothesis. -/
theorem factorize_zero_factors : (ZPoly.factorize (0 : ZPoly)).factors = #[] := by
  decide

theorem factorize_scalar_of_leadingCoeff_neg
    {f : ZPoly} (hf : f ≠ 0) (hneg : DensePoly.leadingCoeff f < 0) :
    (ZPoly.factorize f).scalar = -ZPoly.content f := by
  rw [factorize_eq_factorizationOfFactors]
  exact factorizationOfFactors_scalar_of_leadingCoeff_neg (factorFactors f) hf hneg

/-- A nonzero polynomial with positive leading coefficient keeps its content as scalar factor. -/
theorem factorize_scalar_of_leadingCoeff_pos
    {f : ZPoly} (hf : f ≠ 0) (hpos : 0 < DensePoly.leadingCoeff f) :
    (ZPoly.factorize f).scalar = ZPoly.content f := by
  rw [factorize_eq_factorizationOfFactors]
  exact factorizationOfFactors_scalar_of_leadingCoeff_pos (factorFactors f) hf hpos

theorem factorize_scalar_eq_zero_iff (f : ZPoly) :
    (ZPoly.factorize f).scalar = 0 ↔ f = 0 := by
  rw [factorize_eq_factorizationOfFactors]
  exact factorizationOfFactors_scalar_eq_zero_iff f (factorFactors f)

/-- Every recorded entry of the default public factorization has positive
multiplicity. -/
theorem factorize_entry_multiplicity_pos
    (f : ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (ZPoly.factorize f).factors.toList) :
    0 < entry.2 := by
  rw [factorize_eq_factorizationOfFactors] at hmem
  exact factorizationOfFactors_entry_multiplicity_pos f (factorFactors f) entry hmem

/-- Every recorded entry of the default public factorization is fixed by
`normalizeFactorSign`. -/
theorem factorize_entry_normalizeFactorSign_id
    (f : ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (ZPoly.factorize f).factors.toList) :
    normalizeFactorSign entry.1 = entry.1 := by
  rw [factorize_eq_factorizationOfFactors] at hmem
  exact factorizationOfFactors_entry_normalizeFactorSign_id f (factorFactors f) entry hmem
