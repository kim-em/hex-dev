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

public import HexBerlekampZassenhaus.BhksCandidates
public meta import HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.FactorizationData
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.FactorizationResult
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.BhksCandidates

open scoped Hex   -- kernel-reducible Array/Vector equality; see HexBasic.ArrayDecEq

public section
set_option backward.proofsInPublic true

/-!
This module implements the proved direct-coordinate BHKS candidate recovery
used by the CLD lattice method.
-/
namespace Hex

private theorem bhksIndicatorCandidatesStep_fold_getD_candidate
    (f : ZPoly) (d : LiftData)
    (indicators : List (Array Int)) (acc candidates : Array ZPoly)
    (hfold :
      indicators.foldl (bhksIndicatorCandidatesStep f d) (some acc) =
        some candidates) :
    ∀ i, i < indicators.length →
      ∃ quotient,
        bhksIndicatorCandidate? f d (indicators.getD i #[]) =
          some (candidates.getD (acc.size + i) 0, quotient) := by
  induction indicators generalizing acc candidates with
  | nil =>
      intro i hi
      simp at hi
  | cons indicator indicators ih =>
      intro i hi
      rw [List.foldl_cons] at hfold
      cases hhead : bhksIndicatorCandidate? f d indicator with
      | none =>
          have hnone := bhksIndicatorCandidatesStep_fold_none f d indicators
          simp [bhksIndicatorCandidatesStep, hhead, hnone] at hfold
      | some pair =>
          rcases pair with ⟨candidate, quotient⟩
          have hnext :
              indicators.foldl (bhksIndicatorCandidatesStep f d)
                  (some (acc.push candidate)) = some candidates := by
            simpa [bhksIndicatorCandidatesStep, hhead] using hfold
          cases i with
          | zero =>
              have hprefix :
                  candidates.getD acc.size 0 =
                    (acc.push candidate).getD acc.size 0 :=
                bhksIndicatorCandidatesStep_fold_preserves_prefix
                  f d indicators (acc.push candidate) candidates hnext acc.size
                  (by simp)
              have hcandidate : candidates.getD acc.size 0 = candidate := by
                simpa [array_getD_push_size] using hprefix
              refine ⟨quotient, ?_⟩
              rw [Nat.add_zero, hcandidate]
              simpa using hhead
          | succ i =>
              have hi_tail : i < indicators.length := by
                simpa using hi
              rcases ih (acc.push candidate) candidates hnext i hi_tail with
                ⟨quotient, hcandidate⟩
              refine ⟨quotient, ?_⟩
              simpa [List.getD_cons_succ, Array.size_push, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using hcandidate

/--
Per-index extraction from a successful `bhksIndicatorCandidates?` fold.  The
fold records only candidate factors, not quotients, so the quotient is returned
existentially for the corresponding successful `bhksIndicatorCandidate?` call.
-/
theorem bhksIndicatorCandidates?_getD_candidate
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    ∀ i, i < indicators.size →
      ∃ quotient,
        bhksIndicatorCandidate? f d (indicators.getD i #[]) =
          some (candidates.getD i 0, quotient) := by
  intro i hi
  unfold bhksIndicatorCandidates? at h
  rw [← Array.foldl_toList] at h
  have hcandidate :=
    bhksIndicatorCandidatesStep_fold_getD_candidate
      f d indicators.toList #[] candidates h i (by simpa using hi)
  rcases hcandidate with ⟨quotient, hcandidate⟩
  refine ⟨quotient, ?_⟩
  have hindicator :
      indicators.toList.getD i #[] = indicators.getD i #[] :=
    array_toList_getD indicators i #[]
  simpa [hindicator] using hcandidate

private inductive BhksRecoveryResult where
  | success (candidates : Array ZPoly)
  | degenerate
  | candidateFailure
  | productMismatch (candidates : Array ZPoly)
deriving DecidableEq

private def BhksRecoveryResult.toOption : BhksRecoveryResult → Option (Array ZPoly)
  | .success candidates => some candidates
  | .degenerate => none
  | .candidateFailure => none
  | .productMismatch _ => none

private def BhksRecoveryResult.isReconstructionFailure : BhksRecoveryResult → Bool
  | .success _ => false
  | .degenerate => false
  | .candidateFailure => true
  | .productMismatch _ => true

private def BhksRecoveryResult.isLatticeFailure : BhksRecoveryResult → Bool
  | .success _ => false
  | .degenerate => true
  | .candidateFailure => false
  | .productMismatch _ => false

/--
Run the fixed-precision BHKS recovery computation.

This executable glue builds the CLD lattice for the lifted factors, runs LLL
plus the Gram-Schmidt cut, extracts BHKS Lemma 3.3 equivalence-class
indicators by RREF, reconstructs every indicated candidate by centred lifting,
and accepts only when the verified candidates multiply back to `f`.

The lattice method runs the fused `bhksRecoverClassifiedWithAllOnes` instead,
sharing one lattice build between the classification and the all-ones certificate;
keep the two bodies in sync; `bhksRecoverClassifiedWithAllOnes_fst` fails to
build if they drift.
-/
private def bhksRecoverClassified (f : ZPoly) (d : LiftData) : BhksRecoveryResult :=
  let L := bhksLatticeBasis f d.p d.k d.liftedFactors
  if hrows : 1 ≤ L.factorCount + L.coeffWidth then
    let projected := bhksProjectedRows L hrows
    let indicators := bhksEquivalenceClassIndicators projected
    if bhksDegenerateIndicatorPartition projected indicators then
      .degenerate
    else
      match bhksIndicatorCandidates? f d indicators with
      | none => .candidateFailure
      | some candidates =>
          if Array.polyProduct candidates == f then
            .success candidates
          else
            .productMismatch candidates
  else
    .degenerate

/-- Return the factors recovered by the lattice computation when all checks succeed. -/
def bhksRecover? (f : ZPoly) (d : LiftData) : Option (Array ZPoly) :=
  (bhksRecoverClassified f d).toOption

/--
Fused BHKS recovery step: run the CLD lattice / LLL / RREF-indicator computation
**once** and return both the `bhksRecoverClassified` classification and the
single-all-ones partition flag.

The lattice method's `.degenerate` arm needs the all-ones flag to certify
irreducibility, but recomputing it through `bhksSingleAllOnesPartition` rebuilds
the whole Hensel-lift/CLD-lattice/LLL/indicator computation that the classifier
already ran, adding roughly 1.5–2× to the step that dominates irreducible
inputs. This
def shares that pass: `bhksRecoverClassifiedWithAllOnes_fst` pins `.1` to
`bhksRecoverClassified` and `bhksRecoverClassifiedWithAllOnes_snd` (in
`Factorization`) pins `.2` to `bhksSingleAllOnesPartition`, so the loop reads
both off one lattice build with no change to either public surface.
-/
private def bhksRecoverClassifiedWithAllOnes (f : ZPoly) (d : LiftData) :
    BhksRecoveryResult × Bool :=
  let L := bhksLatticeBasis f d.p d.k d.liftedFactors
  if hrows : 1 ≤ L.factorCount + L.coeffWidth then
    let projected := bhksProjectedRows L hrows
    let indicators := bhksEquivalenceClassIndicators projected
    let allOnes := !indicators.isEmpty && !projected.projectedRows.isEmpty &&
      indicators.size == 1 && bhksIndicatorAllOnes projected.factorCount (indicators.getD 0 #[])
    let result :=
      if bhksDegenerateIndicatorPartition projected indicators then
        BhksRecoveryResult.degenerate
      else
        match bhksIndicatorCandidates? f d indicators with
        | none => .candidateFailure
        | some candidates =>
            if Array.polyProduct candidates == f then
              .success candidates
            else
              .productMismatch candidates
    (result, allOnes)
  else
    (.degenerate, false)

/-- The fused recovery step's classification equals the standalone classifier:
the control flow is identical, only the paired all-ones flag is extra. -/
private theorem bhksRecoverClassifiedWithAllOnes_fst (f : ZPoly) (d : LiftData) :
    (bhksRecoverClassifiedWithAllOnes f d).1 = bhksRecoverClassified f d := by
  rw [bhksRecoverClassifiedWithAllOnes, bhksRecoverClassified]
  by_cases hrows :
      1 ≤ (bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount +
        (bhksLatticeBasis f d.p d.k d.liftedFactors).coeffWidth
  · simp only [dif_pos hrows]
  · simp only [dif_neg hrows]

/--
If the executable BHKS recovery guards all pass, `bhksRecover?` returns the
verified candidate array.

This lemma is the public proof-facing surface for callers that should not
unfold the private failure classifier used by the executable.
-/
theorem bhksRecover?_eq_some_of_checks
    (f : ZPoly) (d : LiftData) {candidates : Array ZPoly}
    (hrows : 1 ≤ (bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount +
      (bhksLatticeBasis f d.p d.k d.liftedFactors).coeffWidth)
    (hnondeg :
      bhksDegenerateIndicatorPartition
          (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows
              (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)) = false)
    (hcand :
      bhksIndicatorCandidates? f d
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows
              (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)) =
        some candidates)
    (hprod : Array.polyProduct candidates = f) :
    bhksRecover? f d = some candidates := by
  unfold bhksRecover?
  rw [bhksRecoverClassified]
  have hproductCheck : (Array.polyProduct candidates == f) = true := by
    simpa [beq_iff_eq] using hprod
  simp only [dif_pos hrows, hnondeg, Bool.false_eq_true, if_false, hcand,
    hproductCheck, if_true, BhksRecoveryResult.toOption]

private def bhksIndicatorGuardLift : LiftData :=
  { p := 5
    p_pos := by decide
    k := 2
    liftedFactors := bhksGuardFactors }

#guard bhksIndicatorCandidate? cldGuardF bhksIndicatorGuardLift #[1, 0] =
  some (DensePoly.ofCoeffs #[-2, 1], DensePoly.ofCoeffs #[-3, 1])
#guard bhksIndicatorCandidate? cldGuardF bhksIndicatorGuardLift #[0, 0] = none
#guard bhksIndicatorCandidate? cldGuardF bhksIndicatorGuardLift #[2, 0] = none
#guard (bhksIndicatorCandidate? cldGuardF bhksIndicatorGuardLift #[0, 1]).map Prod.snd =
  some (DensePoly.ofCoeffs #[-2, 1])

#guard bhksRecover? cldGuardF bhksIndicatorGuardLift =
  some bhksGuardFactors
#guard bhksRecoverClassified cldGuardF bhksIndicatorGuardLift =
  .success bhksGuardFactors

private def bhksDegenerateRecoverLift : LiftData :=
  { p := 5
    p_pos := by decide
    k := 2
    liftedFactors := #[DensePoly.ofCoeffs #[1]] }

#guard bhksRecover? cldGuardF bhksDegenerateRecoverLift = none
#guard bhksRecoverClassified cldGuardF bhksDegenerateRecoverLift =
  .degenerate
#guard (bhksRecoverClassified cldGuardF bhksDegenerateRecoverLift).isLatticeFailure
#guard !(bhksRecoverClassified cldGuardF bhksDegenerateRecoverLift).isReconstructionFailure

private def bhksFailedDivisionRecoverLift : LiftData :=
  { p := 5
    p_pos := by decide
    k := 2
    liftedFactors := #[DensePoly.ofCoeffs #[-2, 1], DensePoly.ofCoeffs #[-4, 1]] }

#guard bhksIndicatorCandidate? cldGuardF bhksFailedDivisionRecoverLift #[0, 1] = none
#guard bhksRecover? cldGuardF bhksFailedDivisionRecoverLift = none
#guard bhksRecoverClassified cldGuardF bhksFailedDivisionRecoverLift =
  .candidateFailure
#guard (bhksRecoverClassified cldGuardF bhksFailedDivisionRecoverLift).isReconstructionFailure
#guard !(bhksRecoverClassified cldGuardF bhksFailedDivisionRecoverLift).isLatticeFailure

private def bhksProductMismatchRecoverLift : LiftData :=
  { p := 5
    k := 2
    liftedFactors := #[DensePoly.ofCoeffs #[-2, 1]]
    p_pos := by decide }

#guard bhksIndicatorCandidate? cldGuardF bhksProductMismatchRecoverLift #[1] =
  some (DensePoly.ofCoeffs #[-2, 1], DensePoly.ofCoeffs #[-3, 1])
#guard BhksRecoveryResult.toOption
    (.productMismatch #[DensePoly.ofCoeffs #[-2, 1]]) = none

end Hex
