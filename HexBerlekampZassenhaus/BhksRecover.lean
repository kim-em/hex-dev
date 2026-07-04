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

public import HexBerlekampZassenhaus.BhksCandidates
public meta import HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.ReassemblyProofs
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.BhksCandidates

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
This module collects `bhksRecover?`/`coreRecover?` and the core-recovery correctness proofs.
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
Run the fixed-precision BHKS recovery pipeline.

This executable glue builds the CLD lattice for the lifted factors, runs LLL
plus the Gram-Schmidt cut, extracts BHKS Lemma 3.3 equivalence-class
indicators by RREF, reconstructs every indicated candidate by centred lifting,
and accepts only when the verified candidates multiply back to `f`.
-/
private def bhksRecoverClassified (f : ZPoly) (d : LiftData) : BhksRecoveryResult :=
  -- The CLD lattice runs in the monic (`M2`, `x ↦ x/ℓf`) coordinate: `d` is a
  -- `toMonicLiftData`, so `d.liftedFactors` are Hensel factors of
  -- `(ZPoly.toMonic f).monic`, and the CLD columns must be computed against
  -- that same monic transform (for monic `f` this is `f` itself).  Building
  -- them against `f` would mix coordinates and empty the columns of meaning
  -- whenever `leadingCoeff f ≢ 1 (mod p)` (#8519).
  let L := bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors
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

def bhksRecover? (f : ZPoly) (d : LiftData) : Option (Array ZPoly) :=
  (bhksRecoverClassified f d).toOption

/--
If the executable BHKS recovery guards all pass, `bhksRecover?` returns the
verified candidate array.

This lemma is the public proof-facing surface for callers that should not
unfold the private failure classifier used by the executable.
-/
theorem bhksRecover?_eq_some_of_checks
    (f : ZPoly) (d : LiftData) {candidates : Array ZPoly}
    (hrows : 1 ≤ (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors).factorCount +
      (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors).coeffWidth)
    (hnondeg :
      bhksDegenerateIndicatorPartition
          (bhksProjectedRows (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors) hrows)
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows
              (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors) hrows)) = false)
    (hcand :
      bhksIndicatorCandidates? f d
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows
              (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors) hrows)) =
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

/--
Reconstruct and verify one BHKS equivalence-class indicator in `core`'s own
coordinate (van Hoeij `M1`).

Mirrors `bhksIndicatorCandidate?`, but the lifted factors here are the monic
factors of the leading-coefficient-faithful `monicTarget` (`core · ℓf⁻¹ mod
p^k`), so the integer factor of `core` is recovered with **no** `dilate`: scale
the selected lifted product by `ℓf = leadingCoeff f`, reduce modulo `p^k`,
centre-lift, and take the primitive part.  This is the executable image of the
M1 recovery formula `RecoveredAtLiftM1.candidate_eq`
(`primitivePart (centeredLiftPoly ((ℓf · ∏ selected) % p^k))`), with the outer
sign normalisation that makes the candidate canonical for the division check.
-/
def bhksIndicatorCandidateCore?
    (f : ZPoly) (d : LiftData) (indicator : Array Int) : Option (ZPoly × ZPoly) :=
  match bhksIndicatorSelectedFactors d.liftedFactors indicator with
  | none => none
  | some selected =>
      let modulus := liftModulus d
      let candidate := normalizeFactorSign <|
        ZPoly.primitivePart <|
          centeredLiftPoly
            (ZPoly.reduceModPow
              (DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected))
              d.p d.k)
            modulus
      if shouldRecordPolynomialFactor candidate then
        match exactQuotient? f candidate with
        | some quotient => some (candidate, quotient)
        | none => none
      else
        none

private def bhksIndicatorCandidatesCoreStep
    (f : ZPoly) (d : LiftData) :
    Option (Array ZPoly) → Array Int → Option (Array ZPoly)
  | none, _ => none
  | some candidates, indicator =>
      match bhksIndicatorCandidateCore? f d indicator with
      | some candidate => some (candidates.push candidate.1)
      | none => none

/-- Core-coordinate analogue of `bhksIndicatorCandidates?`: folds
`bhksIndicatorCandidateCore?` over the indicator vectors, pushing each verified
`M1` candidate factor onto the accumulator and short-circuiting to `none` on the
first reconstruction failure. -/
def bhksIndicatorCandidatesCore?
    (f : ZPoly) (d : LiftData) (indicators : Array (Array Int)) :
    Option (Array ZPoly) :=
  indicators.foldl (bhksIndicatorCandidatesCoreStep f d) (some #[])

/--
Core-coordinate (van Hoeij `M1`) analogue of `bhksRecoverClassified`.

Runs the same fixed-precision BHKS recovery pipeline — CLD lattice, LLL plus the
Gram-Schmidt cut, RREF equivalence-class indicators, product check — but
reconstructs each indicated candidate through `bhksIndicatorCandidateCore?`,
which lifts `monicTarget`'s monic factors back into `core`'s own coordinate with
no `dilate`.  The lattice basis and indicator partition machinery is shared
verbatim; only the per-indicator candidate shape differs.
-/
private def bhksRecoverClassifiedCore (f : ZPoly) (d : LiftData) : BhksRecoveryResult :=
  let L := bhksLatticeBasis f d.p d.k d.liftedFactors
  if hrows : 1 ≤ L.factorCount + L.coeffWidth then
    let projected := bhksProjectedRows L hrows
    let indicators := bhksEquivalenceClassIndicators projected
    if bhksDegenerateIndicatorPartition projected indicators then
      .degenerate
    else
      match bhksIndicatorCandidatesCore? f d indicators with
      | none => .candidateFailure
      | some candidates =>
          if Array.polyProduct candidates == f then
            .success candidates
          else
            .productMismatch candidates
  else
    .degenerate

/-- Core-coordinate (van Hoeij `M1`) fast recovery: the recovered factor array
on success, `none` on any failure class.  Coordinate-faithful counterpart to
`bhksRecover?`, consuming `coreLiftData` rather than `toMonicLiftData`. -/
def coreRecover? (f : ZPoly) (d : LiftData) : Option (Array ZPoly) :=
  (bhksRecoverClassifiedCore f d).toOption

private theorem bhksIndicatorCandidateCore?_normalizeFactorSign
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidateCore? f d indicator = some (candidate, quotient)) :
    normalizeFactorSign candidate = candidate := by
  unfold bhksIndicatorCandidateCore? at h
  cases hselected : bhksIndicatorSelectedFactors d.liftedFactors indicator with
  | none =>
      simp [hselected] at h
  | some selected =>
      simp only [hselected] at h
      let modulus := liftModulus d
      let candidate0 :=
        ZPoly.primitivePart
          (centeredLiftPoly
            (ZPoly.reduceModPow
              (DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected))
              d.p d.k)
            modulus)
      let candidate' := normalizeFactorSign candidate0
      change
        (if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? f candidate' with
          | some quotient => some (candidate', quotient)
          | none => none
        else
          none) = some (candidate, quotient) at h
      by_cases hrecord : shouldRecordPolynomialFactor candidate'
      · rw [if_pos hrecord] at h
        cases hquot : exactQuotient? f candidate' with
        | none =>
            simp [hquot] at h
        | some quotient' =>
            simp [hquot] at h
            rcases h with ⟨hcandidate, _hquotient⟩
            subst candidate
            exact normalizeFactorSign_idem candidate0
      · rw [if_neg hrecord] at h
        simp at h

private theorem bhksIndicatorCandidateCore?_shouldRecord
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidateCore? f d indicator = some (candidate, quotient)) :
    shouldRecordPolynomialFactor candidate = true := by
  unfold bhksIndicatorCandidateCore? at h
  cases hselected : bhksIndicatorSelectedFactors d.liftedFactors indicator with
  | none =>
      simp [hselected] at h
  | some selected =>
      simp only [hselected] at h
      let modulus := liftModulus d
      let candidate0 :=
        ZPoly.primitivePart
          (centeredLiftPoly
            (ZPoly.reduceModPow
              (DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected))
              d.p d.k)
            modulus)
      let candidate' := normalizeFactorSign candidate0
      change
        (if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? f candidate' with
          | some quotient => some (candidate', quotient)
          | none => none
        else
          none) = some (candidate, quotient) at h
      by_cases hrecord : shouldRecordPolynomialFactor candidate'
      · rw [if_pos hrecord] at h
        cases hquot : exactQuotient? f candidate' with
        | none =>
            simp [hquot] at h
        | some quotient' =>
            simp [hquot] at h
            rcases h with ⟨hcandidate, _hquotient⟩
            subst candidate
            exact hrecord
      · rw [if_neg hrecord] at h
        simp at h

/--
A successful Core indicator candidate divides `f`. As with the M2
`bhksIndicatorCandidate?`, the executable only returns `some (candidate, _)`
after `exactQuotient? f candidate` succeeds, so the candidate is a verified
integer divisor of `f`.
-/
theorem bhksIndicatorCandidateCore?_dvd
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidateCore? f d indicator = some (candidate, quotient)) :
    candidate ∣ f := by
  unfold bhksIndicatorCandidateCore? at h
  cases hselected : bhksIndicatorSelectedFactors d.liftedFactors indicator with
  | none =>
      simp [hselected] at h
  | some selected =>
      simp only [hselected] at h
      let modulus := liftModulus d
      let candidate0 :=
        ZPoly.primitivePart
          (centeredLiftPoly
            (ZPoly.reduceModPow
              (DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected))
              d.p d.k)
            modulus)
      let candidate' := normalizeFactorSign candidate0
      change
        (if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? f candidate' with
          | some quotient => some (candidate', quotient)
          | none => none
        else
          none) = some (candidate, quotient) at h
      by_cases hrecord : shouldRecordPolynomialFactor candidate'
      · rw [if_pos hrecord] at h
        cases hquot : exactQuotient? f candidate' with
        | none =>
            simp [hquot] at h
        | some quotient' =>
            simp [hquot] at h
            rcases h with ⟨hcandidate, hquotient⟩
            subst candidate
            subst quotient
            have hmul : quotient' * candidate' = f := exactQuotient?_product hquot
            refine ⟨quotient', ?_⟩
            rw [DensePoly.mul_comm_poly (S := Int)]
            exact hmul.symm
      · rw [if_neg hrecord] at h
        simp at h

/-- A successful Core indicator candidate has nonnegative leading coefficient:
the final `normalizeFactorSign` layer is a fixed point on the candidate, so the
candidate inherits the `≥ 0` leading-coefficient guarantee of
`normalizeFactorSign`. -/
private theorem bhksIndicatorCandidateCore?_leadingCoeff_nonneg
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidateCore? f d indicator = some (candidate, quotient)) :
    0 ≤ DensePoly.leadingCoeff candidate := by
  have hnorm := bhksIndicatorCandidateCore?_normalizeFactorSign h
  have hsign := normalizeFactorSign_leadingCoeff_nonneg candidate
  rwa [hnorm] at hsign

/-- A successful Core indicator candidate is primitive: the candidate equals
`normalizeFactorSign (ZPoly.primitivePart _)`, and `shouldRecord = true` forces
the primitive part to be nonzero, hence the centred lift has nonzero content and
its primitive part is genuinely primitive. -/
theorem bhksIndicatorCandidateCore?_primitive
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidateCore? f d indicator = some (candidate, quotient)) :
    ZPoly.Primitive candidate := by
  unfold bhksIndicatorCandidateCore? at h
  cases hselected : bhksIndicatorSelectedFactors d.liftedFactors indicator with
  | none =>
      simp [hselected] at h
  | some selected =>
      simp only [hselected] at h
      let modulus := liftModulus d
      let inner :=
        centeredLiftPoly
          (ZPoly.reduceModPow
            (DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected))
            d.p d.k)
          modulus
      let candidate0 := ZPoly.primitivePart inner
      let candidate' := normalizeFactorSign candidate0
      change
        (if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? f candidate' with
          | some quotient => some (candidate', quotient)
          | none => none
        else
          none) = some (candidate, quotient) at h
      by_cases hrecord : shouldRecordPolynomialFactor candidate'
      · rw [if_pos hrecord] at h
        cases hquot : exactQuotient? f candidate' with
        | none =>
            simp [hquot] at h
        | some quotient' =>
            simp [hquot] at h
            rcases h with ⟨hcandidate, _hquotient⟩
            subst candidate
            have hcand'_ne : candidate' ≠ 0 := by
              intro hzero
              rw [hzero] at hrecord
              unfold shouldRecordPolynomialFactor at hrecord
              simp at hrecord
            have hcand0_ne : candidate0 ≠ 0 := by
              intro hzero
              apply hcand'_ne
              show normalizeFactorSign candidate0 = 0
              rw [hzero]
              unfold normalizeFactorSign
              have hlc :
                  ¬ DensePoly.leadingCoeff (0 : ZPoly) < 0 := by
                simp
              rw [if_neg hlc]
            have hinner_content_ne : ZPoly.content inner ≠ 0 := by
              intro hzero
              apply hcand0_ne
              show DensePoly.primitivePart inner = 0
              exact
                DensePoly.primitivePart_eq_zero_of_content_eq_zero inner
                  (by simpa [ZPoly.content] using hzero)
            have hprim_cand0 : ZPoly.Primitive candidate0 :=
              ZPoly.primitivePart_primitive inner hinner_content_ne
            exact normalizeFactorSign_primitive _ hprim_cand0
      · rw [if_neg hrecord] at h
        simp at h

/-- A successful Core indicator candidate has positive degree: it is primitive
with nonnegative leading coefficient and is not a unit, so it cannot be a
constant polynomial. -/
private theorem bhksIndicatorCandidateCore?_positive_degree
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidateCore? f d indicator = some (candidate, quotient)) :
    0 < candidate.degree?.getD 0 := by
  have hrecord := bhksIndicatorCandidateCore?_shouldRecord h
  have hprim := bhksIndicatorCandidateCore?_primitive h
  have hsign := bhksIndicatorCandidateCore?_leadingCoeff_nonneg h
  have hne : candidate ≠ 0 := by
    intro hzero
    rw [hzero] at hrecord
    unfold shouldRecordPolynomialFactor at hrecord
    simp at hrecord
  have hne_one : candidate ≠ 1 := by
    intro hone
    rw [hone] at hrecord
    unfold shouldRecordPolynomialFactor at hrecord
    simp at hrecord
  have hne_neg : candidate ≠ DensePoly.C (-1 : Int) := by
    intro hneg
    rw [hneg] at hrecord
    unfold shouldRecordPolynomialFactor at hrecord
    simp at hrecord
  have hsize_pos : 0 < candidate.size := by
    rcases Nat.lt_or_ge 0 candidate.size with hpos | _hle
    · exact hpos
    · have hsz : candidate.size = 0 := by omega
      have hcand_zero : candidate = 0 := by
        apply DensePoly.ext_coeff
        intro n
        rw [DensePoly.coeff_zero]
        exact DensePoly.coeff_eq_zero_of_size_le candidate (by omega)
      exact False.elim (hne hcand_zero)
  have hsize_ge_two : 2 ≤ candidate.size := by
    rcases Nat.lt_or_ge 1 candidate.size with hge | _hle
    · omega
    · have hsize_one : candidate.size = 1 := by omega
      have hcandidate_eq : candidate = DensePoly.C (candidate.coeff 0) := by
        apply DensePoly.ext_coeff
        intro n
        cases n with
        | zero =>
            rw [DensePoly.coeff_C]
            simp
        | succ n =>
            rw [DensePoly.coeff_C, if_neg (Nat.succ_ne_zero n)]
            exact DensePoly.coeff_eq_zero_of_size_le candidate (by omega)
      have hprim_C :
          DensePoly.content (DensePoly.C (candidate.coeff 0)) = 1 := by
        have hcontent_eq : DensePoly.content candidate
            = DensePoly.content (DensePoly.C (candidate.coeff 0)) :=
          congrArg DensePoly.content hcandidate_eq
        exact hcontent_eq.symm.trans hprim
      have hcontent_C_eq :
          DensePoly.content (DensePoly.C (candidate.coeff 0))
            = Int.ofNat (candidate.coeff 0).natAbs :=
        DensePoly.content_C (candidate.coeff 0)
      have hnat_int :
          Int.ofNat (candidate.coeff 0).natAbs = 1 := by
        rw [← hcontent_C_eq]
        exact hprim_C
      have hnat : (candidate.coeff 0).natAbs = 1 := by
        exact Int.ofNat.inj hnat_int
      have hc_cases :
          candidate.coeff 0 = ↑(1 : Nat) ∨ candidate.coeff 0 = -↑(1 : Nat) :=
        Int.natAbs_eq_iff.mp hnat
      exfalso
      rcases hc_cases with hpos | hneg
      · apply hne_one
        rw [hcandidate_eq]
        show DensePoly.C (candidate.coeff 0) = DensePoly.C 1
        rw [hpos]
        rfl
      · apply hne_neg
        rw [hcandidate_eq]
        show DensePoly.C (candidate.coeff 0) = DensePoly.C (-1)
        rw [hneg]
        rfl
  have hne_size : candidate.size ≠ 0 := by omega
  have hdeg_eq :
      (DensePoly.degree? candidate).getD 0 = candidate.size - 1 := by
    unfold DensePoly.degree?
    rw [dif_neg hne_size]
    rfl
  show 0 < (DensePoly.degree? candidate).getD 0
  rw [hdeg_eq]
  omega

private theorem bhksIndicatorCandidatesCoreStep_fold_none
    (f : ZPoly) (d : LiftData) (indicators : List (Array Int)) :
    List.foldl (bhksIndicatorCandidatesCoreStep f d) none indicators = none := by
  induction indicators with
  | nil => rfl
  | cons indicator indicators ih =>
      rw [List.foldl_cons]
      simpa [bhksIndicatorCandidatesCoreStep] using ih

private theorem bhksIndicatorCandidatesCoreStep_fold_all_of_candidate
    (P : ZPoly → Prop)
    (f : ZPoly) (d : LiftData)
    (hcandidate :
      ∀ {indicator candidate quotient},
        bhksIndicatorCandidateCore? f d indicator = some (candidate, quotient) →
          P candidate) :
    ∀ (indicators : List (Array Int)) (acc candidates : Array ZPoly),
      (∀ factor ∈ acc.toList, P factor) →
        List.foldl (bhksIndicatorCandidatesCoreStep f d) (some acc) indicators =
            some candidates →
          ∀ factor ∈ candidates.toList, P factor
  | [], acc, candidates, hacc, hfold => by
      simp at hfold
      cases hfold
      exact hacc
  | indicator :: indicators, acc, candidates, hacc, hfold => by
      rw [List.foldl_cons] at hfold
      cases hhead : bhksIndicatorCandidateCore? f d indicator with
      | none =>
          have hnone :=
            bhksIndicatorCandidatesCoreStep_fold_none f d indicators
          simp [bhksIndicatorCandidatesCoreStep, hhead, hnone] at hfold
      | some pair =>
          rcases pair with ⟨candidate, quotient⟩
          have hnext :
              List.foldl (bhksIndicatorCandidatesCoreStep f d) (some (acc.push candidate))
                  indicators = some candidates := by
            simpa [bhksIndicatorCandidatesCoreStep, hhead] using hfold
          have hacc_push :
              ∀ factor ∈ (acc.push candidate).toList, P factor := by
            intro factor hmem
            rw [Array.toList_push] at hmem
            simp only [List.mem_append, List.mem_singleton] at hmem
            cases hmem with
            | inl hacc_mem => exact hacc factor hacc_mem
            | inr hfactor =>
                rw [hfactor]
                exact hcandidate hhead
          exact
            bhksIndicatorCandidatesCoreStep_fold_all_of_candidate
              P f d hcandidate indicators (acc.push candidate) candidates
              hacc_push hnext

private theorem bhksIndicatorCandidatesCore?_all_of_candidate
    (P : ZPoly → Prop)
    (f : ZPoly) (d : LiftData)
    (hcandidate :
      ∀ {indicator candidate quotient},
        bhksIndicatorCandidateCore? f d indicator = some (candidate, quotient) →
          P candidate)
    {indicators : Array (Array Int)} {candidates : Array ZPoly}
    (h : bhksIndicatorCandidatesCore? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, P factor := by
  unfold bhksIndicatorCandidatesCore? at h
  rw [← Array.foldl_toList] at h
  exact
    bhksIndicatorCandidatesCoreStep_fold_all_of_candidate
      P f d hcandidate indicators.toList #[] candidates (by simp) h

private theorem bhksIndicatorCandidatesCore?_normalizeFactorSign
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidatesCore? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, normalizeFactorSign factor = factor :=
  bhksIndicatorCandidatesCore?_all_of_candidate
    (fun factor => normalizeFactorSign factor = factor)
    f d (fun hcandidate => bhksIndicatorCandidateCore?_normalizeFactorSign hcandidate) h

private theorem bhksIndicatorCandidatesCore?_shouldRecord
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidatesCore? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, shouldRecordPolynomialFactor factor = true :=
  bhksIndicatorCandidatesCore?_all_of_candidate
    (fun factor => shouldRecordPolynomialFactor factor = true)
    f d (fun hcandidate => bhksIndicatorCandidateCore?_shouldRecord hcandidate) h

/-- Every candidate emitted by `bhksIndicatorCandidatesCore?` divides the input
polynomial; the Core-coordinate analogue of `bhksIndicatorCandidates?_dvd`. -/
theorem bhksIndicatorCandidatesCore?_dvd
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidatesCore? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, factor ∣ f :=
  bhksIndicatorCandidatesCore?_all_of_candidate
    (fun factor => factor ∣ f)
    f d (fun hcandidate => bhksIndicatorCandidateCore?_dvd hcandidate) h

/-- Every candidate emitted by `bhksIndicatorCandidatesCore?` is primitive; the
Core-coordinate analogue of `bhksIndicatorCandidates?_primitive`. -/
theorem bhksIndicatorCandidatesCore?_primitive
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidatesCore? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, ZPoly.Primitive factor :=
  bhksIndicatorCandidatesCore?_all_of_candidate
    (fun factor => ZPoly.Primitive factor)
    f d (fun hcandidate => bhksIndicatorCandidateCore?_primitive hcandidate) h

/-- Every candidate emitted by `bhksIndicatorCandidatesCore?` has nonnegative
leading coefficient; the Core-coordinate analogue of
`bhksIndicatorCandidates?_leadingCoeff_nonneg`. -/
theorem bhksIndicatorCandidatesCore?_leadingCoeff_nonneg
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidatesCore? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, 0 ≤ DensePoly.leadingCoeff factor :=
  bhksIndicatorCandidatesCore?_all_of_candidate
    (fun factor => 0 ≤ DensePoly.leadingCoeff factor)
    f d (fun hcandidate => bhksIndicatorCandidateCore?_leadingCoeff_nonneg hcandidate) h

/-- Every candidate emitted by `bhksIndicatorCandidatesCore?` has positive degree;
the Core-coordinate analogue of `bhksIndicatorCandidates?_positive_degree`. -/
theorem bhksIndicatorCandidatesCore?_positive_degree
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidatesCore? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, 0 < factor.degree?.getD 0 :=
  bhksIndicatorCandidatesCore?_all_of_candidate
    (fun factor => 0 < factor.degree?.getD 0)
    f d (fun hcandidate => bhksIndicatorCandidateCore?_positive_degree hcandidate) h

private theorem bhksIndicatorCandidatesCoreStep_fold_size_eq
    (f : ZPoly) (d : LiftData) :
    ∀ (indicators : List (Array Int)) (acc candidates : Array ZPoly),
      List.foldl (bhksIndicatorCandidatesCoreStep f d) (some acc) indicators =
          some candidates →
        candidates.size = acc.size + indicators.length
  | [], acc, candidates, hfold => by
      simp at hfold
      cases hfold
      simp
  | indicator :: indicators, acc, candidates, hfold => by
      rw [List.foldl_cons] at hfold
      cases hhead : bhksIndicatorCandidateCore? f d indicator with
      | none =>
          have hnone :=
            bhksIndicatorCandidatesCoreStep_fold_none f d indicators
          simp [bhksIndicatorCandidatesCoreStep, hhead, hnone] at hfold
      | some pair =>
          rcases pair with ⟨candidate, quotient⟩
          have hnext :
              List.foldl (bhksIndicatorCandidatesCoreStep f d)
                  (some (acc.push candidate)) indicators = some candidates := by
            simpa [bhksIndicatorCandidatesCoreStep, hhead] using hfold
          have ih :=
            bhksIndicatorCandidatesCoreStep_fold_size_eq f d indicators
              (acc.push candidate) candidates hnext
          rw [ih, Array.size_push, List.length_cons]
          omega

/--
A successful Core indicator-candidate fold produces a candidate array of the
same size as the input indicator array.  The Core-coordinate analogue of
`bhksIndicatorCandidates?_size_eq`, needed by the size wrapper consumers.
-/
theorem bhksIndicatorCandidatesCore?_size_eq
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidatesCore? f d indicators = some candidates) :
    candidates.size = indicators.size := by
  unfold bhksIndicatorCandidatesCore? at h
  rw [← Array.foldl_toList] at h
  have hfold :=
    bhksIndicatorCandidatesCoreStep_fold_size_eq f d indicators.toList #[] candidates h
  simpa [Array.length_toList] using hfold

private theorem bhksIndicatorCandidatesCoreStep_fold_eq_some_append
    (f : ZPoly) (d : LiftData) :
    ∀ (indicators : List (Array Int)) (candidates : List ZPoly) (acc : Array ZPoly),
      (hlength : candidates.length = indicators.length) →
      (∀ i (hi : i < indicators.length),
        ∃ quotient,
          bhksIndicatorCandidateCore? f d indicators[i] =
            some (candidates[i]'(by rw [hlength]; exact hi), quotient)) →
      List.foldl (bhksIndicatorCandidatesCoreStep f d) (some acc) indicators =
        some (acc ++ candidates.toArray)
  | [], candidates, acc, hlength, _ => by
      have hcandidates : candidates = [] := List.eq_nil_of_length_eq_zero hlength
      subst hcandidates
      apply congrArg some
      rw [← Array.toList_inj]
      simp
  | indicator :: indicators, candidates, acc, hlength, hcandidate => by
      cases candidates with
      | nil => simp at hlength
      | cons candidate candidates =>
          have hhead :
              ∃ quotient,
                bhksIndicatorCandidateCore? f d indicator =
                  some (candidate, quotient) := by
            simpa using hcandidate 0 (Nat.succ_pos _)
          rcases hhead with ⟨quotient, hhead⟩
          have hlength_tail : candidates.length = indicators.length := by
            simpa using Nat.succ.inj hlength
          have htail :
              ∀ i (hi : i < indicators.length),
                ∃ quotient,
                  bhksIndicatorCandidateCore? f d indicators[i] =
                    some (candidates[i]'(by rw [hlength_tail]; exact hi), quotient) := by
            intro i hi
            simpa using hcandidate (i + 1) (Nat.succ_lt_succ hi)
          calc
            List.foldl (bhksIndicatorCandidatesCoreStep f d) (some acc)
                (indicator :: indicators)
                =
              List.foldl (bhksIndicatorCandidatesCoreStep f d)
                (some (acc.push candidate)) indicators := by
                  simp [bhksIndicatorCandidatesCoreStep, hhead]
            _ = some (acc.push candidate ++ candidates.toArray) := by
                  exact bhksIndicatorCandidatesCoreStep_fold_eq_some_append
                    f d indicators candidates (acc.push candidate) hlength_tail htail
            _ = some (acc ++ (candidate :: candidates).toArray) := by
                  apply congrArg some
                  rw [← Array.toList_inj]
                  simp [Array.toList_append]

/--
Assemble the Core indicator-candidate fold from per-indicator reconstruction
facts.  The Core-coordinate (van Hoeij `M1`) analogue of
`bhksIndicatorCandidates?_eq_some_of_getD`: with a size agreement and one
quotient witness for each indicator row, the executable Core fold returns the
requested candidate array.
-/
theorem bhksIndicatorCandidatesCore?_eq_some_of_getD
    (f : ZPoly) (d : LiftData)
    (indicators : Array (Array Int)) (candidates : Array ZPoly)
    (hsize : candidates.size = indicators.size)
    (hcandidate :
      ∀ i, i < indicators.size →
        ∃ quotient,
          bhksIndicatorCandidateCore? f d (indicators.getD i #[]) =
            some (candidates.getD i 0, quotient)) :
    bhksIndicatorCandidatesCore? f d indicators = some candidates := by
  unfold bhksIndicatorCandidatesCore?
  rw [← Array.foldl_toList]
  have hlength : candidates.toList.length = indicators.toList.length := by
    simpa [Array.length_toList] using hsize
  have hcandidate_list :
      ∀ i (hi : i < indicators.toList.length),
        ∃ quotient,
          bhksIndicatorCandidateCore? f d indicators.toList[i] =
            some (candidates.toList[i]'(by rw [hlength]; exact hi), quotient) := by
    intro i hi
    have hi_array : i < indicators.size := by
      simpa [Array.length_toList] using hi
    have hi_candidates : i < candidates.size := by
      simpa [hsize] using hi_array
    rcases hcandidate i hi_array with ⟨quotient, hquotient⟩
    refine ⟨quotient, ?_⟩
    have hind :
        indicators.toList[i] = indicators.getD i #[] := by
      simp [Array.getD, Array.getElem_toList, hi_array]
    have hcand :
        candidates.toList[i] = candidates.getD i 0 := by
      simp [Array.getD, Array.getElem_toList, hi_candidates]
    rw [hind, hcand]
    exact hquotient
  have hfold :=
    bhksIndicatorCandidatesCoreStep_fold_eq_some_append f d
      indicators.toList candidates.toList #[] hlength hcandidate_list
  rw [hfold]
  apply congrArg some
  rw [← Array.toList_inj]
  simp

/--
If the executable Core BHKS recovery guards all pass, `coreRecover?` returns the
verified candidate array.  Core-coordinate (van Hoeij `M1`) analogue of
`bhksRecover?_eq_some_of_checks`: the public proof-facing surface for callers
that should not unfold the private failure classifier.
-/
theorem coreRecover?_eq_some_of_checks
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
      bhksIndicatorCandidatesCore? f d
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows
              (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)) =
        some candidates)
    (hprod : Array.polyProduct candidates = f) :
    coreRecover? f d = some candidates := by
  unfold coreRecover?
  rw [bhksRecoverClassifiedCore]
  have hproductCheck : (Array.polyProduct candidates == f) = true := by
    simpa [beq_iff_eq] using hprod
  simp only [dif_pos hrows, hnondeg, Bool.false_eq_true, if_false, hcand,
    hproductCheck, if_true, BhksRecoveryResult.toOption]

end Hex
