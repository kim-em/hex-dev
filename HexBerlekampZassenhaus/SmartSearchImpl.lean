/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.Recombination

public section
set_option backward.proofsInPublic true

/-!
Proof-backed compiled implementations for the size-ordered classical
recombination search.
-/

namespace Hex

/-- A proper-subset candidate is known not to peel the current target. This is
deliberately stronger than a failed recursive factorization: the prefilter
rejects it, it is not recordable, or exact division itself fails. -/
@[expose]
def smartCandidateRejects
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (selected : List ZPoly) : Bool :=
  if scaledCandidatePrefilter coreLc target modulus selected then
    let candidate :=
      normalizeFactorSign <| ZPoly.primitivePart <| ZPoly.dilate coreLc <|
        centeredLiftPoly (Array.polyProduct selected.toArray) modulus
    if shouldRecordPolynomialFactor candidate then
      (exactQuotient? target candidate).isNone
    else
      true
  else
    true

/-- Scan a flat candidate list while threading exactly the candidate budget and
fuel consumed by `scaledRecombinationSmartCandLoop`. `some remaining` means
every candidate was rejected before recursive factorization was needed. -/
@[expose]
def scanSmartCandidates
    (coreLc : Int) (target : ZPoly) (modulus : Nat) :
    List (List ZPoly × List ZPoly) → Nat → Nat → Option Nat
  | [], budget, _ => some budget
  | _ :: _, 0, _ => none
  | _ :: _, _ + 1, 0 => none
  | split :: rest, budget + 1, fuel + 1 =>
      if smartCandidateRejects coreLc target modulus split.1 then
        scanSmartCandidates coreLc target modulus rest budget fuel
      else
        none

/-- Scan whole subset-size levels, excluding whatever suffix the caller wants
to handle normally. The second returned component is the size-loop fuel after
the scanned levels; candidate-loop fuel is local to each level, matching the
reference search. -/
@[expose]
def scanSmartSizes
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (head : ZPoly) (tail : List ZPoly) :
    List Nat → Nat → Nat → Option (Nat × Nat)
  | [], budget, fuel => some (budget, fuel)
  | _ :: _, 0, _ => none
  | _ :: _, _ + 1, 0 => none
  | d :: ds, budget + 1, fuel + 1 =>
      let splits :=
        (subsetsOfSizeWithComplement tail d).map fun sc => (head :: sc.1, sc.2)
      match scanSmartCandidates coreLc target modulus splits (budget + 1) fuel with
      | none => none
      | some remaining =>
          scanSmartSizes coreLc target modulus head tail ds remaining fuel

theorem scaledRecombinationSmartCandLoop_eq_none_of_scan_some
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (splits : List (List ZPoly × List ZPoly)) (budget fuel remaining : Nat)
    (hscan : scanSmartCandidates coreLc target modulus splits budget fuel =
      some remaining) :
    scaledRecombinationSmartCandLoop coreLc target modulus splits budget fuel =
      (none, remaining) := by
  induction splits generalizing budget fuel remaining with
  | nil =>
      simp only [scanSmartCandidates, Option.some.injEq] at hscan
      subst remaining
      simp only [scaledRecombinationSmartCandLoop]
  | cons split rest ih =>
      cases budget with
      | zero => simp [scanSmartCandidates] at hscan
      | succ budget =>
          cases fuel with
          | zero => simp [scanSmartCandidates] at hscan
          | succ fuel =>
              simp only [scanSmartCandidates] at hscan
              simp only [smartCandidateRejects] at hscan
              simp only [scaledRecombinationSmartCandLoop, Nat.succ_ne_zero, if_false,
                Nat.add_sub_cancel]
              split at hscan <;> rename_i hprefilter
              · simp only [hprefilter, if_true]
                split at hscan <;> rename_i hrecord
                · simp only [hrecord, if_true]
                  cases hquot : exactQuotient? target
                      (normalizeFactorSign (ZPoly.primitivePart
                        (ZPoly.dilate coreLc
                          (centeredLiftPoly (Array.polyProduct split.1.toArray)
                            modulus)))) with
                  | none =>
                      simp only [hquot, Option.isNone_none, if_true] at hscan
                      exact ih budget fuel remaining hscan
                  | some quotient =>
                      simp only [hquot, Option.isNone_some] at hscan
                      simp at hscan
                · simp only [hrecord]
                  exact ih budget fuel remaining hscan
              · simp only [hprefilter]
                exact ih budget fuel remaining hscan

theorem scaledRecombinationSmartSizeLoop_eq_suffix_of_scan_some
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (head : ZPoly) (tail : List ZPoly)
    (sizes suffix : List Nat) (budget fuel remaining remainingFuel : Nat)
    (hscan : scanSmartSizes coreLc target modulus head tail sizes budget fuel =
      some (remaining, remainingFuel)) :
    scaledRecombinationSmartSizeLoop coreLc target modulus head tail
        (sizes ++ suffix) budget fuel =
      scaledRecombinationSmartSizeLoop coreLc target modulus head tail
        suffix remaining remainingFuel := by
  induction sizes generalizing budget fuel remaining remainingFuel with
  | nil =>
      simp only [scanSmartSizes, Option.some.injEq, Prod.mk.injEq] at hscan
      obtain ⟨rfl, rfl⟩ := hscan
      rfl
  | cons d ds ih =>
      cases budget with
      | zero => simp [scanSmartSizes] at hscan
      | succ budget =>
          cases fuel with
          | zero => simp [scanSmartSizes] at hscan
          | succ fuel =>
              simp only [scanSmartSizes] at hscan
              let splits :=
                (subsetsOfSizeWithComplement tail d).map fun sc => (head :: sc.1, sc.2)
              generalize hflat : scanSmartCandidates coreLc target modulus splits
                (budget + 1) fuel = scanned at hscan
              cases scanned with
              | none => simp at hscan
              | some nextBudget =>
                  have hcand := scaledRecombinationSmartCandLoop_eq_none_of_scan_some
                    coreLc target modulus splits (budget + 1) fuel nextBudget hflat
                  dsimp only [splits] at hcand
                  simp only [List.cons_append, scaledRecombinationSmartSizeLoop,
                    Nat.succ_ne_zero, if_false, hcand]
                  exact ih nextBudget fuel remaining remainingFuel hscan

theorem subsetsOfSizeWithComplement_eq_nil_of_length_lt {α : Type} :
    ∀ (xs : List α) (k : Nat), xs.length < k →
      subsetsOfSizeWithComplement xs k = []
  | xs, 0, h => by omega
  | [], _ + 1, _ => rfl
  | x :: xs, k + 1, h => by
      simp only [List.length_cons] at h
      simp only [subsetsOfSizeWithComplement]
      rw [subsetsOfSizeWithComplement_eq_nil_of_length_lt xs k (by omega)]
      rw [subsetsOfSizeWithComplement_eq_nil_of_length_lt xs (k + 1) (by omega)]
      rfl

theorem subsetsOfSizeWithComplement_length_self {α : Type} :
    ∀ xs : List α, subsetsOfSizeWithComplement xs xs.length = [(xs, [])]
  | [] => rfl
  | x :: xs => by
      simp only [List.length_cons, subsetsOfSizeWithComplement]
      rw [subsetsOfSizeWithComplement_length_self xs]
      rw [subsetsOfSizeWithComplement_eq_nil_of_length_lt xs (xs.length + 1)
        (Nat.lt_succ_self _)]
      simp

/-- Raw modular product used while extending a selected-factor prefix. -/
@[expose]
def rawSelectionResidue
    (coeffOf : ZPoly → Int) (selected : List ZPoly) (modulus : Int) : Int :=
  selected.foldl (fun acc g => acc * coeffOf g % modulus) 1

theorem selectedDegreeSum_append_one (selected : List ZPoly) (g : ZPoly) :
    selectedDegreeSum (selected ++ [g]) =
      selectedDegreeSum selected + g.degree?.getD 0 := by
  simp [selectedDegreeSum, List.foldl_append]

theorem rawSelectionResidue_append_one
    (coeffOf : ZPoly → Int) (selected : List ZPoly) (g : ZPoly) (modulus : Int) :
    rawSelectionResidue coeffOf (selected ++ [g]) modulus =
      rawSelectionResidue coeffOf selected modulus * coeffOf g % modulus := by
  simp [rawSelectionResidue, List.foldl_append]

theorem foldResidue_emod
    (coeffOf : ZPoly → Int) (modulus : Int) (xs : List ZPoly) (acc : Int) :
    (xs.foldl (fun r g => r * coeffOf g % modulus) (acc % modulus)) % modulus =
      xs.foldl (fun r g => r * coeffOf g % modulus) (acc % modulus) := by
  induction xs generalizing acc with
  | nil => exact Int.emod_emod _ _
  | cons g gs ih =>
      simp only [List.foldl]
      exact ih (acc % modulus * coeffOf g)

theorem rawSelectionResidue_emod
    (coeffOf : ZPoly → Int) (selected : List ZPoly) (modulus : Int)
    (hmodulus : 1 < modulus) :
    rawSelectionResidue coeffOf selected modulus % modulus =
      rawSelectionResidue coeffOf selected modulus := by
  have hone : (1 : Int) % modulus = 1 := Int.emod_eq_of_lt (by omega) hmodulus
  simpa only [rawSelectionResidue, hone] using
    foldResidue_emod coeffOf modulus selected 1

/-- Center a residue already reduced modulo `modulus`, avoiding a second
arbitrary-precision remainder. -/
@[expose]
def centeredReduced (residue : Int) (modulus : Nat) : Int :=
  if 2 * residue.natAbs ≤ modulus then
    residue
  else if residue < 0 then
    residue + Int.ofNat modulus
  else
    residue - Int.ofNat modulus

theorem centeredReduced_emod (z : Int) (modulus : Nat) (hmodulus : modulus ≠ 0) :
    centeredReduced (z % Int.ofNat modulus) modulus = centeredModNat z modulus := by
  unfold centeredReduced centeredModNat
  simp only [hmodulus, if_false]

/-- Exact integer divisibility with a cheap magnitude rejection before the
arbitrary-precision remainder. -/
@[expose]
def intDividesFast (numerator divisor : Int) : Bool :=
  if numerator.natAbs < divisor.natAbs ∧ numerator ≠ 0 then
    false
  else
    numerator % divisor == 0

@[simp] theorem intDividesFast_eq (numerator divisor : Int) :
    intDividesFast numerator divisor = (numerator % divisor == 0) := by
  unfold intDividesFast
  split
  · rename_i hlarge
    apply Eq.symm
    apply Bool.eq_false_iff.mpr
    intro hemod
    have hemod' : numerator % divisor = 0 := beq_iff_eq.mp hemod
    have hdvdAbs : divisor.natAbs ∣ numerator.natAbs :=
      Int.natAbs_dvd_natAbs.mpr (Int.dvd_of_emod_eq_zero hemod')
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hlarge.2) hdvdAbs
    omega
  · rfl

/-- Compiled smart-candidate prefilter with the same cheap exact-divisibility
guard as the cached subset scan, including the common monic fast path. -/
def scaledCandidatePrefilterImpl
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (selected : List ZPoly) : Bool :=
  let degreeSum := selectedDegreeSum selected
  let leadingResidue := selectedProductResidue DensePoly.leadingCoeff selected modulus
  let trailingResidue := selectedProductResidue (fun g => g.coeff 0) selected modulus
  (coreLc == 0 || leadingResidue == 0 || decide (target = 0) ||
      decide (degreeSum ≤ target.degree?.getD 0)) &&
    (if coreLc == 1 then
      intDividesFast (leadingResidue * target.coeff 0) trailingResidue
    else
      intDividesFast
        (coreLc ^ degreeSum * leadingResidue * target.coeff 0) trailingResidue)

@[csimp] theorem scaledCandidatePrefilter_eq_impl :
    @scaledCandidatePrefilter = @scaledCandidatePrefilterImpl := by
  funext coreLc target modulus selected
  unfold scaledCandidatePrefilter scaledCandidatePrefilterImpl
  simp only [intDividesFast_eq]
  by_cases hcore : coreLc = 1
  · subst coreLc
    simp [Int.one_pow]
  · simp [hcore]

/-- The smart prefilter evaluated from cached degree and coefficient-product
residues. -/
@[expose]
def selectionPrefilter
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (degreeSum : Nat) (leadingResidue trailingResidue : Int) : Bool :=
  let lcRes := centeredReduced leadingResidue modulus
  let trailRes := centeredReduced trailingResidue modulus
  (coreLc == 0 || lcRes == 0 || decide (target = 0) ||
      decide (degreeSum ≤ target.degree?.getD 0)) &&
    (if coreLc == 1 then
      intDividesFast (lcRes * target.coeff 0) trailRes
    else
      intDividesFast (coreLc ^ degreeSum * lcRes * target.coeff 0) trailRes)

/-- Rejection test with the prefilter statistics supplied by the subset
enumerator. The selected tail stays reversed until the prefilter accepts it. -/
def selectionRejectsRev
    (coreLc : Int) (target head : ZPoly) (modulus : Nat) (selectedRev : List ZPoly)
    (degreeSum : Nat) (leadingResidue trailingResidue : Int) : Bool :=
  if selectionPrefilter coreLc target modulus degreeSum leadingResidue trailingResidue then
    let selected := head :: selectedRev.reverse
    let candidate :=
      normalizeFactorSign <| ZPoly.primitivePart <| ZPoly.dilate coreLc <|
        centeredLiftPoly (Array.polyProduct selected.toArray) modulus
    if shouldRecordPolynomialFactor candidate then
      (exactQuotient? target candidate).isNone
    else
      true
  else
    true

theorem selectionPrefilter_eq
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (selected : List ZPoly)
    (degreeSum : Nat) (leadingResidue trailingResidue : Int)
    (hmodulus : 1 < modulus)
    (hdegree : degreeSum = selectedDegreeSum selected)
    (hleading : leadingResidue =
      rawSelectionResidue DensePoly.leadingCoeff selected (modulus : Int))
    (htrailing : trailingResidue =
      rawSelectionResidue (fun g => g.coeff 0) selected (modulus : Int)) :
    selectionPrefilter coreLc target modulus degreeSum leadingResidue trailingResidue =
      scaledCandidatePrefilter coreLc target modulus selected := by
  subst degreeSum
  subst leadingResidue
  subst trailingResidue
  have hmodulusInt : (1 : Int) < (modulus : Int) := Int.ofNat_lt.mpr hmodulus
  have hmodulusNe : modulus ≠ 0 := by omega
  have hlc :
      centeredReduced (rawSelectionResidue DensePoly.leadingCoeff selected (modulus : Int))
          modulus =
        centeredModNat (rawSelectionResidue DensePoly.leadingCoeff selected (modulus : Int))
          modulus := by
    calc
      _ = centeredReduced
          (rawSelectionResidue DensePoly.leadingCoeff selected (modulus : Int) %
            (modulus : Int)) modulus := by
        apply congrArg (fun z => centeredReduced z modulus)
        exact (rawSelectionResidue_emod DensePoly.leadingCoeff selected (modulus : Int)
          hmodulusInt).symm
      _ = _ := centeredReduced_emod _ _ hmodulusNe
  have htrail :
      centeredReduced
          (rawSelectionResidue (fun g => g.coeff 0) selected (modulus : Int)) modulus =
        centeredModNat
          (rawSelectionResidue (fun g => g.coeff 0) selected (modulus : Int)) modulus := by
    calc
      _ = centeredReduced
          (rawSelectionResidue (fun g => g.coeff 0) selected (modulus : Int) %
            (modulus : Int)) modulus := by
        apply congrArg (fun z => centeredReduced z modulus)
        exact (rawSelectionResidue_emod (fun g => g.coeff 0) selected (modulus : Int)
          hmodulusInt).symm
      _ = _ := centeredReduced_emod _ _ hmodulusNe
  unfold selectionPrefilter
  rw [show centeredReduced
        (rawSelectionResidue DensePoly.leadingCoeff selected (modulus : Int)) modulus = _
      from hlc]
  rw [show centeredReduced
        (rawSelectionResidue (fun g => g.coeff 0) selected (modulus : Int)) modulus = _
      from htrail]
  by_cases hcore : coreLc = 1
  · simp [scaledCandidatePrefilter, selectedProductResidue, hcore,
      rawSelectionResidue]
    simp only [Int.one_pow, Int.one_mul]
  · simp [scaledCandidatePrefilter, selectedProductResidue, hcore,
      rawSelectionResidue]

theorem selectionRejectsRev_eq
    (coreLc : Int) (target head : ZPoly) (modulus : Nat) (selectedRev : List ZPoly)
    (degreeSum : Nat) (leadingResidue trailingResidue : Int)
    (hmodulus : 1 < modulus)
    (hdegree : degreeSum = selectedDegreeSum (head :: selectedRev.reverse))
    (hleading : leadingResidue =
      rawSelectionResidue DensePoly.leadingCoeff (head :: selectedRev.reverse) (modulus : Int))
    (htrailing : trailingResidue =
      rawSelectionResidue (fun g => g.coeff 0) (head :: selectedRev.reverse)
        (modulus : Int)) :
    selectionRejectsRev coreLc target head modulus selectedRev degreeSum leadingResidue
        trailingResidue =
      smartCandidateRejects coreLc target modulus (head :: selectedRev.reverse) := by
  unfold selectionRejectsRev smartCandidateRejects
  rw [selectionPrefilter_eq coreLc target modulus (head :: selectedRev.reverse) degreeSum
    leadingResidue trailingResidue hmodulus hdegree hleading htrailing]

/-- Logical complete proper-subset rejection scan. `excluded` records whether
the current selection has already omitted a factor, so the one full subset is
not tested. -/
@[expose]
def allProperSelectionsReject
    (coreLc : Int) (target head : ZPoly) (modulus : Nat) :
    List ZPoly → List ZPoly → Bool → Bool
  | [], selected, excluded =>
      if excluded then smartCandidateRejects coreLc target modulus (head :: selected)
      else true
  | g :: gs, selected, excluded =>
      allProperSelectionsReject coreLc target head modulus gs selected true &&
        allProperSelectionsReject coreLc target head modulus gs (selected ++ [g]) excluded

/-- Cached implementation of `allProperSelectionsReject`. Each edge of the
subset tree performs one degree addition and two modular multiplications. The
selected tail is stored in reverse order, so extending it is constant-time;
it is reversed only on the rare path that survives the cached prefilter. -/
def allProperSelectionsRejectImpl
    (coreLc : Int) (target head : ZPoly) (modulusNat : Nat) (modulus : Int) :
    List ZPoly → List ZPoly → Nat → Int → Int → Bool → Bool
  | [], selectedRev, degreeSum, leadingResidue, trailingResidue, excluded =>
      if excluded then
        selectionRejectsRev coreLc target head modulusNat selectedRev degreeSum
          leadingResidue trailingResidue
      else
        true
  | g :: gs, selectedRev, degreeSum, leadingResidue, trailingResidue, excluded =>
      allProperSelectionsRejectImpl coreLc target head modulusNat modulus gs selectedRev
          degreeSum leadingResidue trailingResidue true &&
        allProperSelectionsRejectImpl coreLc target head modulusNat modulus gs
          (g :: selectedRev) (degreeSum + g.degree?.getD 0)
          (mulModOneFast leadingResidue (DensePoly.leadingCoeff g) modulus)
          (trailingResidue * g.coeff 0 % modulus) excluded

theorem allProperSelectionsRejectImpl_eq
    (coreLc : Int) (target head : ZPoly) (modulusNat : Nat)
    (hmodulus : 1 < modulusNat) (xs selected selectedRev : List ZPoly)
    (degreeSum : Nat) (leadingResidue trailingResidue : Int) (excluded : Bool)
    (hreverse : selectedRev.reverse = selected)
    (hdegree : degreeSum = selectedDegreeSum (head :: selected))
    (hleading : leadingResidue =
      rawSelectionResidue DensePoly.leadingCoeff (head :: selected) (modulusNat : Int))
    (htrailing : trailingResidue =
      rawSelectionResidue (fun g => g.coeff 0) (head :: selected) (modulusNat : Int)) :
    allProperSelectionsRejectImpl coreLc target head modulusNat (modulusNat : Int) xs
        selectedRev degreeSum leadingResidue trailingResidue excluded =
      allProperSelectionsReject coreLc target head modulusNat xs selected excluded := by
  induction xs generalizing selected selectedRev degreeSum leadingResidue trailingResidue
      excluded with
  | nil =>
      simp only [allProperSelectionsRejectImpl, allProperSelectionsReject]
      split
      · rw [← hreverse] at hdegree hleading htrailing ⊢
        exact selectionRejectsRev_eq coreLc target head modulusNat selectedRev degreeSum
          leadingResidue trailingResidue hmodulus hdegree hleading htrailing
      · rfl
  | cons g gs ih =>
      simp only [allProperSelectionsRejectImpl, allProperSelectionsReject]
      have hreverse' : (g :: selectedRev).reverse = selected ++ [g] := by
        simp only [List.reverse_cons]
        rw [hreverse]
      have hdegree' :
          degreeSum + g.degree?.getD 0 =
            selectedDegreeSum (head :: (selected ++ [g])) := by
        change degreeSum + g.degree?.getD 0 =
          selectedDegreeSum ((head :: selected) ++ [g])
        rw [selectedDegreeSum_append_one]
        exact congrArg (· + g.degree?.getD 0) hdegree
      have hleading' :
          mulModOneFast leadingResidue (DensePoly.leadingCoeff g) (modulusNat : Int) =
            rawSelectionResidue DensePoly.leadingCoeff (head :: (selected ++ [g]))
              (modulusNat : Int) := by
        change mulModOneFast leadingResidue (DensePoly.leadingCoeff g) (modulusNat : Int) =
          rawSelectionResidue DensePoly.leadingCoeff ((head :: selected) ++ [g])
            (modulusNat : Int)
        rw [mulModOneFast_eq_of_one_lt]
        · rw [rawSelectionResidue_append_one]
          exact congrArg (fun x => x * DensePoly.leadingCoeff g % (modulusNat : Int))
            hleading
        · exact_mod_cast hmodulus
      have htrailing' :
          trailingResidue * g.coeff 0 % (modulusNat : Int) =
            rawSelectionResidue (fun p => p.coeff 0) (head :: (selected ++ [g]))
              (modulusNat : Int) := by
        change trailingResidue * g.coeff 0 % (modulusNat : Int) =
          rawSelectionResidue (fun p => p.coeff 0) ((head :: selected) ++ [g])
            (modulusNat : Int)
        rw [rawSelectionResidue_append_one]
        exact congrArg (fun x => x * g.coeff 0 % (modulusNat : Int)) htrailing
      rw [ih selected selectedRev degreeSum leadingResidue trailingResidue true hreverse hdegree
        hleading htrailing]
      rw [ih (selected ++ [g]) (g :: selectedRev) (degreeSum + g.degree?.getD 0)
        (mulModOneFast leadingResidue (DensePoly.leadingCoeff g) (modulusNat : Int))
        (trailingResidue * g.coeff 0 % (modulusNat : Int)) excluded hreverse' hdegree'
        hleading' htrailing']

/-- Complete cached proper-subset rejection scan from the head-forced initial
selection. -/
def allProperRejectCached
    (coreLc : Int) (target head : ZPoly) (modulus : Nat) (tail : List ZPoly) : Bool :=
  let modulusInt : Int := modulus
  allProperSelectionsRejectImpl coreLc target head modulus modulusInt tail []
    (head.degree?.getD 0) (DensePoly.leadingCoeff head % modulusInt)
    (head.coeff 0 % modulusInt) false

theorem allProperRejectCached_eq
    (coreLc : Int) (target head : ZPoly) (modulus : Nat) (tail : List ZPoly)
    (hmodulus : 1 < modulus) :
    allProperRejectCached coreLc target head modulus tail =
      allProperSelectionsReject coreLc target head modulus tail [] false := by
  unfold allProperRejectCached
  apply allProperSelectionsRejectImpl_eq coreLc target head modulus hmodulus
  · rfl
  · simp [selectedDegreeSum]
  · simp [rawSelectionResidue]
  · simp [rawSelectionResidue]

theorem allProperSelectionsReject_subset
    (coreLc : Int) (target head : ZPoly) (modulus : Nat) :
    ∀ (xs selected : List ZPoly) (excluded : Bool),
      allProperSelectionsReject coreLc target head modulus xs selected excluded = true →
      ∀ (k : Nat) (split : List ZPoly × List ZPoly),
        split ∈ subsetsOfSizeWithComplement xs k →
        (excluded = true ∨ k < xs.length) →
        smartCandidateRejects coreLc target modulus
          (head :: (selected ++ split.1)) = true := by
  intro xs
  induction xs with
  | nil =>
      intro selected excluded hall k split hsplit hproper
      cases k with
      | zero =>
          simp only [subsetsOfSizeWithComplement, List.mem_singleton] at hsplit
          subst split
          simp only [List.append_nil]
          have hexcluded : excluded = true := by
            rcases hproper with hproper | hproper
            · exact hproper
            · simp at hproper
          subst excluded
          simpa [allProperSelectionsReject] using hall
      | succ k =>
          simp [subsetsOfSizeWithComplement] at hsplit
  | cons g gs ih =>
      intro selected excluded hall k split hsplit hproper
      cases hleft : allProperSelectionsReject coreLc target head modulus gs
          (selected ++ [g]) excluded <;>
        cases hright : allProperSelectionsReject coreLc target head modulus gs selected true <;>
        simp [allProperSelectionsReject, hleft, hright] at hall
      cases k with
      | zero =>
          simp only [subsetsOfSizeWithComplement, List.mem_singleton] at hsplit
          subst split
          simp only [List.append_nil]
          simpa using ih selected true hright 0 ([], gs)
            (by simp [subsetsOfSizeWithComplement]) (Or.inl rfl)
      | succ k =>
          simp only [subsetsOfSizeWithComplement, List.mem_append, List.mem_map] at hsplit
          rcases hsplit with hinclude | hexclude
          · rcases hinclude with ⟨inner, hinner, rfl⟩
            change smartCandidateRejects coreLc target modulus
              (head :: (selected ++ ([g] ++ inner.1))) = true
            rw [← List.append_assoc]
            apply ih (selected ++ [g]) excluded hleft k inner hinner
            rcases hproper with hproper | hproper
            · exact Or.inl hproper
            · exact Or.inr (by simpa using hproper)
          · rcases hexclude with ⟨inner, hinner, rfl⟩
            exact ih selected true hright (k + 1) inner hinner (Or.inl rfl)

theorem scanSmartCandidates_eq_some_of_all_reject
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (splits : List (List ZPoly × List ZPoly)) (budget fuel : Nat)
    (hbudget : splits.length < budget) (hfuel : splits.length < fuel)
    (hreject : ∀ split ∈ splits,
      smartCandidateRejects coreLc target modulus split.1 = true) :
    scanSmartCandidates coreLc target modulus splits budget fuel =
      some (budget - splits.length) := by
  induction splits generalizing budget fuel with
  | nil => simp [scanSmartCandidates]
  | cons split rest ih =>
      cases budget with
      | zero => omega
      | succ budget =>
          cases fuel with
          | zero => omega
          | succ fuel =>
              simp only [scanSmartCandidates]
              rw [hreject split (by simp)]
              rw [ih budget fuel (by simp only [List.length_cons] at hbudget ⊢; omega)
                (by simp only [List.length_cons] at hfuel ⊢; omega)
                (fun candidate hmem => hreject candidate (by simp [hmem]))]
              simp [List.length_cons]

/-- Number of candidates in a list of proper subset-size levels. -/
@[expose]
def smartCandidateCount (tail : List ZPoly) : List Nat → Nat
  | [] => 0
  | d :: ds => (subsetsOfSizeWithComplement tail d).length + smartCandidateCount tail ds

/-- Cardinality of one subset-size level, without materializing its splits. -/
@[expose]
def subsetSplitCount : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => subsetSplitCount n k + subsetSplitCount n (k + 1)

theorem subsetsOfSizeWithComplement_length_eq_subsetSplitCount {α : Type} :
    ∀ (xs : List α) (k : Nat),
      (subsetsOfSizeWithComplement xs k).length = subsetSplitCount xs.length k
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | x :: xs, k + 1 => by
      simp only [subsetsOfSizeWithComplement, List.length_append, List.length_map,
        List.length_cons, subsetSplitCount]
      rw [subsetsOfSizeWithComplement_length_eq_subsetSplitCount xs k]
      rw [subsetsOfSizeWithComplement_length_eq_subsetSplitCount xs (k + 1)]

/-- Allocation-free implementation of `smartCandidateCount`. -/
def smartCandidateCountImpl (tail : List ZPoly) : List Nat → Nat
  | [] => 0
  | d :: ds => subsetSplitCount tail.length d + smartCandidateCountImpl tail ds

@[csimp] theorem smartCandidateCount_eq_impl :
    @smartCandidateCount = @smartCandidateCountImpl := by
  funext tail sizes
  induction sizes with
  | nil => rfl
  | cons d ds ih =>
      simp only [smartCandidateCount, smartCandidateCountImpl]
      rw [subsetsOfSizeWithComplement_length_eq_subsetSplitCount, ih]

theorem scanSmartSizes_eq_some_of_all_reject
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (head : ZPoly) (tail : List ZPoly) :
    ∀ (sizes : List Nat) (budget fuel : Nat),
      (∀ d ∈ sizes, ∀ split ∈ subsetsOfSizeWithComplement tail d,
        smartCandidateRejects coreLc target modulus (head :: split.1) = true) →
      smartCandidateCount tail sizes < budget →
      smartCandidateCount tail sizes + sizes.length < fuel →
      scanSmartSizes coreLc target modulus head tail sizes budget fuel =
        some (budget - smartCandidateCount tail sizes, fuel - sizes.length) := by
  intro sizes
  induction sizes with
  | nil =>
      intro budget fuel _ _ _
      simp [smartCandidateCount, scanSmartSizes]
  | cons d ds ih =>
      intro budget fuel hreject hbudget hfuel
      cases budget with
      | zero => omega
      | succ budget =>
          cases fuel with
          | zero => omega
          | succ fuel =>
              let splits :=
                (subsetsOfSizeWithComplement tail d).map fun sc => (head :: sc.1, sc.2)
              have hflat : scanSmartCandidates coreLc target modulus splits (budget + 1) fuel =
                  some ((budget + 1) - splits.length) := by
                apply scanSmartCandidates_eq_some_of_all_reject
                · simp only [smartCandidateCount] at hbudget
                  simp [splits] at hbudget ⊢
                  omega
                · simp only [smartCandidateCount, List.length_cons] at hfuel
                  simp [splits] at hfuel ⊢
                  omega
                · intro split hmem
                  simp only [splits, List.mem_map] at hmem
                  rcases hmem with ⟨source, hsource, rfl⟩
                  exact hreject d (by simp) source hsource
              have hrest := ih ((budget + 1) - splits.length) fuel
                (fun d hd split hs => hreject d (by simp [hd]) split hs)
                (by
                  simp only [smartCandidateCount] at hbudget
                  simp [splits] at hbudget ⊢
                  omega)
                (by
                  simp only [smartCandidateCount, List.length_cons] at hfuel
                  omega)
              simp only [scanSmartSizes]
              dsimp only [splits] at hflat hrest
              rw [hflat]
              simp only
              rw [hrest]
              simp [smartCandidateCount, Nat.sub_sub]

/-- Cached complete-proper-subset variant of the singleton shortcut. It is
used only when the entire proper search fits strictly inside the reference
budget and fuel, so subset ordering is immaterial. The factor-count guard is
checked before computing the binomial candidate total: from 20 factors onward
the head-forced proper search already has at least `2^19 - 1` candidates, beyond
the default budget, and even counting that tree would be counterproductive. -/
@[expose]
def cachedSingletonShortcut?
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (localFactors : List ZPoly)
    (budget fuel : Nat) : Option (Option (List ZPoly) × Nat) :=
  if target = 1 || budget = 0 then none else
  if 1 < modulus then
    if localFactors.length < 20 then
      match fuel with
      | 0 => none
      | sizeFuel + 1 =>
          match localFactors with
          | [] => none
          | head :: tail =>
              let sizes := List.range tail.length
              let count := smartCandidateCount tail sizes
              if count < budget then
                if count + sizes.length < sizeFuel then
                  if allProperRejectCached coreLc target head modulus tail then
                    let remaining := budget - count
                    match sizeFuel - sizes.length with
                    | 0 => none
                    | remainingFuel + 1 =>
                        let result :=
                          scaledRecombinationSmartCandLoop coreLc target modulus
                            [(localFactors, [])] remaining remainingFuel
                        some result
                  else
                    none
                else
                  none
              else
                none
    else
      none
  else
    none

theorem cachedSingletonShortcut?_sound
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (localFactors : List ZPoly)
    (budget fuel : Nat) (result : Option (List ZPoly) × Nat)
    (h : cachedSingletonShortcut? coreLc target modulus localFactors budget fuel =
      some result) :
    scaledRecombinationSmartAux coreLc target modulus localFactors budget fuel = result := by
  unfold cachedSingletonShortcut? at h
  by_cases htarget : target = 1
  · simp [htarget] at h
  · by_cases hbudget : budget = 0
    · simp [htarget, hbudget] at h
    · simp only [htarget, hbudget, decide_false, Bool.false_or] at h
      by_cases hmodulus : 1 < modulus
      · rw [if_pos hmodulus] at h
        by_cases hsmall : localFactors.length < 20
        · rw [if_pos hsmall] at h
          cases fuel with
          | zero => simp at h
          | succ sizeFuel =>
              cases localFactors with
              | nil => simp at h
              | cons head tail =>
                  rw [← Nat.succ_eq_add_one] at h
                  simp only at h
                  let sizes := List.range tail.length
                  let count := smartCandidateCount tail sizes
                  by_cases hcountBudget : count < budget
                  · rw [if_pos hcountBudget] at h
                    by_cases hcountFuel : count + sizes.length < sizeFuel
                    · rw [if_pos hcountFuel] at h
                      cases hcached : allProperRejectCached coreLc target head modulus tail
                      · simp [hcached] at h
                      · simp only [hcached, if_true] at h
                        have hlogical :
                            allProperSelectionsReject coreLc target head modulus tail [] false =
                              true := by
                          rw [← allProperRejectCached_eq coreLc target head modulus tail hmodulus]
                          exact hcached
                        have hreject :
                            ∀ d ∈ sizes, ∀ split ∈ subsetsOfSizeWithComplement tail d,
                              smartCandidateRejects coreLc target modulus
                                (head :: split.1) = true := by
                          intro d hd split hsplit
                          apply allProperSelectionsReject_subset coreLc target head modulus tail
                            [] false hlogical d split hsplit
                          exact Or.inr (by simpa [sizes] using hd)
                        have hscan := scanSmartSizes_eq_some_of_all_reject
                          coreLc target modulus head tail sizes budget sizeFuel hreject
                            hcountBudget hcountFuel
                        generalize hremainingFuel : sizeFuel - sizes.length = remainingFuel at h
                        cases remainingFuel with
                        | zero => simp at h
                        | succ remainingFuel =>
                            rw [← Nat.succ_eq_add_one] at h
                            simp only at h
                            generalize hfull : scaledRecombinationSmartCandLoop coreLc target
                              modulus [((head :: tail), [])] (budget - count)
                                remainingFuel = fullResult at h
                            cases fullResult with
                            | mk ores b =>
                                simp at h
                                subst result
                                have hscan' :
                                    scanSmartSizes coreLc target modulus head tail sizes
                                        budget sizeFuel =
                                      some (budget - count, remainingFuel + 1) := by
                                  rw [hscan, hremainingFuel]
                                have hsizes :=
                                  scaledRecombinationSmartSizeLoop_eq_suffix_of_scan_some
                                    coreLc target modulus head tail sizes [tail.length]
                                    budget sizeFuel (budget - count) (remainingFuel + 1) hscan'
                                have hsizesRange : sizes ++ [tail.length] =
                                    List.range (tail.length + 1) := by
                                  simp [sizes, List.range_succ]
                                rw [hsizesRange] at hsizes
                                have hlast :
                                    scaledRecombinationSmartSizeLoop coreLc target modulus
                                        head tail [tail.length] (budget - count)
                                          (remainingFuel + 1) =
                                      (ores, b) := by
                                  have hremaining : budget - count ≠ 0 := by omega
                                  simp [scaledRecombinationSmartSizeLoop,
                                    subsetsOfSizeWithComplement_length_self, hremaining, hfull]
                                  cases ores <;> rfl
                                rw [hlast] at hsizes
                                unfold scaledRecombinationSmartAux
                                simp only [htarget, hbudget, if_false]
                                rw [hsizes]
                    · rw [if_neg hcountFuel] at h
                      simp at h
                  · rw [if_neg hcountBudget] at h
                    simp at h
        · rw [if_neg hsmall] at h
          simp at h
      · rw [if_neg hmodulus] at h
        simp at h

/-- Compiled wrapper with a rejection-only irreducible shortcut. The ordinary
verified search remains the fallback for every input on which the shortcut
cannot reproduce its singleton result exactly. -/
def scaledRecombinationSmartImpl
    (coreLc : Int) (f : ZPoly) (modulus : Nat) (localFactors : List ZPoly)
    (budget : Nat := defaultSubsetBudget) : Option (List ZPoly) × RecombStats :=
  let r := localFactors.length
  let levelBudget := levelAwareSubsetBudget r budget
  let fuel := levelBudget + (r + 1) * (2 * r + 3)
  let (res, remaining) :=
    match cachedSingletonShortcut? coreLc f modulus localFactors levelBudget fuel with
    | some result => result
    | none => scaledRecombinationSmartAux coreLc f modulus localFactors levelBudget fuel
  (res,
    { candidatesTried := levelBudget - remaining
      budgetExhausted := res.isNone && remaining == 0 })

@[csimp] theorem scaledRecombinationSmart_eq_impl :
    @scaledRecombinationSmart = @scaledRecombinationSmartImpl := by
  funext coreLc f modulus localFactors budget
  unfold scaledRecombinationSmart scaledRecombinationSmartImpl
  generalize hshortcut : cachedSingletonShortcut? coreLc f modulus localFactors
    (levelAwareSubsetBudget localFactors.length budget)
    (levelAwareSubsetBudget localFactors.length budget +
      (localFactors.length + 1) * (2 * localFactors.length + 3)) = shortcut
  cases shortcut with
  | none =>
      simp only [hshortcut]
  | some result =>
      have hsound := cachedSingletonShortcut?_sound _ _ _ _ _ _ result hshortcut
      simp only [hshortcut, hsound]

end Hex
