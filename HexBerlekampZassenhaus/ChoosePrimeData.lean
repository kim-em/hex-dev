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

public import HexBerlekampZassenhaus.Certificate
public meta import HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.FactorizationData
import all HexBerlekampZassenhaus.Certificate

open scoped Hex   -- kernel-reducible Array/Vector equality; see HexBasic.ArrayDecEq

public section
set_option backward.proofsInPublic true

/-!
This module collects `choosePrimeData?`/`Walk?`/`Score` with their correctness lemmas and `henselLiftData`.
-/
namespace Hex

/--
Compiled certificate generator for irreducibility of `f` over `ℤ`; the *prep*
half of the certifying-irreducibility pattern for integer polynomials.

It selects admissible small primes, factors `f` modulo each with Berlekamp,
attaches a nested Rabin certificate to every modular factor, and assembles the
per-prime degree data plus the degree obstructions that rule out every
nontrivial integer factor degree. The whole assembled certificate is checked
with `checkIrreducibleCert` before being returned, so the generator never emits
a certificate the kernel checker would reject: a `some` result is always a
valid certificate, and anything that would not check yields `none`.

This carries no soundness proof of its own; correctness rides entirely on the
downstream `checkIrreducibleCert_sound`. Expensive Berlekamp/Rabin work runs
here in compiled code; the kernel only replays the cheap `checkIrreducibleCert`
reduction on the finished data.

The generator declines non-primitive and constant inputs up front, mirroring
the `IsPrimitive` / `0 < natDegree` side conditions of
`checkIrreducibleCert_sound`. Without this guard the checker accepts vacuous
certificates for inputs those side conditions exclude (e.g. an empty
certificate for a constant, or a full certificate for the non-primitive
`2·x² + 2`, reducible over `ℤ` as `2·(x² + 1)`), so guarding here keeps
`certifyIrreducible? f = some _` an honest irreducibility signal: every side
condition a consumer must discharge is already executable-checked.
-/
def certifyIrreducible? (f : ZPoly) : Option ZPolyIrreducibilityCertificate :=
  if ZPoly.content f != 1 || f.degree?.getD 0 == 0 then none else
  let blocks := (smallPrimeCandidates.filterMap fun c => buildPrimeFactorData? f c).toArray
  match buildDegreeObstructions f blocks with
  | none => none
  | some obstructions =>
    -- Keep only the prime blocks an obstruction actually references (in
    -- first-seen order) and reindex the obstructions against them, so the
    -- certificate the kernel later checks carries no unused Rabin data.
    let used : Array Nat :=
      obstructions.foldl
        (fun acc o => if acc.contains o.primeIndex then acc else acc.push o.primeIndex)
        #[]
    let perPrime := used.filterMap fun i => blocks[i]?
    let obstructions' := obstructions.map fun o =>
      { o with primeIndex := (used.findIdx? (· == o.primeIndex)).getD 0 }
    let cert : ZPolyIrreducibilityCertificate :=
      { perPrime := perPrime, degreeObstructions := obstructions' }
    if checkIrreducibleCert f cert then some cert else none

/-- A successful modular factorization paired with its number of factors. -/
structure PrimeChoiceDataScore where
  /-- The modular factorization data. -/
  data : PrimeChoiceData
  /-- The number of factors in `data.factorsModP`. -/
  factorCount : Nat

private def primeChoiceDataScore (f : ZPoly) (c : SmallPrimeCandidate) :
    Option PrimeChoiceDataScore :=
  letI := c.bounds
  if isGoodPrime f c.p then
    let fModP := ZPoly.modP c.p f
    let factorsModP := berlekampFactorsModP f c
    some
      { data := { p := c.p, fModP, factorsModP }
        factorCount := factorsModP.size }
  else
    none

/--
Factor `f` at one explicit small-prime candidate, returning the same
`PrimeChoiceData` payload used by the production selector when the candidate
is good.

This is a diagnostic surface for attributing adaptive-prime work and inspecting
the modular degree information already computed by a trial.  It deliberately
shares `primeChoiceDataScore` with the selector so benchmark instrumentation
cannot drift to a different modular computation.
-/
def probePrimeData? (f : ZPoly) (c : SmallPrimeCandidate) :
    Option PrimeChoiceData :=
  (primeChoiceDataScore f c).map (·.data)

/-- Whether a checked prime removes at least one quarter of the current modular
factors. -/
private def isMaterialFactorReduction (oldCount newCount : Nat) : Bool :=
  decide (4 * newCount ≤ 3 * oldCount)

#guard isMaterialFactorReduction 12 9 = true
#guard isMaterialFactorReduction 12 10 = false

/-- Prefer a checked prime only after a material modular-width reduction. Tiny
`r` reductions do not reliably predict cheaper recombination and are not worth
abandoning the deterministic first choice. -/
private def betterPrimeChoiceDataScore
    (old new : PrimeChoiceDataScore) : PrimeChoiceDataScore :=
  if isMaterialFactorReduction old.factorCount new.factorCount then
    new
  else
    old

/-- Keep the prime factorization with the lower recombination score. -/
def choosePrimeDataScoreStep
    (f : ZPoly) (best : Option PrimeChoiceDataScore) (c : SmallPrimeCandidate) :
    Option PrimeChoiceDataScore :=
  -- First-suitable selection (matching the verified Isabelle/AFP
  -- `Berlekamp_Zassenhaus` `find_prime`): once a suitable prime has been found,
  -- keep it and stop; crucially, do **not** evaluate `primeChoiceDataScore f c`
  -- (which factors `f mod c.p`) for any later candidate. The old "fewest modular
  -- factors" rule factored at every good prime, costing ~95 modular
  -- factorizations per call; van Hoeij's recombination is polynomial in the
  -- factor count, so the optimisation bought almost nothing.
  match best with
  | some old => some old
  | none => primeChoiceDataScore f c

private theorem primeChoiceDataScore_prime
    (f : ZPoly) (c : SmallPrimeCandidate) (score : PrimeChoiceDataScore)
    (hscore : primeChoiceDataScore f c = some score) :
    Nat.Prime score.data.p := by
  unfold primeChoiceDataScore at hscore
  letI := c.bounds
  by_cases hgood : isGoodPrime f c.p
  · simp [hgood] at hscore
    cases hscore
    exact c.prime
  · simp [hgood] at hscore

private theorem primeChoiceDataScore_p_le
    (f : ZPoly) (c : SmallPrimeCandidate) (score : PrimeChoiceDataScore)
    (hc : c.p ≤ 500)
    (hscore : primeChoiceDataScore f c = some score) :
    score.data.p ≤ 500 := by
  unfold primeChoiceDataScore at hscore
  letI := c.bounds
  by_cases hgood : isGoodPrime f c.p
  · simp [hgood] at hscore
    cases hscore
    exact hc
  · simp [hgood] at hscore

private theorem primeChoiceDataScore_fModP_eq
    (f : ZPoly) (c : SmallPrimeCandidate) (score : PrimeChoiceDataScore)
    (hscore : primeChoiceDataScore f c = some score) :
    score.data.fModP =
      @ZPoly.modP score.data.p score.data.bounds f := by
  unfold primeChoiceDataScore at hscore
  letI := c.bounds
  by_cases hgood : isGoodPrime f c.p
  · simp [hgood] at hscore
    cases hscore
    rfl
  · simp [hgood] at hscore

private theorem betterPrimeChoiceDataScore_prime
    (old new score : PrimeChoiceDataScore)
    (hold : Nat.Prime old.data.p)
    (hnew : Nat.Prime new.data.p)
    (hscore : betterPrimeChoiceDataScore old new = score) :
    Nat.Prime score.data.p := by
  unfold betterPrimeChoiceDataScore at hscore
  split at hscore
  · cases hscore
    exact hnew
  · cases hscore
    exact hold

private theorem betterPrimeChoiceDataScore_fModP_eq
    (f : ZPoly) (old new score : PrimeChoiceDataScore)
    (hold :
      old.data.fModP =
        @ZPoly.modP old.data.p old.data.bounds f)
    (hnew :
      new.data.fModP =
        @ZPoly.modP new.data.p new.data.bounds f)
    (hscore : betterPrimeChoiceDataScore old new = score) :
    score.data.fModP =
      @ZPoly.modP score.data.p score.data.bounds f := by
  unfold betterPrimeChoiceDataScore at hscore
  split at hscore
  · cases hscore
    exact hnew
  · cases hscore
    exact hold

private theorem choosePrimeDataScoreStep_prime
    (f : ZPoly) (best : Option PrimeChoiceDataScore) (c : SmallPrimeCandidate)
    (score : PrimeChoiceDataScore)
    (hbest : ∀ old, best = some old → Nat.Prime old.data.p)
    (hscore : choosePrimeDataScoreStep f best c = some score) :
    Nat.Prime score.data.p := by
  unfold choosePrimeDataScoreStep at hscore
  cases hbest_eq : best with
  | some old =>
      rw [hbest_eq] at hscore
      simp only [Option.some.injEq] at hscore
      rw [← hscore]
      exact hbest old hbest_eq
  | none =>
      rw [hbest_eq] at hscore
      exact primeChoiceDataScore_prime f c score hscore

private theorem choosePrimeDataScoreStep_p_le
    (f : ZPoly) (best : Option PrimeChoiceDataScore) (c : SmallPrimeCandidate)
    (score : PrimeChoiceDataScore)
    (hc : c.p ≤ 500)
    (hbest : ∀ old, best = some old → old.data.p ≤ 500)
    (hscore : choosePrimeDataScoreStep f best c = some score) :
    score.data.p ≤ 500 := by
  unfold choosePrimeDataScoreStep at hscore
  cases hbest_eq : best with
  | some old =>
      rw [hbest_eq] at hscore
      simp only [Option.some.injEq] at hscore
      rw [← hscore]
      exact hbest old hbest_eq
  | none =>
      rw [hbest_eq] at hscore
      exact primeChoiceDataScore_p_le f c score hc hscore

private theorem choosePrimeDataScoreStep_fModP_eq
    (f : ZPoly) (best : Option PrimeChoiceDataScore) (c : SmallPrimeCandidate)
    (score : PrimeChoiceDataScore)
    (hbest : ∀ old, best = some old →
      old.data.fModP =
        @ZPoly.modP old.data.p old.data.bounds f)
    (hscore : choosePrimeDataScoreStep f best c = some score) :
    score.data.fModP =
      @ZPoly.modP score.data.p score.data.bounds f := by
  unfold choosePrimeDataScoreStep at hscore
  cases hbest_eq : best with
  | some old =>
      rw [hbest_eq] at hscore
      simp only [Option.some.injEq] at hscore
      rw [← hscore]
      exact hbest old hbest_eq
  | none =>
      rw [hbest_eq] at hscore
      exact primeChoiceDataScore_fModP_eq f c score hscore

private theorem choosePrimeDataScore_fold_prime
    (f : ZPoly) (candidates : List SmallPrimeCandidate)
    (best : Option PrimeChoiceDataScore) (score : PrimeChoiceDataScore)
    (hbest : ∀ old, best = some old → Nat.Prime old.data.p)
    (hscore :
      candidates.foldl (choosePrimeDataScoreStep f) best = some score) :
    Nat.Prime score.data.p := by
  induction candidates generalizing best with
  | nil =>
      exact hbest score hscore
  | cons c candidates ih =>
      exact ih (choosePrimeDataScoreStep f best c)
        (fun old hold =>
          choosePrimeDataScoreStep_prime f best c old hbest hold)
        hscore

private theorem choosePrimeDataScore_fold_p_le
    (f : ZPoly) (candidates : List SmallPrimeCandidate)
    (best : Option PrimeChoiceDataScore) (score : PrimeChoiceDataScore)
    (hcandidates : ∀ c ∈ candidates, c.p ≤ 500)
    (hbest : ∀ old, best = some old → old.data.p ≤ 500)
    (hscore :
      candidates.foldl (choosePrimeDataScoreStep f) best = some score) :
    score.data.p ≤ 500 := by
  induction candidates generalizing best with
  | nil =>
      exact hbest score hscore
  | cons c candidates ih =>
      exact ih (choosePrimeDataScoreStep f best c)
        (fun c' hc' => hcandidates c' (List.mem_cons_of_mem c hc'))
        (fun old hold =>
          choosePrimeDataScoreStep_p_le f best c old
            (hcandidates c (List.mem_cons_self)) hbest hold)
        hscore

private theorem choosePrimeDataScore_fold_fModP_eq
    (f : ZPoly) (candidates : List SmallPrimeCandidate)
    (best : Option PrimeChoiceDataScore) (score : PrimeChoiceDataScore)
    (hbest : ∀ old, best = some old →
      old.data.fModP =
        @ZPoly.modP old.data.p old.data.bounds f)
    (hscore :
      candidates.foldl (choosePrimeDataScoreStep f) best = some score) :
    score.data.fModP =
      @ZPoly.modP score.data.p score.data.bounds f := by
  induction candidates generalizing best with
  | nil =>
      exact hbest score hscore
  | cons c candidates ih =>
      exact ih (choosePrimeDataScoreStep f best c)
        (fun old hold =>
          choosePrimeDataScoreStep_fModP_eq f best c old hbest hold)
        hscore

private theorem primeChoiceDataScore_isGoodPrime
    (f : ZPoly) (c : SmallPrimeCandidate) (score : PrimeChoiceDataScore)
    (hscore : primeChoiceDataScore f c = some score) :
    @isGoodPrime f score.data.p score.data.bounds = true := by
  unfold primeChoiceDataScore at hscore
  letI := c.bounds
  by_cases hgood : isGoodPrime f c.p
  · simp [hgood] at hscore
    cases hscore
    exact hgood
  · simp [hgood] at hscore

private theorem betterPrimeChoiceDataScore_isGoodPrime
    (f : ZPoly) (old new score : PrimeChoiceDataScore)
    (hold : @isGoodPrime f old.data.p old.data.bounds = true)
    (hnew : @isGoodPrime f new.data.p new.data.bounds = true)
    (hscore : betterPrimeChoiceDataScore old new = score) :
    @isGoodPrime f score.data.p score.data.bounds = true := by
  unfold betterPrimeChoiceDataScore at hscore
  split at hscore
  · cases hscore
    exact hnew
  · cases hscore
    exact hold

private theorem choosePrimeDataScoreStep_isGoodPrime
    (f : ZPoly) (best : Option PrimeChoiceDataScore) (c : SmallPrimeCandidate)
    (score : PrimeChoiceDataScore)
    (hbest : ∀ old, best = some old →
      @isGoodPrime f old.data.p old.data.bounds = true)
    (hscore : choosePrimeDataScoreStep f best c = some score) :
    @isGoodPrime f score.data.p score.data.bounds = true := by
  unfold choosePrimeDataScoreStep at hscore
  cases hbest_eq : best with
  | some old =>
      rw [hbest_eq] at hscore
      simp only [Option.some.injEq] at hscore
      rw [← hscore]
      exact hbest old hbest_eq
  | none =>
      rw [hbest_eq] at hscore
      exact primeChoiceDataScore_isGoodPrime f c score hscore

private theorem choosePrimeDataScore_fold_isGoodPrime
    (f : ZPoly) (candidates : List SmallPrimeCandidate)
    (best : Option PrimeChoiceDataScore) (score : PrimeChoiceDataScore)
    (hbest : ∀ old, best = some old →
      @isGoodPrime f old.data.p old.data.bounds = true)
    (hscore :
      candidates.foldl (choosePrimeDataScoreStep f) best = some score) :
    @isGoodPrime f score.data.p score.data.bounds = true := by
  induction candidates generalizing best with
  | nil =>
      exact hbest score hscore
  | cons c candidates ih =>
      exact ih (choosePrimeDataScoreStep f best c)
        (fun old hold =>
          choosePrimeDataScoreStep_isGoodPrime f best c old hbest hold)
        hscore

/--
Optional prime selection: returns `some` with the chosen `PrimeChoiceData` when
the fixed candidate search finds a good prime for `f`, and `none` otherwise.

The search first folds `choosePrimeDataScoreStep` over the deterministic
small-prime prefix. If that prefix selects an admissible prime, the original
tie-breaking is preserved. If the prefix exhausts without selecting any prime,
the search folds over the fixed extended prime list through `499`, covering
every odd prime in the hot-path interval `[3, 500]`.
-/
@[expose]
def choosePrimeData? (f : ZPoly) : Option PrimeChoiceData :=
  match smallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
  | some score => some score.data
  | none =>
      (extendedSmallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none)
      |>.map (fun score => score.data)

/-- Do not stop a prime trial on a halving improvement below this factor count;
at small width, continuing toward a modular irreducibility certificate is cheap
and disproportionately valuable. -/
private def probeEarlyFactorFloor : Nat := 8

/-- Continue from a first good prime for at most `extra` further good primes,
retaining a choice only after a material modular-width reduction. Non-good
candidates do not consume fuel, so the scan is additionally bounded by the
finite candidate list. Stop on an irreducible image, or on a halving improvement
that still leaves substantial Hensel width. -/
private def improvePrimeData? (f : ZPoly) (first : PrimeChoiceDataScore) :
    Nat → List SmallPrimeCandidate → PrimeChoiceDataScore
  | _, [] => first
  | 0, _ => first
  | extra + 1, c :: candidates =>
      match primeChoiceDataScore f c with
      | some score =>
          if score.factorCount = 1 then score
          else if probeEarlyFactorFloor ≤ score.factorCount ∧
              2 * score.factorCount ≤ first.factorCount then score
          else improvePrimeData? f (betterPrimeChoiceDataScore first score) extra candidates
      | none => improvePrimeData? f first (extra + 1) candidates

/-- Minimum modular width that justifies checking a high-degree transform. -/
private def probeMinFactors : Nat := 24

/-- Minimum modular width that justifies checking a coefficient-swollen transform. -/
private def probeSwollenFactors : Nat := 9

/-- Degree above which a very wide modular image justifies a bounded trial. -/
private def probeMinDegree : Nat := 50

/-- Degree above which a prime cyclotomic's uniform coefficients justify a trial. -/
private def probeCyclotomicDegree : Nat := 50

/-- Minimum coefficient `log2` that marks a swollen monic transform. -/
private def probeCoeffLog : Nat := 512

/-- Recognize `x^n - 1` with even `n`. Recursive classical splitting already
peels the explicit difference-of-squares structure cheaply, so a large modular
factor count is not evidence that prime look-ahead will pay for itself. -/
private def isEvenPowerDifference (f : ZPoly) : Bool :=
  decide (f.degree?.getD 0 % 2 = 0) &&
    match f.toArray.toList with
    | -1 :: coeffs =>
        match coeffs.reverse with
        | 1 :: middle => middle.all (fun coeff => coeff == 0)
        | _ => false
    | _ => false

#guard isEvenPowerDifference (DensePoly.ofCoeffs #[-1, 0, 0, 0, 1]) = true
#guard isEvenPowerDifference (DensePoly.ofCoeffs #[-1, 0, 0, 1]) = false
#guard isEvenPowerDifference (DensePoly.ofCoeffs #[-1, 1, 0, 0, 1]) = false
#guard isEvenPowerDifference (DensePoly.ofCoeffs #[1, 0, 0, 0, 1]) = false

/-- Whether the first modular factorization predicts enough downstream work to
justify bounded prime look-ahead. -/
private def shouldProbePrime (f : ZPoly) (score : PrimeChoiceDataScore) : Bool :=
  let coeffs := f.toArray
  let degree := f.degree?.getD 0
  (decide (probeSwollenFactors ≤ score.factorCount) &&
      coeffs.any (fun coeff => probeCoeffLog ≤ coeff.natAbs.log2)) ||
    (decide (probeMinDegree ≤ degree) &&
      decide (probeMinFactors ≤ score.factorCount) && !isEvenPowerDifference f) ||
    (decide (probeCyclotomicDegree ≤ degree) &&
      Hex.Nat.isPrimeTrial coeffs.size && coeffs.all (fun coeff => coeff == 1))

private def probeGuardScore (factorCount : Nat) : PrimeChoiceDataScore :=
  { data := default, factorCount }

private def probeGuardPowerSum : ZPoly :=
  DensePoly.ofCoeffs <|
    ((Array.replicate 51 (0 : Int)).set! 0 1).set! 50 1

private def probeGuardPowerDifference : ZPoly :=
  DensePoly.ofCoeffs <|
    ((Array.replicate 51 (0 : Int)).set! 0 (-1)).set! 50 1

private def probeGuardLowDegree : ZPoly :=
  DensePoly.ofCoeffs <|
    ((Array.replicate 50 (0 : Int)).set! 0 1).set! 49 1

#guard shouldProbePrime probeGuardPowerSum (probeGuardScore 24) = true
#guard shouldProbePrime probeGuardPowerDifference (probeGuardScore 24) = false
#guard shouldProbePrime probeGuardLowDegree (probeGuardScore 24) = false
#guard shouldProbePrime
    (DensePoly.ofCoeffs (Array.replicate 61 (1 : Int))) (probeGuardScore 2) = true
#guard shouldProbePrime
    (DensePoly.ofCoeffs #[(Int.ofNat (2 ^ 512)), 0, 1]) (probeGuardScore 9) = true

/-- First-good selection with bounded modular-factor-width look-ahead. -/
private def chooseAdaptiveFrom? (f : ZPoly) (extra : Nat) :
    List SmallPrimeCandidate → Option PrimeChoiceDataScore
  | [] => none
  | c :: candidates =>
      match primeChoiceDataScore f c with
      | some score =>
          if score.factorCount = 1 then some score
          else if shouldProbePrime f score then
            some (improvePrimeData? f score extra candidates)
          else
            some score
      | none => chooseAdaptiveFrom? f extra candidates

/-- Select the first good prime, except that a split modular image receives a
bounded search for a good prime with fewer modular factors, with the early-stop
policy implemented by `improvePrimeData?`. -/
def choosePrimeDataAdaptive? (f : ZPoly) (extra : Nat) : Option PrimeChoiceData :=
  (chooseAdaptiveFrom? f extra
    (smallPrimeCandidates ++ extendedSmallPrimeCandidates)).map (·.data)

private theorem improvePrimeData?_property
    (f : ZPoly) (P : PrimeChoiceDataScore → Prop) (first : PrimeChoiceDataScore)
    (hfirst : P first)
    (hcandidate : ∀ c score, primeChoiceDataScore f c = some score → P score) :
    ∀ extra candidates, P (improvePrimeData? f first extra candidates) := by
  intro extra candidates
  induction candidates generalizing extra first with
  | nil => simp [improvePrimeData?, hfirst]
  | cons c candidates ih =>
      cases extra with
      | zero => simp [improvePrimeData?, hfirst]
      | succ extra =>
          simp only [improvePrimeData?]
          cases hscore : primeChoiceDataScore f c with
          | none =>
              simp only
              exact ih (first := first) (extra := extra + 1) hfirst
          | some score =>
              simp only
              by_cases hone : score.factorCount = 1
              · simp only [hone, if_true]
                exact hcandidate c score hscore
              · simp only [hone, if_false]
                by_cases hhalf : probeEarlyFactorFloor ≤ score.factorCount ∧
                    2 * score.factorCount ≤ first.factorCount
                · simp only [hhalf]
                  exact hcandidate c score hscore
                · simp only [hhalf, if_false]
                  apply ih (first := betterPrimeChoiceDataScore first score)
                    (extra := extra)
                  unfold betterPrimeChoiceDataScore
                  split
                  · exact hcandidate c score hscore
                  · exact hfirst

private theorem improvePrimeData?_p_le
    (f : ZPoly) (first : PrimeChoiceDataScore)
    (hfirst : first.data.p ≤ 500) :
    ∀ extra candidates,
      (∀ c ∈ candidates, c.p ≤ 500) →
      (improvePrimeData? f first extra candidates).data.p ≤ 500 := by
  intro extra candidates hall
  induction candidates generalizing extra first with
  | nil => simp [improvePrimeData?, hfirst]
  | cons c candidates ih =>
      have htail : ∀ d ∈ candidates, d.p ≤ 500 := by
        intro d hd
        exact hall d (List.mem_cons_of_mem c hd)
      cases extra with
      | zero => simp [improvePrimeData?, hfirst]
      | succ extra =>
          simp only [improvePrimeData?]
          cases hscore : primeChoiceDataScore f c with
          | none =>
              simp only
              exact ih (first := first) (extra := extra + 1) hfirst htail
          | some score =>
              simp only
              by_cases hone : score.factorCount = 1
              · simp only [hone, if_true]
                exact primeChoiceDataScore_p_le f c score
                  (hall c (by simp)) hscore
              · simp only [hone, if_false]
                by_cases hhalf : probeEarlyFactorFloor ≤ score.factorCount ∧
                    2 * score.factorCount ≤ first.factorCount
                · simp only [hhalf]
                  exact primeChoiceDataScore_p_le f c score
                    (hall c (by simp)) hscore
                · simp only [hhalf, if_false]
                  apply ih (first := betterPrimeChoiceDataScore first score)
                    (extra := extra)
                  · unfold betterPrimeChoiceDataScore
                    split
                    · exact primeChoiceDataScore_p_le f c score
                        (hall c (by simp)) hscore
                    · exact hfirst
                  · exact htail

private theorem chooseAdaptiveFrom?_property
    (f : ZPoly) (extra : Nat) (P : PrimeChoiceDataScore → Prop)
    (hcandidate : ∀ c score, primeChoiceDataScore f c = some score → P score) :
    ∀ candidates score,
      chooseAdaptiveFrom? f extra candidates = some score → P score := by
  intro candidates score h
  induction candidates generalizing score with
  | nil => simp [chooseAdaptiveFrom?] at h
  | cons c candidates ih =>
      simp only [chooseAdaptiveFrom?] at h
      cases hcurrent : primeChoiceDataScore f c with
      | none =>
          simp only [hcurrent] at h
          exact ih score h
      | some current =>
          simp only [hcurrent] at h
          have hproperty : P current := hcandidate c current hcurrent
          by_cases hone : current.factorCount = 1
          · simp only [hone, if_true, Option.some.injEq] at h
            rw [← h]
            exact hproperty
          · simp only [hone, if_false] at h
            by_cases hprobe : shouldProbePrime f current = true
            · simp only [hprobe, if_true, Option.some.injEq] at h
              rw [← h]
              exact improvePrimeData?_property f P current hproperty hcandidate extra candidates
            · have hfalse : shouldProbePrime f current = false :=
                Bool.eq_false_iff.mpr hprobe
              simp only [hfalse, Bool.false_eq_true, if_false, Option.some.injEq] at h
              rw [← h]
              exact hproperty

private theorem chooseAdaptiveFrom?_p_le
    (f : ZPoly) (extra : Nat) :
    ∀ candidates score,
      (∀ c ∈ candidates, c.p ≤ 500) →
      chooseAdaptiveFrom? f extra candidates = some score →
      score.data.p ≤ 500 := by
  intro candidates score hall h
  induction candidates generalizing score with
  | nil => simp [chooseAdaptiveFrom?] at h
  | cons c candidates ih =>
      have htail : ∀ d ∈ candidates, d.p ≤ 500 := by
        intro d hd
        exact hall d (List.mem_cons_of_mem c hd)
      simp only [chooseAdaptiveFrom?] at h
      cases hcurrent : primeChoiceDataScore f c with
      | none =>
          simp only [hcurrent] at h
          exact ih score htail h
      | some current =>
          simp only [hcurrent] at h
          have hcurrent_le : current.data.p ≤ 500 :=
            primeChoiceDataScore_p_le f c current (hall c (by simp)) hcurrent
          by_cases hone : current.factorCount = 1
          · simp only [hone, if_true, Option.some.injEq] at h
            rw [← h]
            exact hcurrent_le
          · simp only [hone, if_false] at h
            split at h
            · simp only [Option.some.injEq] at h
              rw [← h]
              exact improvePrimeData?_p_le f current hcurrent_le extra candidates htail
            · simp only [Option.some.injEq] at h
              rw [← h]
              exact hcurrent_le

private theorem choosePrimeDataAdaptive?_property
    (f : ZPoly) (extra : Nat) (data : PrimeChoiceData)
    (P : PrimeChoiceDataScore → Prop)
    (hcandidate : ∀ c score, primeChoiceDataScore f c = some score → P score)
    (hdata : choosePrimeDataAdaptive? f extra = some data) :
    ∃ score, score.data = data ∧ P score := by
  unfold choosePrimeDataAdaptive? at hdata
  cases hscore : chooseAdaptiveFrom? f extra
      (smallPrimeCandidates ++ extendedSmallPrimeCandidates) with
  | none => simp [hscore] at hdata
  | some score =>
      simp [hscore] at hdata
      exact ⟨score, hdata, chooseAdaptiveFrom?_property f extra P hcandidate _ _ hscore⟩

/-- Adaptive prime selection returns only prime moduli. -/
theorem choosePrimeDataAdaptive?_prime
    (f : ZPoly) (extra : Nat) (data : PrimeChoiceData)
    (hdata : choosePrimeDataAdaptive? f extra = some data) :
    Nat.Prime data.p := by
  obtain ⟨score, rfl, hprime⟩ := choosePrimeDataAdaptive?_property f extra data
    (fun score => Nat.Prime score.data.p)
    (fun c score hscore => primeChoiceDataScore_prime f c score hscore) hdata
  exact hprime

theorem choosePrimeDataAdaptive?_p_le_500
    (f : ZPoly) (extra : Nat) (data : PrimeChoiceData)
    (hdata : choosePrimeDataAdaptive? f extra = some data) :
    data.p ≤ 500 := by
  unfold choosePrimeDataAdaptive? at hdata
  cases hscore : chooseAdaptiveFrom? f extra
      (smallPrimeCandidates ++ extendedSmallPrimeCandidates) with
  | none => simp [hscore] at hdata
  | some score =>
      simp [hscore] at hdata
      rw [← hdata]
      exact chooseAdaptiveFrom?_p_le f extra _ score
        (fun c hc => (mem_hotPathCandidates_prime hc).2.2) hscore

/-- Adaptive prime selection caches the reduction of its input polynomial. -/
theorem choosePrimeDataAdaptive?_fModP_eq
    (f : ZPoly) (extra : Nat) (data : PrimeChoiceData)
    (hdata : choosePrimeDataAdaptive? f extra = some data) :
    data.fModP = @ZPoly.modP data.p data.bounds f := by
  obtain ⟨score, rfl, heq⟩ := choosePrimeDataAdaptive?_property f extra data
    (fun score => score.data.fModP =
      @ZPoly.modP score.data.p score.data.bounds f)
    (fun c score hscore => primeChoiceDataScore_fModP_eq f c score hscore) hdata
  exact heq

/-- Adaptive prime selection returns a prime satisfying the admissibility test. -/
theorem choosePrimeDataAdaptive?_isGoodPrime
    (f : ZPoly) (extra : Nat) (data : PrimeChoiceData)
    (hdata : choosePrimeDataAdaptive? f extra = some data) :
    @isGoodPrime f data.p data.bounds = true := by
  obtain ⟨score, rfl, hgood⟩ := choosePrimeDataAdaptive?_property f extra data
    (fun score => @isGoodPrime f score.data.p score.data.bounds = true)
    (fun c score hscore => primeChoiceDataScore_isGoodPrime f c score hscore) hdata
  exact hgood

/-- Ordinary prime selection returns only prime moduli. -/
theorem choosePrimeData?_prime
    (f : ZPoly) (data : PrimeChoiceData)
    (hdata : choosePrimeData? f = some data) :
    Nat.Prime data.p := by
  unfold choosePrimeData? at hdata
  cases hscore :
      smallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
  | some score =>
      simp [hscore] at hdata
      cases hdata
      exact choosePrimeDataScore_fold_prime f smallPrimeCandidates none score
        (by intro old hnone; cases hnone)
        hscore
  | none =>
      simp [hscore] at hdata
      cases hext :
          extendedSmallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
      | none =>
          simp [hext] at hdata
      | some escore =>
          simp [hext] at hdata
          cases hdata
          exact choosePrimeDataScore_fold_prime f extendedSmallPrimeCandidates none
            escore (by intro old hnone; cases hnone) hext

/--
Every prime returned by the fixed hot-path search is at most `500`.
-/
theorem choosePrimeData?_p_le_500
    (f : ZPoly) (data : PrimeChoiceData)
    (hdata : choosePrimeData? f = some data) :
    data.p ≤ 500 := by
  unfold choosePrimeData? at hdata
  cases hscore :
      smallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
  | some score =>
      simp [hscore] at hdata
      cases hdata
      exact choosePrimeDataScore_fold_p_le f smallPrimeCandidates none score
        (fun c hc =>
          (mem_hotPathCandidates_prime
            (show c ∈ hotPathCandidates from List.mem_append_left _ hc)).2.2)
        (by intro old hnone; cases hnone)
        hscore
  | none =>
      simp [hscore] at hdata
      cases hext :
          extendedSmallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
      | none =>
          simp [hext] at hdata
      | some escore =>
          simp [hext] at hdata
          cases hdata
          exact choosePrimeDataScore_fold_p_le f extendedSmallPrimeCandidates none
            escore
            (fun c hc =>
              (mem_hotPathCandidates_prime
                (show c ∈ hotPathCandidates from List.mem_append_right _ hc)).2.2)
            (by intro old hnone; cases hnone)
            hext

/-- Ordinary prime selection caches the reduction of its input polynomial. -/
theorem choosePrimeData?_fModP_eq
    (f : ZPoly) (data : PrimeChoiceData)
    (hdata : choosePrimeData? f = some data) :
    data.fModP = @ZPoly.modP data.p data.bounds f := by
  unfold choosePrimeData? at hdata
  cases hscore :
      smallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
  | some score =>
      simp [hscore] at hdata
      cases hdata
      exact choosePrimeDataScore_fold_fModP_eq f smallPrimeCandidates none score
        (by intro old hnone; cases hnone)
        hscore
  | none =>
      simp [hscore] at hdata
      cases hext :
          extendedSmallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
      | none =>
          simp [hext] at hdata
      | some escore =>
          simp [hext] at hdata
          cases hdata
          exact choosePrimeDataScore_fold_fModP_eq f extendedSmallPrimeCandidates none
            escore (by intro old hnone; cases hnone) hext

/--
When `choosePrimeData? f` succeeds, the selected prime is a good prime for `f`
in the executable sense (modulus at least three, leading coefficient survives
reduction, modular image is square-free).
-/
theorem choosePrimeData?_isGoodPrime
    (f : ZPoly) (data : PrimeChoiceData)
    (hdata : choosePrimeData? f = some data) :
    @isGoodPrime f data.p data.bounds = true := by
  unfold choosePrimeData? at hdata
  cases hscore :
      smallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
  | some score =>
      simp [hscore] at hdata
      cases hdata
      exact choosePrimeDataScore_fold_isGoodPrime f smallPrimeCandidates none score
        (by intro old hnone; cases hnone)
        hscore
  | none =>
      simp [hscore] at hdata
      cases hext :
          extendedSmallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
      | none =>
          simp [hext] at hdata
      | some escore =>
          simp [hext] at hdata
          cases hdata
          exact choosePrimeDataScore_fold_isGoodPrime f extendedSmallPrimeCandidates none
            escore (by intro old hnone; cases hnone) hext

private theorem primeChoiceDataScore_eq_none_iff
    (f : ZPoly) (c : SmallPrimeCandidate) :
    primeChoiceDataScore f c = none ↔
      @isGoodPrime f c.p c.bounds = false := by
  unfold primeChoiceDataScore
  letI := c.bounds
  cases isGoodPrime f c.p with
  | true => simp
  | false => simp

private theorem choosePrimeDataScoreStep_some_ne_none
    (f : ZPoly) (old : PrimeChoiceDataScore) (c : SmallPrimeCandidate) :
    choosePrimeDataScoreStep f (some old) c ≠ none := by
  unfold choosePrimeDataScoreStep
  cases primeChoiceDataScore f c <;> simp

private theorem choosePrimeDataScore_fold_some_ne_none
    (f : ZPoly) (candidates : List SmallPrimeCandidate)
    (old : PrimeChoiceDataScore) :
    candidates.foldl (choosePrimeDataScoreStep f) (some old) ≠ none := by
  induction candidates generalizing old with
  | nil => simp
  | cons c cs ih =>
      simp only [List.foldl_cons]
      cases hstep : choosePrimeDataScoreStep f (some old) c with
      | none => exact (choosePrimeDataScoreStep_some_ne_none f old c hstep).elim
      | some new => exact ih new

private theorem choosePrimeDataScore_fold_none_forall_isGoodPrime_false
    (f : ZPoly) (candidates : List SmallPrimeCandidate)
    (hfold : candidates.foldl (choosePrimeDataScoreStep f) none = none) :
    ∀ c ∈ candidates, @isGoodPrime f c.p c.bounds = false := by
  induction candidates with
  | nil => intro c hc; exact absurd hc List.not_mem_nil
  | cons c cs ih =>
      simp only [List.foldl_cons] at hfold
      have hstep_eq :
          choosePrimeDataScoreStep f none c = primeChoiceDataScore f c := by
        unfold choosePrimeDataScoreStep
        cases primeChoiceDataScore f c <;> rfl
      rw [hstep_eq] at hfold
      cases hscore : primeChoiceDataScore f c with
      | none =>
          rw [hscore] at hfold
          have hbad : @isGoodPrime f c.p c.bounds = false :=
            (primeChoiceDataScore_eq_none_iff f c).mp hscore
          intro c' hc'
          rcases List.mem_cons.mp hc' with rfl | hin
          · exact hbad
          · exact ih hfold c' hin
      | some new =>
          rw [hscore] at hfold
          exact (choosePrimeDataScore_fold_some_ne_none f cs new hfold).elim

/--
When `choosePrimeData? f` returns `none`, every candidate in the hot-path
prime list fails the executable good-prime predicate `Hex.isGoodPrime f`.

This records that failure of the fixed candidate fold means every retained
candidate was tried and rejected.
-/
theorem mem_hotPathCandidates_isGoodPrime_false_of_choosePrimeData?_none
    {f : ZPoly} (hf : choosePrimeData? f = none)
    {c : SmallPrimeCandidate} (hc : c ∈ hotPathCandidates) :
    @isGoodPrime f c.p c.bounds = false := by
  unfold choosePrimeData? at hf
  cases hsmall :
      smallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
  | some score => simp [hsmall] at hf
  | none =>
      simp [hsmall] at hf
      cases hext :
          extendedSmallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
      | some score => simp [hext] at hf
      | none =>
          unfold hotPathCandidates at hc
          rcases List.mem_append.mp hc with hsmall_mem | hext_mem
          · exact choosePrimeDataScore_fold_none_forall_isGoodPrime_false f
              smallPrimeCandidates hsmall c hsmall_mem
          · exact choosePrimeDataScore_fold_none_forall_isGoodPrime_false f
              extendedSmallPrimeCandidates hext c hext_mem

/-- A good member of the fixed hot-path list forces prime selection to
succeed.  This is the direct contrapositive of the selector's complete
failure certificate. -/
theorem choosePrimeData?_ne_none_of_good
    {f : ZPoly} {c : SmallPrimeCandidate}
    (hc : c ∈ hotPathCandidates)
    (hgood : @isGoodPrime f c.p c.bounds = true) :
    choosePrimeData? f ≠ none := by
  intro hnone
  have hbad :=
    mem_hotPathCandidates_isGoodPrime_false_of_choosePrimeData?_none hnone hc
  rw [hgood] at hbad
  simp at hbad

private theorem chooseAdaptiveFrom?_ne_none_of_good
    (f : ZPoly) (extra : Nat) {c : SmallPrimeCandidate}
    (hgood : @isGoodPrime f c.p c.bounds = true) :
    ∀ candidates, c ∈ candidates → chooseAdaptiveFrom? f extra candidates ≠ none := by
  intro candidates hc
  induction candidates with
  | nil => simp at hc
  | cons head tail ih =>
      unfold chooseAdaptiveFrom?
      cases hscore : primeChoiceDataScore f head with
      | some score =>
          by_cases hone : score.factorCount = 1
          · simp [hone]
          · simp only [hone, if_false]
            split <;> simp
      | none =>
          simp only
          have hne : c ≠ head := by
            intro heq
            subst head
            have hbad := (primeChoiceDataScore_eq_none_iff f c).mp hscore
            rw [hgood] at hbad
            simp at hbad
          exact ih ((List.mem_cons.mp hc).resolve_left hne)

/-- A good member of the fixed hot-path list also forces the adaptive selector
to succeed; its look-ahead changes only which successful record is returned. -/
theorem choosePrimeDataAdaptive?_ne_none_of_good
    {f : ZPoly} {c : SmallPrimeCandidate} {extra : Nat}
    (hc : c ∈ hotPathCandidates)
    (hgood : @isGoodPrime f c.p c.bounds = true) :
    choosePrimeDataAdaptive? f extra ≠ none := by
  unfold choosePrimeDataAdaptive?
  unfold hotPathCandidates at hc
  have hselected := chooseAdaptiveFrom?_ne_none_of_good f extra hgood _ hc
  intro hmap
  cases hscore : chooseAdaptiveFrom? f extra
      (smallPrimeCandidates ++ extendedSmallPrimeCandidates) with
  | none => exact hselected hscore
  | some score => simp [hscore] at hmap

/--
Invariant capturing that `data.factorsModP` is exactly the Berlekamp factor
output for the monic modular image used by prime selection.  Phrased as an
existential bundling the prime witness and the nonzero-image proof so that
it threads through the executable prime-selection fold; the `Lean.Grind.Field`
instance required by `Berlekamp.berlekampFactor` is constructed explicitly
from `hprime`, so callers can match it against any field instance built from
the same prime witness via proof irrelevance of `ZMod64.PrimeModulus`.
-/
@[expose]
def factorsModPBerlekampForm
    (f : ZPoly) (data : PrimeChoiceData) : Prop :=
  letI := data.bounds
  ∃ (hprime : Nat.Prime data.p)
    (hzero : (ZPoly.modP data.p f).isZero = false),
    data.factorsModP =
      ((@Berlekamp.berlekampFactor data.p data.bounds
        (monicModularImage (ZPoly.modP data.p f))
        (monicModularImage_monic hprime (ZPoly.modP data.p f) hzero)
        (@zmod64FieldOfPrime data.p data.bounds
          (ZMod64.primeModulusOfPrime hprime))).factors.map monicModularImage).toArray

private theorem primeChoiceDataScore_factorsModPBerlekampForm
    (f : ZPoly) (c : SmallPrimeCandidate) (score : PrimeChoiceDataScore)
    (hscore : primeChoiceDataScore f c = some score) :
    factorsModPBerlekampForm f score.data := by
  unfold primeChoiceDataScore at hscore
  letI := c.bounds
  by_cases hgood : isGoodPrime f c.p
  · simp [hgood] at hscore
    cases hscore
    have hzero : (ZPoly.modP c.p f).isZero = false :=
      isGoodPrime_modP_isZero_false f c.p hgood
    refine ⟨c.prime, hzero, ?_⟩
    show berlekampFactorsModP f c = _
    exact berlekampFactorsModP_eq_of_isZero_false f c hzero
  · simp [hgood] at hscore

private theorem betterPrimeChoiceDataScore_factorsModPBerlekampForm
    (f : ZPoly) (old new score : PrimeChoiceDataScore)
    (hold : factorsModPBerlekampForm f old.data)
    (hnew : factorsModPBerlekampForm f new.data)
    (hscore : betterPrimeChoiceDataScore old new = score) :
    factorsModPBerlekampForm f score.data := by
  unfold betterPrimeChoiceDataScore at hscore
  split at hscore
  · cases hscore
    exact hnew
  · cases hscore
    exact hold

private theorem choosePrimeDataScoreStep_factorsModPBerlekampForm
    (f : ZPoly) (best : Option PrimeChoiceDataScore) (c : SmallPrimeCandidate)
    (score : PrimeChoiceDataScore)
    (hbest : ∀ old, best = some old → factorsModPBerlekampForm f old.data)
    (hscore : choosePrimeDataScoreStep f best c = some score) :
    factorsModPBerlekampForm f score.data := by
  unfold choosePrimeDataScoreStep at hscore
  cases hbest_eq : best with
  | some old =>
      rw [hbest_eq] at hscore
      simp only [Option.some.injEq] at hscore
      rw [← hscore]
      exact hbest old hbest_eq
  | none =>
      rw [hbest_eq] at hscore
      exact primeChoiceDataScore_factorsModPBerlekampForm f c score hscore

private theorem choosePrimeDataScore_fold_factorsModPBerlekampForm
    (f : ZPoly) (candidates : List SmallPrimeCandidate)
    (best : Option PrimeChoiceDataScore) (score : PrimeChoiceDataScore)
    (hbest : ∀ old, best = some old → factorsModPBerlekampForm f old.data)
    (hscore :
      candidates.foldl (choosePrimeDataScoreStep f) best = some score) :
    factorsModPBerlekampForm f score.data := by
  induction candidates generalizing best with
  | nil =>
      exact hbest score hscore
  | cons c candidates ih =>
      exact ih (choosePrimeDataScoreStep f best c)
        (fun old hold =>
          choosePrimeDataScoreStep_factorsModPBerlekampForm f best c old hbest hold)
        hscore

/-- Primality provenance for one explicit diagnostic/degree-obstruction trial. -/
theorem probePrimeData?_prime
    (f : ZPoly) (c : SmallPrimeCandidate) (data : PrimeChoiceData)
    (hdata : probePrimeData? f c = some data) :
    Nat.Prime data.p := by
  unfold probePrimeData? at hdata
  cases hscore : primeChoiceDataScore f c with
  | none => simp [hscore] at hdata
  | some score =>
      simp [hscore] at hdata
      subst data
      exact primeChoiceDataScore_prime f c score hscore

/-- An explicit trial inherits any proved upper bound on its candidate prime. -/
theorem probePrimeData?_p_le
    (f : ZPoly) (c : SmallPrimeCandidate) (data : PrimeChoiceData)
    (hc : c.p ≤ 500)
    (hdata : probePrimeData? f c = some data) :
    data.p ≤ 500 := by
  unfold probePrimeData? at hdata
  cases hscore : primeChoiceDataScore f c with
  | none => simp [hscore] at hdata
  | some score =>
      simp [hscore] at hdata
      subst data
      exact primeChoiceDataScore_p_le f c score hc hscore

/-- Good-prime provenance for one explicit diagnostic/degree-obstruction trial. -/
theorem probePrimeData?_isGoodPrime
    (f : ZPoly) (c : SmallPrimeCandidate) (data : PrimeChoiceData)
    (hdata : probePrimeData? f c = some data) :
    @isGoodPrime f data.p data.bounds = true := by
  unfold probePrimeData? at hdata
  cases hscore : primeChoiceDataScore f c with
  | none => simp [hscore] at hdata
  | some score =>
      simp [hscore] at hdata
      subst data
      exact primeChoiceDataScore_isGoodPrime f c score hscore

/-- Modular-image provenance for one explicit trial. -/
theorem probePrimeData?_fModP_eq
    (f : ZPoly) (c : SmallPrimeCandidate) (data : PrimeChoiceData)
    (hdata : probePrimeData? f c = some data) :
    data.fModP = @ZPoly.modP data.p data.bounds f := by
  unfold probePrimeData? at hdata
  cases hscore : primeChoiceDataScore f c with
  | none => simp [hscore] at hdata
  | some score =>
      simp [hscore] at hdata
      subst data
      exact primeChoiceDataScore_fModP_eq f c score hscore

/-- Berlekamp-factor provenance for one explicit trial. -/
theorem probePrimeData?_form
    (f : ZPoly) (c : SmallPrimeCandidate) (data : PrimeChoiceData)
    (hdata : probePrimeData? f c = some data) :
    factorsModPBerlekampForm f data := by
  unfold probePrimeData? at hdata
  cases hscore : primeChoiceDataScore f c with
  | none => simp [hscore] at hdata
  | some score =>
      simp [hscore] at hdata
      subst data
      exact primeChoiceDataScore_factorsModPBerlekampForm f c score hscore

/-- Adaptive selection returns the certified Berlekamp factorization of the modular image. -/
theorem choosePrimeDataAdaptive?_form
    (f : ZPoly) (extra : Nat) (data : PrimeChoiceData)
    (hdata : choosePrimeDataAdaptive? f extra = some data) :
    letI := data.bounds
    ∃ (hzero : (ZPoly.modP data.p f).isZero = false),
      data.factorsModP =
        ((@Berlekamp.berlekampFactor data.p data.bounds
          (monicModularImage (ZPoly.modP data.p f))
          (monicModularImage_monic
            (choosePrimeDataAdaptive?_prime f extra data hdata)
            (ZPoly.modP data.p f) hzero)
          (@zmod64FieldOfPrime data.p data.bounds
            (ZMod64.primeModulusOfPrime
              (choosePrimeDataAdaptive?_prime f extra data hdata)))).factors.map
                monicModularImage).toArray := by
  obtain ⟨score, rfl, hform⟩ := choosePrimeDataAdaptive?_property f extra data
    (fun score => factorsModPBerlekampForm f score.data)
    (fun c score hscore =>
      primeChoiceDataScore_factorsModPBerlekampForm f c score hscore) hdata
  obtain ⟨_, hzero, heq⟩ := hform
  exact ⟨hzero, heq⟩

/--
When `choosePrimeData? f` succeeds, the stored modular factor array is exactly
the Berlekamp factor output for the monic modular image of the selected
candidate.  Mirrors the `_prime` / `_fModP_eq` / `_isGoodPrime` provenance
chains, exposing the executable surface used by the small-mod singleton
irreducibility composition.
-/
theorem choosePrimeData?_factorsModP_berlekamp_form
    (f : ZPoly) (data : PrimeChoiceData)
    (hdata : choosePrimeData? f = some data) :
    letI := data.bounds
    ∃ (hzero : (ZPoly.modP data.p f).isZero = false),
      data.factorsModP =
        ((@Berlekamp.berlekampFactor data.p data.bounds
          (monicModularImage (ZPoly.modP data.p f))
          (monicModularImage_monic
            (choosePrimeData?_prime f data hdata)
            (ZPoly.modP data.p f) hzero)
          (@zmod64FieldOfPrime data.p data.bounds
            (ZMod64.primeModulusOfPrime
              (choosePrimeData?_prime f data hdata)))).factors.map
                monicModularImage).toArray := by
  unfold choosePrimeData? at hdata
  cases hscore :
      smallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
  | some score =>
      simp [hscore] at hdata
      cases hdata
      have hform :=
        choosePrimeDataScore_fold_factorsModPBerlekampForm f smallPrimeCandidates none
          score (by intro old hnone; cases hnone) hscore
      obtain ⟨_, hzero, heq⟩ := hform
      exact ⟨hzero, heq⟩
  | none =>
      simp [hscore] at hdata
      cases hext :
          extendedSmallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
      | none =>
          simp [hext] at hdata
      | some escore =>
          simp [hext] at hdata
          cases hdata
          have hform :=
            choosePrimeDataScore_fold_factorsModPBerlekampForm f
              extendedSmallPrimeCandidates none escore
              (by intro old hnone; cases hnone) hext
          obtain ⟨_, hzero, heq⟩ := hform
          exact ⟨hzero, heq⟩

/--
Small-mod singleton executable branch fact for the selected monic modular
image.

When `choosePrimeData?` succeeds and the public `factorsModP` field has size at
most one, the underlying Berlekamp factor list for
`monicModularImage (ZPoly.modP data.p f)` also has length at most one.  This is
the Mathlib-free shape fact needed before applying Berlekamp soundness in a
caller that already imports the heavier Rabin proof module.
-/
theorem choosePrimeData?_berlekampFactor_factors_length_le_one_of_small
    (f : ZPoly) (data : PrimeChoiceData)
    (hdata : choosePrimeData? f = some data)
    (hsmall : data.factorsModP.size ≤ 1) :
    letI := data.bounds
    ∃ (hzero : (@ZPoly.modP data.p data.bounds f).isZero = false),
      (@Berlekamp.berlekampFactor data.p data.bounds
        (@monicModularImage data.p data.bounds
          (@ZPoly.modP data.p data.bounds f))
        (monicModularImage_monic
          (choosePrimeData?_prime f data hdata)
          (@ZPoly.modP data.p data.bounds f) hzero)
        (@zmod64FieldOfPrime data.p data.bounds
          (ZMod64.primeModulusOfPrime
            (choosePrimeData?_prime f data hdata)))).factors.length ≤ 1 := by
  letI := data.bounds
  obtain ⟨hzero, hform⟩ :=
    choosePrimeData?_factorsModP_berlekamp_form f data hdata
  refine ⟨hzero, ?_⟩
  have hlen :
      (@Berlekamp.berlekampFactor data.p data.bounds
        (@monicModularImage data.p data.bounds
          (@ZPoly.modP data.p data.bounds f))
        (monicModularImage_monic
          (choosePrimeData?_prime f data hdata)
          (@ZPoly.modP data.p data.bounds f) hzero)
        (@zmod64FieldOfPrime data.p data.bounds
          (ZMod64.primeModulusOfPrime
            (choosePrimeData?_prime f data hdata)))).factors.length ≤ 1 := by
    simpa [hform] using hsmall
  exact hlen

/--
Lift the chosen modular factors to the requested precision for integer
recombination.
-/
@[expose]
def henselLiftData (f : ZPoly) (B : Nat) (d : PrimeChoiceData) : LiftData :=
  letI := d.bounds
  let factors := d.factorsModP.map (fun factor => FpPoly.liftToZ factor)
  { p := d.p
    p_pos := ZMod64.Bounds.pPos (p := d.p)
    k := B
    liftedFactors := ZPoly.multifactorLiftQuadratic d.p B f factors }

@[simp, grind =] theorem henselLiftData_p (f : ZPoly) (B : Nat) (d : PrimeChoiceData) :
    (henselLiftData f B d).p = d.p := rfl

@[simp, grind =] theorem henselLiftData_k (f : ZPoly) (B : Nat) (d : PrimeChoiceData) :
    (henselLiftData f B d).k = B := rfl

end Hex
