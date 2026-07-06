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

public import HexBerlekampZassenhaus.Certificate
public meta import HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.Certificate

public section
set_option backward.proofsInPublic true

/-!
This module collects `choosePrimeData?`/`Walk?`/`Score` with their correctness lemmas and `henselLiftData`.
-/
namespace Hex

/--
Compiled certificate generator for irreducibility of `f` over `ℤ` — the *prep*
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

structure PrimeChoiceDataScore where
  data : PrimeChoiceData
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

private def betterPrimeChoiceDataScore
    (old new : PrimeChoiceDataScore) : PrimeChoiceDataScore :=
  if new.factorCount < old.factorCount then
    new
  else
    old

def choosePrimeDataScoreStep
    (f : ZPoly) (best : Option PrimeChoiceDataScore) (c : SmallPrimeCandidate) :
    Option PrimeChoiceDataScore :=
  -- First-suitable selection (matching the verified Isabelle/AFP
  -- `Berlekamp_Zassenhaus` `find_prime`): once a suitable prime has been found,
  -- keep it and stop — crucially, do **not** evaluate `primeChoiceDataScore f c`
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
Build a `SmallPrimeCandidate` from an arbitrary natural number `p` if
`p` passes the executable trial-division primality test and satisfies the
small-modulus bound `p < 2^31`. Used by the post-prefix prime walk to produce candidates beyond
the fixed `smallPrimeCandidates` list with explicit primality and
`ZMod64.Bounds` evidence.
-/
private def mkExtendedSmallPrimeCandidate? (p : Nat) :
    Option SmallPrimeCandidate :=
  if hprime : Hex.Nat.isPrimeTrial p = true then
    if hbound : p < 2 ^ 31 then
      let prime := Hex.Nat.isPrimeTrial_isPrime hprime
      let bounds : ZMod64.Bounds p := { pPos := prime.pos, pLtR := hbound }
      some { p, bounds, prime }
    else
      none
  else
    none

/--
Input-dependent fuel for the post-prefix prime walk.

The small-prime prefix remains fixed for stable tie-breaking, but the fallback
walk is no longer a closed candidate set: larger coefficients give the trial
walk more room before the `Option` boundary reports `none`. The Mathlib-side D2
leaf theorem will prove this fuel is sufficient on primitive square-free inputs;
at this executable layer it is just the structurally recursive bound.
-/
private def choosePrimeDataWalkFuel (f : ZPoly) : Nat :=
  max 256 <| f.toArray.foldl (fun acc coeff => acc + coeff.natAbs) (2 * f.size + 1)

/--
Walk odd natural candidates starting at `start`, using `isPrimeTrial` to build
candidate records and stopping at the first good prime. The `fuel` argument is
only the Lean termination measure; callers choose it as a function of the input
polynomial.
-/
private def choosePrimeDataWalk? (f : ZPoly) : Nat → Nat → Option PrimeChoiceDataScore
  | _, 0 => none
  | start, fuel + 1 =>
      match mkExtendedSmallPrimeCandidate? start with
      | some c =>
          match primeChoiceDataScore f c with
          | some score => some score
          | none => choosePrimeDataWalk? f (start + 2) fuel
      | none => choosePrimeDataWalk? f (start + 2) fuel

private theorem choosePrimeDataWalk?_prime
    (f : ZPoly) (start fuel : Nat) (score : PrimeChoiceDataScore)
    (hscore : choosePrimeDataWalk? f start fuel = some score) :
    Nat.Prime score.data.p := by
  induction fuel generalizing start with
  | zero =>
      simp [choosePrimeDataWalk?] at hscore
  | succ fuel ih =>
      unfold choosePrimeDataWalk? at hscore
      cases hc : mkExtendedSmallPrimeCandidate? start with
      | none =>
          simp [hc] at hscore
          exact ih (start + 2) hscore
      | some c =>
          cases hs : primeChoiceDataScore f c with
          | none =>
              simp [hc, hs] at hscore
              exact ih (start + 2) hscore
          | some currentScore =>
              simp [hc, hs] at hscore
              cases hscore
              exact primeChoiceDataScore_prime f c score hs

private theorem choosePrimeDataWalk?_fModP_eq
    (f : ZPoly) (start fuel : Nat) (score : PrimeChoiceDataScore)
    (hscore : choosePrimeDataWalk? f start fuel = some score) :
    score.data.fModP =
      @ZPoly.modP score.data.p score.data.bounds f := by
  induction fuel generalizing start with
  | zero =>
      simp [choosePrimeDataWalk?] at hscore
  | succ fuel ih =>
      unfold choosePrimeDataWalk? at hscore
      cases hc : mkExtendedSmallPrimeCandidate? start with
      | none =>
          simp [hc] at hscore
          exact ih (start + 2) hscore
      | some c =>
          cases hs : primeChoiceDataScore f c with
          | none =>
              simp [hc, hs] at hscore
              exact ih (start + 2) hscore
          | some currentScore =>
              simp [hc, hs] at hscore
              cases hscore
              exact primeChoiceDataScore_fModP_eq f c score hs

private theorem choosePrimeDataWalk?_isGoodPrime
    (f : ZPoly) (start fuel : Nat) (score : PrimeChoiceDataScore)
    (hscore : choosePrimeDataWalk? f start fuel = some score) :
    @isGoodPrime f score.data.p score.data.bounds = true := by
  induction fuel generalizing start with
  | zero =>
      simp [choosePrimeDataWalk?] at hscore
  | succ fuel ih =>
      unfold choosePrimeDataWalk? at hscore
      cases hc : mkExtendedSmallPrimeCandidate? start with
      | none =>
          simp [hc] at hscore
          exact ih (start + 2) hscore
      | some c =>
          cases hs : primeChoiceDataScore f c with
          | none =>
              simp [hc, hs] at hscore
              exact ih (start + 2) hscore
          | some currentScore =>
              simp [hc, hs] at hscore
              cases hscore
              exact primeChoiceDataScore_isGoodPrime f c score hs

/--
Optional prime selection: returns `some` with the chosen `PrimeChoiceData` when
the executable walk finds a good prime for `f`, and `none` otherwise.

The search first folds `choosePrimeDataScoreStep` over the deterministic
small-prime prefix. If that prefix selects an admissible prime, the original
tie-breaking is preserved. If the prefix exhausts without selecting any prime,
the search folds over the fixed extended prime list through `499`, covering
every odd prime in the SPEC hot-path interval `[3, 500]`.
-/
@[expose]
def choosePrimeData? (f : ZPoly) : Option PrimeChoiceData :=
  match smallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
  | some score => some score.data
  | none =>
      (extendedSmallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none)
      |>.map (fun score => score.data)

/--
Choose an admissible small prime and package the modular image together with
its Berlekamp irreducible factor data for the rest of the pipeline.

The returned record stores the selected prime's `ZMod64.Bounds` instance, so
callers can consume `fModP` and `factorsModP` directly without re-running the
prime search or reconstructing typeclass evidence.

This total wrapper is retained for compatibility with existing total slow-path
statements. It fails through `Option.get!` when no admissible prime is selected;
new call sites that require an actual selected prime should use
`choosePrimeData?` directly and carry the local `some` witness.
-/
def choosePrimeData (f : ZPoly) : PrimeChoiceData :=
  (choosePrimeData? f).get!

theorem choosePrimeData_eq_of_choosePrimeData?_some
    {f : ZPoly} {data : PrimeChoiceData}
    (hdata : choosePrimeData? f = some data) :
    choosePrimeData f = data := by
  simp [choosePrimeData, hdata]

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
When `choosePrimeData? f` returns `none`, every candidate in the SPEC hot-path
prime list fails the executable good-prime predicate `Hex.isGoodPrime f`.

This is the provenance ingredient for SPEC D2's
`choosePrimeData?_none_implies_huge` composition: the executable's failure to
find any good prime over the fixed list means every prime in the admissible
range was tried and rejected, and rejection (`isGoodPrime ... = false`) feeds
the Mathlib-side per-prime divisibility bridge.
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

set_option maxHeartbeats 800000 in
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

set_option maxHeartbeats 800000 in
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

private theorem choosePrimeDataWalk?_factorsModPBerlekampForm
    (f : ZPoly) (start fuel : Nat) (score : PrimeChoiceDataScore)
    (hscore : choosePrimeDataWalk? f start fuel = some score) :
    factorsModPBerlekampForm f score.data := by
  induction fuel generalizing start with
  | zero =>
      simp [choosePrimeDataWalk?] at hscore
  | succ fuel ih =>
      unfold choosePrimeDataWalk? at hscore
      cases hc : mkExtendedSmallPrimeCandidate? start with
      | none =>
          simp [hc] at hscore
          exact ih (start + 2) hscore
      | some c =>
          cases hs : primeChoiceDataScore f c with
          | none =>
              simp [hc, hs] at hscore
              exact ih (start + 2) hscore
          | some currentScore =>
              simp [hc, hs] at hscore
              cases hscore
              exact primeChoiceDataScore_factorsModPBerlekampForm f c score hs

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
