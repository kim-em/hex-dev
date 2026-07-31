/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.Data

public section
set_option backward.proofsInPublic true

/-!
# Direct-coordinate prime planning

The planner factors `monicModularImage (modP p core)` directly.  It retains
every successful factorization it computes and chooses among those cached
results using a downstream recombination cost, not coefficient swell in a
different coordinate.
-/

namespace Hex

/-- Degree list retained beside a direct modular factorization. -/
@[expose]
def directFactorDegrees (data : PrimeChoiceData) : Array Nat :=
  data.factorsModP.map (fun g => g.degree?.getD 0)

/-- One subset-sum DP step.  The returned Boolean array records whether each
degree at most `maxDegree` can be formed after admitting `degree`. -/
@[expose]
def directDegreeBitsStep
    (maxDegree : Nat) (reachable : Array Bool) (degree : Nat) : Array Bool :=
  (List.range (maxDegree + 1)).toArray.map fun i =>
    reachable[i]?.getD false ||
      (degree ≤ i && reachable[i - degree]?.getD false)

/-- Predictable `O(number of factors × degree)` subset-degree bitset.

Unlike the former recursive degree-subset enumeration, this has no width cap.
Index `i` is true exactly when the planner has found a modular-factor subset
whose degrees sum to `i`; the Mathlib side supplies the semantic theorem. -/
@[expose]
def directDegreeBits (maxDegree : Nat) (degrees : Array Nat) : Array Bool :=
  degrees.foldl (directDegreeBitsStep maxDegree)
    (#[true] ++ Array.replicate maxDegree false)

/-- Build the indexed cached probe and its degree DP in one place. -/
@[expose]
def DirectPrimeProbe.ofData
    (core : CoreProblem) (candidate : SmallPrimeCandidate)
    (data : PrimeChoiceData) : DirectPrimeProbe core :=
  let degrees := directFactorDegrees data
  { candidate
    data
    factorDegrees := degrees
    reachableDegrees := directDegreeBits (core.poly.degree?.getD 0) degrees }

/-- Number of proper degrees still possible at a modular probe.  Fewer
reachable degrees means more cheap degree rejections during recombination. -/
@[expose]
def directReachableProperCount {core : CoreProblem}
    (probe : DirectPrimeProbe core) : Nat :=
  (probe.reachableDegrees.toList.drop 1).dropLast.count true

/-- Candidate count of a complete head-forced subset search. -/
@[expose]
def directSubsetCost (factorCount : Nat) : Nat :=
  if factorCount = 0 then 0 else 2 ^ (factorCount - 1)

/-- Lexicographic downstream score: complete subset work first, then cached
degree-obstruction opportunities, lift precision, and prime as a stable tie
breaker.  Width is already reflected exponentially by `directSubsetCost`. -/
@[expose]
def directProbeScore (core : CoreProblem) (probe : DirectPrimeProbe core) :
    Nat × Nat × Nat × Nat :=
  let data := probe.data
  (directSubsetCost data.factorsModP.size,
    directReachableProperCount probe,
    precisionForCoeffBound (ZPoly.defaultFactorCoeffBound core.poly) data.p,
    data.p)

private def probeBetter {core : CoreProblem}
    (a b : DirectPrimeProbe core) : Bool :=
  let sa := directProbeScore core a
  let sb := directProbeScore core b
  decide (sb.1 < sa.1 ||
    (sb.1 = sa.1 && (sb.2.1 < sa.2.1 ||
      (sb.2.1 = sa.2.1 && (sb.2.2.1 < sa.2.2.1 ||
        (sb.2.2.1 = sa.2.2.1 && sb.2.2.2 < sa.2.2.2))))))

/-- Once a first good prime has at most this many modular factors, complete
direct recombination is cheaper than another Berlekamp probe on the measured
classical corpus. -/
def directProbeWidth : Nat := 8

/-- Number of further *good* primes considered when the first direct image is
too wide.  Bad primes do not spend this allowance because they never run
Berlekamp factorization. -/
def directProbeFuel : Nat := 2

def improveDirectPlan
    (core : CoreProblem) :
    Nat → List SmallPrimeCandidate → DirectPrimeProbe core →
      Array (DirectPrimeProbe core) →
      DirectPrimeProbe core × Array (DirectPrimeProbe core)
  | 0, _, best, probes => (best, probes)
  | _, [], best, probes => (best, probes)
  | fuel + 1, candidate :: candidates, best, probes =>
      match probePrimeData? core.poly candidate with
      | none => improveDirectPlan core (fuel + 1) candidates best probes
      | some data =>
          let probe := DirectPrimeProbe.ofData core candidate data
          if data.factorsModP.size = 1 then
            (probe, probes.push best)
          else if probeBetter best probe then
            improveDirectPlan core fuel candidates probe
              (probes.push best)
          else
            improveDirectPlan core fuel candidates best
              (probes.push probe)

def firstDirectPlan?
    (core : CoreProblem) :
    List SmallPrimeCandidate → Option (DirectPrimePlan core)
  | [] => none
  | candidate :: candidates =>
      match probePrimeData? core.poly candidate with
      | none => firstDirectPlan? core candidates
      | some data =>
          let first := DirectPrimeProbe.ofData core candidate data
          if data.factorsModP.size ≤ directProbeWidth then
            some (DirectPrimePlan.ofSelection first #[])
          else
            let improved :=
              improveDirectPlan core directProbeFuel candidates first #[]
            some (DirectPrimePlan.ofSelection improved.1 improved.2)

/-- Plan and cache a good direct-coordinate modular factorization. -/
@[expose]
def directPrimePlan? (core : CoreProblem) : Option (DirectPrimePlan core) :=
  firstDirectPlan? core (smallPrimeCandidates ++ extendedSmallPrimeCandidates)

private theorem improveDirectPlan_selected_spec
    (core : CoreProblem) :
    ∀ fuel candidates first probes,
      probePrimeData? core.poly first.candidate = some first.data →
      let result := improveDirectPlan core fuel candidates first probes
      probePrimeData? core.poly result.1.candidate = some result.1.data := by
  intro fuel candidates first probes hfirst
  induction candidates generalizing fuel first probes with
  | nil =>
      cases fuel <;> simp [improveDirectPlan, hfirst]
  | cons candidate candidates ih =>
      cases fuel with
      | zero => simp [improveDirectPlan, hfirst]
      | succ fuel =>
          simp only [improveDirectPlan]
          cases hprobe : probePrimeData? core.poly candidate with
          | none => exact ih (fuel + 1) first probes hfirst
          | some data =>
              simp only
              by_cases hone : data.factorsModP.size = 1
              · simp only [hone, if_true]
                exact hprobe
              · simp only [hone, if_false]
                cases hbetter :
                    probeBetter first
                      (DirectPrimeProbe.ofData core candidate data) with
                | false =>
                  simp only [Bool.false_eq_true, if_false]
                  exact ih fuel first
                    (probes.push (DirectPrimeProbe.ofData core candidate data))
                    hfirst
                | true =>
                  simp only [if_true]
                  exact ih fuel (DirectPrimeProbe.ofData core candidate data)
                    (probes.push first) hprobe

private theorem firstDirectPlan?_selected_spec
    (core : CoreProblem) :
    ∀ candidates plan,
      firstDirectPlan? core candidates = some plan →
      probePrimeData? core.poly plan.selected.candidate =
        some plan.selected.data := by
  intro candidates
  induction candidates with
  | nil =>
      intro plan h
      simp [firstDirectPlan?] at h
  | cons candidate candidates ih =>
      intro plan h
      simp only [firstDirectPlan?] at h
      cases hprobe : probePrimeData? core.poly candidate with
      | none =>
          simp only [hprobe] at h
          exact ih plan h
      | some data =>
          simp only [hprobe] at h
          by_cases hsmall : data.factorsModP.size ≤ directProbeWidth
          · simp only [hsmall, if_true, Option.some.injEq] at h
            subst plan
            exact hprobe
          · simp only [hsmall, if_false, Option.some.injEq] at h
            subst plan
            exact improveDirectPlan_selected_spec core directProbeFuel candidates
              (DirectPrimeProbe.ofData core candidate data)
              #[] hprobe

/-- The selected cached value is exactly the result of its retained explicit
prime probe. -/
theorem directPrimePlan?_selected_spec
    (core : CoreProblem) (plan : DirectPrimePlan core)
    (h : directPrimePlan? core = some plan) :
    probePrimeData? core.poly plan.selected.candidate =
      some plan.selected.data := by
  exact firstDirectPlan?_selected_spec core
    (smallPrimeCandidates ++ extendedSmallPrimeCandidates) plan
      (by simpa [directPrimePlan?] using h)

end Hex
