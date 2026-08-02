/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekamp.DegreePattern
public import HexBerlekampZassenhaus.ChoosePrimeData
public import HexBerlekampZassenhaus.SquareFreeInput
public import HexBerlekampZassenhaus.Recombination

public section
set_option backward.proofsInPublic true

/-!
# Direct-coordinate prime planning

The planner factors `monicModularImage (modP p core)` directly.  It retains
every successful factorization it computes and chooses among those cached
results using a downstream recombination cost, not coefficient swell in a
different coordinate.

Splitting a modular image is the expensive part, and the planner only ever
needs a *width* -- the number of local factors -- to decide whether a prime is
worth using.  A width can be bounded without splitting anything: the bounded
distinct-degree scout in `HexBerlekamp/DegreePattern.lean` separates the image
by factor degree and brackets the factor count from both sides, stopping as
soon as its bounds settle whether the count is small enough to matter.  So the
walk splits the first good prime, and afterwards splits only those candidates
a scout says can materially narrow it.
-/

namespace Hex

/-- One good-prime factorization computed while planning. The candidate is
retained with its result so proof provenance and diagnostics never need to
recover it by searching the candidate table. -/
structure DirectPrimeProbe (core : SquareFreeInput) where
  /-- The candidate prime and its primality witness. -/
  candidate : SmallPrimeCandidate
  /-- The modular image and its factorization. -/
  data : PrimeChoiceData
  /-- Degrees of the cached modular factors. -/
  factorDegrees : Array Nat
  /-- Subset-degree reachability bitset, indexed from zero through
  `degree core`. This is computed once with the modular factorization and is
  reused by planning and optional degree-obstruction checks. -/
  reachableDegrees : Array Bool

/-- Cached direct-coordinate modular plan. Every successful trial performed by
the planner is retained. The selected trial is stored separately from the
other successful trials, so it is structurally impossible for the choice to
refer to an uncached factorization. -/
structure DirectPrimePlan (core : SquareFreeInput) where
  /-- The successful trial chosen for Hensel lifting and recombination. -/
  selected : DirectPrimeProbe core
  /-- Other successful trials retained for degree-obstruction certificates. -/
  otherProbes : Array (DirectPrimeProbe core)

namespace DirectPrimePlan

/-- Build a plan from its selected successful trial and all other successful
trials. This is the only constructor exposed outside this module. -/
@[expose]
def ofSelection {core : SquareFreeInput} (selected : DirectPrimeProbe core)
    (otherProbes : Array (DirectPrimeProbe core)) : DirectPrimePlan core :=
  ⟨selected, otherProbes⟩

/-- All cached successful trials, with the selected value first. -/
@[expose]
def probes {core : SquareFreeInput} (plan : DirectPrimePlan core) :
    Array (DirectPrimeProbe core) :=
  #[plan.selected] ++ plan.otherProbes

/-- Selected modular factorization. -/
@[expose]
def data {core : SquareFreeInput} (plan : DirectPrimePlan core) : PrimeChoiceData :=
  plan.selected.data

/-- Selected prime. -/
@[expose]
def prime {core : SquareFreeInput} (plan : DirectPrimePlan core) : Nat :=
  plan.data.p

/-- Number of local factors at the selected prime. -/
@[expose]
def width {core : SquareFreeInput} (plan : DirectPrimePlan core) : Nat :=
  plan.data.factorsModP.size

end DirectPrimePlan

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

/-- Build the indexed cached trial and its degree DP in one place. -/
@[expose]
def DirectPrimeProbe.ofData
    (core : SquareFreeInput) (candidate : SmallPrimeCandidate)
    (data : PrimeChoiceData) : DirectPrimeProbe core :=
  let degrees := directFactorDegrees data
  { candidate
    data
    factorDegrees := degrees
    reachableDegrees := directDegreeBits (core.poly.degree?.getD 0) degrees }

/-- Number of proper degrees still possible at a modular trial.  Fewer
reachable degrees means more cheap degree rejections during recombination. -/
@[expose]
def directReachableProperCount {core : SquareFreeInput}
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
def directProbeScore (core : SquareFreeInput) (probe : DirectPrimeProbe core) :
    Nat × Nat × Nat × Nat :=
  let data := probe.data
  (directSubsetCost data.factorsModP.size,
    directReachableProperCount probe,
    precisionForCoeffBound (ZPoly.defaultFactorCoeffBound core.poly) data.p,
    data.p)

private def probeBetter {core : SquareFreeInput}
    (a b : DirectPrimeProbe core) : Bool :=
  let sa := directProbeScore core a
  let sb := directProbeScore core b
  decide (sb.1 < sa.1 ||
    (sb.1 = sa.1 && (sb.2.1 < sa.2.1 ||
      (sb.2.1 = sa.2.1 && (sb.2.2.1 < sa.2.2.1 ||
        (sb.2.2.1 = sa.2.2.1 && sb.2.2.2 < sa.2.2.2))))))

/-- Modular width at which a complete direct recombination is already cheaper
than any further modular work, so the first good prime is used unexamined.

The head-forced subset search over `w` local factors visits at most `2^(w-1)`
subsets, which at `w = 8` is 128 -- below the cost of a single Frobenius power
of a scout on any input this planner sees.  Below this width there is nothing
to shop for. -/
def scoutWidth : Nat := 8

/-- Hard bound on the good primes a plan scouts.  A scout costs one Frobenius
power and one gcd per separated factor degree and stops as soon as its bounds
settle the materiality question, so the walk's whole modular budget is one full
split, at most `scoutFuel` bounded scouts, and one further full split per
accepted scout.  Bad primes do not spend the allowance: they never reach a
scout. -/
def scoutFuel : Nat := 2

/-- Widest modular image worth splitting against a current width of `width`.

Recombination work is governed by the local factor count, and a candidate that
does not remove at least a quarter of the current factors does not reliably
reduce it -- while confirming the candidate costs a full Berlekamp split.  This
is the materiality rule of `isMaterialFactorReduction`, read as a bound on the
new width: `4 * new ≤ 3 * width` exactly when `new ≤ 3 * width / 4`. -/
@[expose]
def materialWidth (width : Nat) : Nat := 3 * width / 4

/-- Scout one candidate's modular degree pattern, without splitting it.

`none` when the candidate is not a good prime, which is the only case a scout
declines; the returned pattern's `upperBound` and `lowerBound` bracket the
candidate's modular width, and the scout runs only as far as is needed to
settle whether that width is at most `target`. -/
def probeDegreePattern? (f : ZPoly) (c : SmallPrimeCandidate) (target : Nat) :
    Option Berlekamp.DegreePattern :=
  letI := c.bounds
  if isGoodPrime f c.p then
    let fModP := ZPoly.modP c.p f
    if hzero : fModP.isZero = false then
      some (Berlekamp.scoutDegreePattern (monicModularImage fModP)
        (monicModularImage_monic c.prime fModP hzero) target)
    else
      none
  else
    none

/-- Trial further good primes, splitting only those whose scouted degree
pattern can materially narrow the current modular image, and retain the least
expensive direct recombination plan. -/
def scoutDirectPlan
    (core : SquareFreeInput) :
    Nat → List SmallPrimeCandidate → DirectPrimeProbe core →
      Array (DirectPrimeProbe core) →
      DirectPrimeProbe core × Array (DirectPrimeProbe core)
  | 0, _, best, probes => (best, probes)
  | _, [], best, probes => (best, probes)
  | fuel + 1, candidate :: candidates, best, probes =>
      let target := materialWidth best.data.factorsModP.size
      match probeDegreePattern? core.poly candidate target with
      | none => scoutDirectPlan core (fuel + 1) candidates best probes
      | some pattern =>
          if pattern.upperBound ≤ target then
            match probePrimeData? core.poly candidate with
            | none => scoutDirectPlan core fuel candidates best probes
            | some data =>
                let probe := DirectPrimeProbe.ofData core candidate data
                if probeBetter best probe then
                  if data.factorsModP.size ≤ scoutWidth then
                    (probe, probes.push best)
                  else
                    scoutDirectPlan core fuel candidates probe (probes.push best)
                else
                  scoutDirectPlan core fuel candidates best (probes.push probe)
          else
            scoutDirectPlan core fuel candidates best probes

/-- Select the first good prime and optionally improve a wide modular factorization. -/
def firstDirectPlan?
    (core : SquareFreeInput) :
    List SmallPrimeCandidate → Option (DirectPrimePlan core)
  | [] => none
  | candidate :: candidates =>
      match probePrimeData? core.poly candidate with
      | none => firstDirectPlan? core candidates
      | some data =>
          let first := DirectPrimeProbe.ofData core candidate data
          if data.factorsModP.size ≤ scoutWidth then
            some (DirectPrimePlan.ofSelection first #[])
          else
            let improved :=
              scoutDirectPlan core scoutFuel candidates first #[]
            some (DirectPrimePlan.ofSelection improved.1 improved.2)

/-- Plan and cache a good direct-coordinate modular factorization. -/
@[expose]
def directPrimePlan? (core : SquareFreeInput) : Option (DirectPrimePlan core) :=
  firstDirectPlan? core (smallPrimeCandidates ++ extendedSmallPrimeCandidates)

private theorem scoutDirectPlan_selected_spec
    (core : SquareFreeInput) :
    ∀ fuel candidates first probes,
      probePrimeData? core.poly first.candidate = some first.data →
      let result := scoutDirectPlan core fuel candidates first probes
      probePrimeData? core.poly result.1.candidate = some result.1.data := by
  intro fuel candidates first probes hfirst
  induction candidates generalizing fuel first probes with
  | nil =>
      cases fuel <;> simp [scoutDirectPlan, hfirst]
  | cons candidate candidates ih =>
      cases fuel with
      | zero => simp [scoutDirectPlan, hfirst]
      | succ fuel =>
          simp only [scoutDirectPlan]
          cases hpat : probeDegreePattern? core.poly candidate
              (materialWidth first.data.factorsModP.size) with
          | none => exact ih (fuel + 1) first probes hfirst
          | some pattern =>
              simp only
              by_cases haccept :
                  pattern.upperBound ≤ materialWidth first.data.factorsModP.size
              · simp only [haccept, if_true]
                cases hprobe : probePrimeData? core.poly candidate with
                | none => exact ih fuel first probes hfirst
                | some data =>
                    simp only
                    cases hbetter :
                        probeBetter first
                          (DirectPrimeProbe.ofData core candidate data) with
                    | false =>
                        simp only [Bool.false_eq_true, if_false]
                        exact ih fuel first
                          (probes.push
                            (DirectPrimeProbe.ofData core candidate data))
                          hfirst
                    | true =>
                        simp only [if_true]
                        by_cases hnarrow : data.factorsModP.size ≤ scoutWidth
                        · simp only [hnarrow, if_true]
                          exact hprobe
                        · simp only [hnarrow, if_false]
                          exact ih fuel
                            (DirectPrimeProbe.ofData core candidate data)
                            (probes.push first) hprobe
              · simp only [haccept, if_false]
                exact ih fuel first probes hfirst

private theorem firstDirectPlan?_selected_spec
    (core : SquareFreeInput) :
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
          by_cases hsmall : data.factorsModP.size ≤ scoutWidth
          · simp only [hsmall, if_true, Option.some.injEq] at h
            subst plan
            exact hprobe
          · simp only [hsmall, if_false, Option.some.injEq] at h
            subst plan
            exact scoutDirectPlan_selected_spec core scoutFuel candidates
              (DirectPrimeProbe.ofData core candidate data)
              #[] hprobe

/-- The selected cached value is exactly the result of its retained explicit
prime trial. -/
theorem directPrimePlan?_selected_spec
    (core : SquareFreeInput) (plan : DirectPrimePlan core)
    (h : directPrimePlan? core = some plan) :
    probePrimeData? core.poly plan.selected.candidate =
      some plan.selected.data := by
  exact firstDirectPlan?_selected_spec core
    (smallPrimeCandidates ++ extendedSmallPrimeCandidates) plan
      (by simpa [directPrimePlan?] using h)

private theorem scoutDirectPlan_selected_mem
    (core : SquareFreeInput) :
    ∀ fuel candidates first probes,
      let result := scoutDirectPlan core fuel candidates first probes
      result.1.candidate = first.candidate ∨
        result.1.candidate ∈ candidates := by
  intro fuel candidates
  induction candidates generalizing fuel with
  | nil =>
      intro first probes
      cases fuel <;> simp [scoutDirectPlan]
  | cons candidate candidates ih =>
      intro first probes
      cases fuel with
      | zero => simp [scoutDirectPlan]
      | succ fuel =>
          simp only [scoutDirectPlan]
          cases hpat : probeDegreePattern? core.poly candidate
              (materialWidth first.data.factorsModP.size) with
          | none =>
              rcases ih (fuel + 1) first probes with h | h
              · exact Or.inl h
              · exact Or.inr (List.mem_cons_of_mem candidate h)
          | some pattern =>
              simp only
              by_cases haccept :
                  pattern.upperBound ≤ materialWidth first.data.factorsModP.size
              · simp only [haccept, if_true]
                cases hprobe : probePrimeData? core.poly candidate with
                | none =>
                    rcases ih fuel first probes with h | h
                    · exact Or.inl h
                    · exact Or.inr (List.mem_cons_of_mem candidate h)
                | some data =>
                    simp only
                    cases hbetter :
                        probeBetter first
                          (DirectPrimeProbe.ofData core candidate data) with
                    | false =>
                        simp only [Bool.false_eq_true, if_false]
                        rcases ih fuel first
                            (probes.push
                              (DirectPrimeProbe.ofData core candidate data)) with
                          h | h
                        · exact Or.inl h
                        · exact Or.inr (List.mem_cons_of_mem candidate h)
                    | true =>
                        simp only [if_true]
                        by_cases hnarrow : data.factorsModP.size ≤ scoutWidth
                        · simp only [hnarrow, if_true]
                          exact Or.inr (by simp [DirectPrimeProbe.ofData])
                        · simp only [hnarrow, if_false]
                          rcases ih fuel
                              (DirectPrimeProbe.ofData core candidate data)
                              (probes.push first) with h | h
                          · exact Or.inr (by
                              rw [h]
                              exact List.mem_cons_self)
                          · exact Or.inr (List.mem_cons_of_mem candidate h)
              · simp only [haccept, if_false]
                rcases ih fuel first probes with h | h
                · exact Or.inl h
                · exact Or.inr (List.mem_cons_of_mem candidate h)

private theorem firstDirectPlan?_selected_mem
    (core : SquareFreeInput) :
    ∀ candidates plan,
      firstDirectPlan? core candidates = some plan →
      plan.selected.candidate ∈ candidates := by
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
          exact List.mem_cons_of_mem candidate (ih plan h)
      | some data =>
          simp only [hprobe] at h
          by_cases hsmall : data.factorsModP.size ≤ scoutWidth
          · simp only [hsmall, if_true, Option.some.injEq] at h
            subst plan
            simp [DirectPrimePlan.ofSelection, DirectPrimeProbe.ofData]
          · simp only [hsmall, if_false, Option.some.injEq] at h
            subst plan
            rcases scoutDirectPlan_selected_mem core scoutFuel candidates
                (DirectPrimeProbe.ofData core candidate data) #[] with hfirst | htail
            · change
                (scoutDirectPlan core scoutFuel candidates
                  (DirectPrimeProbe.ofData core candidate data) #[]).1.candidate ∈
                    candidate :: candidates
              rw [hfirst]
              exact List.mem_cons_self
            · exact List.mem_cons_of_mem candidate htail

/-- The direct planner selects only from the fixed `[3, 500]` hot-path
candidate list. -/
theorem directPrimePlan?_selected_p_le_500
    (core : SquareFreeInput) (plan : DirectPrimePlan core)
    (h : directPrimePlan? core = some plan) :
    plan.prime ≤ 500 := by
  have hmem : plan.selected.candidate ∈
      smallPrimeCandidates ++ extendedSmallPrimeCandidates :=
    firstDirectPlan?_selected_mem core
      (smallPrimeCandidates ++ extendedSmallPrimeCandidates) plan
      (by simpa [directPrimePlan?] using h)
  have hhot : plan.selected.candidate ∈ hotPathCandidates := by
    simpa only [hotPathCandidates] using hmem
  have hc : plan.selected.candidate.p ≤ 500 :=
    (mem_hotPathCandidates_prime hhot).2.2
  exact probePrimeData?_p_le core.poly plan.selected.candidate
    plan.selected.data hc (directPrimePlan?_selected_spec core plan h)

end Hex
