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

/-- Number of proper degrees a subset-degree bitset still admits. -/
@[expose]
def reachableProperCount (reachable : Array Bool) : Nat :=
  (reachable.toList.drop 1).dropLast.count true

/-- Number of proper degrees still possible at a modular trial.  Fewer
reachable degrees means more cheap degree rejections during recombination. -/
@[expose]
def directReachableProperCount {core : SquareFreeInput}
    (probe : DirectPrimeProbe core) : Nat :=
  reachableProperCount probe.reachableDegrees

/-- Candidate count of a complete head-forced subset search. -/
@[expose]
def directSubsetCost (factorCount : Nat) : Nat :=
  if factorCount = 0 then 0 else 2 ^ (factorCount - 1)

/-- Lexicographic downstream score of a modular factorization known only by its
prime and its factor degrees: complete subset work first, then degree-obstruction
opportunities, lift precision, and prime as a stable tie breaker.  Width is
already reflected exponentially by `directSubsetCost`.

Every key is a function of the degree multiset and the prime, so a scouted
degree pattern scores exactly as the factorization it predicts would. -/
@[expose]
def directDegreeScore (core : SquareFreeInput) (p : Nat) (degrees : Array Nat) :
    Nat × Nat × Nat × Nat :=
  (directSubsetCost degrees.size,
    reachableProperCount (directDegreeBits (core.poly.degree?.getD 0) degrees),
    precisionForCoeffBound (ZPoly.defaultFactorCoeffBound core.poly) p,
    p)

/-- Score of a computed modular factorization. -/
@[expose]
def directProbeScore (core : SquareFreeInput) (probe : DirectPrimeProbe core) :
    Nat × Nat × Nat × Nat :=
  directDegreeScore core probe.data.p probe.factorDegrees

/-- Strict lexicographic order on downstream scores; `true` when `b` is the
cheaper plan. -/
@[expose]
def scoreBetter (a b : Nat × Nat × Nat × Nat) : Bool :=
  decide (b.1 < a.1 ||
    (b.1 = a.1 && (b.2.1 < a.2.1 ||
      (b.2.1 = a.2.1 && (b.2.2.1 < a.2.2.1 ||
        (b.2.2.1 = a.2.2.1 && b.2.2.2 < a.2.2.2))))))

/-- Modular width at which a complete direct recombination is already cheaper
than any further modular work, so the first good prime is used unexamined.

The head-forced subset search over `w` local factors visits at most `2^(w-1)`
subsets, which at `w = 8` is 128 -- below the cost of a single Frobenius power
of a scout on any input this planner sees.  Below this width there is nothing
to shop for. -/
def scoutWidth : Nat := 8

/-- Hard bound on the good primes a plan scouts.  A scout costs one Frobenius
power and one gcd per separated factor degree, and is abandoned as soon as the
factors it has separated show the candidate cannot win, so the walk's whole
modular budget is one full split, at most `scoutFuel` bounded scouts, and one
further full split for the scouted winner.  Bad primes do not spend the
allowance: they never reach a scout. -/
def scoutFuel : Nat := 2

/-- A candidate prime together with the modular degree pattern a scout
established for it.  This carries no factorization: the degrees are a
prediction, and the plan splits the winner to obtain the factors. -/
structure PrimeDegreePattern where
  /-- The candidate prime and its primality witness. -/
  candidate : SmallPrimeCandidate
  /-- Degrees of the irreducible factors of the modular image. -/
  degrees : Array Nat

/-- Scout one candidate's modular degree pattern, without splitting it.

`none` when the candidate is not a good prime -- the only case a scout
declines.  A complete pattern records the candidate's exact factor degrees; an
incomplete one records that the candidate has more than `target` local factors,
which is all a wider candidate needs to be discarded. -/
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

/-- Scout further good primes for a cheaper plan than the current best score.

Nothing is split here.  A candidate is discarded as soon as its separated
factors reach the current width, since a wider image can only score worse; and
a candidate whose pattern completes is scored exactly as the factorization it
predicts would be.  So the walk ends holding the plan a policy that split every
candidate would have selected -- except that a scouted image narrow enough to
pass `scoutWidth` ends the walk, the same gate that governs the first good
prime.

Returns the best scouted pattern strictly cheaper than `score`, if any. -/
def scoutBetterPattern (core : SquareFreeInput) :
    Nat → List SmallPrimeCandidate → Nat → Nat × Nat × Nat × Nat →
      Option PrimeDegreePattern → Option PrimeDegreePattern
  | 0, _, _, _, best => best
  | _, [], _, _, best => best
  | fuel + 1, candidate :: candidates, width, score, best =>
      match probeDegreePattern? core.poly candidate width with
      | none => scoutBetterPattern core (fuel + 1) candidates width score best
      | some pattern =>
          if pattern.complete then
            let candidateScore := directDegreeScore core candidate.p pattern.separated
            if scoreBetter score candidateScore then
              if pattern.separated.size ≤ scoutWidth then
                some ⟨candidate, pattern.separated⟩
              else
                scoutBetterPattern core fuel candidates pattern.separated.size
                  candidateScore (some ⟨candidate, pattern.separated⟩)
            else
              scoutBetterPattern core fuel candidates width score best
          else
            scoutBetterPattern core fuel candidates width score best

/-- Split the scouted winner and keep the plan it improves on.

The scout predicted this candidate's factor degrees but computed no factors, so
the plan takes them from the Berlekamp split here.  If that split declines --
which a good prime does not -- the first probe stands. -/
def planOfScout (core : SquareFreeInput) (first : DirectPrimeProbe core) :
    Option PrimeDegreePattern → DirectPrimePlan core
  | none => DirectPrimePlan.ofSelection first #[]
  | some scouted =>
      match probePrimeData? core.poly scouted.candidate with
      | none => DirectPrimePlan.ofSelection first #[]
      | some data =>
          DirectPrimePlan.ofSelection
            (DirectPrimeProbe.ofData core scouted.candidate data) #[first]

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
            some (planOfScout core first
              (scoutBetterPattern core scoutFuel candidates
                data.factorsModP.size (directProbeScore core first) none))

/-- Plan and cache a good direct-coordinate modular factorization. -/
@[expose]
def directPrimePlan? (core : SquareFreeInput) : Option (DirectPrimePlan core) :=
  firstDirectPlan? core (smallPrimeCandidates ++ extendedSmallPrimeCandidates)

private theorem planOfScout_selected_spec
    (core : SquareFreeInput) (first : DirectPrimeProbe core)
    (scouted : Option PrimeDegreePattern)
    (hfirst : probePrimeData? core.poly first.candidate = some first.data) :
    probePrimeData? core.poly (planOfScout core first scouted).selected.candidate =
      some (planOfScout core first scouted).selected.data := by
  cases scouted with
  | none => simpa [planOfScout, DirectPrimePlan.ofSelection] using hfirst
  | some scouted =>
      simp only [planOfScout]
      cases hprobe : probePrimeData? core.poly scouted.candidate with
      | none => simpa [DirectPrimePlan.ofSelection] using hfirst
      | some data =>
          simpa [DirectPrimePlan.ofSelection, DirectPrimeProbe.ofData] using hprobe

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
            exact planOfScout_selected_spec core
              (DirectPrimeProbe.ofData core candidate data) _ hprobe

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

private theorem scoutBetterPattern_mem
    (core : SquareFreeInput) :
    ∀ fuel candidates width score best scouted,
      scoutBetterPattern core fuel candidates width score best = some scouted →
      (∃ b, best = some b ∧ scouted.candidate = b.candidate) ∨
        scouted.candidate ∈ candidates := by
  intro fuel candidates
  induction candidates generalizing fuel with
  | nil =>
      intro width score best scouted h
      cases fuel <;>
        exact Or.inl ⟨scouted, by simpa [scoutBetterPattern] using h, rfl⟩
  | cons candidate candidates ih =>
      intro width score best scouted h
      cases fuel with
      | zero =>
          exact Or.inl ⟨scouted, by simpa [scoutBetterPattern] using h, rfl⟩
      | succ fuel =>
          simp only [scoutBetterPattern] at h
          cases hpat : probeDegreePattern? core.poly candidate width with
          | none =>
              rw [hpat] at h
              rcases ih (fuel + 1) width score best scouted h with hb | hm
              · exact Or.inl hb
              · exact Or.inr (List.mem_cons_of_mem candidate hm)
          | some pattern =>
              rw [hpat] at h
              simp only at h
              by_cases hcomplete : pattern.complete = true
              · rw [if_pos hcomplete] at h
                by_cases hbetter :
                    scoreBetter score
                      (directDegreeScore core candidate.p pattern.separated) = true
                · rw [if_pos hbetter] at h
                  by_cases hnarrow : pattern.separated.size ≤ scoutWidth
                  · rw [if_pos hnarrow] at h
                    exact Or.inr (by
                      cases h
                      exact List.mem_cons_self)
                  · rw [if_neg hnarrow] at h
                    rcases ih fuel pattern.separated.size
                        (directDegreeScore core candidate.p pattern.separated)
                        (some ⟨candidate, pattern.separated⟩) scouted h with
                      ⟨b, hb, hc⟩ | hm
                    · exact Or.inr (by
                        cases hb
                        rw [hc]
                        exact List.mem_cons_self)
                    · exact Or.inr (List.mem_cons_of_mem candidate hm)
                · rw [if_neg hbetter] at h
                  rcases ih fuel width score best scouted h with hb | hm
                  · exact Or.inl hb
                  · exact Or.inr (List.mem_cons_of_mem candidate hm)
              · rw [if_neg hcomplete] at h
                rcases ih fuel width score best scouted h with hb | hm
                · exact Or.inl hb
                · exact Or.inr (List.mem_cons_of_mem candidate hm)

private theorem planOfScout_selected_mem
    (core : SquareFreeInput) (first : DirectPrimeProbe core)
    (scouted : Option PrimeDegreePattern) :
    (planOfScout core first scouted).selected.candidate = first.candidate ∨
      ∃ s, scouted = some s ∧
        (planOfScout core first scouted).selected.candidate = s.candidate := by
  cases scouted with
  | none => exact Or.inl rfl
  | some scouted =>
      simp only [planOfScout]
      cases hprobe : probePrimeData? core.poly scouted.candidate with
      | none => exact Or.inl rfl
      | some data =>
          exact Or.inr ⟨scouted, rfl, rfl⟩

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
            rcases planOfScout_selected_mem core
                (DirectPrimeProbe.ofData core candidate data)
                (scoutBetterPattern core scoutFuel candidates
                  data.factorsModP.size
                  (directProbeScore core (DirectPrimeProbe.ofData core candidate data))
                  none) with hfirst | ⟨s, hs, hsel⟩
            · rw [hfirst]
              exact List.mem_cons_self
            · rcases scoutBetterPattern_mem core scoutFuel candidates
                  data.factorsModP.size
                  (directProbeScore core (DirectPrimeProbe.ofData core candidate data))
                  none s hs with ⟨b, hb, _⟩ | hm
              · exact absurd hb (by simp)
              · rw [hsel]
                exact List.mem_cons_of_mem candidate hm

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
