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

How many candidates it scouts is a price comparison, not a threshold.  A scout
is worth running only when the plan it might replace has enough recombination
work left to repay the scout and the split that acting on it would cost, and
both of those are estimated from the shape already observed -- the input degree,
the primes involved, and the degree patterns of the plans in hand.  `scoutPays`
is that comparison, and it is the walk's only stopping decision: it governs the
first good prime and every scouted candidate alike.
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

/-- Hard bound on the good primes a plan scouts, so the walk terminates in a
fixed number of modular observations however cheap the next one looks.  A scout
costs one Frobenius power and one gcd per separated factor degree, and is
abandoned as soon as the factors it has separated show the candidate cannot win,
so the walk's whole modular budget is one full split, at most `scoutFuel`
bounded scouts, and one further full split for the scouted winner.  Bad primes
do not spend the allowance: they never reach a scout.

Which of those scouts are actually performed is decided by `scoutPays`, not by
this bound. -/
def scoutFuel : Nat := 2

/-! ## Pricing one more modular observation

A scout is only worth running when the plan it might replace still has enough
downstream work left to pay for it.  Both sides of that comparison are
functions of the shape already observed, so the walk can price its own next
step.

Write `n` for the degree of the modular image, `q` for the prime about to be
scouted, `w` and `d` for the width and largest modular factor degree of the
plan currently held, and `W` for the machine words of that plan's Hensel
modulus.

* **What is still on the table.**  A recombination candidate costs about `n^2`
  coefficient operations on `W`-word integers, averaged over the cheap degree
  and trailing-coefficient rejections and the subsets that reach a product.  A
  complete head-forced search visits `directSubsetCost w` candidates, but the
  direct engine abandons the search at `defaultSubsetBudget`, so the work still
  ahead is at most `min (directSubsetCost w) defaultSubsetBudget * n^2 * W`.
  That is a worst case rather than a prediction: an irreducible input inside the
  budget does run the search to exhaustion, and everything else stops earlier.
* **What another observation costs.**  A bounded scout runs one Frobenius power
  and one gcd per separated degree, `bitLen q` squarings of the degree-`n` image
  apiece, and the loop stops at the largest factor degree of the image it is
  separating.  That degree is not known before scouting, so `d` -- the largest
  factor degree of the plan in hand -- stands in for it.  It is a *proxy*, not a
  bound: the next candidate's largest degree can exceed it several times over.
  Acting on what a scout learns costs a further Berlekamp split, whose matrix
  and row reduction are about `bitLen q * n^3`.  A walk with `fuel` observations
  left may spend at most `fuel` scouts and one split.

The two estimates share the factor `n^2`, which cancels, leaving one inequality
on the shape.  What this decides is affordability, not expected value: the left
side is the most any prime could save and the right side the most the remaining
walk could spend, so passing it means the walk *can* pay for itself, not that it
will.  The constants scale the modular side against a recombination candidate,
which the inequality counts as one; changing them changes decisions, and
`scripts/bench/prime_policy_replay.py --sensitivity` reports where.
-/

/-- Machine words in the Hensel lift modulus a plan at `p` needs.  A
recombination candidate's product and trial division run over integers of this
width, so this is the part of a candidate's cost that the prime, rather than the
input, decides.

The modulus is formed rather than estimated from `precision * bitLen p`, which
overshoots by up to one bit per power and so crosses word boundaries the real
modulus does not. -/
@[expose]
def liftWords (core : SquareFreeInput) (p : Nat) : Nat :=
  max 1
    ((ZPoly.bitLen
      (p ^ precisionForCoeffBound (ZPoly.defaultFactorCoeffBound core.poly) p)
        + 63) / 64)

/-- Cost of one bounded-scout word operation, in recombination word operations.

A scout round works modulo a word-sized prime with a polynomial division in its
inner loop; a recombination candidate multiplies and divides multiword integers
in a tighter loop.  Over the recorded per-candidate prices the scout's word
operation runs about ten times the recombination one. -/
def scoutRoundCost : Nat := 10

/-- Cost of one Berlekamp-split word operation, in recombination word
operations.  The fixed-space matrix and its row reduction are the tightest
modular loop the planner runs, about half a scout round's. -/
def splitColumnCost : Nat := 5

/-- The plan a scouting walk is trying to beat: its prime, the degrees of its
modular factors, and its downstream score.  Width and largest factor degree are
read off the degrees, so this carries everything both the comparison and the
pricing need and nothing else. -/
structure ScoutIncumbent where
  /-- The prime the incumbent plan uses. -/
  prime : Nat
  /-- Degrees of the incumbent plan's modular factors. -/
  degrees : Array Nat
  /-- The incumbent plan's lexicographic downstream score. -/
  score : Nat × Nat × Nat × Nat

/-- Largest modular factor degree of the incumbent plan.  A bounded scout stops
at the largest factor degree of the image it separates, so this stands in for
the round count a scout of the *next* candidate would run.  A proxy, not a
bound: a narrower candidate tends to have larger factor degrees, and the walk
has not seen them. -/
@[expose]
def ScoutIncumbent.maxDegree (inc : ScoutIncumbent) : Nat :=
  inc.degrees.foldl max 0

/-- Recombination candidates the incumbent plan may still have to visit: the
complete head-forced count, capped where the direct engine abandons the
search. -/
@[expose]
def ScoutIncumbent.candidatesLeft (inc : ScoutIncumbent) : Nat :=
  min (directSubsetCost inc.degrees.size) defaultSubsetBudget

/-- Whether the walk can still afford one more modular observation: the
recombination work the incumbent plan may have left, against the scouts and
split the rest of the walk may spend.

This is the walk's only stopping decision.  It governs the first good prime and
every scouted candidate alike, and it depends on nothing but the degree of the
input, the primes involved, and the degree patterns already observed.

Both sides are worst cases, so passing means the remaining walk *could* pay for
itself, not that it will. -/
def scoutPays (core : SquareFreeInput) (inc : ScoutIncumbent) (q fuel : Nat) :
    Bool :=
  decide (ZPoly.bitLen q *
      (scoutRoundCost * fuel * inc.maxDegree +
        splitColumnCost * core.poly.degree?.getD 0) <
    inc.candidatesLeft * liftWords core inc.prime)

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
  if isGoodPrime f c.m then
    let fModP := ZPoly.modP c.m f
    if hzero : fModP.isZero = false then
      some (Berlekamp.scoutDegreePattern (monicModularImage fModP)
        (monicModularImage_monic c.prime fModP hzero) target)
    else
      none
  else
    none

/-- Scout further good primes for a cheaper plan than the incumbent's.

Nothing is split here.  The walk stops as soon as `scoutPays` says the
incumbent has too little recombination work left to repay another observation.
Otherwise a candidate is discarded as soon as its separated factors reach the
incumbent's width, since a wider image can only score worse; and a candidate
whose pattern completes is scored exactly as the factorization it predicts would
be, and becomes the incumbent if it wins -- which both tightens the target width
and reprices the next observation against the plan now held.

Returns the best scouted pattern strictly cheaper than the incumbent's score,
if any. -/
def scoutBetterPattern (core : SquareFreeInput) :
    Nat → List SmallPrimeCandidate → ScoutIncumbent →
      Option PrimeDegreePattern → Option PrimeDegreePattern
  | 0, _, _, best => best
  | _, [], _, best => best
  | fuel + 1, candidate :: candidates, inc, best =>
      if scoutPays core inc candidate.m (fuel + 1) then
        match probeDegreePattern? core.poly candidate inc.degrees.size with
        | none => scoutBetterPattern core (fuel + 1) candidates inc best
        | some pattern =>
            if pattern.complete then
              let candidateScore :=
                directDegreeScore core candidate.m pattern.separated
              if scoreBetter inc.score candidateScore then
                scoutBetterPattern core fuel candidates
                  ⟨candidate.m, pattern.separated, candidateScore⟩
                  (some ⟨candidate, pattern.separated⟩)
              else
                scoutBetterPattern core fuel candidates inc best
            else
              scoutBetterPattern core fuel candidates inc best
      else
        best

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

/-- Select the first good prime, then let the walk price further observations
against the recombination work that plan has left. -/
def firstDirectPlan?
    (core : SquareFreeInput) :
    List SmallPrimeCandidate → Option (DirectPrimePlan core)
  | [] => none
  | candidate :: candidates =>
      match probePrimeData? core.poly candidate with
      | none => firstDirectPlan? core candidates
      | some data =>
          let first := DirectPrimeProbe.ofData core candidate data
          some (planOfScout core first
            (scoutBetterPattern core scoutFuel candidates
              ⟨candidate.m, first.factorDegrees, directProbeScore core first⟩
              none))

/-- Plan and cache a good direct-coordinate modular factorization. -/
@[expose]
def directPrimePlan? (core : SquareFreeInput) : Option (DirectPrimePlan core) :=
  firstDirectPlan? core (smallPrimeCandidates ++ extendedSmallPrimeCandidates)

/-- A probe *is* its own good-prime trial: the recorded factorization is what
the explicit trial at its candidate returned, and every derived field --
the factor degrees and the subset-degree bitset -- was computed from that
factorization by `DirectPrimeProbe.ofData`.

The planner retains probes it did not select, and a consumer that reads their
degree data needs both halves: without the first it does not know the
factorization is a factorization of this input at all, and without the second
the cached Booleans are unrelated to the recorded degrees. -/
@[expose]
def DirectPrimeProbe.Trial {core : SquareFreeInput}
    (probe : DirectPrimeProbe core) : Prop :=
  probePrimeData? core.poly probe.candidate = some probe.data ∧
    probe = DirectPrimeProbe.ofData core probe.candidate probe.data

/-- A trial built by `ofData` from a successful explicit trial is one. -/
theorem DirectPrimeProbe.trial_ofData {core : SquareFreeInput}
    {candidate : SmallPrimeCandidate} {data : PrimeChoiceData}
    (h : probePrimeData? core.poly candidate = some data) :
    (DirectPrimeProbe.ofData core candidate data).Trial :=
  ⟨h, rfl⟩

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
          simp only [hprobe, Option.some.injEq] at h
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

private theorem planOfScout_probes_trial
    (core : SquareFreeInput) (first : DirectPrimeProbe core)
    (scouted : Option PrimeDegreePattern) (hfirst : first.Trial) :
    ∀ probe ∈ (planOfScout core first scouted).probes, probe.Trial := by
  cases scouted with
  | none =>
      intro probe hprobe
      simp only [planOfScout, DirectPrimePlan.ofSelection, DirectPrimePlan.probes] at hprobe
      simp only [Array.mem_append, Array.mem_singleton] at hprobe
      rcases hprobe with rfl | hprobe
      · exact hfirst
      · simp at hprobe
  | some scouted =>
      intro probe hprobe
      simp only [planOfScout] at hprobe
      cases hdata : probePrimeData? core.poly scouted.candidate with
      | none =>
          rw [hdata] at hprobe
          simp only [DirectPrimePlan.ofSelection, DirectPrimePlan.probes,
            Array.mem_append, Array.mem_singleton] at hprobe
          rcases hprobe with rfl | hprobe
          · exact hfirst
          · simp at hprobe
      | some data =>
          rw [hdata] at hprobe
          simp only [DirectPrimePlan.ofSelection, DirectPrimePlan.probes,
            Array.mem_append, Array.mem_singleton] at hprobe
          rcases hprobe with rfl | hprobe
          · exact DirectPrimeProbe.trial_ofData hdata
          · subst hprobe
            exact hfirst

private theorem firstDirectPlan?_probes_trial
    (core : SquareFreeInput) :
    ∀ candidates plan,
      firstDirectPlan? core candidates = some plan →
      ∀ probe ∈ plan.probes, probe.Trial := by
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
          simp only [hprobe, Option.some.injEq] at h
          subst plan
          exact planOfScout_probes_trial core
            (DirectPrimeProbe.ofData core candidate data) _
            (DirectPrimeProbe.trial_ofData hprobe)

/-- Every retained cached trial -- the selected one and each other successful
trial the planner kept -- is exactly the result of its own explicit
good-prime trial, with its degree data computed from that result. -/
theorem directPrimePlan?_probes_trial
    (core : SquareFreeInput) (plan : DirectPrimePlan core)
    (h : directPrimePlan? core = some plan) :
    ∀ probe ∈ plan.probes, probe.Trial :=
  firstDirectPlan?_probes_trial core
    (smallPrimeCandidates ++ extendedSmallPrimeCandidates) plan
    (by simpa [directPrimePlan?] using h)

private theorem scoutBetterPattern_mem
    (core : SquareFreeInput) :
    ∀ fuel candidates inc best scouted,
      scoutBetterPattern core fuel candidates inc best = some scouted →
      (∃ b, best = some b ∧ scouted.candidate = b.candidate) ∨
        scouted.candidate ∈ candidates := by
  intro fuel candidates
  induction candidates generalizing fuel with
  | nil =>
      intro inc best scouted h
      cases fuel <;>
        exact Or.inl ⟨scouted, by simpa [scoutBetterPattern] using h, rfl⟩
  | cons candidate candidates ih =>
      intro inc best scouted h
      cases fuel with
      | zero =>
          exact Or.inl ⟨scouted, by simpa [scoutBetterPattern] using h, rfl⟩
      | succ fuel =>
          simp only [scoutBetterPattern] at h
          by_cases hpays : scoutPays core inc candidate.m (fuel + 1) = true
          · rw [if_pos hpays] at h
            cases hpat :
                probeDegreePattern? core.poly candidate inc.degrees.size with
            | none =>
                rw [hpat] at h
                rcases ih (fuel + 1) inc best scouted h with hb | hm
                · exact Or.inl hb
                · exact Or.inr (List.mem_cons_of_mem candidate hm)
            | some pattern =>
                rw [hpat] at h
                simp only at h
                by_cases hcomplete : pattern.complete = true
                · rw [if_pos hcomplete] at h
                  by_cases hbetter :
                      scoreBetter inc.score
                        (directDegreeScore core candidate.m pattern.separated) = true
                  · rw [if_pos hbetter] at h
                    rcases ih fuel
                        ⟨candidate.m, pattern.separated,
                          directDegreeScore core candidate.m pattern.separated⟩
                        (some ⟨candidate, pattern.separated⟩) scouted h with
                      ⟨b, hb, hc⟩ | hm
                    · exact Or.inr (by
                        cases hb
                        rw [hc]
                        exact List.mem_cons_self)
                    · exact Or.inr (List.mem_cons_of_mem candidate hm)
                  · rw [if_neg hbetter] at h
                    rcases ih fuel inc best scouted h with hb | hm
                    · exact Or.inl hb
                    · exact Or.inr (List.mem_cons_of_mem candidate hm)
                · rw [if_neg hcomplete] at h
                  rcases ih fuel inc best scouted h with hb | hm
                  · exact Or.inl hb
                  · exact Or.inr (List.mem_cons_of_mem candidate hm)
          · rw [if_neg hpays] at h
            exact Or.inl ⟨scouted, h, rfl⟩

private theorem planOfScout_probes_mem
    (core : SquareFreeInput) (first : DirectPrimeProbe core)
    (scouted : Option PrimeDegreePattern) :
    ∀ probe ∈ (planOfScout core first scouted).probes,
      probe.candidate = first.candidate ∨
        ∃ s, scouted = some s ∧ probe.candidate = s.candidate := by
  cases scouted with
  | none =>
      intro probe hprobe
      simp only [planOfScout, DirectPrimePlan.ofSelection, DirectPrimePlan.probes,
        Array.mem_append, Array.mem_singleton] at hprobe
      rcases hprobe with rfl | hprobe
      · exact Or.inl rfl
      · simp at hprobe
  | some scouted =>
      intro probe hprobe
      simp only [planOfScout] at hprobe
      cases hdata : probePrimeData? core.poly scouted.candidate with
      | none =>
          rw [hdata] at hprobe
          simp only [DirectPrimePlan.ofSelection, DirectPrimePlan.probes,
            Array.mem_append, Array.mem_singleton] at hprobe
          rcases hprobe with rfl | hprobe
          · exact Or.inl rfl
          · simp at hprobe
      | some data =>
          rw [hdata] at hprobe
          simp only [DirectPrimePlan.ofSelection, DirectPrimePlan.probes,
            Array.mem_append, Array.mem_singleton] at hprobe
          rcases hprobe with rfl | hprobe
          · exact Or.inr ⟨scouted, rfl, rfl⟩
          · subst hprobe
            exact Or.inl rfl

private theorem firstDirectPlan?_probes_mem
    (core : SquareFreeInput) :
    ∀ candidates plan,
      firstDirectPlan? core candidates = some plan →
      ∀ probe ∈ plan.probes, probe.candidate ∈ candidates := by
  intro candidates
  induction candidates with
  | nil =>
      intro plan h
      simp [firstDirectPlan?] at h
  | cons candidate candidates ih =>
      intro plan h probe hmem
      simp only [firstDirectPlan?] at h
      cases hprobe : probePrimeData? core.poly candidate with
      | none =>
          simp only [hprobe] at h
          exact List.mem_cons_of_mem candidate (ih plan h probe hmem)
      | some data =>
          simp only [hprobe, Option.some.injEq] at h
          subst plan
          rcases planOfScout_probes_mem core
              (DirectPrimeProbe.ofData core candidate data)
              (scoutBetterPattern core scoutFuel candidates
                ⟨candidate.m,
                  (DirectPrimeProbe.ofData core candidate data).factorDegrees,
                  directProbeScore core (DirectPrimeProbe.ofData core candidate data)⟩
                none) probe hmem with hfirst | ⟨s, hs, hsel⟩
          · rw [hfirst]
            exact List.mem_cons_self
          · rcases scoutBetterPattern_mem core scoutFuel candidates
                ⟨candidate.m,
                  (DirectPrimeProbe.ofData core candidate data).factorDegrees,
                  directProbeScore core (DirectPrimeProbe.ofData core candidate data)⟩
                none s hs with ⟨b, hb, _⟩ | hm
            · exact absurd hb (by simp)
            · rw [hsel]
              exact List.mem_cons_of_mem candidate hm

/-- The selected trial is one of the retained trials. -/
theorem DirectPrimePlan.selected_mem_probes {core : SquareFreeInput}
    (plan : DirectPrimePlan core) : plan.selected ∈ plan.probes := by
  simp [DirectPrimePlan.probes]

/-- Every retained cached trial uses a prime from the fixed `[3, 500]`
hot-path candidate list. -/
theorem directPrimePlan?_probes_p_le_500
    (core : SquareFreeInput) (plan : DirectPrimePlan core)
    (h : directPrimePlan? core = some plan) :
    ∀ probe ∈ plan.probes, probe.data.p ≤ 500 := by
  intro probe hmem
  have hmem' : probe.candidate ∈
      smallPrimeCandidates ++ extendedSmallPrimeCandidates :=
    firstDirectPlan?_probes_mem core
      (smallPrimeCandidates ++ extendedSmallPrimeCandidates) plan
      (by simpa [directPrimePlan?] using h) probe hmem
  have hhot : probe.candidate ∈ hotPathCandidates := by
    simpa only [hotPathCandidates] using hmem'
  have hc : probe.candidate.m ≤ 500 := (mem_hotPathCandidates_prime hhot).2.2
  exact probePrimeData?_p_le core.poly probe.candidate probe.data hc
    ((directPrimePlan?_probes_trial core plan h probe hmem).1)

/-- The direct planner selects only from the fixed `[3, 500]` hot-path
candidate list. -/
theorem directPrimePlan?_selected_p_le_500
    (core : SquareFreeInput) (plan : DirectPrimePlan core)
    (h : directPrimePlan? core = some plan) :
    plan.prime ≤ 500 :=
  directPrimePlan?_probes_p_le_500 core plan h plan.selected
    plan.selected_mem_probes

end Hex
