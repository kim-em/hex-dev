/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.Classical.CombinationIterator

public section
set_option backward.proofsInPublic true

/-!
# Greedy direct recombination search

The search commits the first dividing head-forced subset.  Correctness proves
that this subset is an irreducible support, so the transitional backtracking
and per-piece refinement are unnecessary.  A separate unforced sweep retains
exact partial factors and indexed residual support for the untrusted proposal
tier; proved classical replay remains its acceptance boundary.
-/

namespace Hex

/-- Global cap on direct classical recombination candidates. -/
def defaultSubsetBudget : Nat := 262144

/-- Why the bounded direct classical engine declined. -/
inductive DeclineReason where
  /-- No admissible modular factorization was found. -/
  | noGoodPrime
  /-- The next complete subset-cardinality level exceeds the remaining budget. -/
  | subsetBudget
  /-- The modular factors could not be lifted to the required precision. -/
  | liftFailure
  /-- The lifted support is routed to incremental partition replay. -/
  | largeSupport
  /-- Every configured unforced cardinality was exhausted without a split. -/
  | cardinalityCap
  /-- The search exhausted all allowed candidates without a valid split. -/
  | invalidCandidate
deriving DecidableEq

namespace DeclineReason

/-- A short diagnostic name for a direct-search resource limit. -/
@[expose]
def name : DeclineReason → String
  | .noGoodPrime => "noGoodPrime"
  | .subsetBudget => "subsetBudget"
  | .liftFailure => "liftFailure"
  | .largeSupport => "largeSupport"
  | .cardinalityCap => "cardinalityCap"
  | .invalidCandidate => "invalidCandidate"

end DeclineReason

/-- Statistics from a direct classical attempt. `completedLevels` records the
fully exhausted head-forced subset cardinalities, in execution order. -/
structure ClassicalStats where
  /-- The prime selected for the successful modular factorization, or zero. -/
  prime : Nat := 0
  /-- The number of prime candidates examined. -/
  primeProbes : Nat := 0
  /-- The number of lifted modular factors. -/
  liftedFactorCount : Nat := 0
  /-- The number of quadratic Hensel lifts performed. -/
  henselLifts : Nat := 0
  /-- The number of recombination candidates tested by exact division. -/
  candidatesTried : Nat := 0
  /-- Subset cardinalities exhausted completely, in execution order. -/
  completedLevels : Array Nat := #[]
  /-- Stage counters from the unforced low-cardinality sweep. -/
  unforced : DirectCandidateStats := {}
  /-- Unforced cardinalities exhausted completely, in execution order. -/
  unforcedCompletedLevels : Array Nat := #[]
  /-- Degrees peeled by the unforced sweep, in discovery order. -/
  peeledFactorDegrees : Array Nat := #[]
  /-- Selected lifted-support sizes of peeled factors. -/
  peeledSupportSizes : Array Nat := #[]
  /-- Complementary support sizes after each successful peel. -/
  peeledComplementSizes : Array Nat := #[]
  /-- Lifted factors left in the retained residual support. -/
  residualLiftedFactorCount : Nat := 0
  /-- Candidate budget retained for the residual problem. -/
  remainingSubsetBudget : Nat := 0
  /-- Why the unforced sweep stopped, if it left a residual problem. -/
  unforcedDecline : Option DeclineReason := none
deriving DecidableEq

/-- Internal result of a head search. -/
inductive DirectHeadResult (basis : LiftData) where
  /-- A factor and exact quotient were found. -/
  | found (split : DirectSplit basis) (budget : Nat)
      (candidates : Nat) (completed : Array Nat)
  /-- The bounded search stopped for the recorded reason. -/
  | declined (reason : DeclineReason) (budget : Nat)
      (candidates : Nat) (completed : Array Nat)

/-- Search complete cardinality levels only.  If the next level does not fit,
decline before evaluating any member of it. -/
@[expose]
def findDirectHead
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (head : DirectLiftedIndex basis)
    (tail : List (DirectLiftedIndex basis)) :
    (levels : List Nat) → (budget candidates : Nat) →
      (completed : Array Nat) → DirectHeadResult basis
  | [], budget, candidates, completed =>
      .declined .invalidCandidate budget candidates completed
  | level :: levels, budget, candidates, completed =>
      let levelCost := Nat.choose tail.length level
      if levelCost > budget then
        .declined .subsetBudget budget candidates completed
      else
        match scanDirectLevel coreLc target basis head tail level with
        | .found split tried =>
            .found split (budget - tried) (candidates + tried) completed
        | .exhausted tried =>
            findDirectHead coreLc target basis head tail levels
              (budget - tried) (candidates + tried) (completed.push level)

/-- Internal recursive result. -/
inductive DirectSearchResult where
  /-- The recursive search produced a complete factor list. -/
  | factored (factors : List ZPoly) (budget : Nat) (stats : ClassicalStats)
  /-- The recursive search stopped for the recorded reason. -/
  | declined (reason : DeclineReason) (budget : Nat) (stats : ClassicalStats)

/-- Search recursively for direct-coordinate factors within the remaining budget. -/
@[expose]
def searchDirectAux
    (coreLc : Int) (basis : LiftData) :
    Nat → ZPoly → List (DirectLiftedIndex basis) → Nat →
      ClassicalStats → DirectSearchResult
  | 0, _, _, budget, stats => .declined .liftFailure budget stats
  | fuel + 1, target, localFactors, budget, stats =>
      if target = 1 then
        .factored [] budget stats
      else
        match localFactors with
        | [] => .declined .liftFailure budget stats
        | head :: tail =>
            match findDirectHead coreLc target basis head tail
                (List.range (tail.length + 1)) budget 0 #[] with
            | .declined reason budget' candidates completed =>
                .declined reason budget'
                  { stats with
                    candidatesTried := stats.candidatesTried + candidates
                    completedLevels := stats.completedLevels ++ completed }
            | .found split budget' candidates completed =>
                let stats' :=
                  { stats with
                    candidatesTried := stats.candidatesTried + candidates
                    completedLevels := stats.completedLevels ++ completed }
                match searchDirectAux coreLc basis fuel split.quotient
                    split.remaining budget' stats' with
                | .factored factors budget'' stats'' =>
                    .factored (split.candidate :: factors) budget'' stats''
                | .declined reason budget'' stats'' =>
                    .declined reason budget'' stats''

/-- Run the direct search with one shared top-level candidate budget. -/
@[expose]
def searchDirect
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (budget : Nat := defaultSubsetBudget) (stats : ClassicalStats := {}) :
    DirectSearchResult :=
  searchDirectAux coreLc basis (basis.liftedFactors.size + 1)
    target (List.finRange basis.liftedFactors.size) budget stats

/-- Result of one sequence of complete unforced cardinality sweeps. -/
inductive DirectSweepResult (basis : LiftData) where
  /-- A factor and exact quotient were found. -/
  | found (split : DirectSplit basis) (budget : Nat)
      (stats : DirectCandidateStats) (completed : Array Nat)
  /-- No factor was found, or the next complete level exceeded the budget. -/
  | stopped (reason : DeclineReason) (budget : Nat)
      (stats : DirectCandidateStats) (completed : Array Nat)

/-- Search complete unforced cardinality levels without materializing subsets. -/
@[expose]
def findDirectSubset
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (support : List (DirectLiftedIndex basis)) :
    (levels : List Nat) → (budget : Nat) →
      (stats : DirectCandidateStats) →
      (completed : Array Nat) → DirectSweepResult basis
  | [], budget, stats, completed =>
      .stopped .cardinalityCap budget stats completed
  | level :: levels, budget, stats, completed =>
      let levelCost := Nat.choose support.length level
      if levelCost > budget then
        .stopped .subsetBudget budget stats completed
      else
        match scanDirectSubsetLevel coreLc target basis support level with
        | .found split levelStats =>
            .found split (budget - levelStats.leaves)
              (stats.add levelStats) completed
        | .exhausted levelStats =>
            findDirectSubset coreLc target basis support levels
              (budget - levelStats.leaves) (stats.add levelStats)
              (completed.push level)

/-- An exact partial factorization together with its indexed lifted support.

This is computational proposal state, not an irreducibility certificate.  The
public factorizer only consumes it after exact reconstruction and proved
classical replay. -/
structure DirectPartialFactorization (basis : LiftData) where
  /-- Exact factors already peeled from the original target. -/
  factors : Array ZPoly
  /-- Exact quotient remaining after the peeled factors. -/
  residual : ZPoly
  /-- Complementary lifted support for `residual`. -/
  support : List (DirectLiftedIndex basis)
  /-- Candidate budget not consumed by complete sweeps. -/
  budget : Nat
  /-- Measurements accumulated by the partial search. -/
  stats : ClassicalStats

/-- Run one retained unforced low-cardinality sweep. The first exact factor is
peeled and its quotient is handed directly to partition proposal, avoiding a
second combinatorial pass over the residual support. -/
@[expose]
def peelDirect
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (maxCardinality : Nat := 3) (budget : Nat := defaultSubsetBudget)
    (stats : ClassicalStats := {}) : DirectPartialFactorization basis :=
  let support := List.finRange basis.liftedFactors.size
  if target = 1 then
    { factors := #[], residual := target, support := [], budget,
      stats :=
        { stats with
          residualLiftedFactorCount := 0
          remainingSubsetBudget := budget } }
  else
    let levels := (List.range maxCardinality).map (· + 1)
    match findDirectSubset coreLc target basis support levels budget {} #[] with
    | .stopped reason budget' sweepStats completed =>
        { factors := #[], residual := target, support, budget := budget'
          stats :=
            { stats with
              candidatesTried :=
                stats.candidatesTried + sweepStats.exactDivisions
              unforced := stats.unforced.add sweepStats
              unforcedCompletedLevels :=
                stats.unforcedCompletedLevels ++ completed
              residualLiftedFactorCount := support.length
              remainingSubsetBudget := budget'
              unforcedDecline := some reason } }
    | .found split budget' sweepStats completed =>
        { factors := #[split.candidate]
          residual := split.quotient
          support := split.remaining
          budget := budget'
          stats :=
            { stats with
              candidatesTried :=
                stats.candidatesTried + sweepStats.exactDivisions
              unforced := stats.unforced.add sweepStats
              unforcedCompletedLevels :=
                stats.unforcedCompletedLevels ++ completed
              peeledFactorDegrees :=
                stats.peeledFactorDegrees.push
                  (split.candidate.degree?.getD 0)
              peeledSupportSizes :=
                stats.peeledSupportSizes.push split.selected.length
              peeledComplementSizes :=
                stats.peeledComplementSizes.push split.remaining.length
              residualLiftedFactorCount := split.remaining.length
              remainingSubsetBudget := budget'
              unforcedDecline := none } }

end Hex
