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
and per-piece refinement are unnecessary.
-/

namespace Hex

/-- Global cap on direct classical recombination candidates. -/
def defaultSubsetBudget : Nat := 262144

/-- Why the bounded direct classical engine declined. -/
inductive DeclineReason where
  | noGoodPrime
  | subsetBudget
  | liftFailure
  | invalidCandidate
deriving DecidableEq

namespace DeclineReason

@[expose]
def name : DeclineReason → String
  | .noGoodPrime => "noGoodPrime"
  | .subsetBudget => "subsetBudget"
  | .liftFailure => "liftFailure"
  | .invalidCandidate => "invalidCandidate"

end DeclineReason

/-- Statistics from a direct classical attempt. `completedLevels` records the
fully exhausted head-forced subset cardinalities, in execution order. -/
structure ClassicalStats where
  prime : Nat := 0
  primeProbes : Nat := 0
  liftedFactorCount : Nat := 0
  henselLifts : Nat := 0
  candidatesTried : Nat := 0
  completedLevels : Array Nat := #[]
deriving DecidableEq

/-- Internal result of a head search. -/
inductive DirectHeadResult (basis : LiftData) where
  | found (split : DirectSplit basis) (budget : Nat)
      (candidates : Nat) (completed : Array Nat)
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
  | factored (factors : List ZPoly) (budget : Nat) (stats : ClassicalStats)
  | declined (reason : DeclineReason) (budget : Nat) (stats : ClassicalStats)

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

end Hex
