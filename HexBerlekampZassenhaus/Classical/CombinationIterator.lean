/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.Classical.Candidate

public section
set_option backward.proofsInPublic true

/-!
# Streaming direct combinations

No list of subset/complement pairs is materialized.  The iterator carries the
selected and rejected prefixes in reverse, plus the cheap candidate statistics,
and stops at the first exact divisor.  The proved classical search uses the
head-forced iterator; the proposal tier uses the unforced low-cardinality
iterator.
-/

namespace Hex

/-- Every selected and rejected entry emitted by the extensional combination
specification comes from its input list. -/
theorem subsetsOfSizeWithComplement_mem {α : Type} :
    ∀ (l : List α) (d : Nat) (sc : List α × List α),
      sc ∈ subsetsOfSizeWithComplement l d →
      (∀ x ∈ sc.1, x ∈ l) ∧ (∀ x ∈ sc.2, x ∈ l)
  | l, 0, sc, h => by
      simp only [subsetsOfSizeWithComplement, List.mem_singleton] at h
      subst h
      exact ⟨by simp, fun x hx => hx⟩
  | [], d + 1, sc, h => by
      simp [subsetsOfSizeWithComplement] at h
  | a :: l, d + 1, sc, h => by
      simp only [subsetsOfSizeWithComplement, List.mem_append,
        List.mem_map] at h
      rcases h with ⟨sc', hsc', rfl⟩ | ⟨sc', hsc', rfl⟩
      · obtain ⟨h1, h2⟩ := subsetsOfSizeWithComplement_mem l d sc' hsc'
        refine ⟨?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem a (h1 x hx)
        · intro x hx
          exact List.mem_cons_of_mem a (h2 x hx)
      · obtain ⟨h1, h2⟩ :=
          subsetsOfSizeWithComplement_mem l (d + 1) sc' hsc'
        refine ⟨?_, ?_⟩
        · intro x hx
          exact List.mem_cons_of_mem a (h1 x hx)
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem a (h2 x hx)

/-- A dividing candidate and the exact unused support complement. -/
structure DirectSplit (basis : LiftData) where
  /-- The lifted factors used in the candidate product. -/
  selected : List (DirectLiftedIndex basis)
  /-- The exact complementary lifted factors. -/
  remaining : List (DirectLiftedIndex basis)
  /-- The primitive normalized integer candidate. -/
  candidate : ZPoly
  /-- The exact quotient of the current target by `candidate`. -/
  quotient : ZPoly

/-- Result of streaming one complete subset-cardinality level. -/
inductive DirectLevelResult (basis : LiftData) where
  /-- A candidate divides the target; `tried` records the work performed. -/
  | found (split : DirectSplit basis) (tried : Nat)
  /-- Every candidate at this cardinality was tested without success. -/
  | exhausted (tried : Nat)

/-- Lifted polynomials selected by an indexed support list. -/
@[expose]
def directSelectedFactors (basis : LiftData)
    (selected : List (DirectLiftedIndex basis)) : List ZPoly :=
  selected.map (directLiftedFactor basis)

/-- Cached degree statistic evaluated before candidate construction. -/
@[expose]
def directSelectedDegree (basis : LiftData)
    (selected : List (DirectLiftedIndex basis)) : Nat :=
  (directSelectedFactors basis selected).foldl
    (fun sum factor => sum + factor.degree?.getD 0) 0

/-- Cached trailing-coefficient residue evaluated before candidate
construction. -/
@[expose]
def directSelectedTrail (basis : LiftData)
    (selected : List (DirectLiftedIndex basis)) : Int :=
  (directSelectedFactors basis selected).foldl
    (fun residue factor =>
      residue * factor.coeff 0 % (liftModulus basis : Int)) 1

/-- Evaluate one indexed direct split after its cheap cached statistics. -/
@[expose]
def tryDirectSplit
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (selected : List (DirectLiftedIndex basis)) :
    Option (ZPoly × ZPoly) :=
  tryDirectCandidate coreLc target (liftModulus basis)
    (directSelectedFactors basis selected)
    (directSelectedDegree basis selected)
    (directSelectedTrail basis selected)

/-- Stream the `choose`-element subsets of `xs`.  `selectedRev` and
`rejectedRev` are prefixes already decided by the caller.  Inclusion is visited
before exclusion, matching the ordinary lexicographic combination order. -/
@[expose]
def scanDirectCombinations
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (head : DirectLiftedIndex basis) :
    (xs : List (DirectLiftedIndex basis)) → (choose : Nat) →
      (selectedRev rejectedRev : List (DirectLiftedIndex basis)) →
      (selectedDegree : Nat) → (selectedTrail : Int) →
      DirectLevelResult basis
  | xs, 0, selectedRev, rejectedRev, selectedDegree, selectedTrail =>
      let selected := head :: selectedRev.reverse
      let remaining := rejectedRev.reverse ++ xs
      match tryDirectCandidate coreLc target (liftModulus basis)
          (directSelectedFactors basis selected) selectedDegree selectedTrail with
      | some (candidate, quotient) =>
          .found { selected, remaining, candidate, quotient } 1
      | none => .exhausted 1
  | [], _ + 1, _, _, _, _ => .exhausted 0
  | x :: xs, choose + 1, selectedRev, rejectedRev,
      selectedDegree, selectedTrail =>
      let factor := directLiftedFactor basis x
      let included :=
        scanDirectCombinations coreLc target basis head xs choose
          (x :: selectedRev) rejectedRev
          (selectedDegree + factor.degree?.getD 0)
          (selectedTrail * factor.coeff 0 % (liftModulus basis : Int))
      match included with
      | .found split tried => .found split tried
      | .exhausted triedLeft =>
          match scanDirectCombinations coreLc target basis head xs (choose + 1)
              selectedRev (x :: rejectedRev) selectedDegree selectedTrail with
          | .found split triedRight => .found split (triedLeft + triedRight)
          | .exhausted triedRight => .exhausted (triedLeft + triedRight)

/-- Stream one head-forced level. -/
@[expose]
def scanDirectLevel
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (head : DirectLiftedIndex basis)
    (tail : List (DirectLiftedIndex basis)) (tailCard : Nat) :
    DirectLevelResult basis :=
  let factor := directLiftedFactor basis head
  scanDirectCombinations coreLc target basis head tail tailCard [] []
    (factor.degree?.getD 0)
    (factor.coeff 0 % (liftModulus basis : Int))

/-- Stage counters for the unforced low-cardinality candidate sweep. -/
structure DirectCandidateStats where
  /-- Combinatorial leaves visited. -/
  leaves : Nat := 0
  /-- Leaves surviving the cached degree bound. -/
  degreeSurvivors : Nat := 0
  /-- Leaves also surviving the trailing-coefficient divisibility test. -/
  trailingSurvivors : Nat := 0
  /-- Integer candidate polynomials constructed. -/
  constructed : Nat := 0
  /-- Constructed candidates passing the nonunit recording filter. -/
  recordable : Nat := 0
  /-- Candidates sent to exact polynomial division. -/
  exactDivisions : Nat := 0
deriving DecidableEq

/-- Add candidate-stage counters componentwise. -/
@[expose]
def DirectCandidateStats.add
    (left right : DirectCandidateStats) : DirectCandidateStats :=
  { leaves := left.leaves + right.leaves
    degreeSurvivors := left.degreeSurvivors + right.degreeSurvivors
    trailingSurvivors := left.trailingSurvivors + right.trailingSurvivors
    constructed := left.constructed + right.constructed
    recordable := left.recordable + right.recordable
    exactDivisions := left.exactDivisions + right.exactDivisions }

/-- Result of one instrumented unforced subset-cardinality level. -/
inductive DirectSubsetLevelResult (basis : LiftData) where
  /-- A candidate divides the target. -/
  | found (split : DirectSplit basis) (stats : DirectCandidateStats)
  /-- Every candidate at this cardinality was rejected. -/
  | exhausted (stats : DirectCandidateStats)

/-- Stream the `choose`-element subsets of the complete lifted support.

Unlike `scanDirectCombinations`, no distinguished factor is forced into every
candidate.  This is the low-cardinality iterator: it visits each subset once,
retains the exact complementary support, and never materializes the family of
subsets. -/
@[expose]
def scanDirectSubsets
    (coreLc : Int) (target : ZPoly) (basis : LiftData) :
    (xs : List (DirectLiftedIndex basis)) → (choose : Nat) →
      (selectedRev rejectedRev : List (DirectLiftedIndex basis)) →
      (selectedDegree : Nat) → (selectedTrail : Int) →
      DirectSubsetLevelResult basis
  | xs, 0, selectedRev, rejectedRev, selectedDegree, selectedTrail =>
      let selected := selectedRev.reverse
      let remaining := rejectedRev.reverse ++ xs
      let visited : DirectCandidateStats := { leaves := 1 }
      if directDegreePrefilter coreLc target selectedDegree then
        let degreePassed := { visited with degreeSurvivors := 1 }
        if directTrailingPrefilter coreLc target (liftModulus basis) selectedTrail then
          let filtered := { degreePassed with trailingSurvivors := 1 }
          let candidate := directCandidate coreLc (liftModulus basis)
            (directSelectedFactors basis selected)
          let constructed := { filtered with constructed := 1 }
          if shouldRecordPolynomialFactor candidate then
            let divided :=
              { constructed with recordable := 1, exactDivisions := 1 }
            match exactQuotient? target candidate with
            | some quotient =>
                .found { selected, remaining, candidate, quotient } divided
            | none => .exhausted divided
          else
            .exhausted constructed
        else
          .exhausted degreePassed
      else
        .exhausted visited
  | [], _ + 1, _, _, _, _ => .exhausted {}
  | x :: xs, choose + 1, selectedRev, rejectedRev,
      selectedDegree, selectedTrail =>
      let factor := directLiftedFactor basis x
      let included :=
        scanDirectSubsets coreLc target basis xs choose
          (x :: selectedRev) rejectedRev
          (selectedDegree + factor.degree?.getD 0)
          (selectedTrail * factor.coeff 0 % (liftModulus basis : Int))
      match included with
      | .found split stats => .found split stats
      | .exhausted leftStats =>
          match scanDirectSubsets coreLc target basis xs (choose + 1)
              selectedRev (x :: rejectedRev) selectedDegree selectedTrail with
          | .found split rightStats =>
              .found split (leftStats.add rightStats)
          | .exhausted rightStats =>
              .exhausted (leftStats.add rightStats)

/-- Stream one unforced subset-cardinality level. -/
@[expose]
def scanDirectSubsetLevel
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (support : List (DirectLiftedIndex basis)) (cardinality : Nat) :
    DirectSubsetLevelResult basis :=
  scanDirectSubsets coreLc target basis support cardinality [] [] 0 1

end Hex
