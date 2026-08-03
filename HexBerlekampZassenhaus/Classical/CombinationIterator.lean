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

Two properties keep the traversal off a rejected support's back.  `SupportMeta`
records the lift modulus and each lifted factor's degree and trailing
coefficient once, so a traversal step is an array read and one modular multiply
rather than a fresh `p ^ k` and a fresh `Option`.  And every leaf runs its
metadata-only filters before it reverses the selected indices, maps them to
lifted polynomials, or concatenates the complementary support -- the last of
which is built only once an exact divisor is in hand.  A rejected leaf still
pays for the filters themselves, which are modular arithmetic on the lift
modulus; what it no longer pays for is the support representation.
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

/-- Traversal metadata for one lifted basis against one target, computed once
per sweep.

The lift modulus is `basis.p ^ basis.k`, which at recovery precision is wide
enough to need several limbs, and rebuilding it at every traversal step is the
dominant cost of a support that no candidate test ever sees.  The word-prime
image of the target is the other value a leaf needs and no leaf should
recompute.  The proof fields pin the arrays to the lifted factors elementwise
and to their length, so a traversal reading this metadata is interchangeable
with one reading the factors directly. -/
structure SupportMeta (basis : LiftData) (target : ZPoly) where
  /-- The lift modulus `basis.p ^ basis.k`. -/
  modulus : Nat
  /-- The lift modulus as an integer, so the traversal never reconverts it. -/
  modulusInt : Int
  /-- Degree of each lifted factor, in basis order. -/
  degrees : Array Nat
  /-- Trailing coefficient of each lifted factor, in basis order. -/
  trails : Array Int
  /-- The target's image in `F_q[X]`, carrying its own reduction proof. -/
  image : TargetImage target
  /-- The recorded modulus is the lift modulus. -/
  modulus_eq : modulus = liftModulus basis
  /-- The recorded integer modulus is the recorded modulus. -/
  modulusInt_eq : modulusInt = (modulus : Int)
  /-- There is one recorded degree per lifted factor. -/
  degrees_size : degrees.size = basis.liftedFactors.size
  /-- There is one recorded trailing coefficient per lifted factor. -/
  trails_size : trails.size = basis.liftedFactors.size
  /-- Each recorded degree is its lifted factor's degree. -/
  degrees_eq : ∀ i : DirectLiftedIndex basis,
    degrees.getD i.1 0 = (directLiftedFactor basis i).degree?.getD 0
  /-- Each recorded trailing coefficient is its lifted factor's constant term. -/
  trails_eq : ∀ i : DirectLiftedIndex basis,
    trails.getD i.1 0 = (directLiftedFactor basis i).coeff 0

namespace SupportMeta

/-- The recorded degree of a lifted factor. -/
@[expose]
def degree {basis : LiftData} {target : ZPoly} (metadata : SupportMeta basis target)
    (i : DirectLiftedIndex basis) : Nat :=
  metadata.degrees.getD i.1 0

/-- The recorded trailing coefficient of a lifted factor. -/
@[expose]
def trail {basis : LiftData} {target : ZPoly} (metadata : SupportMeta basis target)
    (i : DirectLiftedIndex basis) : Int :=
  metadata.trails.getD i.1 0

/-- A recorded degree is the degree of the lifted factor it indexes. -/
@[simp]
theorem degree_spec {basis : LiftData} {target : ZPoly} (metadata : SupportMeta basis target)
    (i : DirectLiftedIndex basis) :
    metadata.degree i = (directLiftedFactor basis i).degree?.getD 0 :=
  metadata.degrees_eq i

/-- A recorded trailing coefficient is the constant term of the lifted factor
it indexes. -/
@[simp]
theorem trail_spec {basis : LiftData} {target : ZPoly} (metadata : SupportMeta basis target)
    (i : DirectLiftedIndex basis) :
    metadata.trail i = (directLiftedFactor basis i).coeff 0 :=
  metadata.trails_eq i

/-- The recorded modulus is the lift modulus. -/
@[simp]
theorem modulus_spec {basis : LiftData} {target : ZPoly} (metadata : SupportMeta basis target) :
    metadata.modulus = liftModulus basis :=
  metadata.modulus_eq

/-- The recorded integer modulus is the lift modulus. -/
@[simp]
theorem modulusInt_spec {basis : LiftData} {target : ZPoly} (metadata : SupportMeta basis target) :
    metadata.modulusInt = (liftModulus basis : Int) := by
  rw [metadata.modulusInt_eq, metadata.modulus_eq]

end SupportMeta

/-- Compute the traversal metadata of a lifted basis against a target. -/
@[expose]
def supportMeta (basis : LiftData) (target : ZPoly) : SupportMeta basis target :=
  let modulus := liftModulus basis
  { modulus
    modulusInt := (modulus : Int)
    degrees := basis.liftedFactors.map fun factor => factor.degree?.getD 0
    trails := basis.liftedFactors.map fun factor => factor.coeff 0
    image := targetImage target
    modulus_eq := rfl
    modulusInt_eq := rfl
    degrees_size := by simp
    trails_size := by simp
    degrees_eq := by
      intro i
      simp [Array.getD, directLiftedFactor]
    trails_eq := by
      intro i
      simp [Array.getD, directLiftedFactor] }

/-- Evaluate one traversal leaf.

The degree and trailing-coefficient filters read only the incrementally
maintained statistics, so a support they reject never reverses the selected
indices, never maps them to lifted polynomials, and never builds a candidate.
The complementary support is concatenated only after an exact divisor is found.
The prefilter runs once: a surviving leaf continues with
`directCandidateAfterPrefilter` rather than re-entering `tryDirectCandidate`. -/
@[expose]
def directLeaf
    (coreLc : Int) (target : ZPoly) (cached : TargetImage target)
    (basis : LiftData) (modulus : Nat)
    (head : DirectLiftedIndex basis)
    (xs selectedRev rejectedRev : List (DirectLiftedIndex basis))
    (selectedDegree : Nat) (selectedTrail : Int) : DirectLevelResult basis :=
  if directCandidatePrefilter coreLc target modulus selectedDegree
      selectedTrail then
    let selected := head :: selectedRev.reverse
    match directCandidateAfterObstruction coreLc target cached modulus
        (directSelectedFactors basis selected) with
    | some (candidate, quotient) =>
        .found
          { selected, remaining := rejectedRev.reverse ++ xs,
            candidate, quotient } 1
    | none => .exhausted 1
  else
    .exhausted 1

/-- The guarded leaf agrees with evaluating the candidate test directly.  The
prefilter is `tryDirectCandidate`'s own first step, so guarding on it changes
only when the arguments are built, and every field of the result -- including
the `tried` count -- is unchanged. -/
theorem directLeaf_eq
    (coreLc : Int) (target : ZPoly) (cached : TargetImage target)
    (basis : LiftData) (modulus : Nat)
    (head : DirectLiftedIndex basis)
    (xs selectedRev rejectedRev : List (DirectLiftedIndex basis))
    (selectedDegree : Nat) (selectedTrail : Int) :
    directLeaf coreLc target cached basis modulus head xs selectedRev rejectedRev
        selectedDegree selectedTrail =
      match tryDirectCandidate coreLc target modulus
          (directSelectedFactors basis (head :: selectedRev.reverse))
          selectedDegree selectedTrail with
      | some (candidate, quotient) =>
          .found
            { selected := head :: selectedRev.reverse,
              remaining := rejectedRev.reverse ++ xs,
              candidate, quotient } 1
      | none => .exhausted 1 := by
  unfold directLeaf tryDirectCandidate
  cases directCandidatePrefilter coreLc target modulus selectedDegree
      selectedTrail <;>
    simp [directCandidateAfterObstruction_eq]

/-- Stream the `choose`-element subsets of `xs`.  `selectedRev` and
`rejectedRev` are prefixes already decided by the caller.  Inclusion is visited
before exclusion, matching the ordinary lexicographic combination order. -/
@[expose]
def scanDirectCombinations
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (metadata : SupportMeta basis target) (head : DirectLiftedIndex basis) :
    (xs : List (DirectLiftedIndex basis)) → (choose : Nat) →
      (selectedRev rejectedRev : List (DirectLiftedIndex basis)) →
      (selectedDegree : Nat) → (selectedTrail : Int) →
      DirectLevelResult basis
  | xs, 0, selectedRev, rejectedRev, selectedDegree, selectedTrail =>
      directLeaf coreLc target metadata.image basis metadata.modulus head xs
        selectedRev rejectedRev selectedDegree selectedTrail
  | [], _ + 1, _, _, _, _ => .exhausted 0
  | x :: xs, choose + 1, selectedRev, rejectedRev,
      selectedDegree, selectedTrail =>
      match scanDirectCombinations coreLc target basis metadata head xs choose
          (x :: selectedRev) rejectedRev
          (selectedDegree + metadata.degree x)
          (selectedTrail * metadata.trail x % metadata.modulusInt) with
      | .found split tried => .found split tried
      | .exhausted triedLeft =>
          match scanDirectCombinations coreLc target basis metadata head xs
              (choose + 1) selectedRev (x :: rejectedRev) selectedDegree
              selectedTrail with
          | .found split triedRight => .found split (triedLeft + triedRight)
          | .exhausted triedRight => .exhausted (triedLeft + triedRight)

/-- Stream one head-forced level. -/
@[expose]
def scanDirectLevel
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (head : DirectLiftedIndex basis)
    (tail : List (DirectLiftedIndex basis)) (tailCard : Nat) :
    DirectLevelResult basis :=
  let metadata := supportMeta basis target
  scanDirectCombinations coreLc target basis metadata head tail tailCard [] []
    (metadata.degree head) (metadata.trail head % metadata.modulusInt)

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
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (metadata : SupportMeta basis target) :
    (xs : List (DirectLiftedIndex basis)) → (choose : Nat) →
      (selectedRev rejectedRev : List (DirectLiftedIndex basis)) →
      (selectedDegree : Nat) → (selectedTrail : Int) →
      DirectSubsetLevelResult basis
  | xs, 0, selectedRev, rejectedRev, selectedDegree, selectedTrail =>
      let visited : DirectCandidateStats := { leaves := 1 }
      if directDegreePrefilter coreLc target selectedDegree then
        let degreePassed := { visited with degreeSurvivors := 1 }
        if directTrailingPrefilter coreLc target metadata.modulus selectedTrail then
          let filtered := { degreePassed with trailingSurvivors := 1 }
          let selected := selectedRev.reverse
          let candidate := directCandidate coreLc metadata.modulus
            (directSelectedFactors basis selected)
          let constructed := { filtered with constructed := 1 }
          if shouldRecordPolynomialFactor candidate then
            let recorded := { constructed with recordable := 1 }
            if obstructs metadata.image candidate then
              .exhausted recorded
            else
              let divided := { recorded with exactDivisions := 1 }
              match exactQuotient? target candidate with
              | some quotient =>
                  .found
                    { selected, remaining := rejectedRev.reverse ++ xs,
                      candidate, quotient } divided
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
      match scanDirectSubsets coreLc target basis metadata xs choose
          (x :: selectedRev) rejectedRev
          (selectedDegree + metadata.degree x)
          (selectedTrail * metadata.trail x % metadata.modulusInt) with
      | .found split stats => .found split stats
      | .exhausted leftStats =>
          match scanDirectSubsets coreLc target basis metadata xs (choose + 1)
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
  scanDirectSubsets coreLc target basis (supportMeta basis target) support
    cardinality
    [] [] 0 1

end Hex
