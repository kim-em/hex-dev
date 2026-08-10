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

Three properties keep the traversal off a rejected support's back.
`LiftSupport` records the lift modulus and each lifted factor's degree and
trailing coefficient, and `TargetImage` records the target's word-prime image,
so a traversal step is an array read and one modular multiply rather than a
fresh `p ^ k` and a fresh reduction.  The two objects have different lifetimes:
the first depends only on the lifted basis and is constant for a whole peel run,
the second depends on the residual polynomial being searched and is rebuilt
whenever an exact split replaces it.  Every leaf runs its recorded-data filters
before it reverses the
selected indices, maps them to lifted polynomials, or concatenates the
complementary support -- the last of which is built only once an exact divisor
is in hand.  And a leaf that does build a candidate puts it to the finite-field
divisibility obstruction, which rejects in machine-word arithmetic what would
otherwise cost a multi-limb integer long division.

A rejected leaf still pays for the recorded-data filters themselves, which are
modular arithmetic on the lift modulus; what it no longer pays for is the
support representation, and -- past the filters -- the exact division.
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
  tryDirectCandidate coreLc target (LiftModulus.ofNat (liftModulus basis))
    (directSelectedFactors basis selected)
    (directSelectedDegree basis selected)
    (directSelectedTrail basis selected)

/-- The traversal data of one lifted basis, computed once per lift.

Nothing here mentions a target: the lift modulus and the lifted factors are what
a Hensel lift produced, so this object outlives every residual polynomial the
peel run searches against.

The lift modulus is `basis.p ^ basis.k`, which at recovery precision is wide
enough to need several limbs, and rebuilding it at every traversal step is the
dominant cost of a support that no candidate test ever sees.  It is recorded
prepared, in every representation the traversal reduces against: the residue
update multiplies modulo its integer form and the trailing filter compares
against its halfway threshold, so neither derives anything from the modulus at
a leaf.  The proof fields pin the arrays to the lifted factors elementwise and
to their length, so a traversal reading this is interchangeable with one reading
the factors directly. -/
structure LiftSupport (basis : LiftData) where
  /-- The lift modulus `basis.p ^ basis.k`, prepared for centred reduction. -/
  modulus : LiftModulus
  /-- Degree of each lifted factor, in basis order. -/
  degrees : Array Nat
  /-- Trailing coefficient of each lifted factor, in basis order. -/
  trails : Array Int
  /-- The recorded modulus is the prepared lift modulus. -/
  modulus_eq : modulus = LiftModulus.ofNat (liftModulus basis)
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

namespace LiftSupport

/-- The recorded degree of a lifted factor. -/
@[expose]
def degree {basis : LiftData} (lift : LiftSupport basis)
    (i : DirectLiftedIndex basis) : Nat :=
  lift.degrees.getD i.1 0

/-- The recorded trailing coefficient of a lifted factor. -/
@[expose]
def trail {basis : LiftData} (lift : LiftSupport basis)
    (i : DirectLiftedIndex basis) : Int :=
  lift.trails.getD i.1 0

/-- A recorded degree is the degree of the lifted factor it indexes. -/
@[simp]
theorem degree_spec {basis : LiftData} (lift : LiftSupport basis)
    (i : DirectLiftedIndex basis) :
    lift.degree i = (directLiftedFactor basis i).degree?.getD 0 :=
  lift.degrees_eq i

/-- A recorded trailing coefficient is the constant term of the lifted factor
it indexes. -/
@[simp]
theorem trail_spec {basis : LiftData} (lift : LiftSupport basis)
    (i : DirectLiftedIndex basis) :
    lift.trail i = (directLiftedFactor basis i).coeff 0 :=
  lift.trails_eq i

/-- The recorded modulus is the prepared lift modulus. -/
@[simp]
theorem modulus_spec {basis : LiftData} (lift : LiftSupport basis) :
    lift.modulus = LiftModulus.ofNat (liftModulus basis) :=
  lift.modulus_eq

/-- The recorded modulus records the lift modulus. -/
@[simp]
theorem modulusNat_spec {basis : LiftData} (lift : LiftSupport basis) :
    lift.modulus.nat = liftModulus basis := by
  rw [lift.modulus_eq]
  rfl

/-- The recorded integer modulus is the lift modulus. -/
@[simp]
theorem modulusInt_spec {basis : LiftData} (lift : LiftSupport basis) :
    lift.modulus.int = (liftModulus basis : Int) := by
  rw [lift.modulus_eq]
  rfl

end LiftSupport

/-- Compute the traversal data of a lifted basis. -/
@[expose]
def liftSupport (basis : LiftData) : LiftSupport basis :=
  { modulus := LiftModulus.ofNat (liftModulus basis)
    degrees := basis.liftedFactors.map fun factor => factor.degree?.getD 0
    trails := basis.liftedFactors.map fun factor => factor.coeff 0
    modulus_eq := rfl
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
    (basis : LiftData) (modulus : LiftModulus)
    (head : DirectLiftedIndex basis)
    (xs selectedRev rejectedRev : List (DirectLiftedIndex basis))
    (selectedDegree : Nat) (selectedTrail : Int) : DirectLevelResult basis :=
  if directCandidatePrefilter coreLc target modulus selectedDegree
      selectedTrail then
    let selected := head :: selectedRev.reverse
    match directCandidateAfterObstruction coreLc target cached modulus.nat
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
    (basis : LiftData) (modulus : LiftModulus)
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
    (lift : LiftSupport basis) (image : TargetImage target)
    (head : DirectLiftedIndex basis) :
    (xs : List (DirectLiftedIndex basis)) → (choose : Nat) →
      (selectedRev rejectedRev : List (DirectLiftedIndex basis)) →
      (selectedDegree : Nat) → (selectedTrail : Int) →
      DirectLevelResult basis
  | xs, 0, selectedRev, rejectedRev, selectedDegree, selectedTrail =>
      directLeaf coreLc target image basis lift.modulus head xs
        selectedRev rejectedRev selectedDegree selectedTrail
  | [], _ + 1, _, _, _, _ => .exhausted 0
  | x :: xs, choose + 1, selectedRev, rejectedRev,
      selectedDegree, selectedTrail =>
      match scanDirectCombinations coreLc target basis lift image head xs choose
          (x :: selectedRev) rejectedRev
          (selectedDegree + lift.degree x)
          (selectedTrail * lift.trail x % lift.modulus.int) with
      | .found split tried => .found split tried
      | .exhausted triedLeft =>
          match scanDirectCombinations coreLc target basis lift image head xs
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
  let lift := liftSupport basis
  scanDirectCombinations coreLc target basis lift (targetImage target) head tail
    tailCard [] []
    (lift.degree head) (lift.trail head % lift.modulus.int)

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
    (lift : LiftSupport basis) (image : TargetImage target) :
    (xs : List (DirectLiftedIndex basis)) → (choose : Nat) →
      (selectedRev rejectedRev : List (DirectLiftedIndex basis)) →
      (selectedDegree : Nat) → (selectedTrail : Int) →
      DirectSubsetLevelResult basis
  | xs, 0, selectedRev, rejectedRev, selectedDegree, selectedTrail =>
      let visited : DirectCandidateStats := { leaves := 1 }
      if directDegreePrefilter coreLc target selectedDegree then
        let degreePassed := { visited with degreeSurvivors := 1 }
        if directTrailingPrefilter coreLc target lift.modulus selectedTrail then
          let filtered := { degreePassed with trailingSurvivors := 1 }
          let selected := selectedRev.reverse
          let candidate := directCandidate coreLc lift.modulus.nat
            (directSelectedFactors basis selected)
          let constructed := { filtered with constructed := 1 }
          if shouldRecordPolynomialFactor candidate then
            let recorded := { constructed with recordable := 1 }
            if obstructs image candidate then
              .exhausted recorded
            else
              let divided := { recorded with exactDivisions := 1 }
              -- `obstructedQuotient?` rather than `exactQuotient?`: the
              -- accepting step of both traversals goes through the one guarded
              -- entry point, so `obstructedQuotient?_eq` is what keeps either
              -- of them unchanged.  The guard is already known false here, so
              -- this is the same work.
              match obstructedQuotient? image candidate with
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
      match scanDirectSubsets coreLc target basis lift image xs choose
          (x :: selectedRev) rejectedRev
          (selectedDegree + lift.degree x)
          (selectedTrail * lift.trail x % lift.modulus.int) with
      | .found split stats => .found split stats
      | .exhausted leftStats =>
          match scanDirectSubsets coreLc target basis lift image xs (choose + 1)
              selectedRev (x :: rejectedRev) selectedDegree selectedTrail with
          | .found split rightStats =>
              .found split (leftStats.add rightStats)
          | .exhausted rightStats =>
              .exhausted (leftStats.add rightStats)

/-- Stream one unforced subset-cardinality level.

Both prepared objects are supplied by the caller: the lift data is constant for
the peel run, and the target image belongs to the residual whose cardinality
schedule this level is one step of. -/
@[expose]
def scanDirectSubsetLevel
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (lift : LiftSupport basis) (image : TargetImage target)
    (support : List (DirectLiftedIndex basis)) (cardinality : Nat) :
    DirectSubsetLevelResult basis :=
  scanDirectSubsets coreLc target basis lift image support cardinality
    [] [] 0 1

end Hex
