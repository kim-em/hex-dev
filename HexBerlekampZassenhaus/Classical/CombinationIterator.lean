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
# Streaming head-forced combinations

No list of subset/complement pairs is materialized.  The iterator carries the
selected and rejected prefixes in reverse, plus the cheap candidate statistics,
and stops at the first exact divisor.
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

end Hex
