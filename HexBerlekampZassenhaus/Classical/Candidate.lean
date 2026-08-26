/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.Classical.Obstruction
public import HexBerlekampZassenhaus.Hensel.DirectLift

public section
set_option backward.proofsInPublic true

/-!
# Direct-coordinate recombination candidates
-/

namespace Hex

/-- Reconstruct an original-coordinate candidate from selected monic Hensel
factors. -/
@[expose]
def directCandidate
    (coreLc : Int) (modulus : Nat) (selected : List ZPoly) : ZPoly :=
  normalizeFactorSign <| ZPoly.primitivePart <|
    centeredLiftPoly
      (DensePoly.scale coreLc (Array.polyProduct selected.toArray)) modulus

/-- Exact integer divisibility with a magnitude rejection before remainder
calculation.  The arguments are the prospective multiple and divisor. -/
@[expose]
def intDivides (multiple divisor : Int) : Bool :=
  if multiple.natAbs < divisor.natAbs ∧ multiple ≠ 0 then
    false
  else
    multiple % divisor == 0

/-- The guarded integer divisibility test agrees with a zero-remainder test. -/
@[simp]
theorem intDivides_eq (multiple divisor : Int) :
    intDivides multiple divisor = (multiple % divisor == 0) := by
  unfold intDivides
  split
  · rename_i hlarge
    apply Eq.symm
    apply Bool.eq_false_iff.mpr
    intro hemod
    have hemod' : multiple % divisor = 0 := beq_iff_eq.mp hemod
    have hdvdAbs : divisor.natAbs ∣ multiple.natAbs :=
      Int.natAbs_dvd_natAbs.mpr (Int.dvd_of_emod_eq_zero hemod')
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hlarge.2) hdvdAbs
    omega
  · rfl

/-- Cached degree prefilter for a direct candidate. -/
@[expose]
def directDegreePrefilter
    (coreLc : Int) (target : ZPoly) (degreeSum : Nat) : Bool :=
  coreLc == 0 || decide (target = 0) ||
    decide (degreeSum ≤ target.degree?.getD 0)

/-- Cached trailing-coefficient prefilter for a direct candidate.

The modulus arrives prepared, so the leaf reduces against the integer value the
traversal already holds rather than rebuilding it. -/
@[expose]
def directTrailingPrefilter
    (coreLc : Int) (target : ZPoly) (modulus : LiftModulus)
    (trailingResidue : Int) : Bool :=
  let rawTrail := modulus.centered (coreLc * trailingResidue)
  intDivides (coreLc * target.coeff 0) rawTrail

/-- The prepared prefilter tests divisibility by the centred representative. -/
@[simp]
theorem directTrailingPrefilter_eq
    (coreLc : Int) (target : ZPoly) (modulus : LiftModulus)
    (trailingResidue : Int) :
    directTrailingPrefilter coreLc target modulus trailingResidue =
      intDivides (coreLc * target.coeff 0)
        (centeredModNat (coreLc * trailingResidue) modulus.nat) := by
  unfold directTrailingPrefilter
  rw [LiftModulus.centered_eq]

/-- Cached degree/trailing-coefficient prefilter for a direct candidate.

The selected Hensel factors are monic.  At recovery precision the centered
leading coefficient is `coreLc`, so the selected product has the supplied
degree.  If its primitive part divides `target`, its centered constant
coefficient divides `coreLc * target(0)`.  Both checks happen before the
polynomial product is formed.  Conservative zero cases are retained for the
standalone executable surface. -/
@[expose]
def directCandidatePrefilter
    (coreLc : Int) (target : ZPoly) (modulus : LiftModulus)
    (degreeSum : Nat) (trailingResidue : Int) : Bool :=
  directDegreePrefilter coreLc target degreeSum &&
    directTrailingPrefilter coreLc target modulus trailingResidue

/-- The candidate computation itself, for a selection the cached prefilters have
already accepted.  The streaming traversal runs the prefilter itself, so that it
can decide whether to build `selected` at all, and then calls this rather than
paying for the prefilter twice. -/
@[expose]
def directCandidateAfterPrefilter
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (selected : List ZPoly) :
    Option (ZPoly × ZPoly) :=
  let candidate := directCandidate coreLc modulus selected
  if shouldRecordPolynomialFactor candidate then
    (exactQuotient? target candidate).map fun quotient => (candidate, quotient)
  else
    none

/-- The candidate computation for a selection the cached prefilters accepted,
with the word-prime divisibility obstruction ahead of exact integer division.

`obstructs` fires only on candidates that provably do not divide the target, so
the value returned is `directCandidateAfterPrefilter`'s.  What changes is that
a candidate the obstruction rejects is never put to multi-limb integer long
division. -/
@[expose]
def directCandidateAfterObstruction
    (coreLc : Int) (target : ZPoly) (cached : TargetImage target)
    (modulus : Nat) (selected : List ZPoly) : Option (ZPoly × ZPoly) :=
  let candidate := directCandidate coreLc modulus selected
  if shouldRecordPolynomialFactor candidate then
    (obstructedQuotient? cached candidate).map fun quotient => (candidate, quotient)
  else
    none

/-- Skipping an obstructed candidate's exact division changes nothing: exact
division would have returned `none` on it. -/
theorem directCandidateAfterObstruction_eq
    (coreLc : Int) (target : ZPoly) (cached : TargetImage target)
    (modulus : Nat) (selected : List ZPoly) :
    directCandidateAfterObstruction coreLc target cached modulus selected =
      directCandidateAfterPrefilter coreLc target modulus selected := by
  unfold directCandidateAfterObstruction directCandidateAfterPrefilter
  simp [obstructedQuotient?_eq]

/-- Evaluate the candidate computation after the cached prefilters. -/
@[expose]
def tryDirectCandidate
    (coreLc : Int) (target : ZPoly) (modulus : LiftModulus)
    (selected : List ZPoly) (degreeSum : Nat) (trailingResidue : Int) :
    Option (ZPoly × ZPoly) :=
  if directCandidatePrefilter coreLc target modulus degreeSum trailingResidue then
    directCandidateAfterPrefilter coreLc target modulus.nat selected
  else
    none

end Hex
