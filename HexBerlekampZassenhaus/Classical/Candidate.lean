/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

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

/-- Cached degree/trailing-coefficient prefilter for a direct candidate.

The selected Hensel factors are monic.  At recovery precision the centered
leading coefficient is `coreLc`, so the selected product has the supplied
degree.  If its primitive part divides `target`, its centered constant
coefficient divides `coreLc * target(0)`.  Both checks happen before the
polynomial product is formed.  Conservative zero cases are retained for the
standalone executable surface. -/
@[expose]
def directCandidatePrefilter
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (degreeSum : Nat) (trailingResidue : Int) : Bool :=
  let rawTrail := centeredModNat (coreLc * trailingResidue) modulus
  (coreLc == 0 || decide (target = 0) ||
      decide (degreeSum ≤ target.degree?.getD 0)) &&
    (rawTrail != 0 || target.coeff 0 == 0)

/-- Evaluate the candidate pipeline after the cached prefilters. -/
@[expose]
def tryDirectCandidate
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (selected : List ZPoly) (degreeSum : Nat) (trailingResidue : Int) :
    Option (ZPoly × ZPoly) :=
  if directCandidatePrefilter coreLc target modulus degreeSum trailingResidue then
    let candidate := directCandidate coreLc modulus selected
    if shouldRecordPolynomialFactor candidate then
      (exactQuotient? target candidate).map fun quotient => (candidate, quotient)
    else
      none
  else
    none

end Hex
