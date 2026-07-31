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

/-- A dividing candidate and the exact unused support complement. -/
structure DirectSplit (basis : LiftData) where
  selected : List (DirectLiftedIndex basis)
  remaining : List (DirectLiftedIndex basis)
  candidate : ZPoly
  quotient : ZPoly

/-- Result of streaming one complete subset-cardinality level. -/
inductive DirectLevelResult (basis : LiftData) where
  | found (split : DirectSplit basis) (tried : Nat)
  | exhausted (tried : Nat)

namespace DirectLevelResult

@[expose]
def tried {basis : LiftData} : DirectLevelResult basis → Nat
  | .found _ n => n
  | .exhausted n => n

end DirectLevelResult

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
      DirectLevelResult basis
  | xs, 0, selectedRev, rejectedRev =>
      let selected := head :: selectedRev.reverse
      let remaining := rejectedRev.reverse ++ xs
      match tryDirectSplit coreLc target basis selected with
      | some (candidate, quotient) =>
          .found { selected, remaining, candidate, quotient } 1
      | none => .exhausted 1
  | [], _ + 1, _, _ => .exhausted 0
  | x :: xs, choose + 1, selectedRev, rejectedRev =>
      let included :=
        scanDirectCombinations coreLc target basis head xs choose
          (x :: selectedRev) rejectedRev
      match included with
      | .found split tried => .found split tried
      | .exhausted triedLeft =>
          match scanDirectCombinations coreLc target basis head xs (choose + 1)
              selectedRev (x :: rejectedRev) with
          | .found split triedRight => .found split (triedLeft + triedRight)
          | .exhausted triedRight => .exhausted (triedLeft + triedRight)

/-- Stream one head-forced level. -/
@[expose]
def scanDirectLevel
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (head : DirectLiftedIndex basis)
    (tail : List (DirectLiftedIndex basis)) (tailCard : Nat) :
    DirectLevelResult basis :=
  scanDirectCombinations coreLc target basis head tail tailCard [] []

end Hex
