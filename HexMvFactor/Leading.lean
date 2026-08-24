/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvFactor.Decomp
public import HexMvHensel.Cert

@[expose] public section

/-!
Wang's leading-coefficient assignment.

The implementation deliberately works with the evaluated integer values of
the recursively decomposed leading coefficient.  It neither factors those
integers nor guesses a placement: the non-divisor pass isolates a value for
each polynomial part, repeated exact division assigns its multiplicity, and
the forced integer multipliers are allocated before the residual scalar.
-/

namespace Hex.MvFactor

open Hex
open Hex.MvPoly

variable {n : Nat} {cmp' : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp']

/-! # Integer non-divisors -/

/-- Remove every factor shared with `r`.  Each nonterminal division is exact
and strictly decreases `q`; no factorization of either integer is involved. -/
def stripCommon (q r : Nat) : Nat :=
  if _hq : q ≤ 1 then q
  else
    let g := Nat.gcd q r
    if _hg : g ≤ 1 then q else stripCommon (q / g) r
termination_by q
decreasing_by
  exact Nat.div_lt_self (by omega) (by omega)

/-- Strip the factors already visible in all earlier values. -/
def stripPrevious (q : Nat) : List Nat → Nat
  | [] => q
  | r :: rs => stripPrevious (stripCommon q r) rs

/-- Wang's non-divisor pass.  The scalar is the first earlier value; each
accepted residual is then included when separating later polynomial parts. -/
def nonDivisors (scalar : Int) : List Int → Option (List Nat) :=
  let rec go (previous : List Nat) : List Int → Option (List Nat)
    | [] => some []
    | d :: ds => do
        let q := stripPrevious d.natAbs previous
        if q ≤ 1 then none
        else
          let tail ← go (q :: previous) ds
          some (q :: tail)
  go [scalar.natAbs]

/-- Count at most `fuel` exact divisions by a nontrivial natural divisor. -/
def divisorMultiplicity (d : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, value =>
      if d ≤ 1 || value % d != 0 then 0
      else 1 + divisorMultiplicity d fuel (value / d)

/-! # Polynomial-part assignment -/

/-- Evaluated values of the non-scalar entries of a decomposition. -/
def leadingValues (a : Fin n → Int) (D : Decomp n cmp') : List Int :=
  D.factors.map fun entry => MvPoly.eval a entry.factor

def countsFor (scalar : Int) (d multiplicity : Nat) :
    List ZPoly → List Nat
  | [] => []
  | h :: hs =>
      divisorMultiplicity d multiplicity
          (h.leadingCoeff * scalar).natAbs ::
        countsFor scalar d multiplicity hs

def multiplyAssigned (omega : MvPoly n Int cmp') :
    List (MvPoly n Int cmp') → List Nat →
      Option (List (MvPoly n Int cmp'))
  | [], [] => some []
  | p :: ps, e :: es => do
      let tail ← multiplyAssigned omega ps es
      some (p * omega ^ e :: tail)
  | _, _ => none

def assignPolynomialParts (scalar : Int) :
    List (Factor n cmp') → List Nat → List ZPoly →
      List (MvPoly n Int cmp') → Option (List (MvPoly n Int cmp'))
  | [], [], _, assigned => some assigned
  | entry :: entries, d :: ds, uni, assigned => do
      let counts := countsFor scalar d entry.multiplicity uni
      if counts.sum != entry.multiplicity then none
      else
        let assigned ← multiplyAssigned entry.factor assigned counts
        assignPolynomialParts scalar entries ds uni assigned
  | _, _, _, _ => none

/-! # Forced scalar allocation and rescaling -/

/-- Forced integer multipliers at the actual evaluation point. -/
def needsAt (a : Fin n → Int) :
    List (MvPoly n Int cmp') → List ZPoly → Option (List Nat)
  | [], [] => some []
  | p :: ps, h :: hs => do
      let lead := h.leadingCoeff.natAbs
      if lead = 0 then none
      else
        let need := lead / Nat.gcd lead (MvPoly.eval a p).natAbs
        let tail ← needsAt a ps hs
        some (need :: tail)
  | _, _ => none

def scalarMultipliers (scalar : Int) : List Nat → Option (List Int)
  | [] => none
  | need :: needs =>
      let forced := (need :: needs).prod
      if forced = 0 || scalar.natAbs % forced != 0 then none
      else
        let residual := scalar.natAbs / forced
        let firstMagnitude := need * residual
        let first : Int :=
          if scalar < 0 then -(Int.ofNat firstMagnitude)
          else Int.ofNat firstMagnitude
        some (first :: needs.map Int.ofNat)

def attachScalars : List (MvPoly n Int cmp') → List Int →
    Option (List (MvPoly n Int cmp'))
  | [], [] => some []
  | p :: ps, c :: cs => do
      let tail ← attachScalars ps cs
      some (p * C c :: tail)
  | _, _ => none

def rescaleImages (a : Fin n → Int) :
    List (MvPoly n Int cmp') → List ZPoly → Option (List ZPoly)
  | [], [] => some []
  | L :: Ls, h :: hs => do
      let lead := h.leadingCoeff
      if lead = 0 then none
      else
        let value := MvPoly.eval a L
        let gamma := value / lead
        if gamma * lead != value then none
        else
          let tail ← rescaleImages a Ls hs
          some (DensePoly.scaleImpl gamma h :: tail)
  | _, _ => none

def leadingImagesAgree (a : Fin n → Int) :
    List (MvPoly n Int cmp') → List ZPoly → Bool
  | [], [] => true
  | L :: Ls, F :: Fs =>
      MvPoly.eval a L == F.leadingCoeff && leadingImagesAgree a Ls Fs
  | _, _ => false

/-- Assign the recursively decomposed leading coefficient to primitive
univariate factors and rescale those factors so V3 and V4 can hold together.
Every integer division is checked before its quotient affects the result. -/
def distributeCore? (a : Fin n → Int) (lc : Decomp n cmp')
    (uni : List ZPoly) (scalar : Int) :
    Option (List (MvPoly n Int cmp') × List ZPoly) := do
  if uni.isEmpty || scalar = 0 then none else pure ()
  let values := leadingValues a lc
  -- The stripped residuals witness separability only.  Multiplicities must
  -- be counted by dividing by the full evaluated value `Ω_m(a)`, not by
  -- that residual (and not by one of its prime divisors).
  let _ ← nonDivisors lc.content values
  let parts ← assignPolynomialParts lc.content lc.factors
    (values.map Int.natAbs) uni
    (List.replicate uni.length 1)
  let needs ← needsAt a parts uni
  let multipliers ← scalarMultipliers lc.content needs
  let leading ← attachScalars parts multipliers
  let images ← rescaleImages a leading uni
  if MvHensel.mvProduct leading != lc.product then none
  else if !leadingImagesAgree a leading images then none
  else if MvHensel.uniProduct images !=
      DensePoly.scaleImpl scalar (MvHensel.uniProduct uni) then none
  else some (leading, images)

/-- Public SPEC-shaped wrapper.  The main-variable index records the ambient
arity for callers even though all work here is already in the `n` remaining
variables. -/
def distribute? (_i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (a : Fin n → Int) (lc : Decomp n cmp')
    (uni : List ZPoly) (scalar : Int) :
    Option (List (MvPoly n Int cmp') × List ZPoly) :=
  distributeCore? a lc uni scalar

end Hex.MvFactor
