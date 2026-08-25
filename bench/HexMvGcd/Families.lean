/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvGcd

/-!
Deterministic input constructors for the `hex-mv-gcd` Phase 4 shape matrix.

Every constructor returns a fully materialized canonical sparse polynomial.
Benchmark registrations store those values in global references, keeping
construction outside the timed region.
-/

namespace Hex.MvGcdBench.Families

open Hex
open Hex.MvPoly

abbrev P (n : Nat) (R : Type) [Zero R] := MvPoly n R Mono.lex

/-- Stable structural hash of a canonical sparse polynomial. -/
def checksum [Zero R] [Hashable R]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n R cmp) : UInt64 :=
  p.termsList.foldl
    (fun acc term =>
      mixHash (mixHash acc (hash term.1.toList)) (hash term.2))
    0

instance [Zero R] [Hashable R]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
    Hashable (MvPoly n R cmp) where
  hash := checksum

/-- Every monomial in the arity-`n`, per-variable degree-`degree` box. -/
def denseBox [Lean.Grind.CommRing R] [DecidableEq R]
    [BEq R] [LawfulBEq R] [OfNat R 1]
    (n degree : Nat) : P n R :=
  let radix := degree + 1
  ofTerms <| (List.range (radix ^ n)).map fun encoded =>
    (Hex.Vector.ofFn' fun i => encoded / radix ^ i.val % radix, 1)

/-- A dense coprime pair: the right input differs from the left by one. -/
def denseCoprime [Lean.Grind.CommRing R] [DecidableEq R]
    [BEq R] [LawfulBEq R] [OfNat R 1]
    (n degree : Nat) : P n R × P n R :=
  let left := denseBox (R := R) n degree
  (left, left + 1)

/-- A high-degree pair with `n + 1` supported terms in each input. -/
def sparseCoprime (n degree : Nat) : P n Int × P n Int :=
  let left : P n Int := ofTerms <|
    (Mono.zero, 1) :: (List.finRange n).map fun axis =>
      (Hex.Vector.ofFn' fun i => if i = axis then degree + axis.val else 0,
        Int.ofNat (axis.val + 2))
  (left, left + 1)

/-- A linear common factor involving every variable. -/
def commonFactor (n : Nat) : P n Int :=
  (List.finRange n).foldl
    (fun polynomial i => polynomial + C (Int.ofNat (i.val + 1)) * X i) 1

/-- High-degree, low-support inputs with a known linear common factor and
nonconsecutive coprime cofactors. -/
def sparseGcd (n degree : Nat) (hn : 0 < n := by omega) :
    P n Int × P n Int :=
  let sparse := (sparseCoprime n degree).1
  let common := commonFactor n
  let rightCofactor := X ⟨0, hn⟩ * sparse + 1
  (common * sparse, common * rightCofactor)

/-- Dense inputs with a known linear gcd and nonconsecutive coprime cofactors.
The right cofactor is `x₀ * left + 1`, so a direct Bézout identity exists
without triggering the unit-difference shortcut. -/
def denseGcd (n degree : Nat) (hn : 0 < n := by omega) :
    P n Int × P n Int :=
  let common := commonFactor n
  let leftCofactor := denseBox (R := Int) n degree
  let rightCofactor := X ⟨0, hn⟩ * leftCofactor + 1
  (common * leftCofactor, common * rightCofactor)

/-- The rational analogue of `denseGcd`, with nonintegral scalar content. -/
def rationalGcd (n degree : Nat) (hn : 0 < n := by omega) :
    P n Rat × P n Rat :=
  let common : P n Rat :=
    (List.finRange n).foldl
      (fun polynomial i =>
        polynomial + C ((Int.ofNat (i.val + 1) : Rat) / 2) * X i) 1
  let leftCofactor := denseBox (R := Rat) n degree
  let rightCofactor := X ⟨0, hn⟩ * leftCofactor + 1
  (common * leftCofactor, common * rightCofactor)

/-- A nonconstant linear factor which involves every available variable. -/
def linearFactor (n salt : Nat) : P n Int :=
  (List.finRange n).foldl
    (fun polynomial i =>
      polynomial + C (Int.ofNat (salt + i.val + 1)) * X i)
    (C (Int.ofNat (salt + n + 1)))

/-- Product of distinct linear factors carrying the requested multiplicities. -/
def squarefreeShape (n : Nat) (multiplicities : List Nat) : P n Int :=
  (multiplicities.zipIdx).foldl
    (fun polynomial entry =>
      polynomial * linearFactor n (entry.2 + 1) ^ entry.1)
    1

/-- Five-variable multiplicity stress without the incidental dense expansion
of four factors which each involve every variable.  The first factor couples
the fifth variable to the first; the other three keep every requested
multiplicity distinct while all five variables remain active. -/
def squarefreeStress5 : P 5 Int :=
  let x0 : P 5 Int := X 0
  let x1 : P 5 Int := X 1
  let x2 : P 5 Int := X 2
  let x3 : P 5 Int := X 3
  let x4 : P 5 Int := X 4
  (x0 + x4 + 2) ^ 2 * (x1 + 3) ^ 3 *
    (x2 + 5) ^ 5 * (x3 + 7) ^ 7

end Hex.MvGcdBench.Families
