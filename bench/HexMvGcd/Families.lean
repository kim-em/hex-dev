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

/-- High-degree, low-support inputs with a known linear common factor. -/
def sparseGcd (n degree : Nat) : P n Int × P n Int :=
  let sparse := (sparseCoprime n degree).1
  let common := commonFactor n
  (common * sparse, common * (sparse + 1))

/-- Dense inputs with a known linear gcd and consecutive dense cofactors. -/
def denseGcd (n degree : Nat) : P n Int × P n Int :=
  let common := commonFactor n
  let leftCofactor := denseBox (R := Int) n degree
  (common * leftCofactor, common * (leftCofactor + 1))

/-- The rational analogue of `denseGcd`, with nonintegral scalar content. -/
def rationalGcd (n degree : Nat) : P n Rat × P n Rat :=
  let common : P n Rat :=
    (List.finRange n).foldl
      (fun polynomial i =>
        polynomial + C ((Int.ofNat (i.val + 1) : Rat) / 2) * X i) 1
  let leftCofactor := denseBox (R := Rat) n degree
  (common * leftCofactor,
    common * (leftCofactor + C ((1 : Rat) / 3)))

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

end Hex.MvGcdBench.Families
