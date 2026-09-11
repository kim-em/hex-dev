/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexDet
import Lean.Data.Json

/-!
Symbolic carrier fixtures for `hex-det`, in the canonical wire encoding
`scripts/oracle/matrix_carriers.py` reads.

Every emitted determinant is `Hex.Det.det`, so the SymPy oracle checks the answer
dispatch returns over the identical exact polynomial domain. Entries are
nonconstant, so the Bareiss recurrence divides by polynomial pivots of positive
degree throughout.

This module belongs to the conformance target, not the published library.
-/

namespace Hex.DetCarriers

open Lean
open Hex Hex.Det

scoped instance : ZMod64.Bounds 101 := ⟨by decide, by decide⟩
scoped instance : ZMod64.PrimeModulus 101 :=
  ZMod64.primeModulusOfPrime (by decide)

abbrev Mod := ZMod64 101
abbrev Sparse (n : Nat) (R : Type) [Zero R] := MvPoly n R Mono.grevlex

/-- The exact domain a fixture's entries live in. -/
structure Domain where
  /-- Carrier family the oracle builds: `dense` or `mv`. -/
  carrier : String
  /-- Ground domain: `ZZ`, `QQ` or `GF`. -/
  base : String
  /-- Number of indeterminates. -/
  arity : Nat := 1
  /-- Prime modulus, zero outside `GF`. -/
  modulus : Nat := 0

def denseInt : Domain := ⟨"dense", "ZZ", 1, 0⟩
def denseRat : Domain := ⟨"dense", "QQ", 1, 0⟩
def denseMod : Domain := ⟨"dense", "GF", 1, 101⟩
def mvInt (n : Nat) : Domain := ⟨"mv", "ZZ", n, 0⟩
def mvRat (n : Nat) : Domain := ⟨"mv", "QQ", n, 0⟩

def ratJson (r : Rat) : Json := toJson (#[toJson r.num, toJson r.den])

def polyJson [Zero R] [DecidableEq R] (encode : R → Json) (p : DensePoly R) : Json :=
  .arr (p.toArray.map encode)

def mvJson [Zero R] (encode : R → Json) (p : Sparse n R) : Json :=
  toJson (p.termsList.map fun (m, c) => Json.arr #[toJson m.toList, encode c])

def request (domain : Domain) (encode : R → Json) (M : Matrix R n n) : Json :=
  Json.mkObj [("kind", toJson "det"), ("carrier", toJson domain.carrier),
    ("base", toJson domain.base), ("arity", toJson domain.arity),
    ("modulus", toJson domain.modulus), ("n", toJson n),
    ("matrix", toJson ((List.finRange n).map fun i =>
      toJson ((List.finRange n).map fun j => encode M[(i, j)])))]

/-- One fixture record: the input matrix in the oracle's encoding, together with
the determinant dispatch returns for it. -/
def record [Lean.Grind.CommRing R] [DetOps R] (domain : Domain) (encode : R → Json)
    (name : String) (M : Matrix R n n) : Json :=
  (request domain encode M).setObjVal! "case" (toJson name)
    |>.setObjVal! "determinant" (encode (Hex.Det.det M))

/-- Four three-by-three shapes over one carrier: nonconstant pivots, a row swap
of the same matrix, a singular matrix, and an upper-triangular one. -/
def fixtures [Lean.Grind.CommRing R] [DetOps R] (domain : Domain)
    (encode : R → Json) (a b c : R) : Array Json :=
  let dense : Matrix R 3 3 :=
    Matrix.ofFn fun i j =>
      if i = j then a else if i.val < j.val then b else c
  let singular : Matrix R 3 3 :=
    Matrix.ofFn fun i j => if i.val = 2 then a * b else if i.val = 0 then a else b
  let triangular : Matrix R 3 3 :=
    Matrix.ofFn fun i j => if i.val > j.val then 0 else if i = j then a else b
  #[record domain encode "nonconstant" dense,
    record domain encode "row-swap" (Matrix.rowSwap dense 0 1),
    record domain encode "singular" singular,
    record domain encode "triangular" triangular]

/-- Mixed monomials in each of two variables, with a scaled linear term. -/
def mixed [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (n : Nat) (c : R) : Sparse n R :=
  MvPoly.ofTerms [(Vector.ofFn (fun _ => 1), c),
    (Vector.ofFn (fun i => if i.val = 0 then 2 else 0), 1)]

def allFixtures : Array Json :=
  fixtures denseInt (polyJson toJson)
      (DensePoly.ofList [1, 2, 1] : DensePoly Int)
      (DensePoly.ofList [-1, 1]) (DensePoly.ofList [2, 1]) ++
  fixtures denseRat (polyJson ratJson)
      (DensePoly.ofList [1/2, 2/3, 1] : DensePoly Rat)
      (DensePoly.ofList [-1/3, 1]) (DensePoly.ofList [2/5, 1]) ++
  fixtures denseMod (polyJson (fun c : Mod => toJson c.toNat))
      (DensePoly.ofList ([3, 5, 1].map (fun z : Int => (z : Mod))) : DensePoly Mod)
      (DensePoly.ofList ([-1, 7].map (fun z : Int => (z : Mod))))
      (DensePoly.ofList ([2, 11].map (fun z : Int => (z : Mod)))) ++
  fixtures (mvInt 2) (mvJson toJson)
      (mixed 2 (2 : Int)) (mixed 2 (-1 : Int) + 1) (mixed 2 (3 : Int)) ++
  fixtures (mvRat 2) (mvJson ratJson)
      (mixed 2 (2/3 : Rat)) (mixed 2 (-1/2 : Rat) + 1) (mixed 2 (3/5 : Rat))

end Hex.DetCarriers
