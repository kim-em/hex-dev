/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexDeterminant
import HexPoly.Instances
import HexModArith
import HexMvPoly.Ring
import HexRationalFn.Field
import Lean.Data.Json

/-! Integration fixtures and canonical wire encodings for symbolic determinants.
This module belongs to the conformance target, not the published library. -/

namespace Hex.DeterminantCarriers
open Lean

scoped instance : ZMod64.Bounds 101 := ⟨by decide, by decide⟩
abbrev Mod := ZMod64 101

-- The generic instance elaborates at this type, but instance search cannot
-- unfold the coefficient ring's Zero projection at instances transparency.
scoped instance : Lean.Grind.CommRing (DensePoly Mod) :=
  Hex.instGrindCommRingDensePoly
abbrev Sparse (n : Nat) (R : Type) [Zero R] := MvPoly n R Mono.grevlex

structure Domain where
  carrier : String
  base : String
  arity : Nat := 1
  modulus : Nat := 0

def denseInt : Domain := ⟨"dense", "ZZ", 1, 0⟩
def denseRat : Domain := ⟨"dense", "QQ", 1, 0⟩
def denseMod : Domain := ⟨"dense", "GF", 1, 101⟩
def mvInt (n : Nat) : Domain := ⟨"mv", "ZZ", n, 0⟩
def mvRat (n : Nat) : Domain := ⟨"mv", "QQ", n, 0⟩
def ratFn : Domain := ⟨"ratfn", "QQ", 1, 0⟩

def ratJson (r : Rat) : Json := toJson (#[toJson r.num, toJson r.den])
def polyJson [Zero R] [DecidableEq R] (encode : R → Json) (p : DensePoly R) : Json :=
  .arr (p.toArray.map encode)
def mvJson [Zero R] (encode : R → Json) (p : Sparse n R) : Json :=
  toJson (p.termsList.map fun (m, c) => Json.arr #[toJson m.toList, encode c])
def fractionJson (f : RationalFn Rat) : Json :=
  Json.mkObj [("num", polyJson ratJson f.num), ("den", polyJson ratJson f.den)]

def request (domain : Domain) (encode : R → Json) (M : Matrix R n n) : Json :=
  Json.mkObj [("kind", toJson "det"), ("carrier", toJson domain.carrier),
    ("base", toJson domain.base), ("arity", toJson domain.arity),
    ("modulus", toJson domain.modulus), ("n", toJson n),
    ("matrix", toJson ((List.finRange n).map fun i =>
      toJson ((List.finRange n).map fun j => encode M[(i, j)])))]

def record [Lean.Grind.Ring R] (domain : Domain) (encode : R → Json)
    (name : String) (M : Matrix R n n) : Json :=
  (request domain encode M).setObjVal! "case" (toJson name)
    |>.setObjVal! "determinant" (encode (Matrix.det M))

/-- The cancellation matrix has determinant one for every input polynomial. -/
def cancellation [Lean.Grind.Ring R] (a : R) : Matrix R 2 2 :=
  Matrix.ofFn fun i j => if i = j then a else if i.val = 0 then a + 1 else a - 1

def square [Lean.Grind.Ring R] (a b c : R) : Matrix R 2 2 :=
  Matrix.ofFn fun i j => if i = j then a else if i.val = 0 then b else c

def fixtures [Lean.Grind.Ring R] (domain : Domain) (encode : R → Json)
    (a b c : R) : Array Json :=
  let M := square a b c
  #[record domain encode "empty" (Matrix.identity (R := R) 0),
    record domain encode "scalar" (Matrix.ofFn (m := 1) (n := 1) fun _ _ => a),
    record domain encode "nonconstant" M,
    record domain encode "cancellation" (cancellation a),
    record domain encode "singular" (Matrix.ofFn (m := 2) (n := 2) fun _ j => if j.val = 0 then a else b),
    record domain encode "triangular" (Matrix.ofFn (m := 3) (n := 3) fun i j =>
      if i.val > j.val then 0 else if i = j then a else b),
    record domain encode "row-swap" (Matrix.rowSwap M 0 1)]

/-- Dense, nonzero coefficients; row/column salts prevent a low-rank affine family. -/
def coefficient (row col k : Nat) : Int :=
  let h := (row + 3) * 73856093 ^ (k + 1) + (col + 5) * 19349663 ^ (k + 2)
  let c := (h % 17 : Int) - 8
  if c = 0 then 3 else c

def intPoly (row col degree : Nat) : DensePoly Int :=
  DensePoly.ofCoeffs ((Array.range (degree + 1)).map (coefficient row col))
def ratPoly (row col degree : Nat) : DensePoly Rat :=
  DensePoly.ofCoeffs ((Array.range (degree + 1)).map fun k =>
    (coefficient row col k : Rat) / ((k % 3 + 2 : Nat) : Rat))
def modPoly (row col degree : Nat) : DensePoly Mod :=
  DensePoly.ofCoeffs ((Array.range (degree + 1)).map fun k =>
    (fun z : Int => (z : Mod)) (coefficient row col k + 303))

/-- Three-variable homogeneous degree-four support, in a fixed enumeration. -/
def monomials : List (Mono 3) :=
  let mixed : List (Mono 3) := [#v[1, 1, 2], #v[2, 1, 1]]
  let all := (List.range 5).flatMap fun a => (List.range (5 - a)).map fun b =>
    Vector.ofFn fun i => if i.val = 0 then a else if i.val = 1 then b else 4 - a - b
  mixed ++ all.filter (fun m => !mixed.contains m)

def intMv (row col terms : Nat) : Sparse 3 Int :=
  MvPoly.ofTerms ((monomials.take terms).zipIdx.map fun (m, k) => (m, coefficient row col k))
def ratMv (row col terms : Nat) : Sparse 3 Rat :=
  MvPoly.ofTerms ((monomials.take terms).zipIdx.map fun (m, k) =>
    (m, (coefficient row col k : Rat) / ((k % 3 + 2 : Nat) : Rat)))

def fraction (row col degree : Nat) : RationalFn Rat :=
  let p := ratPoly row col degree
  let q := (DensePoly.ofList [0, 1] : DensePoly Rat) ^ degree + 1
  (RationalFn.ofFraction? p q).getD 0

def matrix (entry : Nat → Nat → Nat → R) (n size : Nat) : Matrix R n n :=
  Matrix.ofFn fun i j => entry i.val j.val size

/-- Mixed monomials in each of two and three variables, with rational scaling. -/
def mixed [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (n : Nat) (c : R) : Sparse n R :=
  MvPoly.ofTerms [(Vector.ofFn (fun _ => 1), c),
    (Vector.ofFn (fun i => if i.val = 0 then 2 else 0), 1)]

def allFixtures : Array Json :=
  fixtures denseInt (polyJson toJson)
      (DensePoly.ofList [1, 2, 1] : DensePoly Int) (DensePoly.ofList [-1, 1]) (DensePoly.ofList [2, 1]) ++
  fixtures denseRat (polyJson ratJson)
      (DensePoly.ofList [1/2, 2/3, 1] : DensePoly Rat) (DensePoly.ofList [-1/3, 1]) (DensePoly.ofList [2/5, 1]) ++
  fixtures denseMod (polyJson (fun c : Mod => toJson c.toNat))
      (DensePoly.ofList ([-102, 204, 102].map (fun z : Int => (z : Mod))) : DensePoly Mod)
      (DensePoly.ofList ([-1, 102].map (fun z : Int => (z : Mod)))) (DensePoly.ofList ([305, -100].map (fun z : Int => (z : Mod)))) ++
  (#[2, 3].flatMap fun n =>
    fixtures (mvInt n) (mvJson toJson) (mixed n (2 : Int)) (mixed n (-1 : Int) + 1) (mixed n (3 : Int)) ++
    fixtures (mvRat n) (mvJson ratJson) (mixed n (2/3 : Rat)) (mixed n (-1/2 : Rat) + 1) (mixed n (3/5 : Rat))) ++
  fixtures ratFn fractionJson (fraction 0 0 2) (fraction 0 1 1) (fraction 1 0 2)

end Hex.DeterminantCarriers
