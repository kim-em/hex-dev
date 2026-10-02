/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexCharPoly
import HexMvPoly.Ring
import HexModArith
import HexRationalFn.Field
import Lean.Data.Json

/-! Exact carrier inputs and canonical wire encodings shared by integration
fixtures and benchmarks. The outer `DensePoly` variable is always fresh. -/
namespace Hex.CharPolyCarriers
open Hex
open Lean (Json toJson)

scoped instance bounds101 : ZMod64.Bounds 101 := ⟨by decide, by decide⟩

-- DensePoly stores its Zero instance in its type. Select the ring numeral
-- (ZMod64.instOfNat 0), rather than ZMod64.instZero: their exported module
-- interfaces are not definitionally interchangeable during instance search.
scoped instance ringZero [ZMod64.Bounds p] : Zero (ZMod64 p) := ⟨0⟩

abbrev Mod := ZMod64 101
abbrev MV (n : Nat) (R : Type) [Zero R] := MvPoly n R Mono.grevlex

def intJson (x : Int) : Json := toJson x
def ratJson (x : Rat) : Json := toJson #[toJson x.num, toJson x.den]
def modJson (x : Mod) : Json := toJson x.val.toNat

def denseJson [Zero R] [DecidableEq R] (encode : R → Json) (p : DensePoly R) : Json :=
  .arr (p.toArray.map encode)

def mvJson [Zero R] {n : Nat} (encode : R → Json) (p : MV n R) : Json :=
  toJson (p.termsList.map fun (m, c) => toJson #[toJson m.toArray, encode c])

def fractionJson (f : RationalFn Rat) : Json :=
  Json.mkObj [("num", denseJson ratJson f.num), ("den", denseJson ratJson f.den)]

def fraction (p q : DensePoly Rat) : RationalFn Rat :=
  letI : Inhabited (RationalFn Rat) := ⟨0⟩
  if h : q ≠ 0 then RationalFn.normalize p q h
  else panic! "carrier input has a zero denominator"

/-- Dense mixed-sign polynomial entries with nonzero leading coefficient and rational
coefficients when requested. Degree is the actual entry degree. -/
def denseEntry [Lean.Grind.CommRing R] [DecidableEq R]
    (scalar : Int → R) (degree i j : Nat) : DensePoly R :=
  DensePoly.ofCoeffs ((Array.range (degree + 1)).map fun k =>
    scalar ((if (i + j + k) % 2 = 0 then 1 else -1) *
      Int.ofNat (1 + (i * 7 + j * 3 + k * 5) % 11)))

def mvEntry [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (scalar : Int → R) (arity terms i j : Nat) : MV arity R :=
  MvPoly.ofTerms ((List.range terms).map fun k =>
    (Vector.ofFn fun v : Fin arity =>
      if v.val = 0 then k % 4 else if v.val = 1 then (if arity = 2 then 3 - k % 4 else k / 4 % 3)
      else if v.val = 2 then 5 - k % 4 - k / 4 % 3 else 0,
     scalar ((if (i + j + k) % 2 = 0 then 1 else -1) *
       Int.ofNat (1 + (i * 7 + j * 3 + k * 5) % 11))))

def ratScalar (x : Int) : Rat := (x : Rat) / 3

def ratFnEntry (degree i j : Nat) : RationalFn Rat :=
  fraction (denseEntry ratScalar degree i j)
    (DensePoly.monomial degree 1 + DensePoly.C ((i + j + 2 : Nat) : Rat))

/-- Repeated rows make the singular case dense over every carrier. -/
def matrix [Zero R] (entry : Nat → Nat → R) (shape : String) (n : Nat) : Matrix R n n :=
  Matrix.ofFn fun i j =>
    if shape = "diagonal" && i.val != j.val then 0
    else if shape = "triangular" && i.val > j.val then 0
    else entry (if shape = "singular" then 0 else i.val) j.val

def shapes : List (String × Nat) :=
  [("empty", 0), ("scalar", 1), ("diagonal", 3), ("triangular", 3),
   ("singular", 3), ("dense", 3)]

def request [Lean.Grind.CommRing R] [DecidableEq R]
    (encode : R → Json) (carrier shape : String) (arity : Nat) (A : Matrix R n n) : Json :=
  Json.mkObj [("kind", toJson "charpoly_carrier"), ("schema", toJson (1 : Nat)),
    ("lib", toJson "HexCharPoly"), ("case", toJson s!"{carrier}/{arity}/{shape}"),
    ("carrier", toJson carrier), ("arity", toJson arity), ("modulus", toJson (101 : Nat)),
    ("n", toJson n), ("rows", toJson (A.rows.toArray.map fun row => row.toArray.map encode))]

end Hex.CharPolyCarriers
