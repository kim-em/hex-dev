/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexCharPoly

/-! Shared integer fixtures for characteristic-polynomial conformance. -/

namespace Hex.CharPolyFixtures

/-- A square matrix fixture with its dimension retained in the value. -/
structure Case where
  id : String
  n : Nat
  matrix : Hex.Matrix Int n n

private def matrixOfRows (n : Nat) (rows : Array (Array Int)) : Hex.Matrix Int n n :=
  Hex.Matrix.ofFn fun i j => (rows.getD i.val #[]).getD j.val 0

private def mk (id : String) (rows : Array (Array Int)) : Case :=
  { id, n := rows.size, matrix := matrixOfRows rows.size rows }

def empty : Case := mk "empty/0x0" #[]
def scalar : Case := mk "scalar/1x1" #[#[-7]]
def zero2 : Case := mk "zero/2x2" #[#[0, 0], #[0, 0]]
def diagonal3 : Case := mk "diagonal/1-2-3" #[#[1, 0, 0], #[0, 2, 0], #[0, 0, 3]]
def nilpotent4 : Case := mk "nilpotent/jordan-4" #[
  #[0, 1, 0, 0], #[0, 0, 1, 0], #[0, 0, 0, 1], #[0, 0, 0, 0]]
def upper4 : Case := mk "triangular/upper-4" #[
  #[2, 1, -3, 4], #[0, -1, 5, 2], #[0, 0, 3, 7], #[0, 0, 0, 6]]
def lower4 : Case := mk "triangular/lower-4" #[
  #[2, 0, 0, 0], #[1, -1, 0, 0], #[-3, 5, 3, 0], #[4, 2, 7, 6]]
def blockTriangular4 : Case := mk "block-triangular/2-plus-2" #[
  #[0, 1, 4, -2], #[-2, 3, 1, 5], #[0, 0, 4, 1], #[0, 0, -3, 2]]

private def transposeBase : Hex.Matrix Int 4 4 := matrixOfRows 4 #[
  #[1, 2, -1, 0], #[3, -2, 4, 1], #[0, 5, 2, -3], #[2, 1, 0, 4]]

def transposeOriginal : Case := { id := "transpose/original", n := 4, matrix := transposeBase }
def transposeImage : Case :=
  { id := "transpose/transposed", n := 4, matrix := transposeBase.transpose }

private def similarBase : Hex.Matrix Int 3 3 := matrixOfRows 3 #[
  #[1, 2, 3], #[0, -2, 4], #[5, 1, 0]]
private def transvection (c : Int) : Hex.Matrix Int 3 3 :=
  Hex.Matrix.rowAdd (Hex.Matrix.identity (R := Int) 3) 1 0 c
private def similarImage : Hex.Matrix Int 3 3 :=
  transvection 3 * similarBase * transvection (-3)

def similarityOriginal : Case :=
  { id := "similarity/original", n := 3, matrix := similarBase }
def similarityConjugate : Case :=
  { id := "similarity/transvection", n := 3, matrix := similarImage }

def repeatedJordan4 : Case := mk "jordan/repeated-eigenvalue" #[
  #[5, 1, 0, 0], #[0, 5, 1, 0], #[0, 0, 5, 0], #[0, 0, 0, 5]]

private def randomMatrix (n salt : Nat) : Hex.Matrix Int n n :=
  Hex.Matrix.ofFn fun i j =>
    let raw := (i.val * 37 + j.val * 19 + salt * 11 + i.val * j.val * 7) % 23
    Int.ofNat raw - 11

def random6 : Case := { id := "random/6x6", n := 6, matrix := randomMatrix 6 1 }
def random7 : Case := { id := "random/7x7", n := 7, matrix := randomMatrix 7 2 }
def random8 : Case := { id := "random/8x8", n := 8, matrix := randomMatrix 8 3 }

private def huge : Int := 9223372036854775808
def large5 : Case := mk "large/near-2pow63-5x5" #[
  #[huge, 1, -2, 3, -4],
  #[-5, huge - 1, 6, -7, 8],
  #[9, -10, -huge, 11, -12],
  #[13, 14, -15, huge + 1, 16],
  #[-17, 18, 19, -20, 2 * huge - 3]]

def all : List Case := [
  empty, scalar, zero2, diagonal3, nilpotent4, upper4, lower4,
  blockTriangular4, transposeOriginal, transposeImage,
  similarityOriginal, similarityConjugate, repeatedJordan4,
  random6, random7, random8, large5]

end Hex.CharPolyFixtures
