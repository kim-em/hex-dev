/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexDeterminantalIdeal

/-!
Single source of committed inputs shared by HexDeterminantalIdeal's Lean
conformance checks and JSONL emit driver.

Every matrix is a matrix of multivariate polynomials over `Int` in the
`grlex` order; an integer matrix is the arity-0 case. `toRat` lifts a matrix
to the field the rank and the locus are computed over, and `pointOf` reads an
integer tuple as a point of that field.
-/

namespace Hex.DeterminantalIdealFixtures

open Hex
open Hex.MvPoly

/-- Entries of a committed matrix: `k` indeterminates over `Int`. -/
abbrev P (k : Nat) := MvPoly k Int Mono.grlex

/-- Entries after lifting to the field the rank is computed over. -/
abbrev Q (k : Nat) := MvPoly k Rat Mono.grlex

/-- A matrix from its rows of polynomials. -/
def polyMatrix {k n m : Nat} (rows : Vector (Vector (P k) m) n) :
    Matrix (P k) n m :=
  Matrix.ofFn fun i j => rows[i][j]

/-- An integer matrix as an arity-0 polynomial matrix of constants. -/
def intMatrix {n m : Nat} (rows : Vector (Vector Int m) n) : Matrix (P 0) n m :=
  Matrix.ofFn fun i j => C rows[i][j]

/-- Lift the coefficients from `Int` to `Rat`. -/
def toRat {k n m : Nat} (A : Matrix (P k) n m) : Matrix (Q k) n m :=
  A.map (mapCoeffs fun c => (c : Rat))

/-- Read an integer tuple as a point of `Rat`. -/
def pointOf {k : Nat} (v : Vector Int k) : Fin k → Rat := fun i => (v[i] : Rat)

/-- The name a point carries in a result `op`: its JSON integer list. -/
def pointName {k : Nat} (v : Vector Int k) : String :=
  "[" ++ String.intercalate "," (v.toList.map toString) ++ "]"

/-! # Committed matrices -/

/-- The `0 × 0` matrix. -/
def empty00 : Matrix (P 0) 0 0 := intMatrix #v[]

/-- A matrix with no rows. -/
def empty02 : Matrix (P 0) 0 2 := intMatrix #v[]

/-- A matrix with no columns. -/
def empty20 : Matrix (P 0) 2 0 := intMatrix #v[#v[], #v[]]

/-- A `2 × 3` integer matrix. -/
def small23 : Matrix (P 0) 2 3 := intMatrix #v[#v[1, 2, 3], #v[4, 5, 6]]

/-- A `3 × 2` integer matrix. -/
def small32 : Matrix (P 0) 3 2 := intMatrix #v[#v[1, 2], #v[3, 4], #v[5, 6]]

/-- A nonsingular `2 × 2` integer matrix. -/
def square22 : Matrix (P 0) 2 2 := intMatrix #v[#v[2, -1], #v[3, 5]]

/-- The zero `2 × 2` matrix. -/
def zero22 : Matrix (P 0) 2 2 := intMatrix #v[#v[0, 0], #v[0, 0]]

/-- Eight distinct integers, so that the six `2 × 2` minors are pairwise
distinct and the column order is visible in the answer. -/
def distinct24 : Matrix (P 0) 2 4 :=
  intMatrix #v[#v[1, 2, 3, 4], #v[5, 7, 11, 13]]

/-- A singular `3 × 3` integer matrix of rank `2`. -/
def singular33 : Matrix (P 0) 3 3 :=
  intMatrix #v[#v[1, 2, 3], #v[4, 5, 6], #v[7, 8, 9]]

/-- The generic `2 × 3` matrix of six indeterminates. -/
def generic23 : Matrix (P 6) 2 3 :=
  polyMatrix #v[#v[X 0, X 1, X 2], #v[X 3, X 4, X 5]]

/-- The generic matrix transposed. -/
def generic32 : Matrix (P 6) 3 2 := generic23.transpose

/-- Two equal columns of indeterminates, so one minor vanishes and the other
two coincide. -/
def equalCols : Matrix (P 4) 2 3 :=
  polyMatrix #v[#v[X 0, X 0, X 2], #v[X 1, X 1, X 3]]

/-- The Vandermonde matrix `V_2`, rows `[1, x_i]`. -/
def vandermonde2 : Matrix (P 2) 2 2 :=
  polyMatrix #v[#v[1, X 0], #v[1, X 1]]

/-- The Vandermonde matrix `V_3`, rows `[1, x_i, x_i ^ 2]`. -/
def vandermonde3 : Matrix (P 3) 3 3 :=
  polyMatrix #v[
    #v[1, X 0, X 0 ^ 2],
    #v[1, X 1, X 1 ^ 2],
    #v[1, X 2, X 2 ^ 2]]

/-- The bordered identity `[[I_1, u], [vᵀ, t]]` in `u = x_0`, `v = x_1`,
`t = x_2`. -/
def bordered1 : Matrix (P 3) 2 2 :=
  polyMatrix #v[#v[1, X 0], #v[X 1, X 2]]

/-- The bordered identity `[[I_2, u], [vᵀ, t]]` in `u = (x_0, x_1)`,
`v = (x_2, x_3)`, `t = x_4`. -/
def bordered2 : Matrix (P 5) 3 3 :=
  polyMatrix #v[
    #v[1, 0, X 0],
    #v[0, 1, X 1],
    #v[X 2, X 3, X 4]]

/-- The matrix whose invariance under a unimodular left factor is recorded. -/
def invarBase : Matrix (P 2) 2 3 :=
  polyMatrix #v[#v[X 0, X 1, 1], #v[1, X 0, X 1]]

/-- An explicit unimodular integer matrix, of determinant `1`. -/
def unimodular : Matrix (P 2) 2 2 :=
  polyMatrix #v[#v[1, 1], #v[1, 2]]

/-- The unimodular left multiple of `invarBase`. -/
def invarImage : Matrix (P 2) 2 3 := unimodular * invarBase

/-! # The committed cases -/

/-- One committed matrix, the minor size recorded for it, and the points at
which the rank and the locus are recorded. -/
structure Case where
  /-- The case name, unique in the stream. -/
  id : String
  /-- The number of indeterminates. -/
  arity : Nat
  /-- The number of rows. -/
  rows : Nat
  /-- The number of columns. -/
  cols : Nat
  /-- The matrix itself. -/
  matrix : Matrix (P arity) rows cols
  /-- The minor size. -/
  r : Nat
  /-- The points, as integer tuples. -/
  points : List (Vector Int arity)

/-- Build a case, reading the arity and the shape off the matrix. -/
def case {k n m : Nat} (id : String) (A : Matrix (P k) n m) (r : Nat)
    (points : List (Vector Int k) := []) : Case :=
  ⟨id, k, n, m, A, r, points⟩

/-- Every committed case, in stream order. -/
def cases : List Case := [
  case "empty/0x0/r0" empty00 0,
  case "empty/0x2/r0" empty02 0,
  case "empty/2x0/r0" empty20 0,
  case "small/2x3/r0" small23 0,
  case "square/2x2/r3" square22 3,
  case "small/2x3/r3" small23 3,
  case "small/3x2/r3" small32 3,
  case "zero/2x2/r1" zero22 1 [#v[]],
  case "distinct/2x4/r2" distinct24 2 [#v[]],
  case "singular/3x3/r2" singular33 2 [#v[]],
  case "singular/3x3/r3" singular33 3 [#v[]],
  case "generic/2x3/r2" generic23 2,
  case "generic/3x2/r2" generic32 2,
  case "equalCols/2x3/r2" equalCols 2,
  case "vandermonde2/r2" vandermonde2 2 [#v[3, 3], #v[2, 5]],
  case "vandermonde2/r1" vandermonde2 1 [#v[4, 4]],
  case "vandermonde3/r3" vandermonde3 3 [#v[1, 1, 2], #v[1, 2, 3]],
  case "vandermonde3/r2" vandermonde3 2 [#v[5, 5, 5]],
  case "bordered1/r1" bordered1 1 [#v[2, 3, 6], #v[2, 3, 7]],
  case "bordered1/r2" bordered1 2 [#v[2, 3, 6], #v[2, 3, 7]],
  case "bordered2/r2" bordered2 2 [#v[2, 3, 5, 7, 31], #v[2, 3, 5, 7, 30]],
  case "bordered2/r3" bordered2 3 [#v[2, 3, 5, 7, 31], #v[2, 3, 5, 7, 30]],
  case "invariance/base" invarBase 2 [#v[2, 3], #v[1, 1]],
  case "invariance/image" invarImage 2 [#v[2, 3], #v[1, 1]]]

end Hex.DeterminantalIdealFixtures
