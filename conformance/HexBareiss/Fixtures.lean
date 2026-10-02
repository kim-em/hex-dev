/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBareiss.Bareiss

namespace Hex.BareissEmit

open Hex

/-- Build a square `Matrix Int n n` from a 2-D array of rows; missing entries
default to `0`. -/
def mkSquare (n : Nat) (rows : Array (Array Int)) : Matrix Int n n :=
  Matrix.ofFn fun i j =>
    (rows.getD i.val #[]).getD j.val 0

def random4 : Matrix Int 4 4 :=
  mkSquare 4 #[#[3, 1, 4, 1], #[5, 9, 2, 6], #[5, 3, 5, 8], #[9, 7, 9, 3]]

def singular4Def1 : Matrix Int 4 4 :=
  mkSquare 4 #[#[2, 0, -1, 3], #[1, 5, 4, -2], #[0, 3, 7, 1],
               #[3, 5, 3, 1]]

def singular4Def2 : Matrix Int 4 4 :=
  mkSquare 4 #[#[1, 2, 3, 4], #[2, 1, 0, -1],
               #[3, 3, 3, 3], #[5, 4, 3, 2]]

def triangular4 : Matrix Int 4 4 :=
  mkSquare 4 #[#[2, 1, 4, 0], #[0, -3, 2, 1], #[0, 0, 5, 6], #[0, 0, 0, 7]]

def random6 : Matrix Int 6 6 :=
  mkSquare 6 #[
    #[ 3,  1, -2,  4,  0,  1],
    #[ 0,  5,  1, -1,  3,  2],
    #[ 2, -1,  4,  0,  1,  3],
    #[ 1,  2,  0,  3, -2,  4],
    #[-1,  0,  2,  1,  4,  0],
    #[ 4,  3,  1,  2, -3,  5]
  ]

def singular6Def1 : Matrix Int 6 6 :=
  mkSquare 6 #[
    #[ 1,  2,  3, -1,  0,  4],
    #[ 0,  1, -2,  3,  1,  2],
    #[ 4, -1,  0,  2,  3,  1],
    #[ 2,  3,  1,  0,  4, -1],
    #[ 1,  0,  4,  3, -2,  2],
    #[ 1,  3,  1,  2,  1,  6]   -- = row0 + row1
  ]

def triangular6 : Matrix Int 6 6 :=
  mkSquare 6 #[
    #[1,  2, -1,  3,  0,  1],
    #[0,  2,  4, -2,  1,  3],
    #[0,  0,  3,  1,  2, -1],
    #[0,  0,  0,  4,  0,  2],
    #[0,  0,  0,  0,  5,  3],
    #[0,  0,  0,  0,  0,  6]
  ]

def random8 : Matrix Int 8 8 :=
  mkSquare 8 #[
    #[ 2,  0,  1, -1,  3,  0,  4,  1],
    #[ 1,  3,  0,  2, -1,  4,  1,  0],
    #[ 0, -2,  3,  1,  4,  0,  2,  1],
    #[ 4,  1, -1,  2,  0,  3,  1,  2],
    #[-1,  2,  0,  1,  3,  1, -2,  4],
    #[ 3,  0,  2, -1,  1,  4,  0,  1],
    #[ 1,  4,  1,  0, -2,  2,  3,  0],
    #[ 0,  1,  3,  4,  1, -1,  2,  3]
  ]

def triangular8 : Matrix Int 8 8 :=
  mkSquare 8 #[
    #[1, 2, 0, 1, 3, -1, 0, 2],
    #[0, 1, 3, -2, 0, 1, 4, 0],
    #[0, 0, 2, 1, -1, 0, 3, 1],
    #[0, 0, 0, 2, 0, 4, -1, 0],
    #[0, 0, 0, 0, 3, 1, 0, 2],
    #[0, 0, 0, 0, 0, 3, 2, -1],
    #[0, 0, 0, 0, 0, 0, 4, 1],
    #[0, 0, 0, 0, 0, 0, 0, 4]
  ]

end Hex.BareissEmit
