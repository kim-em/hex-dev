/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexCharPolyMathlib

public section

open Matrix Polynomial

example : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) Int).charpoly =
    X ^ 2 - 5 * X - 2 := by char_poly

example : (!![] : Matrix (Fin 0) (Fin 0) Int).charpoly = 1 := by char_poly
