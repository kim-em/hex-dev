/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import HexECPPMathlib.Reduction

/-! Correspondence at prime divisors of composite subjects.
The point `(0, 1)` lies on `y² = x³ + x + 1`, whose discriminant factor is 31.
The additions below consume an actual inverse of 2 modulo the parent subject.
-/

open Hex.ECPP

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

example : ∃ P : (shortCurve 5 1 1).toAffine.Point,
    (Point.affine 0 1).Rep 5 1 1 P ∧ P ≠ 0 ∧
    (Point.affine 9 12).Rep 5 1 1 (P + P) := by
  obtain ⟨P, hP, hne⟩ := startingPoint_rep
    (p := 5) (n := 35) (a := 1) (b := 1) (x := 0) (y := 1) (inv := 26)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨P, hP, hne, add_rep (n := 35) (R := .affine 9 12) (ws := [18]) (rest := [])
    (by decide) (by decide) hP hP (by rfl)⟩

example : ∃ P : (shortCurve 7 1 1).toAffine.Point,
    (Point.affine 0 1).Rep 7 1 1 P ∧ P ≠ 0 ∧
    (Point.affine 9 12).Rep 7 1 1 (P + P) := by
  obtain ⟨P, hP, hne⟩ := startingPoint_rep
    (p := 7) (n := 35) (a := 1) (b := 1) (x := 0) (y := 1) (inv := 26)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨P, hP, hne, add_rep (n := 35) (R := .affine 9 12) (ws := [18]) (rest := [])
    (by decide) (by decide) hP hP (by rfl)⟩

example : ∃ P : (shortCurve 7 1 1).toAffine.Point,
    (Point.affine 0 1).Rep 7 1 1 P ∧ P ≠ 0 ∧
    (Point.affine 37 5).Rep 7 1 1 (P + P) := by
  obtain ⟨P, hP, hne⟩ := startingPoint_rep
    (p := 7) (n := 49) (a := 1) (b := 1) (x := 0) (y := 1) (inv := 19)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨P, hP, hne, add_rep (n := 49) (R := .affine 37 5) (ws := [25]) (rest := [])
    (by decide) (by decide) hP hP (by rfl)⟩
