/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
import HexGenericRankMathlib.RankLocus
import Mathlib.Algebra.Field.ZMod

example (x y : ℚ) : True := by
  rank_locus !![x,y]
  have : (!![x,y]).rank < 1 ↔ x = 0 ∧ y = 0 := h
  trivial

example (x : ZMod 3) : True := by
  rank_locus !![x^3-x]
  have : (!![x^3-x]).rank < 1 ↔ x^3-x = 0 := h
  trivial

example (x : ZMod 3) : True := by
  rank_locus !![x, 1; 1, x]
  have : (!![x, 1; 1, x]).rank < 2 ↔ x ^ 2 - 1 = 0 := h
  trivial
