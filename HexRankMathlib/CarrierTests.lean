/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexRankMathlib.QuadraticTactic
import HexRank.PolyProduce
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

open Hex.Matrix HexMatrixMathlib

instance : Zsqrtd.Nonsquare (2 : Nat) := ⟨by
  intro n hn
  have : n < 2 := by nlinarith
  interval_cases n <;> norm_num at hn⟩

instance : IsDomain (Zsqrtd 2) := inferInstanceAs (IsDomain (Zsqrtd (2 : Nat)))

theorem quadraticRank : Matrix.rank (R := Zsqrtd 2) !![⟨0, 1⟩, 1; 1, ⟨0, 1⟩] = 2 := by rank
example : Matrix.rank (R := Zsqrtd 2) !![⟨0, 1⟩, 1; 2, ⟨0, 1⟩] = 1 := by rank
example : Matrix.rank (R := Zsqrtd 2) !![⟨0, 1⟩ + 1, 1; 1, ⟨0, 1⟩ - 1] = 0 + 1 := by rank
example : Matrix.rank (R := GaussianInt) !![⟨0, 1⟩, 1; 1, ⟨0, -1⟩] = 1 := by rank
example : Matrix.rank (R := Zsqrtd 2) !![0, 0; 0, 0] = 0 := by rank
example : Matrix.rank (fun (i j : Fin 2) => (⟨i.val, j.val⟩ : Zsqrtd 2)) = 2 := by rank
example : 1 ≤ Matrix.rank (R := Zsqrtd 2) !![⟨0, 1⟩, 1; 2, ⟨0, 1⟩] := by rank
example : 2 ≥ Matrix.rank (R := Zsqrtd 2) !![⟨0, 1⟩, 1; 2, ⟨0, 1⟩] := by rank
example : 1 = Matrix.rank (R := Zsqrtd 2) !![⟨0, 1⟩, 1; 2, ⟨0, 1⟩] := by rank
example : Matrix.rank (fun (_ : Fin 0) (_ : Fin 3) => (0 : Zsqrtd 2)) = 0 := by rank
example : Matrix.rank (fun (_ : Fin 3) (_ : Fin 0) => (0 : Zsqrtd 2)) = 0 := by rank

/-- info: '_private.HexRankMathlib.CarrierTests.0.quadraticRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadraticRank

/-- error: rank: the target is false: the rank is 1 -/
#guard_msgs in
example : Matrix.rank (R := Zsqrtd 2) !![⟨0, 1⟩, 1; 2, ⟨0, 1⟩] = 2 := by rank

-- Exercise the same producer on monic, nonmonic, cubic, and degree-one
-- presentations, including a composite modular ring and unreduced entries.
#guard (Hex.Matrix.PolyWitness.produce 2 2 [-2, 0, 1]
  [[[0, 1], [1]], [[1], [0, 1]]] [15]).toOption.map (·.rank) = some 2
#guard (Hex.Matrix.PolyWitness.produce 2 2 [-1, 0, 2]
  [[[0, 1], [1]], [[1], [0, 2]]]).toOption.map (·.rank) = some 1
#guard (Hex.Matrix.PolyWitness.produce 2 2 [-2, 0, 0, 1]
  [[[0, 1], [1]], [[0, 0, 1], [0, 1]]]).toOption.map (·.rank) = some 1
#guard (Hex.Matrix.PolyWitness.produce 2 2 [-1, 2]
  [[[0, 1], [1]], [[1], [2]]]).toOption.map (·.rank) = some 1
#guard (Hex.Matrix.PolyWitness.produce 1 1 [-2, 0, 1]
  [[[-2, 0, 1]]]).toOption.map (·.rank) = some 0

-- A composite modulus and a reducible modular polynomial are sufficient.
-- These hand-written certificates also exercise the kernel path directly.
private def composite : Hex.Matrix.PolyWitness :=
  ⟨2, 15, 1, [0, 1], [0, 1], [[[0, 8]], [[-1], [0, 1]]],
    [[[8], []], [[1]]], 1, [], []⟩

example : Hex.Matrix.checkRankPoly 2 2 [-2, 0, 1]
    [[[0, 1], [1]], [[1], [0, 1]]] composite = true := by decide +kernel

-- Over ZMod 7 the defining polynomial splits as (X - 3)(X + 3).
example : Hex.Matrix.checkRankPoly 2 2 [-2, 0, 1]
    [[[0, 1], [1]], [[1], [0, 1]]]
    { composite with
      modulus := 7
      vt := [[[0, 4]], [[-1], [0, 1]]]
      lowerQuot := [[[4], []], [[1]]] } = true := by decide +kernel

example : Hex.Matrix.checkRankPoly 2 2 [-2, 0, 1]
    [[[0, 1], [1]], [[1], [0, 1]]]
    { composite with lowerQuot := [[[7], []], [[1]]] } = false := by decide +kernel

example : Hex.Matrix.checkRankPoly 2 2 [-2, 0, 1]
    [[[0, 1], [1]], [[1], [0, 1]]]
    { composite with leadingInv := 0 } = false := by decide +kernel

private def dependent : Hex.Matrix.PolyWitness :=
  ⟨1, 15, 1, [0], [0], [[[0, 8]]], [[[8]]], 1,
    [[[0, 1]]], [[[-1], []]]⟩

example : Hex.Matrix.checkRankPoly 2 2 [-2, 0, 1]
    [[[0, 1], [1]], [[2], [0, 1]]] dependent = true := by decide +kernel

-- Changing an exact relation by a multiple of the modulus must still fail.
example : Hex.Matrix.checkRankPoly 2 2 [-2, 0, 1]
    [[[0, 1], [1]], [[17], [0, 1]]] dependent = false := by decide +kernel

-- Every guard is necessary independently of the polynomial identities.
example : Hex.Matrix.checkRankPoly 2 2 [-2, 0, 1]
    [[[0, 1], [1]], [[1], [0, 1]]]
    { composite with denom := 0 } = false := by decide +kernel
example : Hex.Matrix.checkRankPoly 2 2 [-2, 0, 1]
    [[[0, 1], [1]], [[1], [0, 1]]]
    { composite with modulus := 1 } = false := by decide +kernel
example : Hex.Matrix.checkRankPoly 2 2 [-2, 0, 1]
    [[[0, 1], [1]], [[1], [0, 1]]]
    { composite with modulus := 0 } = false := by decide +kernel
example : Hex.Matrix.checkRankPoly 2 2 [-2, 0, 1]
    [[[0, 1], [1]], [[1], [0, 1]]]
    { composite with rows := [0, 2] } = false := by decide +kernel
example : Hex.Matrix.checkRankPoly 2 2 [-2, 0, 1]
    [[[0, 1], [1]], [[1], [0, 1]]]
    { composite with rank := 1 } = false := by decide +kernel

/--
error: rank: declined: no integral-domain instance is available for
  ℤ√4
-/
#guard_msgs in
example : Matrix.rank (R := Zsqrtd 4) !![1, 0; 0, 1] = 2 := by rank
