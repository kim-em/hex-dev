/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexPosDef
import Lean.Data.Json

/-! Bounded exact classifications and explicit negative witnesses for the matrix oracle. -/

namespace Hex.PosDefEmit

open Hex.PosDef Lean

def intValue : Certificate Int → Json
  | .positive _ => Json.mkObj [("positive", toJson true)]
  | .negative (.nonpositive v) => Json.mkObj [("positive", toJson false), ("vector", toJson v)]
  | .negative (.notHermitian i j) =>
      Json.mkObj [("positive", toJson false), ("notHermitian", toJson [i, j])]

def emitInt (name : String) (n : Nat) (rows : List (List Int)) : IO Unit := do
  let B := Hex.Matrix.ofFn fun (i j : Fin n) => Hex.Matrix.Lists.get rows i j
  let c ← match Int.certify B with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"{name}: {repr e}")
  Hex.Conformance.Emit.emitMatrixFixture "HexPosDef" name rows
  Hex.Conformance.Emit.emitResult "HexPosDef" name "pos-def" (intValue c).compress

def emitGaussian (name : String) (n : Nat) (rows : List (List Gaussian)) : IO Unit := do
  let get := PosDef.Lists.get PosDef.Lists.gaussianArithmetic rows
  let B := Hex.Matrix.ofFn fun (i j : Fin n) => get i j
  let c ← match Gaussian.certify B with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"{name}: {repr e}")
  let realRows := (List.range (n + n)).map fun i => (List.range (n + n)).map fun j =>
    if i < n then
      if j < n then (get i j).re else -(get i (j - n)).im
    else if j < n then (get (i - n) j).im else (get (i - n) (j - n)).re
  let value := match c with
    | .positive _ => Json.mkObj [("positive", toJson true)]
    | .negative (.nonpositive v) =>
        Json.mkObj [("positive", toJson false), ("vector", toJson (v.map Gaussian.re ++ v.map Gaussian.im))]
    | .negative (.notHermitian i j) =>
        let i' := if (get i j).re = (get j i).re then n + i else i
        Json.mkObj [("positive", toJson false), ("notHermitian", toJson [i', j])]
  Hex.Conformance.Emit.emitMatrixFixture "HexPosDef" name realRows
  Hex.Conformance.Emit.emitResult "HexPosDef" name "pos-def" value.compress

def cartan (n : Nat) : List (List Int) :=
  (List.range n).map fun i => (List.range n).map fun j =>
    if i = j then 2
    else if (i = 0 ∧ j = 2) ∨ (j = 0 ∧ i = 2) ∨
      (i = 1 ∧ j = 3) ∨ (j = 1 ∧ i = 3) ∨
      (2 ≤ i ∧ i + 1 = j) ∨ (2 ≤ j ∧ j + 1 = i) then -1 else 0

def emitAll : IO Unit := do
  emitInt "empty" 0 []
  for n in [6, 7, 8, 9, 10] do emitInt s!"E{n}" n (cartan n)
  for a in [-1, 0, 1, 2] do
    for b in [-1, 0, 1, 2] do
      for d in [-1, 0, 1, 2] do emitInt s!"symmetric/{a}/{b}/{d}" 2 [[a, b], [b, d]]
  emitInt "nonsymmetric" 2 [[1, 2], [0, 1]]
  for d in [0, 1, 2] do
    emitGaussian s!"gaussian/{d}" 2 [[⟨d, 0⟩, ⟨0, 1⟩], [⟨0, -1⟩, ⟨d, 0⟩]]
  emitGaussian "gaussian/three" 3 [[⟨3, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩],
    [⟨0, -1⟩, ⟨3, 0⟩, ⟨0, 1⟩], [⟨0, 0⟩, ⟨0, -1⟩, ⟨3, 0⟩]]
  emitGaussian "gaussian/notHermitian" 1 [[⟨1, 1⟩]]

end Hex.PosDefEmit

def main : IO Unit := Hex.PosDefEmit.emitAll
