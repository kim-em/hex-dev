/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Data
import HexRealClosureMathlib.InverseEquation
open Hex Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Hex.RCF.RealCoefficients.FiniteMatrixTests
open Hex.SignDet
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Reader
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

def argument : Element FiniteTower.first :=
  (Guards.Schema.positive Packings.facts).get ⟨0, by decide +kernel⟩
def entry : Packing FiniteTower.first := Packings.facts.get ⟨27, by decide +kernel⟩
def alternate : Packing FiniteTower.first := Packings.facts.get ⟨28, by decide +kernel⟩

def read (argument : Element FiniteTower.first) (entry : Packing FiniteTower.first)
    (packet : Codec.Json) : Option (Packing.Inverse.Equation entry) := do
  if argument.sign = 0 then none else do
    let raw := FiniteTower.first.root.raw
    let graph ← (Codec.readGraph ValueCodec.rat ValueCodec.nat 7
      raw.head raw.lower raw.upper packet).toOption
    let memo ← graph.validate? Hex.Sturm.orderSign 7 raw.head raw.lower raw.upper
    Packing.Inverse.Equation.readMemo? argument entry memo graph.root

theorem read_argument {argument : Element FiniteTower.first} {entry : Packing FiniteTower.first}
    {packet : Codec.Json} {output : Packing.Inverse.Equation entry}
    (accepted : read argument entry packet = some output) : output.argument = argument := by
  unfold read at accepted
  split at accepted
  · contradiction
  · simp only [bind, Option.bind] at accepted
    split at accepted
    · contradiction
    · dsimp only at accepted
      split at accepted
      · contradiction
      · exact Packing.Inverse.Equation.readMemo?_argument _ _ _ _ accepted
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Reader
