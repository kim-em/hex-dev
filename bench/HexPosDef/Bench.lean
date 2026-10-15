/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPosDef
import HexMatrix.Notation
import LeanBench

/-! Native production and checking on a deterministic integer Gram family.
The cubic model counts scalar operations. Integer operands grow with minors;
it is not a claim of cubic elapsed time. Preparation constructs both the
matrix and the independently checked certificate outside the timed call. -/

namespace Hex.PosDefBench

open Hex.PosDef

def coefficient (n i j : Nat) : Int :=
  Int.ofNat (((1103515245 * (i * n + j + 17) + 12345) % 2147483648) % 11) - 5

def gram (n : Nat) : Hex.Matrix Int n n :=
  Hex.Matrix.ofFn fun i j =>
    ((List.range n).map (fun k => coefficient n k i * coefficient n k j)).sum +
      if i = j then 1 else 0

structure Input where
  n : Nat
  matrix : Hex.Matrix Int n n
  rows : List (List Int)
  certificate : Certificate Int

instance : Inhabited Input :=
  ⟨⟨0, Hex.Matrix.ofFn (fun _ _ => 0), [], .positive (.triangular [])⟩⟩

instance : Hashable Input := ⟨fun input => hash (input.n, input.rows)⟩

def prep (n : Nat) : Input :=
  let matrix := gram n
  match Int.certify matrix with
  | .ok certificate => ⟨n, matrix, matrix.rowLists, certificate⟩
  | .error e => panic! s!"Gram certificate production failed: {repr e}"

def produce (input : Input) : Bool := (Int.certify input.matrix).isOk

def check (input : Input) : Bool := Int.check input.n input.rows input.certificate

setup_benchmark produce n => n * n * n
  with prep := prep
  where { paramFloor := 8, paramCeiling := 32, paramSchedule := .custom #[8, 16, 32] }

setup_benchmark check n => n * n * n
  with prep := prep
  where { paramFloor := 8, paramCeiling := 32, paramSchedule := .custom #[8, 16, 32] }

def gaussian (_ : Unit) : Bool :=
  (Gaussian.certify #m[(⟨2, 0⟩ : Gaussian), ⟨0, 1⟩; ⟨0, -1⟩, ⟨2, 0⟩]).isOk

setup_fixed_benchmark gaussian where { }

end Hex.PosDefBench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
