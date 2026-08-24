/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexHermite
import LeanBench

/-! Mathlib-free HNF benchmarks over the four input families fixed by the SPEC. -/

namespace Hex.HermiteBench

structure Input where
  rows : Nat
  cols : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable

private def entry (salt n i j : Nat) : Int :=
  Int.ofNat (((i + 1) * 37 + (j + 3) * 19 + n * 11 + salt) % 21) - 10

def dense (n : Nat) : Input :=
  { rows := n, cols := n
    entries := (Array.range (n * n)).map fun k =>
      let i := k / n
      let j := k % n
      entry 5 n i j + if i = j then Int.ofNat (4 * n + 1) else 0 }

def deficient (n : Nat) : Input :=
  let rank := n / 2
  { rows := n, cols := n
    entries := (Array.range (n * n)).map fun k =>
      let i := k / n
      let j := k % n
      if i < rank then entry 17 n i j
      else if rank = 0 then 0 else entry 17 n (i % rank) j * Int.ofNat (i + 1) }

def tall (n : Nat) : Input :=
  let rows := 4 * n
  { rows := rows, cols := n
    entries := (Array.range (rows * n)).map fun k =>
      let i := k / n
      let j := k % n
      if i < n then entry 31 n i j + if i = j then Int.ofNat (2 * n + 1) else 0
      else if n = 0 then 0 else entry 31 n (i % n) j * Int.ofNat (i % 5) }

def conjugate (n : Nat) : Input :=
  { rows := n, cols := n
    entries := (Array.range (n * n)).map fun k =>
      let i := k / n
      let j := k % n
      if j = i then Int.ofNat (i + 2)
      else if j < i then Int.ofNat ((i - j + 1) * (j + 2))
      else 0 }

private def matrix (input : Input) : Matrix Int input.rows input.cols :=
  Matrix.ofFn fun i j => input.entries.getD (i.val * input.cols + j.val) 0

private def checksum (M : Matrix Int n m) : Int :=
  M.data.foldl (fun acc x => acc * 65537 + x) 0

def runDense (input : Input) : Int := checksum (Matrix.hnf (matrix input))
def runDeficient (input : Input) : Int := checksum (Matrix.hnf (matrix input))
def runTall (input : Input) : Int := checksum (Matrix.hnf (matrix input))
def runConjugate (input : Input) : Int := checksum (Matrix.hnf (matrix input))

setup_benchmark runDense n => n * n * n with prep := dense where {
  paramFloor := 4, paramCeiling := 20, paramSchedule := .custom #[4, 8, 12, 16, 20]
  maxSecondsPerCall := 10.0
}
setup_benchmark runDeficient n => n * n * n with prep := deficient where {
  paramFloor := 4, paramCeiling := 20, paramSchedule := .custom #[4, 8, 12, 16, 20]
  maxSecondsPerCall := 10.0
}
setup_benchmark runTall n => n * n * n with prep := tall where {
  paramFloor := 2, paramCeiling := 12, paramSchedule := .custom #[2, 4, 6, 8, 12]
  maxSecondsPerCall := 10.0
}
setup_benchmark runConjugate n => n * n * n with prep := conjugate where {
  paramFloor := 4, paramCeiling := 20, paramSchedule := .custom #[4, 8, 12, 16, 20]
  maxSecondsPerCall := 10.0
}

end Hex.HermiteBench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
