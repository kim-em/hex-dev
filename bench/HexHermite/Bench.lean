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

private def bitLength (z : Int) : Nat :=
  let n := z.natAbs
  if n = 0 then 0 else n.log2 + 1

private def matrixBits (M : Matrix Int n m) : Nat :=
  M.data.foldl (fun largest z => max largest (bitLength z)) 0

/-- Diagnostic state for the deliberately untimed entry-growth runner. -/
private structure GrowthState (n m : Nat) where
  result : Matrix.Hermite.Result Unit n m
  peak : Nat

private def observe (s : Matrix.Hermite.Result Unit n m) (peak : Nat) :
    GrowthState n m :=
  ⟨s, max peak (matrixBits s.matrix)⟩

private def growthClear (s : GrowthState n m) (col : Fin m)
    (pivot found : Fin n) : GrowthState n m :=
  let ops := Matrix.Hermite.formAccumulator n
  let s := observe (Matrix.Hermite.swapStep ops s.result pivot found) s.peak
  let s := (List.finRange n).foldl (fun s k =>
    if pivot.val < k.val then
      observe (Matrix.Hermite.gcdStep ops col pivot k s.result) s.peak
    else s) s
  let s := observe (Matrix.Hermite.signStep ops col pivot s.result) s.peak
  (List.finRange n).foldl (fun s k =>
    if k.val < pivot.val then
      observe (Matrix.Hermite.reduceStep ops col pivot k s.result) s.peak
    else s) s

private def growthColumn (s : GrowthState n m) (col : Fin m) : GrowthState n m :=
  if hr : s.result.pivots.length < n then
    let pivot : Fin n := ⟨s.result.pivots.length, hr⟩
    match Matrix.Hermite.findPivot? s.result.matrix col s.result.pivots.length with
    | none => s
    | some found =>
        let next := growthClear s col pivot found
        { next with result := { next.result with pivots := next.result.pivots ++ [col] } }
  else s

/-- Scan the working matrix after every elementary update and return the peak
coefficient bit-size. This runner is intentionally separate from timed
benchmarks so instrumentation does not perturb ordinary timings. -/
def peakBits (input : Input) : Nat :=
  let A := matrix input
  let initial : GrowthState input.rows input.cols :=
    { result :=
        { matrix := A, pivots := []
          accumulator := (Matrix.Hermite.formAccumulator input.rows).init }
      peak := matrixBits A }
  ((List.finRange input.cols).foldl growthColumn initial).peak

/-- Peak-versus-output growth data for the predeclared badly-conditioned
family. -/
def conjugateGrowth (n : Nat) : Nat × Nat :=
  let input := conjugate n
  (peakBits input, matrixBits (Matrix.hnf (matrix input)))

def runDense (input : Input) : Int := checksum (Matrix.hnf (matrix input))
def runDeficient (input : Input) : Int := checksum (Matrix.hnf (matrix input))
def runTall (input : Input) : Int := checksum (Matrix.hnf (matrix input))
def runConjugate (input : Input) : Int := checksum (Matrix.hnf (matrix input))

/- Cost-model derivation: the square dense family scans `n` columns, clears
`O(n)` rows per pivot, and each elementary row update touches `O(n)` entries,
giving `O(n³)` integer operations. -/
setup_benchmark runDense n => n ^ 3 with prep := dense where {
  paramFloor := 4, paramCeiling := 20, paramSchedule := .custom #[4, 8, 12, 16, 20]
  maxSecondsPerCall := 10.0
}
/- Cost-model derivation: rank deficiency changes which pivots are found but
not the worst-case column, row-clear, and row-width loops, so the square
family remains `O(n³)` integer operations. -/
setup_benchmark runDeficient n => n ^ 3 with prep := deficient where {
  paramFloor := 4, paramCeiling := 20, paramSchedule := .custom #[4, 8, 12, 16, 20]
  maxSecondsPerCall := 10.0
}
/- Cost-model derivation: the tall family has `4n` rows and `n` columns;
clearing `O(n)` rows with `O(n)`-wide updates for each of `n` columns is still
`O(n³)` integer operations because the aspect ratio is fixed. -/
setup_benchmark runTall n => n ^ 3 with prep := tall where {
  paramFloor := 2, paramCeiling := 12, paramSchedule := .custom #[2, 4, 6, 8, 12]
  maxSecondsPerCall := 10.0
}
/- Cost-model derivation: conjugation changes coefficient growth but retains
the square `n`-column by `n`-row clearing structure with `n`-wide updates, so
the declared operation-count model is `O(n³)`. -/
setup_benchmark runConjugate n => n ^ 3 with prep := conjugate where {
  paramFloor := 4, paramCeiling := 20, paramSchedule := .custom #[4, 8, 12, 16, 20]
  maxSecondsPerCall := 10.0
}

end Hex.HermiteBench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
