/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRank
import all HexRank.PolyProduce
public import LeanBench

public section

namespace Hex.RankBench

open Hex Hex.Matrix

/-! Native quotient witnesses on the companion's fixed quadratic blocks.
Over Q(√2), each `[[√2,1],[1,√2]]` block has determinant one. Duplicating
its rows supplies deficient inputs with the same bounded coefficients.
This is the existing Algebraic8Hex proof-probe family, extended in dimension;
no polynomial-ring rank is substituted for quotient-field rank.

All phases declare two-sided models on this fixed block family. Coefficients and
denominators remain bounded; the cubic counts below do not claim a model
for arbitrary dense number-field matrices and are not fitted to timings.

The scientific ladder is 128–1024. The retained 4–64 ladder does not resolve
the cubic model: repeated fixed-degree inversions add a substantial quadratic
term before the cubic scans dominate. This range extension preserves the
model and fixture. Verification still uses dimension four. The 600-second
child cap is operational and includes expensive preparation, not a performance
budget or an excuse to discard completed shared-host samples. -/

namespace Quotient

private def defining : List Int := [-2, 0, 1]

structure Input where
  dim : Nat
  rows : List (List (List Int))
  finish : Unit → Except String Nat
  preparedHash : UInt64
  witness : PolyWitness

instance : Inhabited Input where
  default := ⟨0, [], fun _ => .error "unprepared input", 0,
    ⟨0, 2, 1, [], [], [], [], 1, [], []⟩⟩

instance : Hashable Input where
  hash input := hash (input.dim, input.rows, input.preparedHash, input.witness.lowerQuot)

/-- Full or duplicated-row block matrices. The deficient dimension is a
multiple of four, so its pivot block also consists of complete 2×2 blocks. -/
def prep (deficient : Bool) (param : Nat) : Input :=
  let n := max 4 (4 * (param / 4))
  let r := if deficient then n / 2 else n
  let rows := (List.range n).map fun i => (List.range n).map fun j =>
    let i := i % r
    if i == j then [0, 1] else if i / 2 == j / 2 then [1] else []
  match PolyWitness.prepare n n defining rows with
  | .error error => panic! s!"quotient fixture preparation: {error}"
  | .ok data =>
    -- Reuse the prepared rational data when finding the first valid modulus.
    -- The timed public producer still performs its own complete preparation.
    match witnessModuli.findSome? (fun M => (PolyWitness.finish n n defining rows data M).toOption) with
    | none => panic! "quotient fixture: no valid witness modulus"
    | some witness =>
      if witness.rank == r && checkRankPoly n n defining rows witness then
        let fingerprint := hash (data.rank, data.vt.map (·.map fun f => f.toArray),
          data.lowerQuot.map (·.map fun f => f.toArray), data.z, data.upperQuot)
        let finish := fun _ => (PolyWitness.finish n n defining rows data witness.modulus).map (·.rank)
        ⟨n, rows, finish, fingerprint, witness⟩
      else panic! s!"quotient fixture: expected rank {r}, got {witness.rank}"

def runProduce (input : Input) : Nat :=
  match PolyWitness.produce input.dim input.dim defining input.rows with
  | .ok w => w.rank
  | .error error => panic! s!"quotient producer: {error}"

def runPrepare (input : Input) : Nat × List (List (Array Rat)) × List (List (Array Rat)) × Int × List (List (List Int)) × List (List (List Int)) :=
  match PolyWitness.prepare input.dim input.dim defining input.rows with
  | .ok d => (d.rank, d.vt.map (·.map fun f => f.toArray),
      d.lowerQuot.map (·.map fun f => f.toArray), d.denom, d.z, d.upperQuot)
  | .error error => panic! s!"quotient preparation: {error}"

def runFinish (input : Input) : Nat :=
  match input.finish () with
  | .ok rank => rank
  | .error error => panic! s!"quotient modular witness: {error}"

def runCheck (input : Input) : Bool :=
  if checkRankPoly input.dim input.dim defining input.rows input.witness then true
  else panic! "quotient checker rejected its prepared witness"

def prepFull := prep false
def prepDeficient := prep true

def produceFull := runProduce
/- Two-sided cost model, cubic: bounded-coefficient prefix inverses sum Θ(k²) over k,
and lower-quotient dots traverse Θ(n³) entries. -/
setup_benchmark produceFull n => n * n * n
  with prep := prepFull
  where {
    paramFloor := 128
    paramCeiling := 1024
    paramSchedule := .custom #[128, 192, 256, 384, 512, 768, 1024]
    targetInnerNanos := 2000000000
    outerTrials := 6
    maxSecondsPerCall := 600.0
  }

def prepareFull := runPrepare
/- Two-sided cost model, cubic: bounded-coefficient prefix inverses sum Θ(k²) over k,
and lower-quotient dots traverse Θ(n³) entries. -/
setup_benchmark prepareFull n => n * n * n
  with prep := prepFull
  where {
    paramFloor := 128
    paramCeiling := 1024
    paramSchedule := .custom #[128, 192, 256, 384, 512, 768, 1024]
    targetInnerNanos := 2000000000
    outerTrials := 6
    maxSecondsPerCall := 600.0
  }

def finishFull := runFinish
/- Two-sided cost model, cubic: Θ(n²) lower/upper relation dots each traverse Θ(n)
fixed-degree entries; modular construction adds only O(n²). -/
setup_benchmark finishFull n => n * n * n
  with prep := prepFull
  where {
    paramFloor := 128
    paramCeiling := 1024
    paramSchedule := .custom #[128, 192, 256, 384, 512, 768, 1024]
    targetInnerNanos := 2000000000
    outerTrials := 6
    maxSecondsPerCall := 600.0
  }

def checkFull := runCheck
/- Two-sided cost model, cubic: Θ(n²) checked lower/upper relation dots each traverse
Θ(n) fixed-degree, bounded-coefficient entries. -/
setup_benchmark checkFull n => n * n * n
  with prep := prepFull
  where {
    paramFloor := 128
    paramCeiling := 1024
    paramSchedule := .custom #[128, 192, 256, 384, 512, 768, 1024]
    targetInnerNanos := 2000000000
    outerTrials := 6
    maxSecondsPerCall := 600.0
  }

def produceDeficient := runProduce
/- Two-sided cost model, cubic: bounded-coefficient prefix inverses sum Θ(k²) over k,
and lower-quotient dots traverse Θ(n³) entries. -/
setup_benchmark produceDeficient n => n * n * n
  with prep := prepDeficient
  where {
    paramFloor := 128
    paramCeiling := 1024
    paramSchedule := .custom #[128, 192, 256, 384, 512, 768, 1024]
    targetInnerNanos := 2000000000
    outerTrials := 6
    maxSecondsPerCall := 600.0
  }

def prepareDeficient := runPrepare
/- Two-sided cost model, cubic: bounded-coefficient prefix inverses sum Θ(k²) over k,
and lower-quotient dots traverse Θ(n³) entries. -/
setup_benchmark prepareDeficient n => n * n * n
  with prep := prepDeficient
  where {
    paramFloor := 128
    paramCeiling := 1024
    paramSchedule := .custom #[128, 192, 256, 384, 512, 768, 1024]
    targetInnerNanos := 2000000000
    outerTrials := 6
    maxSecondsPerCall := 600.0
  }

def finishDeficient := runFinish
/- Two-sided cost model, cubic: Θ(n²) lower/upper relation dots each traverse Θ(n)
fixed-degree entries; modular construction adds only O(n²). -/
setup_benchmark finishDeficient n => n * n * n
  with prep := prepDeficient
  where {
    paramFloor := 128
    paramCeiling := 1024
    paramSchedule := .custom #[128, 192, 256, 384, 512, 768, 1024]
    targetInnerNanos := 2000000000
    outerTrials := 6
    maxSecondsPerCall := 600.0
  }

def checkDeficient := runCheck
/- Two-sided cost model, cubic: Θ(n²) checked lower/upper relation dots each traverse
Θ(n) fixed-degree, bounded-coefficient entries. -/
setup_benchmark checkDeficient n => n * n * n
  with prep := prepDeficient
  where {
    paramFloor := 128
    paramCeiling := 1024
    paramSchedule := .custom #[128, 192, 256, 384, 512, 768, 1024]
    targetInnerNanos := 2000000000
    outerTrials := 6
    maxSecondsPerCall := 600.0
  }

/-- Fixed-degree sparse rows with two nonzero entries and a bounded dot product. -/
def prepDot (n : Nat) : List (List Int) :=
  [[0, 1], [1]] ++ List.replicate (max 2 n - 2) []

def dot (row : List (List Int)) : Bool :=
  if PolyWitness.dot row row == [1, 0, 1] then true
  else panic! "polynomial dot product disagrees with its exact fixture"

/- Two-sided cost model, linear: the two nonzero products and all accumulator coefficients have
fixed degree and bounded size. Both list traversals inspect Θ(n) entries;
each step does bounded coefficient work, including the zero entries.
Thus time is Θ(n), independently of measurements. This isolates the dominant
native primitive observed inside the quotient checker. -/
setup_benchmark dot n => n
  with prep := prepDot
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 1536, 2048, 3072, 4096, 6144, 8192, 12288, 16384]
    targetInnerNanos := 2000000000
    outerTrials := 6
    maxSecondsPerCall := 60.0
  }

def prepDotArray (n : Nat) : Array (List Int) := (prepDot n).toArray

def dotArray (row : Array (List Int)) : Bool :=
  if PolyWitness.dotArray row row == [1, 0, 1] then true
  else panic! "array polynomial dot product disagrees with its exact fixture"

/- Two-sided cost model: the same bounded-degree and bounded-coefficient fixture as `dot`.
The array loop visits every entry once with constant-time indexed access and
bounded coefficient work. Thus its independently derived time is Θ(n).
The native lower-triangle checker converts each certificate row once, inside
checking, then reuses this primitive; conversion is O(n²) on the block family
and leaves the checker's existing Θ(n³) model unchanged. -/
setup_benchmark dotArray n => n
  with prep := prepDotArray
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 1536, 2048, 3072, 4096, 6144, 8192, 12288, 16384]
    targetInnerNanos := 2000000000
    outerTrials := 6
    maxSecondsPerCall := 60.0
  }

/-- Validate the two structural outputs against prefix selection and ordinary
list transposition before measuring either public selection helper. -/
def prepSelect (deficient : Bool) (n : Nat) : Input :=
  let input := prep deficient n
  let w := input.witness
  let pivotRows := input.rows.take w.rank
  let transposed := pivotRows.foldr (fun row cols => List.zipWith List.cons row cols)
    (List.replicate input.dim [])
  if w.rows == List.range w.rank && w.cols == List.range w.rank &&
      PolyWitness.block input.rows w.rows w.cols == pivotRows.map (·.take w.rank) &&
      PolyWitness.pivotCols input.dim input.rows w.rows == transposed then input
  else panic! "quotient selection disagrees with the canonical block fixture"

def prepSelectFull := prepSelect false
def prepSelectDeficient := prepSelect true

def blockFull (input : Input) : List (List (List Int)) :=
  PolyWitness.block input.rows input.witness.rows input.witness.cols

/- Two-sided cost model: r² selected entries each perform linked-list lookups of mean
length Θ(n), with r=n. Allocation is O(n²); total work is Θ(n³). -/
setup_benchmark blockFull n => n * n * n
  with prep := prepSelectFull
  where {
    paramFloor := 128
    paramCeiling := 1024
    paramSchedule := .custom #[128, 192, 256, 384, 512, 768, 1024]
    targetInnerNanos := 2000000000
    outerTrials := 6
    maxSecondsPerCall := 600.0
  }

def blockDeficient := blockFull
/- Two-sided cost model: r=n/2, so r² entries with mean Θ(n) list lookups still give
Θ(n³) work, with O(n²) output allocation and bounded polynomial entries. -/
setup_benchmark blockDeficient n => n * n * n
  with prep := prepSelectDeficient
  where {
    paramFloor := 128
    paramCeiling := 1024
    paramSchedule := .custom #[128, 192, 256, 384, 512, 768, 1024]
    targetInnerNanos := 2000000000
    outerTrials := 6
    maxSecondsPerCall := 600.0
  }

def pivotColsFull (input : Input) : List (List (List Int)) :=
  PolyWitness.pivotCols input.dim input.rows input.witness.rows

/- Two-sided cost model: n*r entries with r=n each scan an input row index and a column
index, both of mean Θ(n) length. Output allocation O(n²) is lower order. -/
setup_benchmark pivotColsFull n => n * n * n
  with prep := prepSelectFull
  where {
    paramFloor := 128
    paramCeiling := 1024
    paramSchedule := .custom #[128, 192, 256, 384, 512, 768, 1024]
    targetInnerNanos := 2000000000
    outerTrials := 6
    maxSecondsPerCall := 600.0
  }

def pivotColsDeficient := pivotColsFull
/- Two-sided cost model, cubic: n*r entries with r=n/2, each with mean Θ(n) list lookup cost,
give Θ(n³) work. The fixture keeps degrees and coefficients bounded. -/
setup_benchmark pivotColsDeficient n => n * n * n
  with prep := prepSelectDeficient
  where {
    paramFloor := 128
    paramCeiling := 1024
    paramSchedule := .custom #[128, 192, 256, 384, 512, 768, 1024]
    targetInnerNanos := 2000000000
    outerTrials := 6
    maxSecondsPerCall := 600.0
  }

end Quotient

end Hex.RankBench
