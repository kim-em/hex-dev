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
/- Independent mode-1 model for these fixed quadratic blocks: coefficients
and denominators stay bounded. Elimination on a k×2k block matrix scans
Θ(k²) cells, and preparing all prefix inverses sums this to Θ(n³).
The lower-quotient and native verification dot products traverse Θ(n³)
entries (including zeros). Fixed-modulus reduction is O(n²); duplicated
rows add Θ(n³) upper-relation work. Thus each registered phase is Θ(n³).
No claim about generic dense number-field matrices is made. -/
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
/- Independent mode-1 model for these fixed quadratic blocks: coefficients
and denominators stay bounded. Elimination on a k×2k block matrix scans
Θ(k²) cells, and preparing all prefix inverses sums this to Θ(n³).
The lower-quotient and native verification dot products traverse Θ(n³)
entries (including zeros). Fixed-modulus reduction is O(n²); duplicated
rows add Θ(n³) upper-relation work. Thus each registered phase is Θ(n³).
No claim about generic dense number-field matrices is made. -/
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
/- Independent mode-1 model for these fixed quadratic blocks: coefficients
and denominators stay bounded. Elimination on a k×2k block matrix scans
Θ(k²) cells, and preparing all prefix inverses sums this to Θ(n³).
The lower-quotient and native verification dot products traverse Θ(n³)
entries (including zeros). Fixed-modulus reduction is O(n²); duplicated
rows add Θ(n³) upper-relation work. Thus each registered phase is Θ(n³).
No claim about generic dense number-field matrices is made. -/
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
/- Independent mode-1 model for these fixed quadratic blocks: coefficients
and denominators stay bounded. Elimination on a k×2k block matrix scans
Θ(k²) cells, and preparing all prefix inverses sums this to Θ(n³).
The lower-quotient and native verification dot products traverse Θ(n³)
entries (including zeros). Fixed-modulus reduction is O(n²); duplicated
rows add Θ(n³) upper-relation work. Thus each registered phase is Θ(n³).
No claim about generic dense number-field matrices is made. -/
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
/- Independent mode-1 model for these fixed quadratic blocks: coefficients
and denominators stay bounded. Elimination on a k×2k block matrix scans
Θ(k²) cells, and preparing all prefix inverses sums this to Θ(n³).
The lower-quotient and native verification dot products traverse Θ(n³)
entries (including zeros). Fixed-modulus reduction is O(n²); duplicated
rows add Θ(n³) upper-relation work. Thus each registered phase is Θ(n³).
No claim about generic dense number-field matrices is made. -/
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
/- Independent mode-1 model for these fixed quadratic blocks: coefficients
and denominators stay bounded. Elimination on a k×2k block matrix scans
Θ(k²) cells, and preparing all prefix inverses sums this to Θ(n³).
The lower-quotient and native verification dot products traverse Θ(n³)
entries (including zeros). Fixed-modulus reduction is O(n²); duplicated
rows add Θ(n³) upper-relation work. Thus each registered phase is Θ(n³).
No claim about generic dense number-field matrices is made. -/
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
/- Independent mode-1 model for these fixed quadratic blocks: coefficients
and denominators stay bounded. Elimination on a k×2k block matrix scans
Θ(k²) cells, and preparing all prefix inverses sums this to Θ(n³).
The lower-quotient and native verification dot products traverse Θ(n³)
entries (including zeros). Fixed-modulus reduction is O(n²); duplicated
rows add Θ(n³) upper-relation work. Thus each registered phase is Θ(n³).
No claim about generic dense number-field matrices is made. -/
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
/- Independent mode-1 model for these fixed quadratic blocks: coefficients
and denominators stay bounded. Elimination on a k×2k block matrix scans
Θ(k²) cells, and preparing all prefix inverses sums this to Θ(n³).
The lower-quotient and native verification dot products traverse Θ(n³)
entries (including zeros). Fixed-modulus reduction is O(n²); duplicated
rows add Θ(n³) upper-relation work. Thus each registered phase is Θ(n³).
No claim about generic dense number-field matrices is made. -/
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

end Quotient

end Hex.RankBench
