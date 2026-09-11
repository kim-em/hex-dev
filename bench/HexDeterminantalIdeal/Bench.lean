/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexDeterminantalIdeal
import LeanBench

/-!
Benchmark registrations for `hex-determinantal-ideal`.

`minors r A` enumerates `n.choose r * m.choose r` selected submatrices and
takes the Leibniz determinant of each, so the declared cost model is
`n.choose r ^ 2 * r! * r` for a square `n × n` matrix, matching
`SPEC/Libraries/hex-determinantal-ideal.md §"Complexity"`. The parameter is the
minor size `r`, not the dimension: the shape of the curve in `r` at fixed `n`
is what the SPEC's two input families are for. `binomial` and `factorial` below
spell that model out as computable `Nat → Nat` functions (`Hex.Nat.choose` is
`noncomputable`, so it cannot serve as a bench cost model).

Scientific registrations:

* `runMinors4`, `runMinors5`, `runMinors6`: the `dense-int-minors` family,
  square `Matrix Int n n` for `n ∈ {4, 5, 6}` with small deterministic
  pseudo-random entries, every `r` from `1` to `n`. Integer operations cost
  about the same at every `r` at these sizes, so the family isolates the
  enumeration.
* `runSymbolicMinors`: the `symbolic-2var` family, a `4 × 4` matrix over
  `MvPoly 2 Int Mono.grlex` whose entries are deterministic linear forms
  `a + b * x₀ + c * x₁`, for `r ∈ {2, 3, 4}`. The enumeration is the same; each
  ring operation is now a polynomial product whose cost grows with the
  supports, so this curve is expected to rise faster than the declared count.

Matrix construction is hoisted into `prep`, so the timed region is the minor
enumeration alone. Each target folds the resulting list into a structural hash,
which forces every minor and gives LeanBench a conformance signal.

Entries come from a fixed multiply-xorshift hash of the coordinate, so the
inputs are identical on every host and no randomness is drawn at run time.

The SPEC classifies SymPy, the same `combinations` and `det` loop the
conformance oracle runs, as an `informational` comparator, so it is not a
required Phase 4 check. It is not registered here: the comparator would run through
`scripts/oracle/pari_bench_driver.py`, and its `phase4.comparators` entry lands
with this library's `libraries.yml` record.

`signalFloorMultiplier := 1.0` keeps the small-`r` rungs: a `1 × 1` or `2 × 2`
minor sweep finishes well inside the executable-spawn floor, and discarding
those rungs would leave a ladder too narrow to fit.
-/

namespace Hex.DeterminantalIdealBench

/-! # Declared cost model -/

/-- `r!`, the number of Leibniz terms in one `r × r` determinant. -/
def factorial : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factorial k

/-- `n.choose k` by the Pascal recursion. A computable stand-in for the
`noncomputable` `Hex.Nat.choose`, so the cost model evaluates. -/
def binomial : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binomial n k + binomial n (k + 1)

/-- Ring-operation count of `minors r A` for a square `n × n` matrix: one
determinant per pair of strictly increasing `r`-tuples, each an `r!`-term
Leibniz sum of `r`-fold products. -/
def minorsCost (n r : Nat) : Nat :=
  binomial n r ^ 2 * factorial r * r

/-! # Deterministic entries -/

/-- One round of a 32-bit multiply-xorshift hash. The bench inputs are fixed at
compile time; nothing is drawn from a source of randomness at run time. The
multipliers are odd, so residues modulo the small moduli used below are not
degenerate. -/
def mix (x : Nat) : Nat :=
  let y := (x * 2654435761) % 4294967296
  let z := ((y ^^^ (y >>> 15)) * 2246822519) % 4294967296
  z ^^^ (z >>> 13)

/-- A deterministic pseudo-random `Nat` for the coordinate `(salt, row, col)`,
mixed through two hash rounds so neighbouring coordinates do not correlate. -/
def draw (salt row col : Nat) : Nat :=
  mix (mix (8191 * salt + 97 * row + col + 1) + salt)

/-- A deterministic small integer entry in `[-9, 9]`. Small entries keep the
intermediates inside machine words, so the registration measures the
enumeration rather than arbitrary-precision growth. -/
def entry (salt row col : Nat) : Int :=
  Int.ofNat (draw salt row col % 19) - 9

/-! # `dense-int-minors` -/

/-- One prepared square integer matrix together with the minor size. -/
structure IntInput (n : Nat) where
  /-- The minor size, the benchmark parameter. -/
  r : Nat
  /-- The prepared matrix; construction stays out of the timed region. -/
  matrix : Matrix Int n n

private def matrixChecksum {n m : Nat} (M : Matrix Int n m) : UInt64 :=
  M.rows.toArray.foldl (fun acc row => mixHash acc (hash row.toArray)) (hash n)

instance {n : Nat} : Hashable (IntInput n) where
  hash input := mixHash (hash input.r) (matrixChecksum input.matrix)

/-- The deterministic `n × n` integer fixture. -/
def intMatrix (n : Nat) : Matrix Int n n :=
  Matrix.ofFn fun i j => entry n i.val j.val

/-- Per-parameter fixture for the `dense-int-minors` family at dimension 4. -/
def prepMinors4 (r : Nat) : IntInput 4 := { r, matrix := intMatrix 4 }

/-- Per-parameter fixture for the `dense-int-minors` family at dimension 5. -/
def prepMinors5 (r : Nat) : IntInput 5 := { r, matrix := intMatrix 5 }

/-- Per-parameter fixture for the `dense-int-minors` family at dimension 6. -/
def prepMinors6 (r : Nat) : IntInput 6 := { r, matrix := intMatrix 6 }

/-- Benchmark target: every `r × r` minor of the prepared `4 × 4` integer
matrix, folded into a checksum so each minor is forced. -/
def runMinors4 (input : IntInput 4) : UInt64 :=
  hash (Matrix.minors input.r input.matrix)

/-- Benchmark target: every `r × r` minor of the prepared `5 × 5` integer
matrix, folded into a checksum so each minor is forced. -/
def runMinors5 (input : IntInput 5) : UInt64 :=
  hash (Matrix.minors input.r input.matrix)

/-- Benchmark target: every `r × r` minor of the prepared `6 × 6` integer
matrix, folded into a checksum so each minor is forced. -/
def runMinors6 (input : IntInput 6) : UInt64 :=
  hash (Matrix.minors input.r input.matrix)

/-! `runMinors4` cost model: `minors r A` runs over the `4.choose r` strictly
increasing row selections and the `4.choose r` column selections, and each of
the `4.choose r ^ 2` pairs costs one Leibniz determinant, a signed sum of `r!`
products of `r` entries. The ring-operation count is therefore
`4.choose r ^ 2 * r! * r`, i.e. `minorsCost 4 r`. -/
setup_benchmark runMinors4 r => minorsCost 4 r with prep := prepMinors4
  where {
    paramFloor := 1
    paramCeiling := 4
    paramSchedule := .custom #[1, 2, 3, 4]
    maxSecondsPerCall := 1.0
    targetInnerNanos := 200000000
    verdictWarmupFraction := 0.0
    signalFloorMultiplier := 1.0
    outerTrials := 1
  }

/-! `runMinors5` cost model: the same derivation at dimension five. The
`5.choose r ^ 2` selected `r × r` submatrices each cost an `r!`-term Leibniz
sum of `r`-fold products, giving `minorsCost 5 r`. -/
setup_benchmark runMinors5 r => minorsCost 5 r with prep := prepMinors5
  where {
    paramFloor := 1
    paramCeiling := 5
    paramSchedule := .custom #[1, 2, 3, 4, 5]
    maxSecondsPerCall := 1.0
    targetInnerNanos := 200000000
    verdictWarmupFraction := 0.0
    signalFloorMultiplier := 1.0
    outerTrials := 1
  }

/-! `runMinors6` cost model: the same derivation at dimension six, where the
declared complexity peaks near `r = 4`: the binomial factor `6.choose r ^ 2`
falls after the middle while `r! * r` keeps rising. The count is
`minorsCost 6 r`. -/
setup_benchmark runMinors6 r => minorsCost 6 r with prep := prepMinors6
  where {
    paramFloor := 1
    paramCeiling := 6
    paramSchedule := .custom #[1, 2, 3, 4, 5, 6]
    maxSecondsPerCall := 1.5
    targetInnerNanos := 200000000
    verdictWarmupFraction := 0.0
    signalFloorMultiplier := 1.0
    outerTrials := 1
  }

/-! # `symbolic-2var` -/

/-- Bivariate integer polynomials in the graded lexicographic order. -/
abbrev Poly2 := MvPoly 2 Int Mono.grlex

instance : Hashable Poly2 where
  hash p :=
    p.termsList.foldl
      (fun acc term => mixHash (mixHash acc (hash term.1.toArray)) (hash term.2)) 0

/-- A deterministic linear form `a + b * x₀ + c * x₁`. The two leading
coefficients are drawn nonzero, so every entry is genuinely of degree one and
the family really does exercise polynomial arithmetic. -/
def linearForm (row col : Nat) : Poly2 :=
  let a := Int.ofNat (draw 11 row col % 9) - 4
  let b := Int.ofNat (draw 23 row col % 5) + 1
  let c := Int.ofNat (draw 47 row col % 5) + 1
  MvPoly.ofTerms [(Mono.zero, a), (Mono.unit 0, b), (Mono.unit 1, c)]

/-- One prepared `4 × 4` matrix of linear forms together with the minor size. -/
structure PolyInput where
  /-- The minor size, the benchmark parameter. -/
  r : Nat
  /-- The prepared symbolic matrix; construction stays out of the timed
  region. -/
  matrix : Matrix Poly2 4 4

instance : Hashable PolyInput where
  hash input :=
    mixHash (hash input.r) <|
      input.matrix.rows.toArray.foldl
        (fun acc row => mixHash acc (hash row.toArray)) 0

/-- The deterministic `4 × 4` matrix of bivariate linear forms. -/
def polyMatrix : Matrix Poly2 4 4 :=
  Matrix.ofFn fun i j => linearForm i.val j.val

/-- Per-parameter fixture for the `symbolic-2var` family. -/
def prepSymbolic (r : Nat) : PolyInput := { r, matrix := polyMatrix }

/-- Benchmark target: every `r × r` minor of the prepared symbolic matrix,
folded into a checksum over the canonical term lists so each minor is
forced. -/
def runSymbolicMinors (input : PolyInput) : UInt64 :=
  hash (Matrix.minors input.r input.matrix)

/-! `runSymbolicMinors` cost model: the enumeration is the one `runMinors4`
measures, so the ring-operation count is again `4.choose r ^ 2 * r! * r`, i.e.
`minorsCost 4 r`. The declared model counts ring operations, and over
`MvPoly 2 Int Mono.grlex` one operation is a polynomial product whose cost
grows with the supports (a product of `r` linear forms in two indeterminates
carries `Θ(r ^ 2)` terms), so this curve is expected to rise faster than the
count; that gap is what this family measures, not a departure to explain. -/
setup_benchmark runSymbolicMinors r => minorsCost 4 r with prep := prepSymbolic
  where {
    paramFloor := 2
    paramCeiling := 4
    paramSchedule := .custom #[2, 3, 4]
    maxSecondsPerCall := 1.5
    targetInnerNanos := 200000000
    verdictWarmupFraction := 0.0
    signalFloorMultiplier := 1.0
    outerTrials := 1
  }

end Hex.DeterminantalIdealBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
