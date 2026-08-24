/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexSparsePoly
import HexModArith
import HexPolyFp
import LeanBench

/-!
Native benchmark registrations for `hex-sparse-poly`, covering the six
SPEC input families:

* **sparse-arithmetic** — `add` and `mul` of `t`-term inputs at degrees
  `10^3` and `10^6`; the required property is that time depends on `t`
  and not on the degree, which the paired ladders expose.
* **sparse-multiplication** — the three candidate `mul` implementations
  (sort-and-combine, `ExtTreeMap` accumulation, Johnson heap merge) on
  low-collision (spread exponents; pairwise sums almost all distinct)
  and high-collision (arithmetic-progression exponents; `t²` pairwise
  sums land on `2t − 1` keys) inputs. These ladders select the
  `@[csimp]` implementation.
* **crossover** — `add`, `mul`, and `eval` against `DensePoly` at
  matched degree with the term count swept toward the degree, locating
  the density ratio at which dense wins, one operation at a time.
* **evaluation** — gap Horner against dense Horner over `ZMod64 7`
  (constant-size coefficients keep the asymptotics visible).
* **substitution-power** — `substPow` on the `Φ_3` shape with the power
  swept: the sparse route must be flat in `k` while the dense route is
  linear in the output degree.
* **convert-gcd** — `gcd` and `divMod` through the conversions on the
  sparse-remainder `x^n − 1, x^m − 1` pair and on a generic sparse
  pair, with the conversion share (`toDense` + `ofDense` alone)
  registered separately.

Compare groups:

* `compare runMulSortLow runMulTreeLow runMulHeapLow` and
  `compare runMulSortHigh runMulTreeHigh runMulHeapHigh` join the three
  candidate multiplications on result hashes over the shared prepared
  inputs; a divergence is a conformance failure.

Timed targets return structural hashes of the canonical outputs, so
result traversal stays within the declared operation cost and gives
LeanBench a conformance signal. Each child batch autotunes to about
200 ms; `signalFloorMultiplier := 1.0` keeps the autotuned in-process
measurements, as in the sibling bench modules.
-/

namespace Hex.SparsePolyBench

open Hex
open Hex.SparsePoly

instance : ZMod64.Bounds 7 := ⟨by decide, by decide⟩

abbrev PZ := SparsePoly Int
abbrev P7 := SparsePoly (ZMod64 7)

/-- Stable structural hash of a term array. -/
def checksumTerms (ts : Array (Nat × Int)) : UInt64 :=
  ts.foldl (fun acc t => mixHash (mixHash acc (hash t.1)) (hash t.2)) 0

/-- Stable structural hash of a canonical sparse polynomial. -/
def checksum (s : PZ) : UInt64 :=
  checksumTerms s.terms

def checksumMod (s : P7) : UInt64 :=
  s.terms.foldl
    (fun acc t => mixHash (mixHash acc (hash t.1)) (hash (ZMod64.toNat t.2)))
    0

def checksumDense (p : DensePoly Int) : UInt64 :=
  p.coeffs.foldl (fun acc c => mixHash acc (hash c)) 0

def checksumDenseMod (p : DensePoly (ZMod64 7)) : UInt64 :=
  p.coeffs.foldl (fun acc c => mixHash acc (hash (ZMod64.toNat c))) 0

instance : Hashable PZ where
  hash := checksum

instance : Hashable P7 where
  hash := checksumMod

instance : Hashable (SparsePoly Rat) where
  hash s := s.terms.foldl
    (fun acc t => mixHash (mixHash acc (hash t.1)) (hash t.2)) 0

instance : Hashable (DensePoly Int) where
  hash := checksumDense

instance : Hashable (DensePoly (ZMod64 7)) where
  hash := checksumDenseMod

/-- Deterministic nonzero coefficient stream. -/
def coeffAt (salt i : Nat) : Int :=
  let r := (salt * 1103515245 + i * 101 + 12345) % 17
  Int.ofNat (r + 1) - 9 + (if r = 8 then 1 else 0)

/-- `t` terms with exponents spread evenly up to `deg` (low collision:
pairwise sums of two spread supports are almost all distinct). -/
def spreadPoly (t deg salt : Nat) : PZ :=
  ofTerms ((Array.range t).map fun i =>
    (i * (deg / (t + 1)) + i + salt % 3, coeffAt salt i))

/-- `t` terms at pseudo-random exponents below `10^6` (genuinely low
collision: pairwise sums of two such supports are almost all
distinct — the evenly-spread generator would collide, since equal steps
make the sums coincide). -/
def scatterPoly (t salt : Nat) : PZ :=
  ofTerms ((Array.range t).map fun i =>
    ((i * 999983 + salt * 7919) % 1000003, coeffAt salt i))

/-- `t` terms in arithmetic progression (high collision: the `t²`
pairwise sums of two such supports land on `2t − 1` keys). -/
def apPoly (t step salt : Nat) : PZ :=
  ofTerms ((Array.range t).map fun i => (i * step, coeffAt salt i))

def spreadPolyMod (t deg salt : Nat) : P7 :=
  ofTerms ((Array.range t).map fun i =>
    (i * (deg / (t + 1)) + i, ZMod64.ofNat 7 ((salt + i * 3) % 6 + 1)))

/-! **The three candidate multiplications**

`runMulSort*` is the library `mul` (the pairwise product canonicalised
by `ofTerms`'s stable sort-and-combine). The other two candidates
produce the same canonical term array by different algorithms; the
compare groups join all three on hashes. -/

/-- Candidate 2: accumulate the pairwise products in an
`Std.ExtTreeMap Nat Int` and read the ordered nonzero entries. -/
def mulTreeTerms (s t : PZ) : Array (Nat × Int) := Id.run do
  let mut acc : Std.ExtTreeMap Nat Int compare := ∅
  for a in s.terms do
    for b in t.terms do
      let e := a.1 + b.1
      acc := acc.insert e ((acc.getD e 0) + a.2 * b.2)
  let mut out : Array (Nat × Int) := #[]
  for (e, c) in acc do
    if c ≠ 0 then
      out := out.push (e, c)
  return out

/-- Binary min-heap on `(exponent, leftIndex, rightIndex)` keyed on the
exponent, for the Johnson merge. -/
private def siftDown (a : Array (Nat × Nat × Nat)) (i : Nat) :
    Nat → Array (Nat × Nat × Nat)
  | 0 => a
  | fuel + 1 =>
      let l := 2 * i + 1
      let r := 2 * i + 2
      let smallest :=
        if h : l < a.size then
          if (a[l]'h).1 < (a[i]!).1 then l else i
        else i
      let smallest :=
        if h : r < a.size then
          if (a[r]'h).1 < (a[smallest]!).1 then r else smallest
        else smallest
      if smallest ≠ i then
        siftDown (a.swapIfInBounds i smallest) smallest fuel
      else a

private def siftUp (a : Array (Nat × Nat × Nat)) (i : Nat) :
    Array (Nat × Nat × Nat) :=
  if i = 0 then a
  else
    let parent := (i - 1) / 2
    if (a[i]!).1 < (a[parent]!).1 then
      siftUp (a.swapIfInBounds i parent) parent
    else a
termination_by i

private def heapPush (a : Array (Nat × Nat × Nat)) (x : Nat × Nat × Nat) :
    Array (Nat × Nat × Nat) :=
  siftUp (a.push x) a.size

private def heapPop (a : Array (Nat × Nat × Nat)) :
    Option ((Nat × Nat × Nat) × Array (Nat × Nat × Nat)) :=
  if a.isEmpty then none
  else
    let top := a[0]!
    let a := a.swapIfInBounds 0 (a.size - 1)
    some (top, siftDown a.pop 0 a.size)

/-- Candidate 3: Johnson's heap merge. One stream per term of the
smaller operand, each walking the larger operand in exponent order; a
heap of `min(s, t)` current heads pops the output in sorted order. -/
def mulHeapTerms (s t : PZ) : Array (Nat × Int) := Id.run do
  let (small, big) :=
    if s.numTerms ≤ t.numTerms then (s.terms, t.terms)
    else (t.terms, s.terms)
  if small.isEmpty || big.isEmpty then
    return #[]
  let mut heap : Array (Nat × Nat × Nat) := #[]
  for hi : i in [0:small.size] do
    heap := heapPush heap ((small[i]'hi.upper).1 + (big[0]!).1, i, 0)
  let mut out : Array (Nat × Int) := #[]
  let mut currentExp : Nat := 0
  let mut currentCoeff : Int := 0
  let mut started := false
  let fuel := small.size * big.size + 1
  for _ in [0:fuel] do
    match heapPop heap with
    | none => break
    | some ((e, i, j), rest) =>
        let c := (small[i]!).2 * (big[j]!).2
        if started && e = currentExp then
          currentCoeff := currentCoeff + c
        else
          if started && currentCoeff ≠ 0 then
            out := out.push (currentExp, currentCoeff)
          currentExp := e
          currentCoeff := c
          started := true
        heap :=
          if j + 1 < big.size then
            heapPush rest ((small[i]!).1 + (big[j + 1]!).1, i, j + 1)
          else rest
  if started && currentCoeff ≠ 0 then
    out := out.push (currentExp, currentCoeff)
  return out

/-! **sparse-arithmetic** -/

structure ArithInput where
  leftDeg3 : PZ
  rightDeg3 : PZ
  leftDeg6 : PZ
  rightDeg6 : PZ
  deriving Hashable

def prepArith (t : Nat) : ArithInput :=
  { leftDeg3 := spreadPoly t 1000 3
    rightDeg3 := spreadPoly t 1000 5
    leftDeg6 := spreadPoly t 1000000 7
    rightDeg6 := spreadPoly t 1000000 11 }

def runAddDeg3 (input : ArithInput) : UInt64 :=
  checksum (input.leftDeg3 + input.rightDeg3)

def runAddDeg6 (input : ArithInput) : UInt64 :=
  checksum (input.leftDeg6 + input.rightDeg6)

def runMulDeg3 (input : ArithInput) : UInt64 :=
  checksum (input.leftDeg3 * input.rightDeg3)

def runMulDeg6 (input : ArithInput) : UInt64 :=
  checksum (input.leftDeg6 * input.rightDeg6)

/-! **sparse-multiplication (implementation selection)** -/

structure MulSelectInput where
  lowLeft : PZ
  lowRight : PZ
  highLeft : PZ
  highRight : PZ
  deriving Hashable

def prepMulSelect (t : Nat) : MulSelectInput :=
  { lowLeft := scatterPoly t 13
    lowRight := scatterPoly t 17
    highLeft := apPoly t 64 19
    highRight := apPoly t 64 23 }

def runMulSortLow (input : MulSelectInput) : UInt64 :=
  checksum (input.lowLeft * input.lowRight)

def runMulTreeLow (input : MulSelectInput) : UInt64 :=
  checksumTerms (mulTreeTerms input.lowLeft input.lowRight)

def runMulHeapLow (input : MulSelectInput) : UInt64 :=
  checksumTerms (mulHeapTerms input.lowLeft input.lowRight)

def runMulSortHigh (input : MulSelectInput) : UInt64 :=
  checksum (input.highLeft * input.highRight)

def runMulTreeHigh (input : MulSelectInput) : UInt64 :=
  checksumTerms (mulTreeTerms input.highLeft input.highRight)

def runMulHeapHigh (input : MulSelectInput) : UInt64 :=
  checksumTerms (mulHeapTerms input.highLeft input.highRight)

/-! **crossover** -/

structure CrossoverInput where
  sparseLeft : PZ
  sparseRight : PZ
  denseLeft : DensePoly Int
  denseRight : DensePoly Int
  deriving Hashable

/-- Fixed degree `4096`; the term count sweeps toward it. -/
def prepCrossoverAdd (t : Nat) : CrossoverInput :=
  let l := spreadPoly t 4096 29
  let r := spreadPoly t 4096 31
  { sparseLeft := l, sparseRight := r
    denseLeft := l.toDense, denseRight := r.toDense }

/-- Fixed degree `1024` for the quadratic dense product. -/
def prepCrossoverMul (t : Nat) : CrossoverInput :=
  let l := spreadPoly t 1024 37
  let r := spreadPoly t 1024 41
  { sparseLeft := l, sparseRight := r
    denseLeft := l.toDense, denseRight := r.toDense }

def runCrossAddSparse (input : CrossoverInput) : UInt64 :=
  checksum (input.sparseLeft + input.sparseRight)

def runCrossAddDense (input : CrossoverInput) : UInt64 :=
  checksumDense (input.denseLeft + input.denseRight)

def runCrossMulSparse (input : CrossoverInput) : UInt64 :=
  checksum (input.sparseLeft * input.sparseRight)

def runCrossMulDense (input : CrossoverInput) : UInt64 :=
  checksumDense (input.denseLeft * input.denseRight)

/-! **evaluation** -/

instance : Hashable (ZMod64 7) where
  hash a := hash (ZMod64.toNat a)

structure EvalInput where
  sparse : P7
  dense : DensePoly (ZMod64 7)
  point : ZMod64 7
  deriving Hashable

def prepEval (t : Nat) : EvalInput :=
  let s := spreadPolyMod t 65536 43
  { sparse := s, dense := s.toDense, point := ZMod64.ofNat 7 3 }

def runEvalGapSparse (input : EvalInput) : UInt64 :=
  hash (ZMod64.toNat (input.sparse.eval input.point))

def runEvalDense (input : EvalInput) : UInt64 :=
  hash (ZMod64.toNat (input.dense.eval input.point))

/-! **substitution-power** -/

/-- `Φ_3 = 1 + x + x²`. -/
def phi3 : PZ := ofTerms #[(0, 1), (1, 1), (2, 1)]

structure SubstPowInput where
  k : Nat
  deriving Hashable

def prepSubstPow (k : Nat) : SubstPowInput :=
  { k := k }

def runSubstPowSparse (input : SubstPowInput) : UInt64 :=
  checksum (phi3.substPow input.k)

/-- The dense route to the same output: materialise the `2k + 1`
coefficients of `Φ_3(x^k)` as the cyclotomic adapter's dense
construction would. -/
def runSubstPowDense (input : SubstPowInput) : UInt64 :=
  checksumDense (phi3.substPow input.k).toDense

/-! **convert-gcd** -/

structure ConvertGcdInput where
  binomLeft : P7
  binomRight : P7
  genericLeft : P7
  genericRight : P7
  deriving Hashable

/-- The two contrasting shapes over the field `ZMod64 7` (constant-size
coefficients keep time proportional to coefficient operations): the
`x^n − 1, x^m − 1` pair whose remainder sequence stays two-term, and a
generic sparse pair whose remainders fill in. -/
def prepConvertGcd (n : Nat) : ConvertGcdInput :=
  let one := ZMod64.ofNat 7 1
  let negOne := ZMod64.ofNat 7 6
  { binomLeft := ofTerms #[(0, negOne), (n, one)]
    binomRight := ofTerms #[(0, negOne), (n - 7, one)]
    genericLeft := ofTerms #[(0, negOne), (n, one)]
    genericRight := ofTerms #[(0, one), (1, one), (7, one)] }

def runConvertGcdBinomPair (input : ConvertGcdInput) : UInt64 :=
  checksumMod (gcd input.binomLeft input.binomRight)

def runConvertGcdGeneric (input : ConvertGcdInput) : UInt64 :=
  checksumMod (gcd input.genericLeft input.genericRight)

def runConvertDivModBinomPair (input : ConvertGcdInput) : UInt64 :=
  let qr := divMod input.binomLeft input.binomRight
  mixHash (checksumMod qr.1) (checksumMod qr.2)

/-- The conversion share alone: `toDense` both inputs and `ofDense` one
of them back, with no dense algorithm in between. -/
def runGcdConversionShare (input : ConvertGcdInput) : UInt64 :=
  let l := input.binomLeft.toDense
  let r := input.binomRight.toDense
  mixHash (checksumMod (ofDense l)) (hash r.size)

/-! **Registrations** -/

/- Cost model: a linear merge of two `t`-term sorted arrays is `O(t)`
whatever the exponents; the degree-`10^6` twin ladder must match this
one, which is the family's required property. -/
setup_benchmark runAddDeg3 n => n
  with prep := prepArith
  where {
    paramSchedule := .custom #[2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: as `runAddDeg3`; only the exponent magnitudes differ, and
`Nat` exponents this size are still one word. -/
setup_benchmark runAddDeg6 n => n
  with prep := prepArith
  where {
    paramSchedule := .custom #[2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: the specification multiplication builds `t²` pairwise
products and sorts them: `O(t² log t²)` with low collision. -/
setup_benchmark runMulDeg3 n => n * n * Nat.log2 (n * n + 1)
  with prep := prepArith
  where {
    paramSchedule := .custom #[2, 4, 8, 16, 32, 64, 128, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: as `runMulDeg3`; the degree-`10^6` ladder must match. -/
setup_benchmark runMulDeg6 n => n * n * Nat.log2 (n * n + 1)
  with prep := prepArith
  where {
    paramSchedule := .custom #[2, 4, 8, 16, 32, 64, 128, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: sort-and-combine over `t²` products, low collision, so
the sort dominates at `O(t² log t²)`. -/
setup_benchmark runMulSortLow n => n * n * Nat.log2 (n * n + 1)
  with prep := prepMulSelect
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 384, 512]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: `t²` tree-map updates each `O(log t²)` into an output of
up to `t²` keys. -/
setup_benchmark runMulTreeLow n => n * n * Nat.log2 (n * n + 1)
  with prep := prepMulSelect
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 384, 512]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: Johnson's merge pops `t²` heap entries from a heap of
`min(s, t)` streams: `O(t² log t)`. -/
setup_benchmark runMulHeapLow n => n * n * Nat.log2 (n + 1)
  with prep := prepMulSelect
  where {
    paramSchedule := .custom #[2, 4, 8, 16, 32, 64, 128, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: the same sort over `t²` products; high collision shrinks
the output to `2t − 1` keys but not the product set. -/
setup_benchmark runMulSortHigh n => n * n * Nat.log2 (n * n + 1)
  with prep := prepMulSelect
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 384, 512]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: `t²` updates into a tree of only `2t − 1` keys:
`O(t² log t)`. -/
setup_benchmark runMulTreeHigh n => n * n * Nat.log2 (n + 1)
  with prep := prepMulSelect
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 384, 512]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: `t²` pops from a heap of `min(s, t)` streams:
`O(t² log t)`. -/
setup_benchmark runMulHeapHigh n => n * n * Nat.log2 (n + 1)
  with prep := prepMulSelect
  where {
    paramSchedule := .custom #[2, 4, 8, 16, 32, 64, 128, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: the sparse merge is `O(t)`; the paired dense ladder is
flat at the fixed degree, and the report reads the crossover off the
two curves. -/
setup_benchmark runCrossAddSparse n => n
  with prep := prepCrossoverAdd
  where {
    paramSchedule := .custom #[2, 8, 32, 128, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: dense addition walks `degree + 1 = 4097` coefficients
whatever `t`: constant in the swept parameter. -/
setup_benchmark runCrossAddDense n => 1
  with prep := prepCrossoverAdd
  where {
    paramSchedule := .custom #[2, 8, 32, 128, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: `t²` products with the `log` of the sort. -/
setup_benchmark runCrossMulSparse n => n * n * Nat.log2 (n * n + 1)
  with prep := prepCrossoverMul
  where {
    paramSchedule := .custom #[2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: the dense convolution is `O(deg²)` at the fixed degree
`1024`: constant in the swept parameter. -/
setup_benchmark runCrossMulDense n => 1
  with prep := prepCrossoverMul
  where {
    paramSchedule := .custom #[2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: gap Horner does `t` additions and `O(t log(deg/t + 1))`
multiplications; over the fixed degree the whole ladder is within the
`t · log` envelope. -/
setup_benchmark runEvalGapSparse n => n * Nat.log2 (65536 / (n + 1) + 2)
  with prep := prepEval
  where {
    paramSchedule := .custom #[2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: dense Horner multiplies once per coefficient slot at the
fixed degree `65536`: constant in the swept parameter. -/
setup_benchmark runEvalDense n => 1
  with prep := prepEval
  where {
    paramSchedule := .custom #[2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: `substPow` multiplies three exponents by `k` and touches
no coefficient: constant in `k` (up to one-word `Nat` products). A
regression here means the implementation started materialising the
intermediate degrees. -/
setup_benchmark runSubstPowSparse n => 1
  with prep := prepSubstPow
  where {
    paramSchedule := .custom #[2, 8, 32, 128, 512, 2048, 8192, 32768]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: the dense route materialises the output's `2k + 1`
coefficients (three writes into a `2k + 1` array): linear in `k`. -/
setup_benchmark runSubstPowDense n => n
  with prep := prepSubstPow
  where {
    paramSchedule := .custom #[512, 2048, 8192, 32768, 65536, 131072]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: the `x^n − 1, x^m − 1` remainder sequence stays two-term:
a constant number of divisions whose quotients have bounded degree, each
`O(n)` dense coefficient operations, plus the `O(n)` conversions. This
linear model is the family's whole point: it is the case a sparse
division algorithm would win enormously, and the conversion share below
is the number that says what the convert route pays. -/
setup_benchmark runConvertGcdBinomPair n => n
  with prep := prepConvertGcd
  where {
    paramSchedule := .custom #[64, 128, 256, 384, 512, 768, 1024]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: dividing `x^n − 1` by the fixed degree-7 generic divisor
produces a quotient of degree `n − 7` with a bounded number of
coefficient updates per step, and the remaining remainder sequence has
bounded degrees: `O(n)` coefficient operations plus the `O(n)`
conversions. Over the field `ZMod64 7` each coefficient operation is
`O(1)`, so time tracks the model. -/
setup_benchmark runConvertGcdGeneric n => n
  with prep := prepConvertGcd
  where {
    paramSchedule := .custom #[64, 128, 256, 384, 512, 768, 1024]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: one long division of `x^n − 1` by `x^(n−7) − 1`:
`O(n)` dense coefficient operations plus the conversions. -/
setup_benchmark runConvertDivModBinomPair n => n
  with prep := prepConvertGcd
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: `toDense` allocates and writes `n + 1` coefficients and
`ofDense` walks them back: `O(n)`, the conversion share of every
convert-gcd number. -/
setup_benchmark runGcdConversionShare n => n
  with prep := prepConvertGcd
  where {
    paramSchedule := .custom #[256, 512, 1024, 2048, 4096, 8192]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

end Hex.SparsePolyBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
