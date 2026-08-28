/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.BenchOracle.Pari
import HexPolyFp.PrimeField
import HexPolySmith
import Lean.Data.Json
import LeanBench

/-!
Benchmark registrations for polynomial Smith form.

The scientific families separate matrix dimension from polynomial degree and
derive their boundary growth from known invariant-factor chains:

* `*Dimension` fixes base-factor degree at two (boundary degree four) and
  varies square dimension;
* `*Degree` fixes dimension at three and varies polynomial degree;
* `runChainSnf` uses known invariant-factor chains conjugated by deterministic
  unimodular matrices;
* `runRational*` uses nonintegral rational coefficients;
* `runDiagonalSnf` covers diagonal presentations through the public helper;
* `runSmallField` fixes dimension at three and varies degree over `ZMod64 2`,
  independently of evaluation-point supply.

The within-Lean comparison commands use shared prepared domains:

```
compare runDenseSnfDimension runDenseSnfDataDimension
compare runDenseSnfDegree runDenseSnfDataDegree
compare runDirectProductCert runEvaluationCert
```

SymPy `smith_normal_form` and PARI `matsnf` are fixed-rung informational
comparators over the same square `QQ[x]` and `F₂[x]` inputs. Five rungs cover
each declared input family. Both run through the persistent JSON-line service
in `scripts/oracle/pari_bench_driver.py`: one LeanBench child starts one driver
during `warmupFirstIter`, then reuses it throughout the auto-tuned inner-repeat
batch. `runComparatorOverhead` measures the framing and dispatch floor with no
matrix construction.

`growth` is an auxiliary CLI command that checks the derived boundary
polynomial degree and rational coefficient-bit counts (input, output, and
final transforms) for every declared input family; it is diagnostic evidence,
not a timing registration. The unrelated fixed comparator inputs retain the
original generic dense stress cases.
-/

namespace Hex.PolySmithBench

open Hex Hex.PolyMatrix
open Lean (Json JsonNumber)

instance : Hashable (DensePoly Rat) where
  hash p := hash p.toArray

private instance boundsTwo : ZMod64.Bounds 2 := ⟨by decide, by decide⟩

private theorem primeTwo : Hex.Nat.Prime 2 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · exact Or.inr rfl

private instance primeModTwo : ZMod64.PrimeModulus 2 :=
  ZMod64.primeModulusOfPrime primeTwo

instance : Hashable (DensePoly (ZMod64 2)) where
  hash p := hash (p.toArray.map (fun c => c.toNat))

/-- A dynamically sized square rational polynomial matrix. -/
structure Input where
  dimension : Nat
  entries : Array (Array (DensePoly Rat))
  deriving Hashable

instance : Inhabited Input := ⟨{ dimension := 0, entries := #[] }⟩

structure SmallInput where
  dimension : Nat
  entries : Array (Array (DensePoly (ZMod64 2)))
  deriving Hashable

instance : Inhabited SmallInput := ⟨{ dimension := 0, entries := #[] }⟩

structure SolveInput where
  matrix : Input
  rhs : Array (DensePoly Rat)
  deriving Hashable

instance : Inhabited SolveInput := ⟨{ matrix := default, rhs := #[] }⟩

/-- A prepared certificate removes Smith construction from the measured
checker path. Every matrix is stored as rows so the dynamic dimension remains
hashable by LeanBench. -/
structure CertInput where
  dimension : Nat
  matrix : Array (Array (DensePoly Rat))
  rank : Nat
  diag : Array (DensePoly Rat)
  left : Array (Array (DensePoly Rat))
  leftInv : Array (Array (DensePoly Rat))
  right : Array (Array (DensePoly Rat))
  rightInv : Array (Array (DensePoly Rat))
  intermediate : Array (Array (DensePoly Rat))
  deriving Hashable

instance : Inhabited CertInput :=
  ⟨{ dimension := 0, matrix := #[], rank := 0, diag := #[], left := #[],
     leftInv := #[], right := #[], rightInv := #[], intermediate := #[] }⟩

/-- Growth counters emitted by the boundary-value diagnostic path. -/
structure GrowthSample where
  degree : Nat
  coefficientBits : Nat
  deriving Repr, Hashable

private def coeff (salt i j k : Nat) : Rat :=
  let numerator : Int :=
    Int.ofNat (((salt + 11) * (i + 3) + (j + 5) * (k + 7)) % 17 + 1)
  if (i + j + k) % 2 = 0 then numerator else -numerator

private def densePoly (degree salt i j : Nat) : DensePoly Rat :=
  DensePoly.ofCoeffs <| Array.ofFn (n := degree + 1) fun k => coeff salt i j k

private def rationalPoly (degree salt i j : Nat) : DensePoly Rat :=
  DensePoly.ofCoeffs <| Array.ofFn (n := degree + 1) fun k =>
    coeff salt i j k / (Int.ofNat ((i + 2) * (j + 3) * (k.val + 5)) : Rat)

private def rowsOfMatrix {n m : Nat} (A : Matrix (DensePoly Rat) n m) :
    Array (Array (DensePoly Rat)) :=
  A.rows.toArray.map (·.toArray)

private def matrixOfRows (dimension : Nat)
    (rows : Array (Array (DensePoly Rat))) :
    Matrix (DensePoly Rat) dimension dimension :=
  Matrix.ofFn fun i j => (rows.getD i.val #[]).getD j.val 0

private def matrix (input : Input) :
    Matrix (DensePoly Rat) input.dimension input.dimension :=
  matrixOfRows input.dimension input.entries

private def upperUnit (n : Nat) : Matrix (DensePoly Rat) n n :=
  Matrix.ofFn fun i j => if i.val ≤ j.val then 1 else 0

private def lowerUnit (n : Nat) : Matrix (DensePoly Rat) n n :=
  Matrix.ofFn fun i j => if j.val ≤ i.val then 1 else 0

private def conjugateDiagonal {n : Nat} (d : Vector (DensePoly Rat) n) :
    Matrix (DensePoly Rat) n n :=
  upperUnit n * Matrix.diagMatrix d n n * lowerUnit n

private def polyPow (p : DensePoly Rat) (exponent : Nat) : DensePoly Rat :=
  (List.range exponent).foldl (fun product _ => product * p) 1

private def smallPolyPow (p : DensePoly (ZMod64 2)) (exponent : Nat) :
    DensePoly (ZMod64 2) :=
  (List.range exponent).foldl (fun product _ => product * p) 1

private def smallMatrix (input : SmallInput) :
    Matrix (DensePoly (ZMod64 2)) input.dimension input.dimension :=
  Matrix.ofFn fun i j => (input.entries.getD i.val #[]).getD j.val 0

/-- Dense comparator ladder with polynomial degree fixed at two. -/
def prepDenseCompare (n : Nat) : Input :=
  let p := DensePoly.monicize (densePoly 2 37 0 0)
  let q := DensePoly.monicize (densePoly 2 73 1 2)
  let d : Vector (DensePoly Rat) n := Vector.ofFn fun i =>
    if i.val % 2 = 0 then p else q
  { dimension := n, entries := rowsOfMatrix (conjugateDiagonal d) }

/-- Dense comparator ladder with matrix dimension fixed at three. -/
def prepDegreeCompare (degree : Nat) : Input :=
  let d : Vector (DensePoly Rat) 3 := Vector.ofFn fun i =>
    DensePoly.monicize (densePoly degree (37 + 19 * i.val) i.val (i.val + 1))
  { dimension := 3, entries := rowsOfMatrix (conjugateDiagonal d) }

def prepRationalCompare (degree : Nat) : Input :=
  let d : Vector (DensePoly Rat) 3 := Vector.ofFn fun i =>
    DensePoly.monicize (rationalPoly degree (53 + 23 * i.val) (i.val + 1) 2)
  { dimension := 3, entries := rowsOfMatrix (conjugateDiagonal d) }

private def chainFactors (n : Nat) (p : DensePoly Rat) : Vector (DensePoly Rat) n :=
  let square := p * p
  Vector.ofFn fun i => if i.val = 0 then p else square

/-- Dense dimension ladder whose invariant factors and boundary growth are
known from construction. Polynomial degree is fixed at four and coefficient
width grows only with the sum of at most `n` bounded coefficients. -/
def prepDenseDimension (n : Nat) : Input :=
  let p := DensePoly.monicize (densePoly 2 37 0 0)
  { dimension := n, entries := rowsOfMatrix (conjugateDiagonal (chainFactors n p)) }

/-- Dense degree ladder whose factors are `p`, `p^2`, and `p^2`. Thus every
boundary polynomial has degree at most twice the parameter, while bounded
integer coefficients acquire only logarithmic bit width under convolution. -/
def prepDenseDegree (degree : Nat) : Input :=
  let p := DensePoly.monicize (densePoly degree 37 0 0)
  { dimension := 3, entries := rowsOfMatrix (conjugateDiagonal (chainFactors 3 p)) }

def prepRationalDimension (n : Nat) : Input :=
  let p := DensePoly.ofCoeffs #[1 / 4, -(1 / 4), 1]
  { dimension := n, entries := rowsOfMatrix (conjugateDiagonal (chainFactors n p)) }

private def rationalChainPoly (degree : Nat) : DensePoly Rat :=
  let coefficientBits := Nat.log2 (degree + 1) + 1
  let denominator : Rat := (2 ^ coefficientBits : Nat)
  DensePoly.ofCoeffs <| Array.ofFn (n := degree + 1) fun k =>
    if k.val = degree then 1
    else if k.val % 2 = 0 then 1 / denominator else -(1 / denominator)

def prepRationalDegree (degree : Nat) : Input :=
  let p := rationalChainPoly degree
  { dimension := 3, entries := rowsOfMatrix (conjugateDiagonal (chainFactors 3 p)) }

private def monomial (degree : Nat) : DensePoly Rat := DensePoly.monomial degree 1

def prepChain (n : Nat) : Input :=
  let base := monomial 1
  let square := base * base
  let d : Vector (DensePoly Rat) n := Vector.ofFn fun i =>
    if i.val = 0 then base else square
  { dimension := n, entries := rowsOfMatrix (conjugateDiagonal d) }

def prepGradedChain (n : Nat) : Input :=
  let base := monomial 1
  let d : Vector (DensePoly Rat) n := Vector.ofFn fun i => polyPow base (i.val + 1)
  { dimension := n, entries := rowsOfMatrix (conjugateDiagonal d) }

def prepDiagonalCompare (n : Nat) : Input :=
  let base := monomial 1
  let square := base * base
  let d : Vector (DensePoly Rat) n := Vector.ofFn fun i =>
    let p := if i.val < n / 2 then square else base
    DensePoly.scale ((i.val + 2 : Nat) : Rat) p
  { dimension := n, entries := rowsOfMatrix (Matrix.diagMatrix d n n) }

def prepDiagonal (n : Nat) : Input :=
  let base := monomial 1
  let square := base * base
  let d : Vector (DensePoly Rat) n := Vector.ofFn fun i =>
    let p := if i.val = 0 then base else square
    DensePoly.scale ((i.val + 2 : Nat) : Rat) p
  { dimension := n, entries := rowsOfMatrix (Matrix.diagMatrix d n n) }

def prepSmallCompare (n : Nat) : SmallInput :=
  let x : DensePoly (ZMod64 2) := DensePoly.monomial 1 1
  let p := x
  let q := x * (x + 1)
  let upper : Matrix (DensePoly (ZMod64 2)) n n :=
    Matrix.ofFn fun i j => if i.val ≤ j.val then 1 else 0
  let lower : Matrix (DensePoly (ZMod64 2)) n n :=
    Matrix.ofFn fun i j => if j.val ≤ i.val then 1 else 0
  let d : Vector (DensePoly (ZMod64 2)) n := Vector.ofFn fun i =>
    if i.val % 2 = 0 then p else q
  let A := upper * Matrix.diagMatrix d n n * lower
  { dimension := n
    entries := A.rows.toArray.map (fun row => row.toArray) }

def prepSmall (degree : Nat) : SmallInput :=
  let x : DensePoly (ZMod64 2) := DensePoly.monomial 1 1
  let p := smallPolyPow x degree
  let square := p * p
  let upper : Matrix (DensePoly (ZMod64 2)) 3 3 :=
    Matrix.ofFn fun i j => if i.val ≤ j.val then 1 else 0
  let lower : Matrix (DensePoly (ZMod64 2)) 3 3 :=
    Matrix.ofFn fun i j => if j.val ≤ i.val then 1 else 0
  let d : Vector (DensePoly (ZMod64 2)) 3 := Vector.ofFn fun i =>
    if i.val = 0 then p else square
  let A := upper * Matrix.diagMatrix d 3 3 * lower
  { dimension := 3
    entries := A.rows.toArray.map (fun row => row.toArray) }

def prepSolve (n : Nat) : SolveInput :=
  let input := prepDenseDimension n
  let witness : Vector (DensePoly Rat) n := Vector.ofFn fun i =>
    DensePoly.ofList [((i.val + 1 : Nat) : Rat)]
  { matrix := input, rhs := (Matrix.vecMul witness (matrix input)).toArray }

private def upperPolyUnit (n : Nat) : Matrix (DensePoly Rat) n n :=
  let x := DensePoly.monomial 1 (1 : Rat)
  Matrix.ofFn fun i j =>
    if i = j then 1 else if i.val + 1 = j.val then x else 0

private def upperPolyUnitInv (n : Nat) : Matrix (DensePoly Rat) n n :=
  let negX := -(DensePoly.monomial 1 (1 : Rat))
  Matrix.ofFn fun i j =>
    if i.val ≤ j.val then polyPow negX (j.val - i.val) else 0

private def lowerPolyUnit (n : Nat) : Matrix (DensePoly Rat) n n :=
  let x := DensePoly.monomial 1 (1 : Rat)
  Matrix.ofFn fun i j =>
    if i = j then 1 else if j.val + 1 = i.val then x else 0

private def lowerPolyUnitInv (n : Nat) : Matrix (DensePoly Rat) n n :=
  let negX := -(DensePoly.monomial 1 (1 : Rat))
  Matrix.ofFn fun i j =>
    if j.val ≤ i.val then polyPow negX (i.val - j.val) else 0

/-- Certificate ladder with degree-two Smith factors and polynomial
unimodular changes of basis. -/
def prepCertDimension (n : Nat) : CertInput :=
  let p := DensePoly.monicize (densePoly 2 71 0 0)
  let d : Vector (DensePoly Rat) n := Vector.ofFn fun _ => p
  let diagonal := Matrix.diagMatrix d n n
  let left := upperPolyUnit n
  let leftInv := upperPolyUnitInv n
  let right := lowerPolyUnit n
  let rightInv := lowerPolyUnitInv n
  let A := leftInv * diagonal * rightInv
  { dimension := n
    matrix := rowsOfMatrix A
    rank := n
    diag := d.toArray
    left := rowsOfMatrix left
    leftInv := rowsOfMatrix leftInv
    right := rowsOfMatrix right
    rightInv := rowsOfMatrix rightInv
    intermediate := rowsOfMatrix (left * A) }

private def certSmith (input : CertInput) :
    SmithData Rat input.dimension input.dimension :=
  { rank := input.rank
    diag := Vector.ofFn fun i => input.diag.getD i.val 0
    left := matrixOfRows input.dimension input.left
    leftInv := matrixOfRows input.dimension input.leftInv
    right := matrixOfRows input.dimension input.right
    rightInv := matrixOfRows input.dimension input.rightInv }

private def polyChecksum (p : DensePoly Rat) : UInt64 := hash p.toArray

private def diagonalChecksum {n m : Nat} (A : Matrix (DensePoly Rat) n m) : UInt64 :=
  (List.range (min n m)).foldl
    (fun acc i =>
      let p := (A.rows.toArray[i]?).bind fun row => row.toArray[i]?
      mixHash acc (polyChecksum (p.getD 0))) 0

def runSnf (input : Input) : UInt64 := diagonalChecksum (snf (matrix input))

def runSnfData (input : Input) : UInt64 :=
  let S := snfData (matrix input)
  mixHash (hash S.rank) <| mixHash (diagonalChecksum S.left) <|
    mixHash (diagonalChecksum S.right) <|
      S.diag.toArray.foldl (fun acc p => mixHash acc (polyChecksum p)) 0

def runRank (input : Input) : UInt64 := hash (snfRank (matrix input))

def runFactors (input : Input) : UInt64 :=
  hash ((invariantFactors (matrix input)).toArray)

def runStructure (input : Input) : UInt64 :=
  let result := moduleStructure (matrix input)
  mixHash (hash result.1) (hash result.2)

def runOrder (input : Input) : UInt64 := polyChecksum (quotientOrder (matrix input))

def runSolve (input : SolveInput) : UInt64 :=
  let rhs : Vector (DensePoly Rat) input.matrix.dimension :=
    Vector.ofFn fun i => input.rhs.getD i.val 0
  match solve (matrix input.matrix) rhs with
  | some answer => hash answer.toArray
  | none => 0

def runDiagonal (input : Input) : UInt64 :=
  let d : Vector (DensePoly Rat) input.dimension := Vector.ofFn fun i =>
    (input.entries.getD i.val #[]).getD i.val 0
  diagonalChecksum (snfDiagonal d)

def runSmall (input : SmallInput) : UInt64 :=
  let S := snfData (smallMatrix input)
  mixHash (hash S.rank) <|
    S.diag.toArray.foldl
      (fun acc p => mixHash acc (hash (p.toArray.map (fun c => c.toNat)))) 0

def runDirectCert (input : CertInput) : Bool :=
  let S := certSmith input
  snfCert (matrixOfRows input.dimension input.matrix) S
    (matrixOfRows input.dimension input.intermediate)

def runEvalCert (input : CertInput) : Bool :=
  let S := certSmith input
  let pts : Vector Rat (2 * input.dimension + 4) :=
    Vector.ofFn fun i => (i.val : Rat)
  mulEqCertAt pts S.left (matrixOfRows input.dimension input.matrix)
    (matrixOfRows input.dimension input.intermediate)

private def matrixEntries {F : Type} [Zero F] [DecidableEq F] {n m : Nat}
    (A : Matrix (DensePoly F) n m) : List (DensePoly F) :=
  A.rows.toList.flatMap Vector.toList

private def smithEntries {F : Type} [Zero F] [DecidableEq F] {n m : Nat}
    (A : Matrix (DensePoly F) n m) (S : SmithData F n m) : List (DensePoly F) :=
  matrixEntries A ++ S.diag.toList ++ matrixEntries S.left ++
    matrixEntries S.leftInv ++ matrixEntries S.right ++ matrixEntries S.rightInv

private def peakDegree {F : Type} [Zero F] [DecidableEq F]
    (entries : List (DensePoly F)) : Nat :=
  entries.foldl (fun peak p => max peak (p.size - 1)) 0

private def intBits (z : Int) : Nat :=
  if z = 0 then 0 else z.natAbs.log2 + 1

private def ratBits (q : Rat) : Nat :=
  max (intBits q.num) (q.den.log2 + 1)

private def peakRatBits (entries : List (DensePoly Rat)) : Nat :=
  entries.foldl (fun peak p =>
    p.toArray.foldl (fun peak q => max peak (ratBits q)) peak) 0

private def ratGrowth (input : Input) : GrowthSample :=
  let A := matrix input
  let entries := smithEntries A (snfData A)
  { degree := peakDegree entries, coefficientBits := peakRatBits entries }

private def smallGrowth (input : SmallInput) : GrowthSample :=
  let A := smallMatrix input
  let entries := smithEntries A (snfData A)
  { degree := peakDegree entries, coefficientBits := 0 }

def runDenseSnfDimension := runSnf
def runDenseSnfDataDimension := runSnfData
def runDenseSnfDegree := runSnf
def runDenseSnfDataDegree := runSnfData
def runChainSnf := runSnf
def runRationalSnfDataDimension := runSnfData
def runRationalSnfDataDegree := runSnfData
def runDiagonalSnf := runDiagonal
def runSmallField := runSmall
def runSnfRank := runRank
def runInvariantFactors := runFactors
def runModuleStructure := runStructure
def runQuotientOrder := runOrder
def runSolveSystem := runSolve
def runDirectProductCert := runDirectCert
def runEvaluationCert := runEvalCert

#guard runDirectCert (prepCertDimension 4)
#guard runEvalCert (prepCertDimension 4)

private def ratPolyJson (p : DensePoly Rat) : Json :=
  let coefficients := p.toArray
  Json.mkObj
    [("num", Json.arr (coefficients.map fun q => Json.num (JsonNumber.fromInt q.num))),
     ("den", Json.arr (coefficients.map fun q => Json.num (JsonNumber.fromNat q.den)))]

private def matrixJson (input : Input) : Json :=
  Json.mkObj
    [("rows", Json.num (JsonNumber.fromNat input.dimension)),
     ("cols", Json.num (JsonNumber.fromNat input.dimension)),
     ("field", Json.mkObj [("rat", Json.bool true)]),
     ("entries", Json.arr (input.entries.map fun row =>
       Json.arr (row.map ratPolyJson)))]

private def leanSmithJson (input : Input) : String :=
  (Json.arr ((invariantFactors (matrix input)).toArray.map ratPolyJson)).compress

private def smallPolyJson (p : DensePoly (ZMod64 2)) : Json :=
  Json.arr (p.toArray.map fun c => Json.num (JsonNumber.fromNat c.toNat))

private def smallMatrixJson (input : SmallInput) : Json :=
  Json.mkObj
    [("rows", Json.num (JsonNumber.fromNat input.dimension)),
     ("cols", Json.num (JsonNumber.fromNat input.dimension)),
     ("field", Json.mkObj [("p", Json.num (JsonNumber.fromNat 2))]),
     ("entries", Json.arr (input.entries.map fun row =>
       Json.arr (row.map smallPolyJson)))]

private def smallLeanSmithJson (input : SmallInput) : String :=
  (Json.arr ((invariantFactors (smallMatrix input)).toArray.map smallPolyJson)).compress

private def runLeanFixed (input : Input) : Unit → IO String := fun _ =>
  return leanSmithJson input

private def runComparatorFixed (operation : String) (input : Input) :
    Unit → IO String := fun _ => do
  let result ← Hex.BenchOracle.Pari.runOp "polymatrix" operation
    #[("matrix", matrixJson input)]
  return result.compress

private def runLeanSmallFixed (input : SmallInput) : Unit → IO String := fun _ =>
  return smallLeanSmithJson input

private def runSmallComparatorFixed (operation : String) (input : SmallInput) :
    Unit → IO String := fun _ => do
  let result ← Hex.BenchOracle.Pari.runOp "polymatrix" operation
    #[("matrix", smallMatrixJson input)]
  return result.compress

def runComparatorOverhead (_ : Unit) : IO String := do
  let result ← Hex.BenchOracle.Pari.runOp "polymatrix" "overhead" #[]
  return result.compress

initialize compareInput1 : Input ← pure (prepDenseCompare 1)
initialize compareInput2 : Input ← pure (prepDenseCompare 2)
initialize compareInput3 : Input ← pure (prepDenseCompare 3)
initialize compareInput4 : Input ← pure (prepDenseCompare 4)
initialize compareInput5 : Input ← pure (prepDenseCompare 5)

initialize chainCompareInput1 : Input ← pure (prepChain 1)
initialize chainCompareInput2 : Input ← pure (prepChain 2)
initialize chainCompareInput3 : Input ← pure (prepChain 3)
initialize chainCompareInput4 : Input ← pure (prepChain 4)
initialize chainCompareInput5 : Input ← pure (prepChain 5)

initialize rationalCompareInput1 : Input ← pure (prepRationalCompare 1)
initialize rationalCompareInput2 : Input ← pure (prepRationalCompare 2)
initialize rationalCompareInput3 : Input ← pure (prepRationalCompare 3)
initialize rationalCompareInput4 : Input ← pure (prepRationalCompare 4)
initialize rationalCompareInput5 : Input ← pure (prepRationalCompare 5)

initialize diagonalCompareInput1 : Input ← pure (prepDiagonalCompare 2)
initialize diagonalCompareInput2 : Input ← pure (prepDiagonalCompare 4)
initialize diagonalCompareInput3 : Input ← pure (prepDiagonalCompare 6)
initialize diagonalCompareInput4 : Input ← pure (prepDiagonalCompare 8)
initialize diagonalCompareInput5 : Input ← pure (prepDiagonalCompare 10)

initialize smallCompareInput1 : SmallInput ← pure (prepSmallCompare 1)
initialize smallCompareInput2 : SmallInput ← pure (prepSmallCompare 2)
initialize smallCompareInput3 : SmallInput ← pure (prepSmallCompare 3)
initialize smallCompareInput4 : SmallInput ← pure (prepSmallCompare 4)
initialize smallCompareInput5 : SmallInput ← pure (prepSmallCompare 5)

def runLeanSmith1 : Unit → IO String := runLeanFixed compareInput1
def runSymPySmith1 : Unit → IO String := runComparatorFixed "sympy_snf" compareInput1
def runPariSmith1 : Unit → IO String := runComparatorFixed "pari_snf" compareInput1
def runLeanSmith2 : Unit → IO String := runLeanFixed compareInput2
def runSymPySmith2 : Unit → IO String := runComparatorFixed "sympy_snf" compareInput2
def runPariSmith2 : Unit → IO String := runComparatorFixed "pari_snf" compareInput2
def runLeanSmith3 : Unit → IO String := runLeanFixed compareInput3
def runSymPySmith3 : Unit → IO String := runComparatorFixed "sympy_snf" compareInput3
def runPariSmith3 : Unit → IO String := runComparatorFixed "pari_snf" compareInput3
def runLeanSmith4 : Unit → IO String := runLeanFixed compareInput4
def runSymPySmith4 : Unit → IO String := runComparatorFixed "sympy_snf" compareInput4
def runPariSmith4 : Unit → IO String := runComparatorFixed "pari_snf" compareInput4
def runLeanSmith5 : Unit → IO String := runLeanFixed compareInput5
def runSymPySmith5 : Unit → IO String := runComparatorFixed "sympy_snf" compareInput5
def runPariSmith5 : Unit → IO String := runComparatorFixed "pari_snf" compareInput5

def runLeanChain1 : Unit → IO String := runLeanFixed chainCompareInput1
def runSymPyChain1 : Unit → IO String := runComparatorFixed "sympy_snf" chainCompareInput1
def runPariChain1 : Unit → IO String := runComparatorFixed "pari_snf" chainCompareInput1
def runLeanChain2 : Unit → IO String := runLeanFixed chainCompareInput2
def runSymPyChain2 : Unit → IO String := runComparatorFixed "sympy_snf" chainCompareInput2
def runPariChain2 : Unit → IO String := runComparatorFixed "pari_snf" chainCompareInput2
def runLeanChain3 : Unit → IO String := runLeanFixed chainCompareInput3
def runSymPyChain3 : Unit → IO String := runComparatorFixed "sympy_snf" chainCompareInput3
def runPariChain3 : Unit → IO String := runComparatorFixed "pari_snf" chainCompareInput3
def runLeanChain4 : Unit → IO String := runLeanFixed chainCompareInput4
def runSymPyChain4 : Unit → IO String := runComparatorFixed "sympy_snf" chainCompareInput4
def runPariChain4 : Unit → IO String := runComparatorFixed "pari_snf" chainCompareInput4
def runLeanChain5 : Unit → IO String := runLeanFixed chainCompareInput5
def runSymPyChain5 : Unit → IO String := runComparatorFixed "sympy_snf" chainCompareInput5
def runPariChain5 : Unit → IO String := runComparatorFixed "pari_snf" chainCompareInput5

def runLeanRational1 : Unit → IO String := runLeanFixed rationalCompareInput1
def runSymPyRational1 : Unit → IO String := runComparatorFixed "sympy_snf" rationalCompareInput1
def runPariRational1 : Unit → IO String := runComparatorFixed "pari_snf" rationalCompareInput1
def runLeanRational2 : Unit → IO String := runLeanFixed rationalCompareInput2
def runSymPyRational2 : Unit → IO String := runComparatorFixed "sympy_snf" rationalCompareInput2
def runPariRational2 : Unit → IO String := runComparatorFixed "pari_snf" rationalCompareInput2
def runLeanRational3 : Unit → IO String := runLeanFixed rationalCompareInput3
def runSymPyRational3 : Unit → IO String := runComparatorFixed "sympy_snf" rationalCompareInput3
def runPariRational3 : Unit → IO String := runComparatorFixed "pari_snf" rationalCompareInput3
def runLeanRational4 : Unit → IO String := runLeanFixed rationalCompareInput4
def runSymPyRational4 : Unit → IO String := runComparatorFixed "sympy_snf" rationalCompareInput4
def runPariRational4 : Unit → IO String := runComparatorFixed "pari_snf" rationalCompareInput4
def runLeanRational5 : Unit → IO String := runLeanFixed rationalCompareInput5
def runSymPyRational5 : Unit → IO String := runComparatorFixed "sympy_snf" rationalCompareInput5
def runPariRational5 : Unit → IO String := runComparatorFixed "pari_snf" rationalCompareInput5

def runLeanDiagonal1 : Unit → IO String := runLeanFixed diagonalCompareInput1
def runSymPyDiagonal1 : Unit → IO String := runComparatorFixed "sympy_snf" diagonalCompareInput1
def runPariDiagonal1 : Unit → IO String := runComparatorFixed "pari_snf" diagonalCompareInput1
def runLeanDiagonal2 : Unit → IO String := runLeanFixed diagonalCompareInput2
def runSymPyDiagonal2 : Unit → IO String := runComparatorFixed "sympy_snf" diagonalCompareInput2
def runPariDiagonal2 : Unit → IO String := runComparatorFixed "pari_snf" diagonalCompareInput2
def runLeanDiagonal3 : Unit → IO String := runLeanFixed diagonalCompareInput3
def runSymPyDiagonal3 : Unit → IO String := runComparatorFixed "sympy_snf" diagonalCompareInput3
def runPariDiagonal3 : Unit → IO String := runComparatorFixed "pari_snf" diagonalCompareInput3
def runLeanDiagonal4 : Unit → IO String := runLeanFixed diagonalCompareInput4
def runSymPyDiagonal4 : Unit → IO String := runComparatorFixed "sympy_snf" diagonalCompareInput4
def runPariDiagonal4 : Unit → IO String := runComparatorFixed "pari_snf" diagonalCompareInput4
def runLeanDiagonal5 : Unit → IO String := runLeanFixed diagonalCompareInput5
def runSymPyDiagonal5 : Unit → IO String := runComparatorFixed "sympy_snf" diagonalCompareInput5
def runPariDiagonal5 : Unit → IO String := runComparatorFixed "pari_snf" diagonalCompareInput5

def runLeanSmall1 : Unit → IO String := runLeanSmallFixed smallCompareInput1
def runSymPySmall1 : Unit → IO String := runSmallComparatorFixed "sympy_snf" smallCompareInput1
def runPariSmall1 : Unit → IO String := runSmallComparatorFixed "pari_snf" smallCompareInput1
def runLeanSmall2 : Unit → IO String := runLeanSmallFixed smallCompareInput2
def runSymPySmall2 : Unit → IO String := runSmallComparatorFixed "sympy_snf" smallCompareInput2
def runPariSmall2 : Unit → IO String := runSmallComparatorFixed "pari_snf" smallCompareInput2
def runLeanSmall3 : Unit → IO String := runLeanSmallFixed smallCompareInput3
def runSymPySmall3 : Unit → IO String := runSmallComparatorFixed "sympy_snf" smallCompareInput3
def runPariSmall3 : Unit → IO String := runSmallComparatorFixed "pari_snf" smallCompareInput3
def runLeanSmall4 : Unit → IO String := runLeanSmallFixed smallCompareInput4
def runSymPySmall4 : Unit → IO String := runSmallComparatorFixed "sympy_snf" smallCompareInput4
def runPariSmall4 : Unit → IO String := runSmallComparatorFixed "pari_snf" smallCompareInput4
def runLeanSmall5 : Unit → IO String := runLeanSmallFixed smallCompareInput5
def runSymPySmall5 : Unit → IO String := runSmallComparatorFixed "sympy_snf" smallCompareInput5
def runPariSmall5 : Unit → IO String := runSmallComparatorFixed "pari_snf" smallCompareInput5

private def coefficientLimbs (bits : Nat) : Nat := (bits + 63) / 64

private def dimensionCost (n : Nat) : Nat :=
  n * n * n * coefficientLimbs (8 + Nat.log2 (n + 1))
private def degreeCost (degree : Nat) : Nat :=
  let boundaryDegree := 2 * degree
  (boundaryDegree + 1) * (boundaryDegree + 1) *
    coefficientLimbs (12 + Nat.log2 (degree + 1))
private def rationalDegreeCost (degree : Nat) : Nat :=
  let boundaryDegree := 2 * degree
  let boundaryBits := 2 * (Nat.log2 (degree + 1) + 1) + 1
  (boundaryDegree + 1) * (boundaryDegree + 1) * coefficientLimbs boundaryBits
private def chainCost (n : Nat) : Nat := n * n * n
private def gradedChainCost (n : Nat) : Nat := n * n * n * n
private def smallFieldCost (degree : Nat) : Nat :=
  let boundaryDegree := 2 * degree
  (boundaryDegree + 1) * (boundaryDegree + 1)
private def directCertCost (n : Nat) : Nat := n * n * n
private def evaluationCertCost (n : Nat) : Nat :=
  let square := (n + 1) * (n + 1)
  square * square

/- The chain construction fixes boundary degree at four. Its bounded
coefficients are summed at most `n` times, so the cubic dense matrix-update cost
is multiplied by the derived rational-limb count. -/
setup_benchmark runDenseSnfDimension n => dimensionCost n
  with prep := prepDenseDimension
  where {
    paramFloor := 1
    paramCeiling := 128
    paramSchedule := .custom #[1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128]
    verdictWarmupFraction := 0.6
    maxSecondsPerCall := 8.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- The full-data path has the same derived degree and coefficient-width bounds;
accumulating its four dense transform matrices changes only the constant in the
cubic dimension model. -/
setup_benchmark runDenseSnfDataDimension n => dimensionCost n
  with prep := prepDenseDimension
  where {
    paramFloor := 1
    paramCeiling := 128
    paramSchedule := .custom #[1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128]
    verdictWarmupFraction := 0.6
    maxSecondsPerCall := 8.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- At fixed dimension three, the factors are `p`, `p^2`, and `p^2`.
Consequently the maximum degree is `2 * degree`, coefficient width is
logarithmic, and classical dense polynomial arithmetic has the declared
quadratic degree cost times its rational-limb count. -/
setup_benchmark runDenseSnfDegree degree => degreeCost degree
  with prep := prepDenseDegree
  where {
    paramFloor := 1
    paramCeiling := 128
    paramSchedule := .custom #[1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128]
    verdictWarmupFraction := 0.6
    maxSecondsPerCall := 8.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Transform accumulation preserves the same `2 * degree` boundary and changes
only the constant in the fixed-dimension schoolbook model. -/
setup_benchmark runDenseSnfDataDegree degree => degreeCost degree
  with prep := prepDenseDegree
  where {
    paramFloor := 1
    paramCeiling := 128
    paramSchedule := .custom #[1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128]
    verdictWarmupFraction := 0.75
    maxSecondsPerCall := 8.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- The chain family fixes factor degrees at one and two while varying matrix
dimension, leaving the cubic dense matrix-update model. -/
setup_benchmark runChainSnf n => chainCost n
  with prep := prepChain
  where {
    paramFloor := 1
    paramCeiling := 32
    paramSchedule := .custom #[1, 2, 3, 4, 6, 8, 12, 16, 24, 32]
    verdictWarmupFraction := 0.5
    maxSecondsPerCall := 8.0
    signalFloorMultiplier := 1.0
  }

/- The rational chain has fixed degree four. Its fixed denominator and the sum
of at most `n` coefficients give the limb factor in `dimensionCost`. -/
setup_benchmark runRationalSnfDataDimension n => dimensionCost n
  with prep := prepRationalDimension
  where {
    paramFloor := 1
    paramCeiling := 128
    paramSchedule := .custom #[1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128]
    verdictWarmupFraction := 0.6
    maxSecondsPerCall := 8.0
    signalFloorMultiplier := 1.0
  }

/- Every nonleading coefficient of `p` has denominator
`2^(log2 (degree + 1) + 1)`. Squaring doubles that bit width, giving the
independent limb factor in `rationalDegreeCost`; the boundary degree is exactly
`2 * degree`. -/
setup_benchmark runRationalSnfDataDegree degree => rationalDegreeCost degree
  with prep := prepRationalDegree
  where {
    paramFloor := 1
    paramCeiling := 64
    paramSchedule := .custom #[1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64]
    verdictWarmupFraction := 0.6
    maxSecondsPerCall := 8.0
    signalFloorMultiplier := 1.0
  }

/- The ordered diagonal chain makes every pivot divide the full trailing block.
`badBlock` therefore scans all of that block at each stage; summing the
quadratic trailing sizes gives the cubic dimension model. The larger warmup
fraction excludes the independently diagnosed fixed-cost transition rungs. -/
setup_benchmark runDiagonalSnf n => dimensionCost n
  with prep := prepDiagonal
  where {
    paramFloor := 2
    paramCeiling := 768
    paramSchedule := .custom #[2, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512, 768]
    verdictWarmupFraction := 0.75
    maxSecondsPerCall := 30.0
    signalFloorMultiplier := 1.0
  }

/- Dimension is fixed at three and the factors are `x^degree`, `x^(2*degree)`,
and `x^(2*degree)`. With no coefficient growth, the schoolbook degree cost is
quadratic. -/
setup_benchmark runSmallField degree => smallFieldCost degree
  with prep := prepSmall
  where {
    paramFloor := 1
    paramCeiling := 256
    paramSchedule := .custom #[1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256]
    verdictWarmupFraction := 0.7
    maxSecondsPerCall := 8.0
    signalFloorMultiplier := 1.0
  }

/- These public projections run the transform-free Smith loop; the controlled
dense chain has the fixed boundary and limb count in `dimensionCost`, while
their postprocessing is at most linear in the rank. -/
setup_benchmark runSnfRank n => dimensionCost n with prep := prepDenseDimension
  where {
    paramFloor := 1
    paramCeiling := 128
    paramSchedule := .custom #[1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128]
    verdictWarmupFraction := 0.6
    maxSecondsPerCall := 8.0
    signalFloorMultiplier := 1.0
  }
/- The graded chain has factor degrees `1, ..., n`. Dense matrix updates are
cubic and their polynomial scans add the linear maximum-degree factor; the
rank-sized final projection is lower order. -/
setup_benchmark runInvariantFactors n => gradedChainCost n with prep := prepGradedChain
  where {
    paramFloor := 1
    paramCeiling := 32
    paramSchedule := .custom #[1, 2, 3, 4, 6, 8, 12, 16, 24, 32]
    verdictWarmupFraction := 0.5
    maxSecondsPerCall := 8.0
    signalFloorMultiplier := 1.0
  }
/- Module-structure extraction also runs the transform-free Smith loop and
then maps over at most the matrix rank, so it shares the cubic Smith
matrix-operation proxy. -/
setup_benchmark runModuleStructure n => dimensionCost n with prep := prepDenseDimension
  where {
    paramFloor := 1
    paramCeiling := 128
    paramSchedule := .custom #[1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128]
    verdictWarmupFraction := 0.6
    maxSecondsPerCall := 8.0
    signalFloorMultiplier := 1.0
  }
/- Quotient-order computation uses that same transform-free Smith loop and a
rank-sized coefficient product, retaining the cubic fixed-input-degree
matrix-operation proxy. -/
setup_benchmark runQuotientOrder n => dimensionCost n with prep := prepDenseDimension
  where {
    paramFloor := 1
    paramCeiling := 128
    paramSchedule := .custom #[1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128]
    verdictWarmupFraction := 0.6
    maxSecondsPerCall := 8.0
    signalFloorMultiplier := 1.0
  }

/- Prepared right-hand sides leave `solve`'s full-data Smith run dominant, so
it has the same derived cubic dimension, degree, and limb model. -/
setup_benchmark runSolveSystem n => dimensionCost n with prep := prepSolve
  where {
    paramFloor := 1
    paramCeiling := 128
    paramSchedule := .custom #[1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128]
    verdictWarmupFraction := 0.6
    outerTrials := 3
    maxSecondsPerCall := 8.0
    signalFloorMultiplier := 1.0
  }

/- Although inverse-transform degrees grow linearly, only quadratically many
products have nonzero polynomial operands; the remaining dense matrix scan is
also cubic. Thus the direct checker has a cubic wall model. -/
setup_benchmark runDirectProductCert n => directCertCost n with prep := prepCertDimension
  where {
    paramFloor := 1
    paramCeiling := 32
    paramSchedule := .custom #[1, 2, 3, 4, 6, 8, 12, 16, 24, 32]
    verdictWarmupFraction := 0.6
    maxSecondsPerCall := 8.0
    signalFloorMultiplier := 1.0
  }

/- The evaluation checker uses linearly many points. At each point it evaluates
quadratically many degree-linear polynomials and performs a cubic scalar matrix
product, giving the quartic wall model. -/
setup_benchmark runEvaluationCert n => evaluationCertCost n with prep := prepCertDimension
  where {
    paramFloor := 1
    paramCeiling := 32
    paramSchedule := .custom #[1, 2, 3, 4, 6, 8, 12, 16, 24, 32]
    verdictWarmupFraction := 0.6
    maxSecondsPerCall := 8.0
    signalFloorMultiplier := 1.0
  }

def leanCompareConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 8.0, minTotalSeconds := 0.1 }

def externalCompareConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 8.0, warmupFirstIter := true,
    minTotalSeconds := 0.1 }

setup_fixed_benchmark runComparatorOverhead where externalCompareConfig
setup_fixed_benchmark runLeanSmith1 where leanCompareConfig
setup_fixed_benchmark runSymPySmith1 where externalCompareConfig
setup_fixed_benchmark runPariSmith1 where externalCompareConfig
setup_fixed_benchmark runLeanSmith2 where leanCompareConfig
setup_fixed_benchmark runSymPySmith2 where externalCompareConfig
setup_fixed_benchmark runPariSmith2 where externalCompareConfig
setup_fixed_benchmark runLeanSmith3 where leanCompareConfig
setup_fixed_benchmark runSymPySmith3 where externalCompareConfig
setup_fixed_benchmark runPariSmith3 where externalCompareConfig
setup_fixed_benchmark runLeanSmith4 where leanCompareConfig
setup_fixed_benchmark runSymPySmith4 where externalCompareConfig
setup_fixed_benchmark runPariSmith4 where externalCompareConfig
setup_fixed_benchmark runLeanSmith5 where leanCompareConfig
setup_fixed_benchmark runSymPySmith5 where externalCompareConfig
setup_fixed_benchmark runPariSmith5 where externalCompareConfig

setup_fixed_benchmark runLeanChain1 where leanCompareConfig
setup_fixed_benchmark runSymPyChain1 where externalCompareConfig
setup_fixed_benchmark runPariChain1 where externalCompareConfig
setup_fixed_benchmark runLeanChain2 where leanCompareConfig
setup_fixed_benchmark runSymPyChain2 where externalCompareConfig
setup_fixed_benchmark runPariChain2 where externalCompareConfig
setup_fixed_benchmark runLeanChain3 where leanCompareConfig
setup_fixed_benchmark runSymPyChain3 where externalCompareConfig
setup_fixed_benchmark runPariChain3 where externalCompareConfig
setup_fixed_benchmark runLeanChain4 where leanCompareConfig
setup_fixed_benchmark runSymPyChain4 where externalCompareConfig
setup_fixed_benchmark runPariChain4 where externalCompareConfig
setup_fixed_benchmark runLeanChain5 where leanCompareConfig
setup_fixed_benchmark runSymPyChain5 where externalCompareConfig
setup_fixed_benchmark runPariChain5 where externalCompareConfig

setup_fixed_benchmark runLeanRational1 where leanCompareConfig
setup_fixed_benchmark runSymPyRational1 where externalCompareConfig
setup_fixed_benchmark runPariRational1 where externalCompareConfig
setup_fixed_benchmark runLeanRational2 where leanCompareConfig
setup_fixed_benchmark runSymPyRational2 where externalCompareConfig
setup_fixed_benchmark runPariRational2 where externalCompareConfig
setup_fixed_benchmark runLeanRational3 where leanCompareConfig
setup_fixed_benchmark runSymPyRational3 where externalCompareConfig
setup_fixed_benchmark runPariRational3 where externalCompareConfig
setup_fixed_benchmark runLeanRational4 where leanCompareConfig
setup_fixed_benchmark runSymPyRational4 where externalCompareConfig
setup_fixed_benchmark runPariRational4 where externalCompareConfig
setup_fixed_benchmark runLeanRational5 where leanCompareConfig
setup_fixed_benchmark runSymPyRational5 where externalCompareConfig
setup_fixed_benchmark runPariRational5 where externalCompareConfig

setup_fixed_benchmark runLeanDiagonal1 where leanCompareConfig
setup_fixed_benchmark runSymPyDiagonal1 where externalCompareConfig
setup_fixed_benchmark runPariDiagonal1 where externalCompareConfig
setup_fixed_benchmark runLeanDiagonal2 where leanCompareConfig
setup_fixed_benchmark runSymPyDiagonal2 where externalCompareConfig
setup_fixed_benchmark runPariDiagonal2 where externalCompareConfig
setup_fixed_benchmark runLeanDiagonal3 where leanCompareConfig
setup_fixed_benchmark runSymPyDiagonal3 where externalCompareConfig
setup_fixed_benchmark runPariDiagonal3 where externalCompareConfig
setup_fixed_benchmark runLeanDiagonal4 where leanCompareConfig
setup_fixed_benchmark runSymPyDiagonal4 where externalCompareConfig
setup_fixed_benchmark runPariDiagonal4 where externalCompareConfig
setup_fixed_benchmark runLeanDiagonal5 where leanCompareConfig
setup_fixed_benchmark runSymPyDiagonal5 where externalCompareConfig
setup_fixed_benchmark runPariDiagonal5 where externalCompareConfig

setup_fixed_benchmark runLeanSmall1 where leanCompareConfig
setup_fixed_benchmark runSymPySmall1 where externalCompareConfig
setup_fixed_benchmark runPariSmall1 where externalCompareConfig
setup_fixed_benchmark runLeanSmall2 where leanCompareConfig
setup_fixed_benchmark runSymPySmall2 where externalCompareConfig
setup_fixed_benchmark runPariSmall2 where externalCompareConfig
setup_fixed_benchmark runLeanSmall3 where leanCompareConfig
setup_fixed_benchmark runSymPySmall3 where externalCompareConfig
setup_fixed_benchmark runPariSmall3 where externalCompareConfig
setup_fixed_benchmark runLeanSmall4 where leanCompareConfig
setup_fixed_benchmark runSymPySmall4 where externalCompareConfig
setup_fixed_benchmark runPariSmall4 where externalCompareConfig
setup_fixed_benchmark runLeanSmall5 where leanCompareConfig
setup_fixed_benchmark runSymPySmall5 where externalCompareConfig
setup_fixed_benchmark runPariSmall5 where externalCompareConfig

private def printGrowth (family parameter : String) (sample : GrowthSample) : IO Unit :=
  IO.println s!"{family},{parameter},{sample.degree},{sample.coefficientBits}"

/-- Emit deterministic boundary-degree and coefficient-bit diagnostics as CSV. -/
def growthReport : IO UInt32 := do
  IO.println "family,parameter,max_boundary_degree,max_boundary_coefficient_bits"
  for n in #[1, 2, 4, 8, 16, 32, 64] do
    printGrowth "dense-chain-dimension" (toString n) (ratGrowth (prepDenseDimension n))
  for degree in #[1, 2, 4, 8, 16, 32, 64] do
    printGrowth "dense-chain-degree" (toString degree) (ratGrowth (prepDenseDegree degree))
  for n in #[1, 2, 4, 8, 16, 32] do
    printGrowth "chain-conjugate-poly" (toString n) (ratGrowth (prepChain n))
  for n in #[1, 2, 4, 8, 16, 32, 64] do
    printGrowth "rational-chain-dimension" (toString n)
      (ratGrowth (prepRationalDimension n))
  for degree in #[1, 2, 4, 8, 16, 32, 64] do
    printGrowth "rational-chain-degree" (toString degree)
      (ratGrowth (prepRationalDegree degree))
  for n in #[2, 4, 6, 8, 12, 16] do
    printGrowth "diagonal-polysmith" (toString n) (ratGrowth (prepDiagonal n))
  for degree in #[1, 2, 4, 8, 16, 32, 64] do
    printGrowth "small-field-degree" (toString degree) (smallGrowth (prepSmall degree))
  return 0

end Hex.PolySmithBench

def main (args : List String) : IO UInt32 :=
  if args == ["growth"] then Hex.PolySmithBench.growthReport
  else LeanBench.Cli.dispatch args
