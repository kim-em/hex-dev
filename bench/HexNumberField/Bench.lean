/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexNumberField
import LeanBench

/-!
Benchmark registrations for `HexNumberField`.

The fixed cases separate the costs requested by the library SPEC:

* degree-10 fixed-presentation multiplication, inversion, and minimal relation;
* lazy addition eliminant construction;
* isolation and operation-ball disambiguation for a precomputed eliminant;
* the complete lazy addition driver;
* exactification through an irrelevant enclosing factor;
* repeated-root extraction over `ℚ(√2)`.

All fixtures and benchmark kernels are Mathlib-free. External PARI/FLINT
comparison belongs to the conformance profile rather than the timed process.
-/

namespace Hex.NumberFieldBench

open Hex

private def requireSome (case : String) : Option α → IO α
  | some value => pure value
  | none => throw <| IO.userError (case ++ ": benchmark fixture failed")

private def polyChecksum (p : ZPoly) : UInt64 :=
  hash p.toArray

private def dyadicChecksum (d : Dyadic) : UInt64 :=
  let q := d.toRat
  mixHash (hash q.num) (hash (q.den : Int))

private def squareChecksum (square : DyadicSquare) : UInt64 :=
  mixHash (mixHash (dyadicChecksum square.re) (dyadicChecksum square.im))
    (hash square.prec)

private def rootChecksum (a : AlgebraicRoot) : UInt64 :=
  mixHash (polyChecksum a.p) (squareChecksum a.rep.1.square)

private def ratChecksum (q : Rat) : UInt64 :=
  mixHash (hash q.num) (hash (q.den : Int))

private def fixedChecksum {p : ZPoly} {x : SimpleRoot p}
    (a : QAdjoin p x) : UInt64 :=
  a.coeffs.toArray.foldl
    (fun checksum q => mixHash checksum (ratChecksum q))
    (hash a.coeffs.size)

/-! # Degree-10 fixed presentation -/

private def degreeTenPoly : ZPoly :=
  DensePoly.ofList [-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

private def degreeTenSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 19770730768400532067 64, 0, 60⟩

private def degreeTenRep : RefinedIsolation degreeTenPoly :=
  ⟨⟨degreeTenSquare, by
      set_option maxRecDepth 100000 in
      set_option exponentiation.threshold 2000 in
        decide⟩,
    by
      set_option maxRecDepth 100000 in
      set_option exponentiation.threshold 2000 in
        decide⟩

private def degreeTenRoot : SimpleRoot degreeTenPoly :=
  SimpleRoot.mk degreeTenRep

private def degreeTenInput : QAdjoin degreeTenPoly degreeTenRoot :=
  QAdjoin.reduce degreeTenPoly degreeTenRoot
    (DensePoly.ofList [3, -2, 5, 1, -4, 2, 1, 0, -1, 1])

initialize fixedFieldRef : IO.Ref
    (Option (QAdjoin degreeTenPoly degreeTenRoot)) ←
  IO.mkRef (some degreeTenInput)

def runFixedMul : Unit → IO UInt64 := fun _ => do
  let a ← requireSome "fixed/mul" (← fixedFieldRef.get)
  return fixedChecksum (a * a)

def runFixedInv : Unit → IO UInt64 :=
  if hirred : ZPoly.isIrreducible degreeTenPoly = true then
    letI : ZPoly.CheckedIrreducible degreeTenPoly :=
      ⟨hirred, by decide⟩
    fun _ => do
      let a ← requireSome "fixed/inv" (← fixedFieldRef.get)
      return fixedChecksum a⁻¹
  else
    fun _ => throw <| IO.userError "fixed/inv: irreducibility check failed"

def runFixedMinpoly : Unit → IO UInt64 :=
  if hirred : ZPoly.isIrreducible degreeTenPoly = true then
    letI : ZPoly.CheckedIrreducible degreeTenPoly :=
      ⟨hirred, by decide⟩
    fun _ => do
      let a ← requireSome "fixed/minpoly" (← fixedFieldRef.get)
      return polyChecksum (← requireSome "fixed/minpoly" a.minpoly?)
  else
    fun _ => throw <| IO.userError "fixed/minpoly: irreducibility check failed"

/- Degree-`n` dense multiplication followed by reduction modulo a degree-`n`
relation performs `O(n²)` rational coefficient operations. This canonical
`n = 10` case is fixed because the SPEC supplies an absolute 100 ms budget,
not an asymptotic fit requirement. -/
setup_fixed_benchmark runFixedMul where {
  repeats := 5, maxSecondsPerCall := 0.1,
  expectedHash := some 0xc319ee2337214e59
}

/- Extended gcd on two degree-`n` dense rational polynomials performs a
quadratic number of coefficient operations with coefficient-size growth. The
required degree-10 budget is tested as a fixed regression. -/
setup_fixed_benchmark runFixedInv where {
  repeats := 5, maxSecondsPerCall := 0.1,
  expectedHash := some 0x1525969728101d06
}

/- One iterative Krylov orbit is shared across the degree-10 first-dependence
search. This fixed registration catches accidental recomputation of powers in
each span matrix entry before that cost reaches exactification callers. -/
setup_fixed_benchmark runFixedMinpoly where {
  repeats := 3, maxSecondsPerCall := 5.0,
  expectedHash := some 0xb1ed00ebc8d039e9
}

/-! # Lazy arithmetic fixtures -/

private def sqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def sqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def sqrtTwoRep : RefinedIsolation sqrtTwoPoly :=
  ⟨⟨sqrtTwoSquare, by decide⟩, by decide⟩

private def sqrtTwo? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots sqrtTwoPoly then
    some
      { p := sqrtTwoPoly, prim := by rfl, pos_lc := by decide
        pos_degree := by decide, squarefree := hsimple
        x := SimpleRoot.mk sqrtTwoRep, rep := sqrtTwoRep, rep_mk := rfl }
  else none

private def sqrtThreePoly : ZPoly := DensePoly.ofList [-3, 0, 1]

private def sqrtThreeSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 222 7, 0, 8⟩

private def sqrtThreeRep : RefinedIsolation sqrtThreePoly :=
  ⟨⟨sqrtThreeSquare, by decide⟩, by decide⟩

private def sqrtThree? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots sqrtThreePoly then
    some
      { p := sqrtThreePoly, prim := by rfl, pos_lc := by decide
        pos_degree := by decide, squarefree := hsimple
        x := SimpleRoot.mk sqrtThreeRep, rep := sqrtThreeRep, rep_mk := rfl }
  else none

private def lazyPair? : Option (AlgebraicRoot × AlgebraicRoot) := do
  some (← sqrtTwo?, ← sqrtThree?)

initialize lazyPairRef : IO.Ref (Option (AlgebraicRoot × AlgebraicRoot)) ←
  IO.mkRef lazyPair?

private def addRaw : ZPoly :=
  ZPoly.addEliminant sqrtTwoPoly sqrtThreePoly

private def addCore : ZPoly :=
  ZPoly.squareFreeCore addRaw

private structure IsolateInput where
  polynomial : ZPoly
  simple : HasOnlySimpleRoots polynomial
  depth : Nat

private def isolateInput? : Option IsolateInput :=
  if hsimple : HasOnlySimpleRoots addCore then
    some ⟨addCore, hsimple, separationDepth addCore⟩
  else
    none

initialize addInputRef : IO.Ref (Option (ZPoly × ZPoly)) ←
  IO.mkRef (some (sqrtTwoPoly, sqrtThreePoly))

initialize isolateInputRef : IO.Ref (Option IsolateInput) ←
  IO.mkRef isolateInput?

def runAddEliminant : Unit → IO UInt64 := fun _ => do
  let input ← requireSome "lazy/add-eliminant" (← addInputRef.get)
  return polyChecksum (ZPoly.addEliminant input.1 input.2)

def runIsolateAdd : Unit → IO UInt64 := fun _ => do
  let input ← requireSome "lazy/isolate-add" (← isolateInputRef.get)
  let isolations ← requireSome "lazy/isolate-add"
    (isolate input.polynomial input.simple (input.depth : Int))
  return isolations.foldl
    (fun checksum isolation =>
      mixHash checksum (squareChecksum isolation.square))
    (hash isolations.size)

private def selectAdd (a b : AlgebraicRoot) : Option AlgebraicRoot :=
  AlgebraicRoot.ofEliminant? addRaw fun prec => do
    let target := prec + 4
    let ar ← a.rep.refineTo? target
    let br ← b.rep.refineTo? target
    some (ar.1.1.square.toBall.add br.1.1.square.toBall)

def runSelectAdd : Unit → IO UInt64 := fun _ => do
  let (a, b) ← requireSome "lazy/select-add" (← lazyPairRef.get)
  return rootChecksum (← requireSome "lazy/select-add" (selectAdd a b))

def runLazyAdd : Unit → IO UInt64 := fun _ => do
  let (a, b) ← requireSome "lazy/add" (← lazyPairRef.get)
  return rootChecksum (← requireSome "lazy/add" (a.add? b))

/- Brown elimination on the fixed pair of quadratic inputs constructs the
degree-four sum eliminant. This isolates construction cost from all root work;
it is fixed because one degree-product point does not support a scalar model. -/
setup_fixed_benchmark runAddEliminant where {
  repeats := 5, maxSecondsPerCall := 2.0,
  expectedHash := some 0xeb2eecad44116a79
}

/- This registration runs only the fixed root isolator on the precomputed
degree-four square-free eliminant. It is the isolation baseline against which
the following operation-ball selection registration is read. -/
setup_fixed_benchmark runIsolateAdd where {
  repeats := 3, maxSecondsPerCall := 5.0,
  expectedHash := some 0x4367ab34a73ea4ed
}

/- The precomputed degree-four eliminant is square-free normalized, isolated
to its separation depth, and filtered by one certified operation ball. This
fixed case records the selection boundary; comparing it with `runIsolateAdd`
attributes the additional operation-ball disambiguation work. -/
setup_fixed_benchmark runSelectAdd where {
  repeats := 3, maxSecondsPerCall := 5.0,
  expectedHash := some 0xb2956b93cac0235f
}

/- The complete lazy-add path is the preceding eliminant construction followed
by isolation and disambiguation. Its degree product is `2 * 2 = 4`, well below
the merge-facing ceiling `20`; the fixed timing tracks end-to-end cost. -/
setup_fixed_benchmark runLazyAdd where {
  repeats := 3, maxSecondsPerCall := 5.0,
  expectedHash := some 0xb2956b93cac0235f
}

/-! # Exactification and roots -/

private def enclosingPoly : ZPoly :=
  sqrtTwoPoly * DensePoly.ofList [-3, 1]

private def enclosingSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 6074001000 32, 0, 32⟩

private def enclosingRep : RefinedIsolation enclosingPoly :=
  ⟨⟨enclosingSquare, by decide⟩, by decide⟩

private def enclosingRoot? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots enclosingPoly then
    some
      { p := enclosingPoly, prim := by rfl, pos_lc := by decide
        pos_degree := by decide, squarefree := hsimple
        x := SimpleRoot.mk enclosingRep, rep := enclosingRep, rep_mk := rfl }
  else none

initialize exactRef : IO.Ref (Option AlgebraicRoot) ← IO.mkRef enclosingRoot?

def runExact : Unit → IO UInt64 := fun _ => do
  let input ← requireSome "exact" (← exactRef.get)
  let result ← requireSome "exact" input.exact?
  return polyChecksum result.p

/- Exactification factors the degree-three enclosing polynomial, refines the
candidate factors, selects the quadratic root, and canonicalizes it. The input
shape is fixed so this registration attributes that whole extra stage. -/
setup_fixed_benchmark runExact where {
  repeats := 3, maxSecondsPerCall := 5.0,
  expectedHash := some 0xafd3fbfd3a66fc82
}

private def sqrtTwoRoot : SimpleRoot sqrtTwoPoly :=
  SimpleRoot.mk sqrtTwoRep

private def fixedSqrtTwo : QAdjoin sqrtTwoPoly sqrtTwoRoot :=
  QAdjoin.reduce sqrtTwoPoly sqrtTwoRoot
    (DensePoly.ofList ([0, 1] : List Rat))

private def rootsInput : DensePoly (QAdjoin sqrtTwoPoly sqrtTwoRoot) :=
  let linear := DensePoly.ofList [-fixedSqrtTwo, 1]
  linear * linear

initialize rootsRef : IO.Ref
    (Option (DensePoly (QAdjoin sqrtTwoPoly sqrtTwoRoot))) ←
  IO.mkRef (some rootsInput)

private def rootSetChecksum : RootSet → UInt64
  | .all => 1
  | .finite roots => roots.foldl
      (fun checksum root =>
        mixHash checksum
          (mixHash (rootChecksum root.root) (hash root.multiplicity)))
      (hash roots.size)

def runRoots : Unit → IO UInt64 :=
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly :=
      ⟨hirred, by decide⟩
    fun _ => do
      let polynomial ← requireSome "roots" (← rootsRef.get)
      let result ← requireSome "roots"
        (QAdjoin.roots? polynomial sqrtTwoRep rfl)
      return rootSetChecksum result
  else
    fun _ => throw <| IO.userError "roots: irreducibility check failed"

/- The repeated linear factor over `ℚ(√2)` exercises Yun multiplicity
separation, one norm eliminant, candidate isolation, zero retention, and final
deduplication. This fixed end-to-end root case has one root of multiplicity 2. -/
setup_fixed_benchmark runRoots where {
  repeats := 3, maxSecondsPerCall := 5.0,
  expectedHash := some 0x0927e3f02f6eee94
}

end Hex.NumberFieldBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
