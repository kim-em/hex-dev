/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexNumberField
import Hex.BenchOracle.Pari
import Lean.Data.Json
import LeanBench

/-!
Benchmark registrations for `HexNumberField`.

The fixed cases separate the costs requested by the library SPEC:

* degree-10 fixed-presentation multiplication, inversion, and minimal relation;
* lazy addition eliminant construction;
* isolation and operation-ball disambiguation for a precomputed eliminant;
* the complete lazy addition driver;
* isolation-dominated lazy addition on the canonical degree-product-12 input;
* exactification through an irrelevant enclosing factor;
* repeated-root extraction over `ℚ(√2)`;
* isolation-dominated repeated-root extraction on the canonical degree-6
  repeated-component input over `ℚ(√2)`;
* canonical-coefficient roots on the fixed dense degree-6 input with a
  `√2`-dependent coefficient.

The parametric ladders carry the Phase-4 asymptotic evidence:

* `runQAdjoinAddLadder` / `runQAdjoinMulLadder` / `runQAdjoinInvLadder`:
  fixed-field arithmetic in `ℚ(2^{1/n})` at growing modulus degree `n`;
* `runAddEliminantLadder`: Brown-resultant sum-eliminant construction at
  growing first-operand degree;
* `runExactFactorLadder` / `runCanonicalRepLadder`: fixed canonical cases for
  the two separable certification phases exposed by exactification;
* `runExactLadder`: fixed end-to-end exactification through six quadratic
  factors whose modular factorization requires recombination;
* `runMergeRootListLadder`: the duplicate-removal fold across the two Yun
  components of the repeated-factor fixed-field family;
* `runCommonPresentationLadder`: the public common-field construction
  behind `AlgebraicPoly.roots?`, separated per the Attribution rule.

Informational PARI comparator (`SPEC/benchmarking.md` §External comparators
§Process call): PARI's `t_POLMOD` arithmetic (`Mod(a, m) * Mod(b, m)` and
`Mod(a, m)^(-1)`) is the callable PARI surface matching `QAdjoin`
multiplication and inversion. The `runQAdjoinMulPair*` / `runPariPolmodMul*`
rungs run at `n = 4, 6, 8, 12, 16, 20` and the `runQAdjoinInvPair*` /
`runPariPolmodInv*` rungs at `n = 4, 6, 8, 10, 12, 16`: six rungs each rather than
a doubling-only triple, because `SPEC/benchmarking.md` §Headline reports
requires enough eligible rungs for the ratio's shape to be unambiguous, and
both families cross the ratio 1 inside these ranges. The pairs consume identical
deterministic inputs and hash the identical reduced rational coefficient
vector, so `compare` joins them on result hashes. The PARI side runs through
the persistent-subprocess driver `scripts/oracle/pari_bench_driver.py`
(one JSON request per line; the driver is started by a `warmupFirstIter`
call outside the timed region and reused across the child's auto-tuned
inner-repeat batch — see `Hex/BenchOracle/Pari.lean`). Both sides of every
pair use `warmupFirstIter` so the lazily built rung fixture (root isolation
and, for inversion, the irreducibility check) also stays outside the timed
region, and share the same `minTotalSeconds` amortisation floor so per-rung
ratios compare steady-state medians on the same basis. Lazy certified
arithmetic, exactification, and the certified root-set APIs have no
comparable PARI unit surface; see the SPEC's External comparators section.

All fixtures and benchmark kernels are Mathlib-free.
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

private def algebraicChecksum (a : AlgebraicNumber) : UInt64 :=
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
  ⟨⟨degreeTenSquare, .ofWitness (by
      set_option maxRecDepth 100000 in
      set_option exponentiation.threshold 2000 in
        decide)⟩,
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
  ⟨⟨sqrtTwoSquare, .ofWitness (by decide)⟩, by decide⟩

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
  ⟨⟨sqrtThreeSquare, .ofWitness (by decide)⟩, by decide⟩

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
  return rootChecksum (a.add b)

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

/- The total lazy-add wrapper calls the checked path, then performs only the
constant-time proven-unreachable fallback projection. This therefore measures
both `add?` and its total wrapper on the same degree-product-four route. -/
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
  ⟨⟨enclosingSquare, .ofWitness (by decide)⟩, by decide⟩

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

initialize canonicalQAdjoinRef : IO.Ref
    (Option (QAdjoin sqrtTwoPoly sqrtTwoRoot)) ←
  IO.mkRef (some fixedSqrtTwo)

def runQAdjoinCanonical : Unit → IO UInt64 :=
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly := ⟨hirred, by decide⟩
    fun _ => do
      let input ← requireSome "qadjoin/canonical"
        (← canonicalQAdjoinRef.get)
      -- The total wrapper executes `toAlgebraicNumber?` and only projects its
      -- certified result. Group the runtime structural equality decision here.
      return mixHash
        (algebraicChecksum (input.toAlgebraicNumber sqrtTwoRep rfl))
        (hash (decide (input = input)))
  else
    fun _ => throw <| IO.userError "qadjoin/canonical: irreducibility failed"

/- Krylov powers, first-dependence row reduction, normalization, isolation,
and representative selection are all exercised at fixed defining degree two.
The total wrapper adds only the constant-time checked-result projection. -/
setup_fixed_benchmark runQAdjoinCanonical where {
  repeats := 3
  maxSecondsPerCall := 0.25
  killGraceMs := 0
  warmupFirstIter := true
  expectedHash := some 0x6d24385fc39cc6fb
}

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
      let result := QAdjoin.roots polynomial sqrtTwoRep rfl
      return rootSetChecksum result
  else
    fun _ => throw <| IO.userError "roots: irreducibility check failed"

/- The repeated linear factor over `ℚ(√2)` exercises Yun multiplicity
separation, one norm eliminant, candidate isolation, zero retention, and final
deduplication. This fixed end-to-end root case has one root of multiplicity 2. -/
setup_fixed_benchmark runRoots where {
  repeats := 3, maxSecondsPerCall := 5.0,
  expectedHash := some 0x235b18400d87a46c
}

/-! # Advertised fixed-degree API surface -/

/- Mode-3 fixed assessments use a zero-grace whole-child ceiling and warm the
lazy fixture once before measurement. The 250 ms default is over three times
the measured 43 ms clean-spawn floor plus every default-class operation below;
the few slower routes declare their own measured budgets adjacent to them. -/
private def apiFixedConfig : LeanBench.FixedBenchmarkConfig := {
  repeats := 3
  maxSecondsPerCall := 0.25
  killGraceMs := 0
  warmupFirstIter := true
}

/- Closed constant-time accessors are protocol/correctness anchors rather than
performance evidence. They still pin their output and use the same strict
whole-child mechanics so a registration cannot become vacuous. -/
private def apiAnchorConfig : LeanBench.FixedBenchmarkConfig := {
  repeats := 5
  maxSecondsPerCall := 0.25
  killGraceMs := 0
  warmupFirstIter := true
}

private def optionAlgebraicChecksum : Option AlgebraicNumber → UInt64
  | some a => algebraicChecksum a
  | none => 0

def runLazySub : Unit → IO UInt64 := fun _ => do
  let (a, b) ← requireSome "lazy/sub" (← lazyPairRef.get)
  return rootChecksum (a.sub b)

def runLazyMul : Unit → IO UInt64 := fun _ => do
  let (a, b) ← requireSome "lazy/mul" (← lazyPairRef.get)
  return rootChecksum (a.mul b)

def runLazyDiv : Unit → IO UInt64 := fun _ => do
  let (a, b) ← requireSome "lazy/div" (← lazyPairRef.get)
  return rootChecksum (a.div b)

def runLazyInv : Unit → IO UInt64 := fun _ => do
  let (a, _) ← requireSome "lazy/inv" (← lazyPairRef.get)
  return rootChecksum a.inv

def runLazyNeg : Unit → IO UInt64 := fun _ => do
  let (a, _) ← requireSome "lazy/neg" (← lazyPairRef.get)
  return rootChecksum a.neg

/- Subtraction, multiplication, division, and inversion execute their checked
implementation through a total wrapper whose extra `Option.getD` projection
is constant-time. Negation is directly certificate-free. These fixed quadratic
inputs isolate the five public routes without asserting an isolation model. -/
setup_fixed_benchmark runLazySub where
  { apiFixedConfig with expectedHash := some 0x751dc56f8c0d0b2e }
setup_fixed_benchmark runLazyMul where
  { apiFixedConfig with expectedHash := some 0xab6b27ac2b367388 }
setup_fixed_benchmark runLazyDiv where
  { apiFixedConfig with expectedHash := some 0x1122363c42d4fe8d }
setup_fixed_benchmark runLazyInv where
  { apiFixedConfig with expectedHash := some 0x49c2d04def0370f2 }
setup_fixed_benchmark runLazyNeg where
  { apiAnchorConfig with expectedHash := some 0xb98e2baa3432a5d3 }

private def canonicalPair? : Option (AlgebraicNumber × AlgebraicNumber) := do
  some (← sqrtTwo?.bind (fun root => root.exact?),
    ← sqrtThree?.bind (fun root => root.exact?))

initialize canonicalPairRef : IO.Ref
    (Option (AlgebraicNumber × AlgebraicNumber)) ← IO.mkRef none

private def getCanonicalPair : IO (AlgebraicNumber × AlgebraicNumber) := do
  match ← canonicalPairRef.get with
  | some pair => pure pair
  | none =>
    let pair ← requireSome "canonical-pair" canonicalPair?
    canonicalPairRef.set (some pair)
    pure pair

private def withCanonicalPair (_case : String)
    (op : AlgebraicNumber → AlgebraicNumber → AlgebraicNumber) :
    Unit → IO UInt64 := fun _ => do
  let (a, b) ← getCanonicalPair
  return algebraicChecksum (op a b)

def runAlgebraicAdd : Unit → IO UInt64 :=
  withCanonicalPair "algebraic/add" (fun a b => a + b)

def runAlgebraicSub : Unit → IO UInt64 :=
  withCanonicalPair "algebraic/sub" (fun a b => a - b)

def runAlgebraicMul : Unit → IO UInt64 :=
  withCanonicalPair "algebraic/mul" (fun a b => a * b)

def runAlgebraicDiv : Unit → IO UInt64 :=
  withCanonicalPair "algebraic/div" (fun a b => a / b)

def runAlgebraicNeg : Unit → IO UInt64 := fun _ => do
  let (a, _) ← getCanonicalPair
  return algebraicChecksum (-a)

def runAlgebraicInv : Unit → IO UInt64 := fun _ => do
  let (a, _) ← getCanonicalPair
  return algebraicChecksum a⁻¹

/- Canonical arithmetic converts the fixed quadratic inputs to lazy roots,
executes exactly the named lazy route, and exactifies its result. Each route is
registered separately so an arithmetic regression is not hidden by a checksum
combining unrelated operations. -/
setup_fixed_benchmark runAlgebraicAdd where
  { apiFixedConfig with expectedHash := some 0xb2956b93cac0235f }
setup_fixed_benchmark runAlgebraicSub where
  { apiFixedConfig with expectedHash := some 0x751dc56f8c0d0b2e }
setup_fixed_benchmark runAlgebraicMul where
  { apiFixedConfig with expectedHash := some 0xab6b27ac2b367388 }
setup_fixed_benchmark runAlgebraicDiv where
  { apiFixedConfig with expectedHash := some 0x1122363c42d4fe8d }
setup_fixed_benchmark runAlgebraicNeg where
  { apiFixedConfig with expectedHash := some 0xfd13c19e59cd6f82 }
setup_fixed_benchmark runAlgebraicInv where
  { apiFixedConfig with expectedHash := some 0x49c2d04def0370f2 }

initialize rationalInputRef : IO.Ref Rat ← IO.mkRef (7 / 5 : Rat)

def runAlgebraicConstructors : Unit → IO UInt64 := fun _ => do
  let q ← rationalInputRef.get
  let direct := AlgebraicNumber.ofRat q
  let adjoin := direct.toQAdjoin
  let natCast := (q.num.natAbs : AlgebraicNumber)
  let intCast := (q.num : AlgebraicNumber)
  -- `One` and fallback `OfNat` are closed literal forms of the same `ofRat`
  -- route; keep their values in the digest as correctness anchors while the
  -- runtime-fed forms above measure the constructor.
  let one := (1 : AlgebraicNumber)
  let ofNat := (4 : AlgebraicNumber)
  return mixHash (algebraicChecksum direct)
    (mixHash (fixedChecksum adjoin)
      (mixHash (algebraicChecksum natCast)
        (mixHash (algebraicChecksum intCast)
          (mixHash (algebraicChecksum one) (algebraicChecksum ofNat)))))

def runAlgebraicScalars : Unit → IO UInt64 := fun _ => do
  let (a, _) ← getCanonicalPair
  return mixHash (algebraicChecksum ((7 / 5 : Rat) • a))
    (mixHash (algebraicChecksum ((3 : Nat) • a))
      (algebraicChecksum ((-2 : Int) • a)))

def runAlgebraicNatPow : Unit → IO UInt64 := fun _ => do
  let (a, _) ← getCanonicalPair
  return algebraicChecksum (a ^ (7 : Nat))

def runAlgebraicIntPow : Unit → IO UInt64 := fun _ => do
  let (a, _) ← getCanonicalPair
  return algebraicChecksum (a ^ (-5 : Int))

/- `ofRat`, `NatCast`, `IntCast`, and the fallback `OfNat` all enter the same
checked linear-polynomial constructor; one grouped fixed registration honestly
covers that shared route. The three scalar instances likewise differ only in
their constant-time conversion to `Rat` before the same canonical product.
Natural and negative integer powers are kept separate because the latter adds
the public inverse route after repeated squaring. -/
setup_fixed_benchmark runAlgebraicConstructors where {
  apiFixedConfig with expectedHash := some 0x4468729ce98284ed
}
setup_fixed_benchmark runAlgebraicScalars where {
  apiFixedConfig with expectedHash := some 0x1ce92fc1022809fb
}
setup_fixed_benchmark runAlgebraicNatPow where {
  apiFixedConfig with expectedHash := some 0xd753d52eb25eb5dd
}
setup_fixed_benchmark runAlgebraicIntPow where {
  apiFixedConfig with expectedHash := some 0x9feb9fb408e711ea
}

initialize zeroRepRef : IO.Ref (Option (RefinedIsolation ZPoly.X)) ←
  IO.mkRef (some AlgebraicNumber.zeroRep)

initialize zeroNumberRef : IO.Ref AlgebraicNumber ←
  IO.mkRef AlgebraicNumber.zero

def runZeroDecisions : Unit → IO UInt64 := fun _ => do
  let zeroRep ← requireSome "zero/representative" (← zeroRepRef.get)
  let canonical ← zeroNumberRef.get
  let root := canonical.toRoot
  return mixHash (squareChecksum zeroRep.1.square)
    (mixHash (hash zeroRep.containsZero)
      (mixHash (hash root.isZero) (hash canonical.isZero)))

/- `zeroRep` is a closed certified accessor retained as a hash anchor. The
runtime-fed representative and zero number execute `containsZero` and both
public zero predicates, including the true `AlgebraicRoot.isZero` branch that
reaches the containment test. Grouping these constant-time declarations avoids
four ceremonial registrations; this target is a correctness/protocol anchor,
not Phase-4 performance evidence. -/
setup_fixed_benchmark runZeroDecisions where {
  apiAnchorConfig with expectedHash := some 0x071179c329e9a368
}

private structure AlgebraicPolyInput where
  coefficients : Array AlgebraicNumber
  left : AlgebraicPoly
  right : AlgebraicPoly

private instance : Hashable AlgebraicPolyInput where
  hash input := mixHash (hash input.coefficients.size)
    (mixHash (hash input.left.size) (hash input.right.size))

private instance : Inhabited AlgebraicPolyInput :=
  ⟨⟨#[], AlgebraicPoly.ofArray #[], AlgebraicPoly.ofArray #[]⟩⟩

def prepAlgebraicPolyInput (n : Nat) : AlgebraicPolyInput :=
  let one := AlgebraicNumber.ofRat 1
  let zeros := Array.replicate (max n 1) AlgebraicNumber.zero
  let coefficients := #[one] ++ zeros
  -- Build equal coefficient arrays independently, so the equality benchmark
  -- cannot be discharged by pointer identity.
  let leftDense := (Array.range (max n 1)).map fun _ => one
  let rightDense := (Array.range (max n 1)).map fun _ => AlgebraicNumber.ofRat 1
  ⟨coefficients, AlgebraicPoly.ofArray leftDense, AlgebraicPoly.ofArray rightDense⟩

initialize algebraicPolyAccessorRef : IO.Ref (Option AlgebraicPolyInput) ←
  IO.mkRef none

private def getAlgebraicPolyAccessorInput : IO AlgebraicPolyInput := do
  match ← algebraicPolyAccessorRef.get with
  | some input => pure input
  | none =>
    let input := prepAlgebraicPolyInput 8
    algebraicPolyAccessorRef.set (some input)
    pure input

def runAlgebraicPolyOfArray (input : AlgebraicPolyInput) : UInt64 :=
  let f := AlgebraicPoly.ofArray input.coefficients
  mixHash (hash f.size) (hash f.isZero)

def runAlgebraicPolyBeq (input : AlgebraicPolyInput) : UInt64 :=
  hash (AlgebraicPoly.beq input.left input.right)

/- Cost model. `ofArray` removes a suffix of `n` canonical zeros and calls the
constant-time minimal-polynomial zero predicate once per element, hence linear
work in the supplied array length. -/
setup_benchmark runAlgebraicPolyOfArray n => n
  with prep := prepAlgebraicPolyInput
  where {
    -- The operation is sub-microsecond through 64 entries, so extend the
    -- schedule until the suffix traversal clearly dominates fixed call cost.
    paramFloor := 4
    paramCeiling := 2048
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 30.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Cost model. Equality of two length-`n` arrays traverses every coefficient;
each canonical coefficient comparison has fixed linear-polynomial degree on
this fixture, so the public `beq` route is linear. -/
setup_benchmark runAlgebraicPolyBeq n => n
  with prep := prepAlgebraicPolyInput
  where {
    paramFloor := 4
    paramCeiling := 256
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256]
    maxSecondsPerCall := 30.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

def runAlgebraicPolyAccessors : Unit → IO UInt64 := fun _ => do
  let input ← getAlgebraicPolyAccessorInput
  let f := input.left
  return mixHash (algebraicChecksum (f.coeff 3))
    (mixHash (hash f.coeffs.size)
      (mixHash (hash f.size) (mixHash (hash f.degree?) (hash f.isZero))))

/- `coeff` is one `Array.getD`; `coeffs`, `size`, `isZero`, and `degree?` are
constant-time projections/branches on the stored normalized array. Their
shared runtime-fed fixed registration is a correctness/protocol anchor rather
than a performance claim. -/
setup_fixed_benchmark runAlgebraicPolyAccessors where {
  apiAnchorConfig with expectedHash := some 0x256c50de964804d1
}

private structure MajorantInput where
  f : DensePoly Rat

private instance : Hashable MajorantInput where
  hash input := hash input.f.toArray

private instance : Inhabited MajorantInput := ⟨⟨1⟩⟩

def prepMajorantInput (n : Nat) : MajorantInput :=
  ⟨DensePoly.ofCoeffs <| (Array.range (max n 1)).map fun i =>
    mkRat (Int.ofNat (i % 11 + 1)) (i % 6 + 1)⟩

def runEvalMajorant (input : MajorantInput) : UInt64 :=
  hash (Disambiguation.evalMajorant input.f QAdjoin.ratAbsCeil sqrtTwoPoly)

initialize majorantFixedRef : IO.Ref (Option MajorantInput) ← IO.mkRef none

private def getMajorantFixedInput : IO MajorantInput := do
  match ← majorantFixedRef.get with
  | some input => pure input
  | none =>
    let input := prepMajorantInput 4096
    majorantFixedRef.set (some input)
    pure input

def runEvalMajorantFixed : Unit → IO UInt64 := fun _ => do
  return runEvalMajorant (← getMajorantFixedInput)

/- Mode 3. The independently derived `n²` linear-bit model was tested first:
`evalMajorant` performs `n` exact-Nat recurrence steps on state whose bit width
grows linearly. A 32-through-4096 sweep remained faster than that model by
`n^0.689` after the small-Nat/GMP transition, so it supplies no honest
two-sided wall model; no published bound covers this executable as a dominant
profiled phase. The largest controlled input takes 6.0 ms. A 200 ms zero-grace
whole-child budget includes lazy fixture setup, warmup, and more than 3x the
43 ms clean spawn-floor-plus-operation baseline. -/
setup_fixed_benchmark runEvalMajorantFixed where {
  apiFixedConfig with
  maxSecondsPerCall := 0.2
  expectedHash := some 0xd906e705ab7ed934
}

/-! # Parametric ladder fixtures -/

/-- `X^m - 2`, Eisenstein-irreducible at `2` for every `m ≥ 1`. -/
private def xPowSubTwo (m : Nat) : ZPoly :=
  DensePoly.ofList ((-2 : Int) :: List.replicate (m - 1) 0 ++ [1])

/-- Deterministic dense all-nonzero rational coefficients keyed by length and
salt: alternating signs, numerators cycling modulo 11 and denominators modulo
6, so both are bounded independently of `len` and a ladder over `len` varies
the modulus degree alone. Every denominator is in `1 .. 6`, so the reduced
vector's common denominator divides `lcm(1, ..., 6) = 60`.

The bound matters. The earlier form used numerator `±(i + salt + 1)` over
denominator `i + 2`. Since `gcd (i + salt + 1) (i + 2) = gcd (salt - 1) (i + 2)`,
coefficient `i` reduces to denominator `(i + 2) / gcd (i + 2) (salt - 1)`, and
the common denominator is the lcm of those. For the fixed salts in use that
lcm still has `Θ(len)` bit length — it differs from `lcm (2, …, len + 1)` only
by the divisors of `salt - 1`, a constant. So a ladder built on it varied
coefficient height together with degree: not the controlled one-parameter
ladder [PLAN/Phase4.md](../../PLAN/Phase4.md) requires, and no bounded-height
cost model could fit it.

`prepAlgPolyInput` shares this helper for the same reason. -/
private def denseRatCoeff (i salt : Nat) : Rat :=
  let sign : Int := if (i + salt) % 2 == 0 then 1 else -1
  mkRat (sign * Int.ofNat ((i * 7 + salt * 3) % 11 + 1)) ((i * 5 + salt) % 6 + 1)

private def denseRatCoeffs (len salt : Nat) : Array Rat :=
  (Array.range len).map (denseRatCoeff · salt)

/-- Floor the positive `n`th root of `a` by integer Newton iteration. -/
private def nthRootFloor (a n : Nat) : Nat :=
  if n = 0 then 0 else
    let rec go : Nat → Nat → Nat
      | 0, x => x
      | fuel + 1, x =>
        let y := ((n - 1) * x + a / x ^ (n - 1)) / n
        if x ≤ y then x else go fuel y
    go (a.log2 + 2) (2 ^ ((a.log2 + n) / n))

#guard nthRootFloor 2 1 == 2
#guard nthRootFloor 16 2 == 4
#guard nthRootFloor 17 2 == 4
#guard nthRootFloor 4096 6 == 4

/-- A Mahler-precision dyadic approximation to the positive real root of
`X^n - 2`. Integer Newton iteration computes
`⌊2^(1/n) * 2^q⌋` from `2^(qn+1)`, where `q = mahlerPrec p`; the subsequent
atom checker supplies all certification, so the approximation is not trusted. -/
private def ladderRootSeed (p : ZPoly) (n : Nat) : DyadicSquare :=
  let q := mahlerPrec p
  let scaled := 2 ^ (q * n + 1)
  let center := nthRootFloor scaled n
  ⟨Dyadic.ofIntWithPrec (Int.ofNat center) q, 0, q⟩

/-- Deterministically certify the positive real root from its untrusted dyadic
approximation. The local single-atom search does not construct or refine the
other complex roots. -/
private def positiveBinomialRoot? (p : ZPoly) (n : Nat) :
    Option (RefinedIsolation p) :=
  isolateOne? p (mahlerPrec p : Int) (ladderRootSeed p n)

/-- Deterministic refined isolation for a squarefree polynomial: run the
bounded all-roots isolator at separation depth and take its first atom. This
general constructor remains the fixture for ladders whose polynomial is not
the binomial used to choose `ladderRootSeed`. -/
private def refinedOf? (p : ZPoly) (h : HasOnlySimpleRoots p) :
    Option (RefinedIsolation p) := do
  let isolations ← isolate p h (separationDepth p : Int)
  let iso ← isolations[0]?
  iso.toRefined?

/-- Select an enclosing-polynomial isolation that meets the first root of a
candidate factor. This pins exactification fixtures to the intended factor
rather than to the enclosing isolator's emission order. -/
private def refinedFactor? (p q : ZPoly) (hp : HasOnlySimpleRoots p)
    (hq : HasOnlySimpleRoots q) : Option (RefinedIsolation p) := do
  let pIsolations ← isolate p hp (separationDepth p : Int)
  let pRefined ← pIsolations.mapM DyadicRootIsolation.toRefined?
  let qIsolations ← isolate q hq (separationDepth q : Int)
  let qIsolation ← qIsolations[0]?
  let qRefined ← qIsolation.toRefined?
  pRefined.toList.find? fun rep =>
    rep.1.square.discsMeet qRefined.1.square

/-- Deterministic factorization-lazy root of a primitive positive-leading
squarefree polynomial (the first isolated root). -/
private def mkLadderRoot? (p : ZPoly) : Option AlgebraicRoot :=
  if hprim : ZPoly.content p = 1 then
    if hlc : 0 < p.leadingCoeff then
      if hdeg : 0 < p.degree?.getD 0 then
        if hsf : HasOnlySimpleRoots p then
          match refinedOf? p hsf with
          | some rep =>
            some { p := p, prim := hprim, pos_lc := hlc, pos_degree := hdeg
                   squarefree := hsf, x := SimpleRoot.mk rep, rep := rep
                   rep_mk := rfl }
          | none => none
        else none
      else none
    else none
  else none

/-- Factorization-lazy root of `p` selected from the candidate factor `q`. -/
private def mkFactorRoot? (p q : ZPoly) : Option AlgebraicRoot :=
  if hprim : ZPoly.content p = 1 then
    if hlc : 0 < p.leadingCoeff then
      if hdeg : 0 < p.degree?.getD 0 then
        if hsf : HasOnlySimpleRoots p then
          if hq : HasOnlySimpleRoots q then
            match refinedFactor? p q hsf hq with
            | some rep =>
              some { p := p, prim := hprim, pos_lc := hlc, pos_degree := hdeg
                     squarefree := hsf, x := SimpleRoot.mk rep, rep := rep
                     rep_mk := rfl }
            | none => none
          else none
        else none
      else none
    else none
  else none

/-- Prepared degree-`m` fixed-field arithmetic fixture: the field
`ℚ(2^{1/m})` with two dense all-nonzero-coordinate elements. -/
private structure FieldInput where
  p : ZPoly
  x : SimpleRoot p
  rep : RefinedIsolation p
  rep_mk : SimpleRoot.mk rep = x
  a : QAdjoin p x
  b : QAdjoin p x

private instance : Hashable FieldInput where
  hash input :=
    mixHash (hash input.p.toArray)
      (mixHash (fixedChecksum input.a) (fixedChecksum input.b))

private instance : Inhabited FieldInput :=
  ⟨{ p := sqrtTwoPoly, x := sqrtTwoRoot, rep := sqrtTwoRep, rep_mk := rfl,
      a := fixedSqrtTwo, b := fixedSqrtTwo }⟩

def prepFieldInput (n : Nat) : FieldInput :=
  let m := max n 2
  let p := xPowSubTwo m
  match positiveBinomialRoot? p m with
  | some rep =>
    let x := SimpleRoot.mk rep
    { p := p, x := x, rep := rep, rep_mk := rfl
      a := QAdjoin.reduce p x (DensePoly.ofCoeffs (denseRatCoeffs m 3))
      b := QAdjoin.reduce p x (DensePoly.ofCoeffs (denseRatCoeffs m 7)) }
  | none => panic! "prepFieldInput: isolation failed"

/-- Prepared inversion fixture: `FieldInput` data plus the runtime-checked
irreducibility instance, decided in prep so no factorization work leaks
into the timed extended-gcd region. -/
private structure InvInput where
  p : ZPoly
  x : SimpleRoot p
  rep : RefinedIsolation p
  rep_mk : SimpleRoot.mk rep = x
  a : QAdjoin p x
  b : QAdjoin p x
  checked : Option (PLift (ZPoly.CheckedIrreducible p))

private instance : Hashable InvInput where
  hash input := mixHash (hash input.p.toArray)
    (mixHash (fixedChecksum input.a) (fixedChecksum input.b))

private instance : Inhabited InvInput :=
  ⟨{ p := sqrtTwoPoly, x := sqrtTwoRoot, rep := sqrtTwoRep, rep_mk := rfl,
      a := fixedSqrtTwo, b := fixedSqrtTwo, checked := none }⟩

def prepInvInput (n : Nat) : InvInput :=
  let m := max n 2
  let p := xPowSubTwo m
  if hirr : ZPoly.isIrreducible p = true then
    if hdeg : 0 < p.degree?.getD 0 then
      match positiveBinomialRoot? p m with
      | some rep =>
        let x := SimpleRoot.mk rep
        { p := p, x := x, rep := rep, rep_mk := rfl
          a := QAdjoin.reduce p x (DensePoly.ofCoeffs (denseRatCoeffs m 5))
          b := QAdjoin.reduce p x (DensePoly.ofCoeffs (denseRatCoeffs m 9))
          checked := some ⟨⟨hirr, hdeg⟩⟩ }
      | none => panic! "prepInvInput: isolation failed"
    else panic! "prepInvInput: degree check failed"
  else panic! "prepInvInput: irreducibility check failed"

/-! ## Untimed normalized extended-gcd diagnostics -/

private def natBitLength (n : Nat) : Nat :=
  if n = 0 then 0 else n.log2 + 1

private structure RatPolyBits where
  numMax : Nat
  denMax : Nat
  total : Nat
  limbs : Nat

private def ratPolyBits (p : DensePoly Rat) : RatPolyBits :=
  p.coeffs.foldl (init := { numMax := 0, denMax := 0, total := 0, limbs := 0 }) fun stats q =>
    let numBits := natBitLength q.num.natAbs
    let denBits := natBitLength q.den
    { numMax := max stats.numMax numBits
      denMax := max stats.denMax denBits
      total := stats.total + numBits + denBits
      limbs := stats.limbs + (numBits + 63) / 64 + (denBits + 63) / 64 }

private structure InvChainStep where
  index : Nat
  dividendDegree : Nat
  divisorDegree : Nat
  nextRemainderDegree : Nat
  nextRemainderZero : Bool
  divisorNumMax : Nat
  divisorDenMax : Nat
  divisorBits : Nat
  cofactorNumMax : Nat
  cofactorDenMax : Nat
  coefficientOps : Nat
  bitWork : Nat
  limbWork : Nat

private def degreeD (p : DensePoly Rat) : Nat :=
  p.degree?.getD 0

/- Replay `xgcdLeftMonicAux` exactly, retaining diagnostics outside the timed
benchmark. `coefficientOps` counts the scalar slots touched by normalization,
long division, the one-sided Bezout product, and subtraction. `bitWork` is a
linear-width proxy: it charges the normalized scale outputs, the scale factor,
and the input/output polynomials of the remaining operations at this step.
`limbWork` applies the same charge after rounding each numerator and denominator
to 64-bit limbs. These proxies do not model the gcd inside `Rat.normalize` or
the superlinear cost of large-integer arithmetic; their purpose is to avoid
charging every early operation the largest width reached later in the chain. -/
private def invChainStepsAux (r₀ s₀ r₁ s₁ : DensePoly Rat) :
    Nat → Nat → Array InvChainStep → Array InvChainStep
  | 0, _, steps => steps
  | fuel + 1, index, steps =>
      if r₁.isZero then steps
      else
        let c := 1 / r₁.leadingCoeff
        let r₁' := DensePoly.scale c r₁
        let s₁' := DensePoly.scale c s₁
        let qr := DensePoly.divMod r₀ r₁'
        let product := qr.1 * s₁'
        let nextS := s₀ - product
        let divisorBits := ratPolyBits r₁'
        let cofactorBits := ratPolyBits s₁'
        let quotientBits := ratPolyBits qr.1
        let nextRemainderBits := ratPolyBits qr.2
        let nextCofactorBits := ratPolyBits nextS
        let s₀Bits := ratPolyBits s₀
        let productBits := ratPolyBits product
        let cNumBits := natBitLength c.num.natAbs
        let cDenBits := natBitLength c.den
        let cBits := cNumBits + cDenBits
        let cLimbs := (cNumBits + 63) / 64 + (cDenBits + 63) / 64
        let divisions :=
          if r₀.size < r₁'.size then 0
          else (r₀.size - r₁'.size + 1) * r₁'.size
        let coefficientOps := r₁.size + s₁.size + divisions +
          qr.1.size * s₁'.size + max s₀.size product.size
        let normalizeWork := divisorBits.total + r₁.size * cBits +
          cofactorBits.total + s₁.size * cBits
        let divisionWork := r₁'.size * quotientBits.total +
          (if r₀.size < r₁'.size then 0
           else (r₀.size - r₁'.size + 1) * divisorBits.total) +
          nextRemainderBits.total
        let productWork := s₁'.size * quotientBits.total +
          qr.1.size * cofactorBits.total
        let subtractionWork := s₀Bits.total + productBits.total + nextCofactorBits.total
        let normalizeLimbWork := divisorBits.limbs + r₁.size * cLimbs +
          cofactorBits.limbs + s₁.size * cLimbs
        let divisionLimbWork := r₁'.size * quotientBits.limbs +
          (if r₀.size < r₁'.size then 0
           else (r₀.size - r₁'.size + 1) * divisorBits.limbs) +
          nextRemainderBits.limbs
        let productLimbWork := s₁'.size * quotientBits.limbs +
          qr.1.size * cofactorBits.limbs
        let subtractionLimbWork := s₀Bits.limbs + productBits.limbs +
          nextCofactorBits.limbs
        let step :=
          { index := index
            dividendDegree := degreeD r₀
            divisorDegree := degreeD r₁'
            nextRemainderDegree := degreeD qr.2
            nextRemainderZero := qr.2.isZero
            divisorNumMax := divisorBits.numMax
            divisorDenMax := divisorBits.denMax
            divisorBits := divisorBits.total
            cofactorNumMax := cofactorBits.numMax
            cofactorDenMax := cofactorBits.denMax
            coefficientOps := coefficientOps
            bitWork := normalizeWork + divisionWork + productWork + subtractionWork
            limbWork := normalizeLimbWork + divisionLimbWork + productLimbWork +
              subtractionLimbWork }
        invChainStepsAux r₁' s₁' qr.2 nextS fuel (index + 1) (steps.push step)

private def invChainSteps (input : InvInput) : Array InvChainStep :=
  invChainStepsAux input.a.coeffs (1 : DensePoly Rat)
    (ZPoly.toRatPoly input.p) 0
    (input.a.coeffs.size + (ZPoly.toRatPoly input.p).size + 1) 0 #[]

private def printInvChainSteps : IO Unit := do
  IO.println "n,step,dividend_degree,divisor_degree,next_remainder_degree,next_remainder_zero,divisor_num_max,divisor_den_max,divisor_total_bits,cofactor_num_max,cofactor_den_max,coefficient_ops,bit_work,limb_work"
  for n in #[4, 8, 16, 32, 48, 64, 96] do
    for step in invChainSteps (prepInvInput n) do
      IO.println s!"{n},{step.index},{step.dividendDegree},{step.divisorDegree},{step.nextRemainderDegree},{step.nextRemainderZero},{step.divisorNumMax},{step.divisorDenMax},{step.divisorBits},{step.cofactorNumMax},{step.cofactorDenMax},{step.coefficientOps},{step.bitWork},{step.limbWork}"

def runQAdjoinAddLadder (input : FieldInput) : UInt64 :=
  fixedChecksum (input.a + input.b)

def runQAdjoinSubLadder (input : FieldInput) : UInt64 :=
  fixedChecksum (input.a - input.b)

def runQAdjoinNegLadder (input : FieldInput) : UInt64 :=
  fixedChecksum (-input.a)

def runQAdjoinSmulLadder (input : FieldInput) : UInt64 :=
  fixedChecksum ((7 / 5 : Rat) • input.a)

def runQAdjoinMulLadder (input : FieldInput) : UInt64 :=
  fixedChecksum (input.a * input.b)

def runQAdjoinApproxLadder (input : FieldInput) : UInt64 :=
  let result := input.a.approx input.rep input.rep_mk 64
  mixHash (squareChecksum result.1.1.square)
    (mixHash (dyadicChecksum result.2.re)
      (mixHash (dyadicChecksum result.2.im) (dyadicChecksum result.2.radius)))

def runQAdjoinInvLadder (input : InvInput) : UInt64 :=
  match input.checked with
  | some ⟨inst⟩ =>
    letI : ZPoly.CheckedIrreducible input.p := inst
    fixedChecksum input.a⁻¹
  | none => 0

def runQAdjoinDivLadder (input : InvInput) : UInt64 :=
  match input.checked with
  | some ⟨inst⟩ =>
    letI : ZPoly.CheckedIrreducible input.p := inst
    fixedChecksum (input.a / input.b)
  | none => 0

/- Cost model. `QAdjoin` addition adds the two reduced rational coefficient
vectors coordinatewise: exactly `min` sizes rational additions plus a copy of
the tail, `O(n)` operations for two dense degree-`(n-1)` operands over the
degree-`n` modulus. Input numerators and denominators are bounded by the
fixture schedule, so each rational operation is `O(1)` words and the declared
wall model is linear. -/
setup_benchmark runQAdjoinAddLadder n => n
  with prep := prepFieldInput
  where {
    -- The degree-128 ceiling supplies six doublings of the linear operation's
    -- controlled input dimension and matches the multiplication domain. The
    -- single-root fixture is certified independently of the other roots.
    paramFloor := 4
    paramCeiling := 128
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128]
    maxSecondsPerCall := 120.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Cost model. Subtraction traverses the two reduced dense coordinate vectors
once and performs one bounded-height rational subtraction per occupied slot,
the same linear route as addition but through the public `Sub` instance. -/
setup_benchmark runQAdjoinSubLadder n => n
  with prep := prepFieldInput
  where {
    paramFloor := 4
    paramCeiling := 128
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128]
    maxSecondsPerCall := 120.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Cost model. Negation maps rational negation over the `n` canonical
coordinates and `reduce` only trims a zero suffix; bounded coefficient height
makes the public `Neg` route linear in the modulus degree. -/
setup_benchmark runQAdjoinNegLadder n => n
  with prep := prepFieldInput
  where {
    paramFloor := 4
    paramCeiling := 128
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128]
    maxSecondsPerCall := 120.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Cost model. Rational scalar action scales each of the `n` reduced
coordinates by one fixed rational and then trims; the scalar and fixture
heights are bounded, so this is `O(n)` word operations. -/
setup_benchmark runQAdjoinSmulLadder n => n
  with prep := prepFieldInput
  where {
    paramFloor := 4
    paramCeiling := 128
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128]
    maxSecondsPerCall := 120.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Cost model. Dense schoolbook multiplication of two degree-`(n-1)` rational
polynomials performs `O(n^2)` coefficient multiply/adds, and the subsequent
reduction of the degree-`(2n-2)` product modulo the sparse monic degree-`n`
relation `X^n - 2` retires `O(n)` excess coefficients at `O(1)` each. The
quadratic convolution dominates; fixture coefficient heights are bounded, so
the declared model is `n^2`. -/
setup_benchmark runQAdjoinMulLadder n => n * n
  with prep := prepFieldInput
  where {
    -- Six doublings reach degree 128, where the timed dense multiplication is
    -- in the millisecond regime and still far below its per-call ceiling.
    paramFloor := 4
    paramCeiling := 128
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128]
    maxSecondsPerCall := 120.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

initialize qAdjoinApproxRef : IO.Ref (Option FieldInput) ← IO.mkRef none

private def getQAdjoinApproxInput : IO FieldInput := do
  match ← qAdjoinApproxRef.get with
  | some input => pure input
  | none =>
    let input := prepFieldInput 128
    qAdjoinApproxRef.set (some input)
    pure input

def runQAdjoinApprox : Unit → IO UInt64 := fun _ => do
  return runQAdjoinApproxLadder (← getQAdjoinApproxInput)

/- Mode 3. The independently derived conservative bit model is `O(n⁴)`: the
guard makes the refined root ball `O(n)` bits, exact Horner multiplication
grows the accumulator to `O(n²)` bits, and the sum of schoolbook products is
quartic. The controlled 4-through-128 sweep was faster by `n^2.262`, while the
former quadratic proxy accelerated to a local exponent 2.55 at the top and
was not a stable wall model. With no published bound for this exact-ball
implementation, retain the 16.9 ms degree-128 case. Preparing its certified
degree-128 field takes the whole clean child baseline to 2.03 s; a 7 s
zero-grace whole-child budget is over 3x that observed baseline, including lazy
setup and warmup rather than hiding them in process initialization. -/
setup_fixed_benchmark runQAdjoinApprox where {
  apiFixedConfig with
  maxSecondsPerCall := 7.0
  expectedHash := some 0xd65a5f2477fcfa3a
}

/- Cost model. Inversion runs the monic-normalized polynomial extended gcd of
the degree-`(n-1)` element against `X^n - 2` over `ℚ`. On this controlled
bounded-height family the Euclidean chain drops one degree at every nonterminal
step. Long division and the one-sided Bezout update consequently touch `Θ(n)`
rational coefficient slots at each of `Θ(n)` steps.

The untimed `qadjoin-inv-chain-stats` replay records each step's degrees and
separate numerator/denominator widths. The controlled family's recorded widths
are linear in `n`, so the `Θ(n²)` coefficient slots give a cubic linear-bit
aggregate. Rounding each numerator and denominator up to a 64-bit limb adds at
most a constant per slot, hence a quadratic lower-order term: `A*n³ + B*n²`.
A least-squares decomposition of the deterministic limb counts over the
verdict region `n = 8 .. 96` gives `A = 1.424`, `B = 9.563`, and `B/A = 6.72`.
Rounding that dimensionless finite-word transition to 7 yields the declared
`n² * (n + 7)`. This calibrates the lower-order term from operation/operand
counts before the timed rerun; it is not inferred from benchmark timings. The
proxy charges rational operations linearly in operand limbs and does not model
the gcd performed by `Rat.normalize`.

The general Hadamard argument still permits `O(n log n)`-bit coefficients and
therefore the SPEC retains the conservative `O(n³ log n)` worst-case bound. -/
setup_benchmark runQAdjoinInvLadder n => n * n * (n + 7)
  with prep := prepInvInput
  where {
    -- The single-root fixture removes the former setup bottleneck. The
    -- degree-96 ceiling keeps scientific reruns practical while the denser
    -- upper schedule exposes coefficient growth beyond the small-degree regime.
    paramFloor := 4
    paramCeiling := 96
    paramSchedule := .custom #[4, 8, 16, 32, 48, 64, 96]
    maxSecondsPerCall := 120.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Cost model. Public division computes the divisor inverse through the same
monic-normalized extended-gcd chain as `runQAdjoinInvLadder`, then performs one
quadratic fixed-field multiplication. Thus `n²(n + 7)` remains the dominant
finite-word proxy and this separate target ensures the `Div` composition is
compiled and measured rather than inferred. -/
setup_benchmark runQAdjoinDivLadder n => n * n * (n + 7)
  with prep := prepInvInput
  where {
    paramFloor := 4
    paramCeiling := 96
    paramSchedule := .custom #[4, 8, 16, 32, 48, 64, 96]
    maxSecondsPerCall := 120.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-! # Lazy-arithmetic ladders -/

/-- Prepared eliminant-construction pair: `X^m - 2` against the fixed
quadratic `X^2 - 3` (no isolation is needed for construction alone). -/
private structure EliminantInput where
  p : ZPoly
  q : ZPoly

private instance : Hashable EliminantInput where
  hash input := mixHash (hash input.p.toArray) (hash input.q.toArray)

private instance : Inhabited EliminantInput := ⟨⟨sqrtTwoPoly, sqrtThreePoly⟩⟩

def prepEliminantInput (n : Nat) : EliminantInput :=
  ⟨xPowSubTwo (max n 2), sqrtThreePoly⟩

def runAddEliminantLadder (input : EliminantInput) : UInt64 :=
  polyChecksum (ZPoly.addEliminant input.p input.q)

/-- Prepared lazy-addition pair: the first isolated root of `X^m - 2`
against `√3`, degree product `2m` (merge-facing ceiling `20`). -/
private structure LazyAddInput where
  a : Option AlgebraicRoot
  b : Option AlgebraicRoot

private instance : Hashable LazyAddInput where
  hash input :=
    mixHash ((input.a.map rootChecksum).getD 0) ((input.b.map rootChecksum).getD 0)

private instance : Inhabited LazyAddInput := ⟨⟨none, none⟩⟩

def prepLazyAddInput (n : Nat) : LazyAddInput :=
  ⟨mkLadderRoot? (xPowSubTwo (max n 2)), sqrtThree?⟩

private def lazyAddChecksum (input : LazyAddInput) : UInt64 :=
  match input.a, input.b with
  | some a, some b =>
    match a.add? b with
    | some c => rootChecksum c
    | none => 1
  | _, _ => 0

/- Cost model. `addEliminant (X^n - 2) (X^2 - 3)` is the Brown resultant in
`y` of a degree-`n` polynomial with constant coefficients against the monic
`y`-quadratic `(t - y)^2 - 3` whose coefficients have `t`-degree at most 2.
The first (monic) division performs `O(n)` elimination steps whose remainder
coefficients grow to `t`-degree `O(n)`, `O(n^2)` integer coefficient
operations in total; the short tail of the chain on `y`-degree `≤ 1`
remainders with `t`-degree-`O(n)` coefficients adds the same order. Integer
bit growth along the chain is modelled with the logarithmic limb-growth
proxy used by the HexResultant registrations, so the declared wall model is
`n^2 * log n`. -/
setup_benchmark runAddEliminantLadder n => n * n * (Nat.log2 (n + 2) + 1)
  with prep := prepEliminantInput
  where {
    -- The old `4 .. 64` schedule left three contributing rungs, all with
    -- sub-millisecond calls, and its fitted `C` had not settled (178 .. 321,
    -- beta = +0.258). Extending to 256 puts four decades of work under the
    -- fit and flattens `C` to 144 .. 166 at beta = +0.015 against the same
    -- declared model.
    paramFloor := 4
    paramCeiling := 256
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256]
    maxSecondsPerCall := 30.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

initialize lazyAddLadderRef : IO.Ref (Option LazyAddInput) ← IO.mkRef none

private def getLazyAddLadderInput : IO LazyAddInput := do
  match ← lazyAddLadderRef.get with
  | some input => pure input
  | none =>
    let input := prepLazyAddInput 6
    lazyAddLadderRef.set (some input)
    pure input

def runLazyAddLadder : Unit → IO UInt64 := fun _ => do
  return lazyAddChecksum (← getLazyAddLadderInput)

/- Fixed canonical case. The timed `AlgebraicRoot.add?` constructs the sum
eliminant of `X^6 - 2` and `X^2 - 3`, square-free normalizes its degree-12
result, isolates it at the `separationDepth` target, and selects the sum.
The BSSY `Õ(d³ + d²·tau)` theorem is for its `CIsolate` algorithm, not
HexRoots' exact-dyadic fallback, speculative Newton, or global completeness
depth. HexRoots itself gives only a heuristic whole-isolator cost, so no cited
one-parameter wall model applies to this implementation. This project-internal
canonical input is the `n = 6` rung shared by both former schedules and tracks
the SPEC's absolute budget without asserting an asymptotic shape. The historical
`Ladder` name is retained so committed exports continue to identify the same
operation across the mode change. -/
setup_fixed_benchmark runLazyAddLadder where {
  repeats := 3
  maxSecondsPerCall := 12.0
  expectedHash := some 0xc544c942d8336f51
}

/-! # Exactification ladder -/

/-- Prepared certification fixture: a root of `(X^m - 2)(X + 3)` pinned to
the nonlinear candidate, so factor selection always succeeds independently
of the enclosing isolator's emission order. -/
private structure SelectionInput where
  root : Option AlgebraicRoot
  candidate : ZPoly

private instance : Hashable SelectionInput where
  hash input := mixHash ((input.root.map rootChecksum).getD 0)
    (polyChecksum input.candidate)

private instance : Inhabited SelectionInput := ⟨⟨none, 0⟩⟩

def prepExactSelectionInput (n : Nat) : SelectionInput :=
  let factor := xPowSubTwo (max n 2)
  let enclosing := factor * DensePoly.ofList [3, 1]
  ⟨mkFactorRoot? enclosing factor, factor⟩

initialize exactSelectionRef : IO.Ref (Option SelectionInput) ← IO.mkRef none

private def getExactSelection : IO SelectionInput := do
  match ← exactSelectionRef.get with
  | some input => pure input
  | none =>
    let input := prepExactSelectionInput 8
    exactSelectionRef.set (some input)
    pure input

def runExactSelection : Unit → IO UInt64 := fun _ => do
  let input ← getExactSelection
  match input.root with
  | some root =>
    match root.exact? with
    | some a => return polyChecksum a.p
    | none => return 1
  | none => return 0

/- The first isolated root of `(X^8 - 2)(X + 3)` makes exactification inspect
more than one candidate factor, re-isolate the selected candidate against the
enclosing polynomial's precision, and canonicalize it. This is retained as a
fixed certification/selection case: profiling showed that its BZ factorization
is not scaling evidence for the BHKS envelope. -/
setup_fixed_benchmark runExactSelection where {
  repeats := 3, maxSecondsPerCall := 5.0, warmupFirstIter := true,
  expectedHash := some 0xd5512fda51bc6ff6
}

private def exactFactorChecksum (input : SelectionInput) : UInt64 :=
  match input.root with
  | some root =>
    match root.exactFactor? input.candidate with
    | some a => algebraicChecksum a
    | none => 1
  | none => 0

private structure CanonicalInput where
  p : ZPoly
  squarefree : HasOnlySimpleRoots p
  rep : RefinedIsolation p
  nonzero : p ≠ ZPoly.X

private instance : Hashable CanonicalInput where
  hash input := mixHash (polyChecksum input.p)
    (squareChecksum input.rep.1.square)

def prepCanonicalInput (n : Nat) : Option CanonicalInput :=
  let p := xPowSubTwo (max n 2)
  if hsf : HasOnlySimpleRoots p then
    match refinedOf? p hsf with
    | some rep =>
      if hzero : p ≠ ZPoly.X then some ⟨p, hsf, rep, hzero⟩
      else none
    | none => none
  else none

private def canonicalRepChecksum (input : Option CanonicalInput) : UInt64 :=
  match input with
  | some input =>
    match AlgebraicNumber.canonicalRep? input.p input.squarefree input.rep
        input.nonzero with
    | some rep => squareChecksum rep.1.1.square
    | none => 1
  | none => 0

private def exactFactorPrimes : Array Int :=
  #[2, 3, 5, 7, 11, 13, 17, 19]

private def exactFactorFamily (count : Nat) : ZPoly :=
  (exactFactorPrimes.take (max count 2)).foldl
    (fun acc prime => acc * DensePoly.ofList [-prime, 0, 1])
    (1 : ZPoly)

private structure ExactInput where
  root : Option AlgebraicRoot

private instance : Hashable ExactInput where
  hash input := (input.root.map rootChecksum).getD 0

private instance : Inhabited ExactInput := ⟨⟨none⟩⟩

def prepExactInput (n : Nat) : ExactInput :=
  let p := exactFactorFamily n
  ⟨mkLadderRoot? p⟩

private def exactChecksum (input : ExactInput) : UInt64 :=
  match input.root with
  | some root =>
    match root.exact? with
    | some a => algebraicChecksum a
    | none => 1
  | none => 0

private def exactHardPoly : ZPoly :=
  DensePoly.ofList
    [30030, 0, -40361, 0, 20581, 0, -5102, 0, 652, 0, -41, 0, 1]

private def exactHardSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec
      (-101927323007384149321685952252207694872821825932799541131833833248670938989)
      244,
    0, 241⟩

private def exactHardRep : RefinedIsolation exactHardPoly :=
  ⟨⟨exactHardSquare, .ofWitness (by
      set_option maxRecDepth 100000 in
      set_option exponentiation.threshold 10000 in decide)⟩,
    by
      set_option maxRecDepth 100000 in
      set_option exponentiation.threshold 10000 in decide⟩

private def exactHardInput : ExactInput :=
  if hsf : HasOnlySimpleRoots exactHardPoly then
    ⟨some
      { p := exactHardPoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsf
        x := SimpleRoot.mk exactHardRep
        rep := exactHardRep
        rep_mk := rfl }⟩
  else ⟨none⟩

private def factorHardCandidate : ZPoly :=
  DensePoly.ofList [-2, 0, 0, 0, 0, 0, 0, 0, 1]

private def factorHardPoly : ZPoly :=
  DensePoly.ofList [-6, -2, 0, 0, 0, 0, 0, 0, 3, 1]

private def factorHardSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec (-932209243062424318066219) 80,
    Dyadic.ofIntWithPrec (-932209243062424318066219) 80, 77⟩

private def factorHardRep : RefinedIsolation factorHardPoly :=
  ⟨⟨factorHardSquare, .ofWitness (by
      set_option maxRecDepth 100000 in
      set_option exponentiation.threshold 10000 in decide)⟩,
    by
      set_option maxRecDepth 100000 in
      set_option exponentiation.threshold 10000 in decide⟩

private def factorHardInput : SelectionInput :=
  if hsf : HasOnlySimpleRoots factorHardPoly then
    ⟨some
      { p := factorHardPoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsf
        x := SimpleRoot.mk factorHardRep
        rep := factorHardRep
        rep_mk := rfl },
      factorHardCandidate⟩
  else ⟨none, factorHardCandidate⟩

private def canonicalHardSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec (-55564000789071579) 56,
    Dyadic.ofIntWithPrec (-55564000789071579) 56, 53⟩

private def canonicalHardRep : RefinedIsolation factorHardCandidate :=
  ⟨⟨canonicalHardSquare, .ofWitness (by
      set_option maxRecDepth 100000 in
      set_option exponentiation.threshold 10000 in decide)⟩,
    by
      set_option maxRecDepth 100000 in
      set_option exponentiation.threshold 10000 in decide⟩

private def canonicalHardInput : Option CanonicalInput :=
  if hsf : HasOnlySimpleRoots factorHardCandidate then
    some ⟨factorHardCandidate, hsf, canonicalHardRep, by decide⟩
  else none

-- Tie the checked certificates to the top rungs of the archived families.
#guard exactHardPoly == exactFactorFamily 6
#guard factorHardCandidate == xPowSubTwo 8
#guard factorHardPoly == factorHardCandidate * DensePoly.ofList [3, 1]
#guard exactHardSquare.prec == 241
#guard factorHardSquare.prec == 77
#guard canonicalHardSquare.prec == 53

initialize exactHardInputRef : IO.Ref (Option ExactInput) ← IO.mkRef none
initialize factorHardInputRef : IO.Ref (Option SelectionInput) ← IO.mkRef none
initialize canonicalHardInputRef : IO.Ref (Option (Option CanonicalInput)) ←
  IO.mkRef none

private def getExactHardInput : IO ExactInput := do
  match ← exactHardInputRef.get with
  | some input => pure input
  | none =>
    exactHardInputRef.set (some exactHardInput)
    pure exactHardInput

private def getFactorHardInput : IO SelectionInput := do
  match ← factorHardInputRef.get with
  | some input => pure input
  | none =>
    factorHardInputRef.set (some factorHardInput)
    pure factorHardInput

private def getCanonicalHardInput : IO (Option CanonicalInput) := do
  match ← canonicalHardInputRef.get with
  | some input => pure input
  | none =>
    canonicalHardInputRef.set (some canonicalHardInput)
    pure canonicalHardInput

def runExactLadder : Unit → IO UInt64 := fun _ => do
  return exactChecksum (← getExactHardInput)

def runExactFactorLadder : Unit → IO UInt64 := fun _ => do
  return exactFactorChecksum (← getFactorHardInput)

def runCanonicalRepLadder : Unit → IO UInt64 := fun _ => do
  return canonicalRepChecksum (← getCanonicalHardInput)

/- Mode 3. The clean historical sweeps tried factor count on the end-to-end
family and candidate degree on both certification phases. They do not admit a
tight independently derived model: the executable all-roots isolator dominates
certification, differs materially from the published CIsolate algorithm, and
HexRoots documents only a heuristic complexity proxy. The end-to-end BHKS
factorization bound also does not cover its profiled dominant phase.

The three fixed inputs are the top completed rungs of those controlled sweeps.
Six quadratic factors are the largest practical end-to-end case before fixture
construction hits its setup cliff; degree eight is the largest audited
certification case. Each zero-grace ceiling below is an enforced whole-child
budget sized from measured startup, one untimed warmup, and the timed call or
batch. They give about 2.3--3.1x total-process headroom on the reference host
and do not reuse the generic 30-second ladder timeout. The historical `Ladder`
names are retained so the archived failed parametric evidence stays connected
to these operations. -/
setup_fixed_benchmark runExactLadder where {
  repeats := 5
  minTotalSeconds := 0.02
  maxSecondsPerCall := 0.2
  killGraceMs := 0
  warmupFirstIter := true
  expectedHash := some 0xd0642a7d4df3da02
}

setup_fixed_benchmark runExactFactorLadder where {
  repeats := 5
  maxSecondsPerCall := 2.0
  killGraceMs := 0
  warmupFirstIter := true
  expectedHash := some 0xe5c33ee70736a0fb
}

setup_fixed_benchmark runCanonicalRepLadder where {
  repeats := 5
  maxSecondsPerCall := 1.1
  killGraceMs := 0
  warmupFirstIter := true
  expectedHash := some 0x1d7ae08962f9292c
}

/-! # Root-API ladders -/

/-- Prepared fixed-field roots fixture over `ℚ(√2)`: `f = g^2 * (X - 1)` with
`g` dense of degree `m` and every coefficient `√2`-dependent, so Yun
produces a genuine multiplicity-2 component and the norm eliminant has
degree `2m`. -/
private structure FieldRootsInput where
  f : DensePoly (QAdjoin sqrtTwoPoly sqrtTwoRoot)
  checked : Option (PLift (ZPoly.CheckedIrreducible sqrtTwoPoly))

private instance : Inhabited FieldRootsInput :=
  ⟨⟨DensePoly.ofCoeffs #[], none⟩⟩

private def prepFieldRootsInput (n : Nat) : FieldRootsInput :=
  let m := max n 1
  let coeffs := (Array.range (m + 1)).map fun i =>
    QAdjoin.reduce sqrtTwoPoly sqrtTwoRoot
      (DensePoly.ofList
        [mkRat (Int.ofNat (i + 2)) (i + 3),
         mkRat (if i % 2 == 0 then 1 else -1) 2])
  let g := DensePoly.ofCoeffs coeffs
  let linear : DensePoly (QAdjoin sqrtTwoPoly sqrtTwoRoot) :=
    DensePoly.ofList [-1, 1]
  if hirr : ZPoly.isIrreducible sqrtTwoPoly = true then
    ⟨g * g * linear, some ⟨⟨hirr, by decide⟩⟩⟩
  else
    panic! "prepFieldRootsInput: irreducibility check failed"

private def qAdjoinRootsChecksum (input : FieldRootsInput) : UInt64 :=
  match input.checked with
  | some ⟨inst⟩ =>
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly := inst
    rootSetChecksum (QAdjoin.roots input.f sqrtTwoRep rfl)
  | none => 0

initialize qAdjoinRootsLadderRef : IO.Ref (Option FieldRootsInput) ← IO.mkRef none

private def getQAdjoinRootsLadderInput : IO FieldRootsInput := do
  match ← qAdjoinRootsLadderRef.get with
  | some input => pure input
  | none =>
    let input := prepFieldRootsInput 6
    qAdjoinRootsLadderRef.set (some input)
    pure input

def runQAdjoinRootsLadder : Unit → IO UInt64 := fun _ => do
  return qAdjoinRootsChecksum (← getQAdjoinRootsLadderInput)

private structure RootPhaseInput where
  f : DensePoly (QAdjoin sqrtTwoPoly sqrtTwoRoot)
  multiplicity : Nat
  multiplicity_pos : 0 < multiplicity
  eliminant : ZPoly

private def rootPhaseInput? : Option RootPhaseInput :=
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly := ⟨hirred, by decide⟩
    let input := prepFieldRootsInput 6
    match (QAdjoin.Roots.yun input.f).toList.find? fun component =>
        component.1.degree?.getD 0 == 6 with
    | some (f, multiplicity) =>
        if hm : 0 < multiplicity then
          let eliminant := ZPoly.squareFreeCore
            (QAdjoin.Roots.normEliminant f)
          some ⟨f, multiplicity, hm, eliminant⟩
        else none
    | none => none
  else none

initialize rootPhaseInputRef : IO.Ref (Option RootPhaseInput) ←
  IO.mkRef none

private def getRootPhaseInput : IO RootPhaseInput := do
  match ← rootPhaseInputRef.get with
  | some input => pure input
  | none =>
    let input ← requireSome "roots/phase-input" rootPhaseInput?
    rootPhaseInputRef.set (some input)
    pure input

def runNormEliminant : Unit → IO UInt64 := fun _ => do
  let input ← getRootPhaseInput
  return polyChecksum (QAdjoin.Roots.normEliminant input.f)

def runEvalEliminant : Unit → IO UInt64 := fun _ => do
  let input ← getRootPhaseInput
  return polyChecksum (QAdjoin.Roots.evalEliminant input.f input.eliminant)

def runComponentRoots : Unit → IO UInt64 :=
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly := ⟨hirred, by decide⟩
    fun _ => do
      let input ← getRootPhaseInput
      let roots ← requireSome "roots/component" <|
        QAdjoin.Roots.componentRoots? input.f input.multiplicity
          input.multiplicity_pos sqrtTwoRep rfl
      return rootSetChecksum (.finite roots)
  else
    fun _ => throw <| IO.userError "roots/component: irreducibility failed"

/- The degree-six repeated component is the exact profiled root-family case.
It exercises the Brown norm resultant, double evaluation resultant, and
complete certified component-root route. Separate fixed registrations expose
both eliminants and the isolation-dominated `componentRoots?` phase without
inventing a transfer of an external isolator's asymptotic bound. -/
setup_fixed_benchmark runNormEliminant where {
  apiFixedConfig with expectedHash := some 0xbd1f7b595e06cc7d
}
setup_fixed_benchmark runEvalEliminant where {
  apiFixedConfig with expectedHash := some 0x38d1cf2583d846c2
}
setup_fixed_benchmark runComponentRoots where {
  apiFixedConfig with
  maxSecondsPerCall := 8.0
  expectedHash := some 0x1ad4de1ea10497bd
}

/-- Prepared duplicate-removal fixture from the two Yun components of
`prepFieldRootsInput`. Component root construction is intentionally outside
the timed region; the timed kernel starts with the linear component and folds
the degree-`m` component through `mergeRootList`, matching `QAdjoin.roots?`. -/
private structure MergeRootsInput where
  initial : List RootCount
  candidates : Array RootCount

private instance : Hashable MergeRootsInput where
  hash input :=
    input.candidates.foldl
      (fun checksum root => mixHash checksum (rootChecksum root.root))
      (input.initial.foldl
        (fun checksum root => mixHash checksum (rootChecksum root.root))
        (hash input.initial.length))

private instance : Inhabited MergeRootsInput := ⟨⟨[], #[]⟩⟩

def prepMergeRootsInput (n : Nat) : MergeRootsInput :=
  let input := prepFieldRootsInput n
  match input.checked with
  | some ⟨inst⟩ =>
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly := inst
    let componentRoots? := (QAdjoin.Roots.yun input.f).foldlM
      (fun out component =>
        if hm : 0 < component.2 then do
          let roots ← QAdjoin.Roots.componentRoots? component.1 component.2 hm
            sqrtTwoRep rfl
          some (out.push roots)
        else
          none)
      #[]
    match componentRoots? with
    | some roots =>
      match roots.toList with
      | [first, second] => ⟨first.toList, second⟩
      | _ => panic! "prepMergeRootsInput: expected two Yun components"
    | none => panic! "prepMergeRootsInput: component root construction failed"
  | none => panic! "prepMergeRootsInput: irreducibility check failed"

def runMergeRootListLadder (input : MergeRootsInput) : UInt64 :=
  match input.candidates.foldlM
      (fun roots candidate => QAdjoin.Roots.mergeRootList candidate roots)
      input.initial with
  | some roots => rootSetChecksum (.finite roots.toArray)
  | none => 1

/-- Prepared canonical-coefficient roots fixture: a dense degree-`m`
`AlgebraicPoly` whose linear coefficient is `√2` and whose remaining
coefficients are nonzero rationals, forcing a genuine common-field
embedding into `ℚ(√2)` before the fixed-field root algorithm. -/
private structure AlgPolyInput where
  f : AlgebraicPoly

private instance : Hashable AlgPolyInput where
  hash input :=
    input.f.coeffs.foldl
      (fun checksum coefficient => mixHash checksum (polyChecksum coefficient.p))
      (hash input.f.size)

private instance : Inhabited AlgPolyInput := ⟨⟨AlgebraicPoly.ofArray #[]⟩⟩

def prepAlgPolyInput (n : Nat) : AlgPolyInput :=
  let m := max n 1
  match sqrtTwo?.bind (·.exact?) with
  | some sqrt2 =>
    ⟨AlgebraicPoly.ofArray <| (Array.range (m + 1)).map fun i =>
      if i == 1 then sqrt2
      else AlgebraicNumber.ofRat (denseRatCoeff i 2)⟩
  | none => panic! "prepAlgPolyInput: √2 fixture failed"

initialize signedShiftInputRef : IO.Ref Nat ← IO.mkRef 7

def runCommonSignedDegree : Unit → IO UInt64 := fun _ => do
  let (a, _) ← getCanonicalPair
  let shiftInput ← signedShiftInputRef.get
  return mixHash (hash (AlgebraicPoly.Common.signedShift shiftInput))
    (hash (AlgebraicPoly.Common.degree a))

def runCommonRational : Unit → IO UInt64 := fun _ => do
  let q ← rationalInputRef.get
  return optionAlgebraicChecksum (AlgebraicPoly.Common.rational? q)

def runCommonAdd : Unit → IO UInt64 := fun _ => do
  let (a, b) ← getCanonicalPair
  return optionAlgebraicChecksum (AlgebraicPoly.Common.add? a b)

def runCommonMul : Unit → IO UInt64 := fun _ => do
  let (a, b) ← getCanonicalPair
  return optionAlgebraicChecksum (AlgebraicPoly.Common.mul? a b)

def runCommonScale : Unit → IO UInt64 := fun _ => do
  let (a, _) ← getCanonicalPair
  return optionAlgebraicChecksum (AlgebraicPoly.Common.scale? 2 a)

def runCommonShift : Unit → IO UInt64 := fun _ => do
  let (a, b) ← getCanonicalPair
  return optionAlgebraicChecksum (AlgebraicPoly.Common.shift? a b 1)

private def shiftCandidateChecksum :
    Option AlgebraicPoly.Common.ShiftCandidate → UInt64
  | some candidate => mixHash (hash candidate.shift)
      (algebraicChecksum candidate.value)
  | none => 0

def runCommonExtendStep : Unit → IO UInt64 := fun _ => do
  let (a, b) ← getCanonicalPair
  return match AlgebraicPoly.Common.extendShiftStep a b none 1 with
    | some candidate => shiftCandidateChecksum candidate
    | none => 0

def runCommonExtendShift : Unit → IO UInt64 := fun _ => do
  let (a, b) ← getCanonicalPair
  return shiftCandidateChecksum (AlgebraicPoly.Common.extendShift? a b)

def runCommonExtend : Unit → IO UInt64 := fun _ => do
  let (a, b) ← getCanonicalPair
  return optionAlgebraicChecksum (AlgebraicPoly.Common.extend? a b)

def runCommonTrace : Unit → IO UInt64 := fun _ => do
  let (a, _) ← getCanonicalPair
  return hash (AlgebraicPoly.Common.trace? 4 a)

/- `signedShift` and `degree` are constant-time arithmetic/projections and are
grouped. The remaining fixed registrations each isolate one public checked
canonical-construction route at quadratic input degree; no asymptotic claim is
made for the isolation/exactification work they transitively perform. -/
setup_fixed_benchmark runCommonSignedDegree where {
  apiAnchorConfig with expectedHash := some 0x77a094c0cc786289
}
setup_fixed_benchmark runCommonRational where {
  apiFixedConfig with expectedHash := some 0x69274ee3b78c157d
}
setup_fixed_benchmark runCommonAdd where {
  apiFixedConfig with expectedHash := some 0xb2956b93cac0235f
}
setup_fixed_benchmark runCommonMul where {
  apiFixedConfig with expectedHash := some 0xab6b27ac2b367388
}
setup_fixed_benchmark runCommonScale where {
  apiFixedConfig with expectedHash := some 0x9e5141110150d74a
}
setup_fixed_benchmark runCommonShift where {
  apiFixedConfig with expectedHash := some 0xb2956b93cac0235f
}
setup_fixed_benchmark runCommonExtendStep where {
  apiFixedConfig with expectedHash := some 0x780a36b904a3800a
}
setup_fixed_benchmark runCommonExtendShift where {
  apiFixedConfig with
  maxSecondsPerCall := 0.75
  expectedHash := some 0x780a36b904a3800a
}
setup_fixed_benchmark runCommonExtend where {
  apiFixedConfig with
  maxSecondsPerCall := 0.75
  expectedHash := some 0xb2956b93cac0235f
}
setup_fixed_benchmark runCommonTrace where {
  apiAnchorConfig with expectedHash := some 0xad12ba043c7b5045
}

private structure CommonPowersInput where
  gamma : AlgebraicNumber
  last : Nat

private instance : Hashable CommonPowersInput where
  hash input := mixHash (algebraicChecksum input.gamma) (hash input.last)

private instance : Inhabited CommonPowersInput :=
  ⟨⟨AlgebraicNumber.zero, 0⟩⟩

def prepCommonPowersInput (n : Nat) : CommonPowersInput :=
  match canonicalPair? with
  | some (gamma, _) => ⟨gamma, max n 1⟩
  | none => panic! "prepCommonPowersInput: canonical fixture failed"

private def commonPowersChecksum (input : CommonPowersInput) : UInt64 :=
  match AlgebraicPoly.Common.powers? input.gamma input.last with
  | some powers => powers.foldl
      (fun checksum a => mixHash checksum (algebraicChecksum a))
      (hash powers.size)
  | none => 0

initialize commonPowersRef : IO.Ref (Option CommonPowersInput) ←
  IO.mkRef none

private def getCommonPowersInput : IO CommonPowersInput := do
  match ← commonPowersRef.get with
  | some input => pure input
  | none =>
    let input := prepCommonPowersInput 16
    commonPowersRef.set (some input)
    pure input

def runCommonPowers : Unit → IO UInt64 := fun _ => do
  let input ← getCommonPowersInput
  return commonPowersChecksum input

/- Fixed canonical case. A controlled exponent sweep is smooth through 16
but jumps from about 35 ms at 16 to 1.3 s at 24 and exceeds a 30 s child cap
at 32 as canonical multiplication encounters materially different coefficient
shapes. No independently derived one-parameter wall model explains that cliff.
The largest stable pre-cliff case, powers `1, gamma, ..., gamma^16` of the
quadratic generator,
therefore gives direct coverage. The 38 ms median and 43 ms clean spawn floor
fit under a 500 ms zero-grace whole-child budget with over a 6x margin. -/
setup_fixed_benchmark runCommonPowers where {
  apiFixedConfig with
  maxSecondsPerCall := 0.5
  expectedHash := some 0x3187ce8732d0a00b
}

def runCommonPrimitive (input : AlgPolyInput) : UInt64 :=
  optionAlgebraicChecksum
    (AlgebraicPoly.Common.primitive? input.f.coeffs)

/- Cost model. On this controlled family only one of `n + 1` coefficients is
quadratic and all others are rational. Filtering and the fold inspect every
coefficient, while each bounded primitive extension has fixed degree, so the
public `primitive?` operation is linear in coefficient count. -/
setup_benchmark runCommonPrimitive n => n
  with prep := prepAlgPolyInput
  where {
    paramFloor := 2
    paramCeiling := 128
    paramSchedule := .custom #[2, 4, 8, 16, 32, 64, 128]
    maxSecondsPerCall := 60.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

private structure CoordinatesInput where
  gamma : AlgebraicNumber
  a : AlgebraicNumber
  powers : Array AlgebraicNumber

private instance : Hashable CoordinatesInput where
  hash input := mixHash (algebraicChecksum input.gamma)
    (mixHash (algebraicChecksum input.a) (hash input.powers.size))

private instance : Inhabited CoordinatesInput :=
  ⟨⟨AlgebraicNumber.zero, AlgebraicNumber.zero, #[]⟩⟩

private def coordinatesInput? : Option CoordinatesInput := do
  let (gamma, _) ← canonicalPair?
  let powers ← AlgebraicPoly.Common.powers? gamma 2
  some ⟨gamma, gamma, powers⟩

initialize coordinatesInputRef : IO.Ref (Option CoordinatesInput) ←
  IO.mkRef none

private def getCoordinatesInput : IO CoordinatesInput := do
  match ← coordinatesInputRef.get with
  | some input => pure input
  | none =>
    let input ← requireSome "common/coordinates-input" coordinatesInput?
    coordinatesInputRef.set (some input)
    pure input

def runCommonCoordinates : Unit → IO UInt64 := fun _ => do
  let input ← getCoordinatesInput
  return match AlgebraicPoly.Common.coordinates?
      input.gamma input.a input.powers with
    | some coordinate => fixedChecksum coordinate
    | none => 0

/- At fixed quadratic ambient degree, `coordinates?` builds and solves the
2-by-2 trace-pairing system, reconstructs one coordinate polynomial, and
validates it through `toAlgebraicNumber?`. Powers are precomputed so this
registration isolates the advertised coordinate-recovery route. -/
setup_fixed_benchmark runCommonCoordinates where {
  apiFixedConfig with expectedHash := some 0xb278d8da3cd861d6
}

/-- The integer-polynomial parameters that determine an isolation call. The
bit height is recorded separately from the coefficient maximum so values such
as a maximum of `6` are unambiguously reported as three bits. -/
structure IsolationStats where
  parameter : Nat
  degree : Nat
  coeffAbsMax : Nat
  coeffBitHeight : Nat
  isolationTarget : Nat

private def isolationStats (n : Nat) (p : ZPoly) : IsolationStats :=
  let coeffAbsMax := ZPoly.coeffAbsMax p
  { parameter := n
    degree := p.degree?.getD 0
    coeffAbsMax
    coeffBitHeight := ceilLog2 coeffAbsMax
    isolationTarget := separationDepth p }

/-- Parameters of the square-free sum eliminant isolated by the lazy-addition
benchmark family. -/
def lazyAddIsolationStats (n : Nat) : IsolationStats :=
  isolationStats n <| ZPoly.squareFreeCore <|
    ZPoly.addEliminant (xPowSubTwo (max n 2)) sqrtThreePoly

/-- Parameters of the single square-free norm component isolated by the
canonical-coefficient roots benchmark family. -/
def algebraicRootsIsolationStats? (n : Nat) : Option IsolationStats := do
  let input := prepAlgPolyInput n
  let common ← AlgebraicPoly.Common.presentation? input.f.coeffs
  letI : ZPoly.CheckedIrreducible common.generator.p := common.generator.checked
  let polynomial := DensePoly.ofCoeffs common.coefficients
  let components := QAdjoin.Roots.yun polynomial
  if components.size = 1 then do
    let component ← components[0]?
    let eliminant := ZPoly.squareFreeCore (QAdjoin.Roots.normEliminant component.1)
    some (isolationStats n eliminant)
  else
    none

/-- Parameters of the norm eliminant isolated for the dense repeated component
of the fixed-field roots benchmark family. -/
def fixedFieldRootsIsolationStats? (n : Nat) : Option IsolationStats :=
  let input := prepFieldRootsInput n
  match input.checked with
  | some ⟨inst⟩ =>
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly := inst
    let component? := (QAdjoin.Roots.yun input.f).toList.find? fun component =>
      component.1.degree?.getD 0 == max n 1
    component?.map fun component =>
      let eliminant := ZPoly.squareFreeCore (QAdjoin.Roots.normEliminant component.1)
      isolationStats n eliminant
  | none => none

#guard
  let stats := lazyAddIsolationStats 6
  stats.degree = 12 ∧ stats.coeffAbsMax = 1998 ∧
    stats.coeffBitHeight = 11 ∧ stats.isolationTarget = 186

#guard
  match algebraicRootsIsolationStats? 6 with
  | some stats =>
      stats.degree = 12 ∧ stats.coeffAbsMax = 366720 ∧
        stats.coeffBitHeight = 19 ∧ stats.isolationTarget = 274
  | none => False

#guard
  match fixedFieldRootsIsolationStats? 6 with
  | some stats =>
      stats.degree = 12 ∧ stats.coeffAbsMax = 45480960 ∧
        stats.coeffBitHeight = 26 ∧ stats.isolationTarget = 351
  | none => False

private def printIsolationStatsRow (family : String) (stats : IsolationStats) : IO Unit :=
  IO.println s!"{family}\t{stats.parameter}\t{stats.degree}\t{stats.coeffAbsMax}\t{stats.coeffBitHeight}\t{stats.isolationTarget}"

/-- Print the eliminant degree, coefficient maximum, bit height, and isolation
target for every former parametric rung. This is input
characterisation, not a timing path. -/
def printIsolationStats : IO Unit := do
  IO.println "family\tparameter\tdegree\tcoeffAbsMax\tcoeffBitHeight\tisolationTarget"
  for n in #[2, 3, 4, 6, 8, 10] do
    printIsolationStatsRow "lazy-add" (lazyAddIsolationStats n)
  for n in #[3, 4, 5, 6, 8] do
    match algebraicRootsIsolationStats? n with
    | some stats => printIsolationStatsRow "algebraic-roots" stats
    | none => throw <| IO.userError s!"algebraic-roots fixture {n} did not have one Yun component"
  for n in #[2, 3, 4, 6, 8, 12] do
    match fixedFieldRootsIsolationStats? n with
    | some stats => printIsolationStatsRow "fixed-field-roots" stats
    | none =>
      throw <| IO.userError
        s!"fixed-field-roots fixture {n} did not have the repeated component"

private def algebraicRootsChecksum (input : AlgPolyInput) : UInt64 :=
  rootSetChecksum input.f.roots

def runCommonPresentationLadder (input : AlgPolyInput) : UInt64 :=
  match AlgebraicPoly.Common.presentation? input.f.coeffs with
  | some presentation => polyChecksum presentation.generator.p
  | none => 1

/- Cost model. The public common-field construction behind
`AlgebraicPoly.roots?`, separated per the Attribution rule: `primitive?`
folds `extend?` over the `n + 1` coefficients, and with a single quadratic
irrational among rationals every `extend?` tests a constant number of
shifts (`choose(2, 2) + 1 = 2`) with bounded-degree canonical arithmetic,
so the search is `O(n)` constant-size canonical operations; `powers?` is
constant-size at the fixed quadratic generator, and `coordinates?` embeds
each of the `n + 1` coefficients with a constant number of degree-2
trace-pairing operations. The declared wall model is therefore linear in
the coefficient count. -/
setup_benchmark runCommonPresentationLadder n => n
  with prep := prepAlgPolyInput
  where {
    -- `presentation?` carries a fixed start-up cost (the generator's powers
    -- and the first `extend?` shifts) worth roughly four coefficients, so the
    -- bottom of the ladder is start-up dominated. The schedule keeps those
    -- rungs — they are the range `runAlgebraicRootsLadder` actually calls this
    -- at — and extends to 128 so the linear term dominates the fit.
    paramFloor := 2
    paramCeiling := 128
    paramSchedule := .custom #[2, 4, 8, 16, 32, 64, 128]
    maxSecondsPerCall := 60.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/- Cost model. This is the duplicate-removal phase separated under the
Attribution rule. The linear Yun component seeds the list, then `n` roots
from the degree-`n` component are merged. Candidate `k` performs one rational
gcd against the linear component and `k` same-polynomial isolation comparisons.
The gcd of a degree-`2n` norm eliminant and a linear polynomial takes `O(n)`
rational coefficient operations. The eliminant coefficients have
`O(n log n)`-bit height, represented here by one `log₂(n) + 1` limb-growth
factor. The `Θ(n²)` same-polynomial comparisons are exact dyadic-square
intersection tests whose coordinates have the same separation-depth bit scale,
so they fit the same `n² (log₂(n + 2) + 1)` ceiling. The fixture computes Yun,
norm eliminants, isolation, and disambiguation before timing begins. -/
setup_benchmark runMergeRootListLadder n => n ^ 2 * (Nat.log2 (n + 2) + 1)
  with prep := prepMergeRootsInput
  where {
    paramFloor := 2
    paramCeiling := 12
    paramSchedule := .custom #[2, 3, 4, 6, 8, 12]
    -- The timed merge is sub-millisecond, but preparing its isolated component
    -- roots is the same expensive prelude as the end-to-end ladder. At n = 12
    -- that prelude takes about six minutes, still within this whole-batch cap.
    maxSecondsPerCall := 900.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/- Fixed canonical case. `QAdjoin.roots?` runs Yun decomposition on
`g^2 * (X - 1)` over `ℚ(√2)`, constructs the degree-12 norm eliminant of the
dense degree-6 repeated component, isolates it at separation depth, and
disambiguates its six roots. The repaired inclusive profile puts 92.94% of the
profiled process in `componentRoots?` and 85.01% in `isolate`. No tight
scaling of the HexRoots executable on this family has been derived independently of timing,
and BSSY's `Õ(d³ + d²·tau)` result analyzes `CIsolate`, not HexRoots' distinct
driver. The former `n⁵ log² n` declaration instead composed HexRoots'
heuristic isolation proxy and is not a mode-1 or mode-2 model. This
project-internal canonical input is the repaired profile's `n = 6` case and
tracks a 20 s absolute budget without asserting an asymptotic shape. The
historical `Ladder` name is retained so committed exports continue to identify
the same operation across the mode change. -/
setup_fixed_benchmark runQAdjoinRootsLadder where {
  repeats := 3
  maxSecondsPerCall := 20.0
  expectedHash := some 0x63e9dd11895b2211
}

initialize algebraicRootsLadderRef : IO.Ref (Option AlgPolyInput) ← IO.mkRef none

private def getAlgebraicRootsLadderInput : IO AlgPolyInput := do
  match ← algebraicRootsLadderRef.get with
  | some input => pure input
  | none =>
    let input := prepAlgPolyInput 6
    algebraicRootsLadderRef.set (some input)
    pure input

def runAlgebraicRootsLadder : Unit → IO UInt64 := fun _ => do
  return algebraicRootsChecksum (← getAlgebraicRootsLadderInput)

/- Fixed canonical case. `AlgebraicPoly.roots?` first embeds the seven
coefficients into the fixed quadratic field generated by `√2`, then the
fixed-field driver square-free normalizes and isolates the degree-12 norm
eliminant at its `separationDepth` target. BSSY Corollary 6 bounds BSSY's
`CIsolate` on square-free integer polynomials by `Õ(d³ + d²·tau)`, but the
bound does not transfer to HexRoots' materially different driver. The local
HexRoots contract is heuristic, so neither that result nor the former composed
heuristic supplies a cited one-parameter wall model for this operation. The
fixed registration gives up asymptotic detection and checks the SPEC's absolute
budget in full timing runs. The historical `Ladder` name is retained so the
fixed export can supersede the earlier parametric export without changing the
operation identity. -/
setup_fixed_benchmark runAlgebraicRootsLadder where {
  repeats := 3
  maxSecondsPerCall := 15.0
  expectedHash := some 0xb6a44b3ff493da5e
}

/-! # PARI `t_POLMOD` comparator pairs

Fixed per-rung Lean/PARI pairs for `QAdjoin` multiplication and inversion.
Both sides consume the identical deterministic `prepFieldInput` /
`prepInvInput` fixture and hash the identical reduced rational coefficient
vector, so `compare` joins on result hashes. The rung fixtures are built
lazily on the discarded `warmupFirstIter` call, keeping root isolation, the
inversion irreducibility check, and the PARI driver startup out of the timed
region on both sides. -/

/-- Checksum matching `fixedChecksum` on a raw trimmed rational coefficient
vector, used to compare PARI polmod results against `QAdjoin` results. -/
private def ratCoeffsChecksum (coeffs : Array Rat) : UInt64 :=
  coeffs.foldl (fun checksum q => mixHash checksum (ratChecksum q))
    (hash coeffs.size)

initialize mulPairRef4 : IO.Ref (Option FieldInput) ← IO.mkRef none
initialize mulPairRef6 : IO.Ref (Option FieldInput) ← IO.mkRef none
initialize mulPairRef8 : IO.Ref (Option FieldInput) ← IO.mkRef none
initialize mulPairRef12 : IO.Ref (Option FieldInput) ← IO.mkRef none
initialize mulPairRef16 : IO.Ref (Option FieldInput) ← IO.mkRef none
initialize mulPairRef20 : IO.Ref (Option FieldInput) ← IO.mkRef none
initialize invPairRef4 : IO.Ref (Option InvInput) ← IO.mkRef none
initialize invPairRef6 : IO.Ref (Option InvInput) ← IO.mkRef none
initialize invPairRef8 : IO.Ref (Option InvInput) ← IO.mkRef none
initialize invPairRef10 : IO.Ref (Option InvInput) ← IO.mkRef none
initialize invPairRef12 : IO.Ref (Option InvInput) ← IO.mkRef none
initialize invPairRef16 : IO.Ref (Option InvInput) ← IO.mkRef none

private def getMulPair (ref : IO.Ref (Option FieldInput)) (n : Nat) :
    IO FieldInput := do
  match ← ref.get with
  | some input => pure input
  | none =>
    let input := prepFieldInput n
    ref.set (some input)
    pure input

private def getInvPair (ref : IO.Ref (Option InvInput)) (n : Nat) :
    IO InvInput := do
  match ← ref.get with
  | some input => pure input
  | none =>
    let input := prepInvInput n
    ref.set (some input)
    pure input

private def pariPolmodMul (input : FieldInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Pari.runOp "polmod" "mul"
    #[("modulus", Hex.BenchOracle.Flint.intsToJson input.p.toArray.toList),
      ("a", Hex.BenchOracle.Pari.ratsToJson input.a.coeffs.toArray),
      ("b", Hex.BenchOracle.Pari.ratsToJson input.b.coeffs.toArray)]
  return ratCoeffsChecksum (← Hex.BenchOracle.Pari.jsonToRats result)

private def pariPolmodInv (input : InvInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Pari.runOp "polmod" "inv"
    #[("modulus", Hex.BenchOracle.Flint.intsToJson input.p.toArray.toList),
      ("a", Hex.BenchOracle.Pari.ratsToJson input.a.coeffs.toArray)]
  return ratCoeffsChecksum (← Hex.BenchOracle.Pari.jsonToRats result)

def runQAdjoinMulPair4 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinMulLadder (← getMulPair mulPairRef4 4)
def runPariPolmodMul4 : Unit → IO UInt64 := fun _ => do
  pariPolmodMul (← getMulPair mulPairRef4 4)
def runQAdjoinMulPair6 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinMulLadder (← getMulPair mulPairRef6 6)
def runPariPolmodMul6 : Unit → IO UInt64 := fun _ => do
  pariPolmodMul (← getMulPair mulPairRef6 6)
def runQAdjoinMulPair8 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinMulLadder (← getMulPair mulPairRef8 8)
def runPariPolmodMul8 : Unit → IO UInt64 := fun _ => do
  pariPolmodMul (← getMulPair mulPairRef8 8)
def runQAdjoinMulPair12 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinMulLadder (← getMulPair mulPairRef12 12)
def runPariPolmodMul12 : Unit → IO UInt64 := fun _ => do
  pariPolmodMul (← getMulPair mulPairRef12 12)
def runQAdjoinMulPair16 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinMulLadder (← getMulPair mulPairRef16 16)
def runPariPolmodMul16 : Unit → IO UInt64 := fun _ => do
  pariPolmodMul (← getMulPair mulPairRef16 16)
def runQAdjoinMulPair20 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinMulLadder (← getMulPair mulPairRef20 20)
def runPariPolmodMul20 : Unit → IO UInt64 := fun _ => do
  pariPolmodMul (← getMulPair mulPairRef20 20)

def runQAdjoinInvPair4 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinInvLadder (← getInvPair invPairRef4 4)
def runPariPolmodInv4 : Unit → IO UInt64 := fun _ => do
  pariPolmodInv (← getInvPair invPairRef4 4)
def runQAdjoinInvPair6 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinInvLadder (← getInvPair invPairRef6 6)
def runPariPolmodInv6 : Unit → IO UInt64 := fun _ => do
  pariPolmodInv (← getInvPair invPairRef6 6)
def runQAdjoinInvPair8 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinInvLadder (← getInvPair invPairRef8 8)
def runPariPolmodInv8 : Unit → IO UInt64 := fun _ => do
  pariPolmodInv (← getInvPair invPairRef8 8)
def runQAdjoinInvPair10 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinInvLadder (← getInvPair invPairRef10 10)
def runPariPolmodInv10 : Unit → IO UInt64 := fun _ => do
  pariPolmodInv (← getInvPair invPairRef10 10)
def runQAdjoinInvPair12 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinInvLadder (← getInvPair invPairRef12 12)
def runPariPolmodInv12 : Unit → IO UInt64 := fun _ => do
  pariPolmodInv (← getInvPair invPairRef12 12)
def runQAdjoinInvPair16 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinInvLadder (← getInvPair invPairRef16 16)
def runPariPolmodInv16 : Unit → IO UInt64 := fun _ => do
  pariPolmodInv (← getInvPair invPairRef16 16)

/-- Per-call driver overhead for the PARI comparator: one `polmod`-family
request whose PARI-side work is a constant `0`, so the measured time is the
JSON request/reply round trip alone. `SPEC/benchmarking.md` §External
comparators §Process call requires this figure so the headline report can
quote overhead-adjusted ratios. -/
def runPariPolmodOverhead : Unit → IO UInt64 := fun _ => do
  let result ← Hex.BenchOracle.Pari.runOp "polmod" "overhead" #[]
  match result.getInt? with
  | .ok value => return UInt64.ofNat value.toNat
  | .error error =>
    throw <| IO.userError s!"invalid PARI overhead reply: {error}"

/-- Timing shape shared by both sides of every PARI pair: the discarded
`warmupFirstIter` call builds the lazily cached rung fixture (and, on the
PARI side, spawns the persistent driver) outside the timed region, and the
raised `minTotalSeconds` floor amortises steady-state work across the
auto-tuned inner-repeat batch so per-rung ratios compare like with like. -/
def pariCompareConfig : LeanBench.FixedBenchmarkConfig :=
  -- The discarded `warmupFirstIter` call builds the certified single-root
  -- fixture outside the measured region.
  { repeats := 5, maxSecondsPerCall := 120.0, warmupFirstIter := true,
    minTotalSeconds := 0.2 }

/- Fixed per-rung process-call comparator registrations for PARI t_POLMOD
multiplication against `QAdjoin` multiplication (quadratic-cost surface; see
the `runQAdjoinMulLadder` derivation). Identical inputs, identical reduced
rational coefficient hash on both sides. -/
setup_fixed_benchmark runQAdjoinMulPair4 where pariCompareConfig
setup_fixed_benchmark runPariPolmodMul4 where pariCompareConfig
setup_fixed_benchmark runQAdjoinMulPair6 where pariCompareConfig
setup_fixed_benchmark runPariPolmodMul6 where pariCompareConfig
setup_fixed_benchmark runQAdjoinMulPair8 where pariCompareConfig
setup_fixed_benchmark runPariPolmodMul8 where pariCompareConfig
setup_fixed_benchmark runQAdjoinMulPair12 where pariCompareConfig
setup_fixed_benchmark runPariPolmodMul12 where pariCompareConfig
setup_fixed_benchmark runQAdjoinMulPair16 where pariCompareConfig
setup_fixed_benchmark runPariPolmodMul16 where pariCompareConfig
setup_fixed_benchmark runQAdjoinMulPair20 where pariCompareConfig
setup_fixed_benchmark runPariPolmodMul20 where pariCompareConfig

/- Fixed per-rung process-call comparator registrations for PARI t_POLMOD
inversion against `QAdjoin` extended-gcd inversion (quadratic
coefficient-operation surface; see the `runQAdjoinInvLadder` derivation). -/
setup_fixed_benchmark runQAdjoinInvPair4 where pariCompareConfig
setup_fixed_benchmark runPariPolmodInv4 where pariCompareConfig
setup_fixed_benchmark runQAdjoinInvPair6 where pariCompareConfig
setup_fixed_benchmark runPariPolmodInv6 where pariCompareConfig
setup_fixed_benchmark runQAdjoinInvPair8 where pariCompareConfig
setup_fixed_benchmark runPariPolmodInv8 where pariCompareConfig
setup_fixed_benchmark runQAdjoinInvPair10 where pariCompareConfig
setup_fixed_benchmark runPariPolmodInv10 where pariCompareConfig
setup_fixed_benchmark runQAdjoinInvPair12 where pariCompareConfig
setup_fixed_benchmark runPariPolmodInv12 where pariCompareConfig
setup_fixed_benchmark runQAdjoinInvPair16 where pariCompareConfig
setup_fixed_benchmark runPariPolmodInv16 where pariCompareConfig

/- Driver round-trip floor for the PARI comparator: no algorithmic work on
either side, so this registration measures only the per-call request/reply
cost that the headline report subtracts from the PARI wall times. -/
setup_fixed_benchmark runPariPolmodOverhead where
  { pariCompareConfig with expectedHash := some 0x0 }

end Hex.NumberFieldBench

def main (args : List String) : IO UInt32 := do
  match args with
  | ["isolation-stats"] =>
      Hex.NumberFieldBench.printIsolationStats
      return 0
  | ["qadjoin-inv-chain-stats"] =>
      Hex.NumberFieldBench.printInvChainSteps
      return 0
  | _ => LeanBench.Cli.dispatch args
