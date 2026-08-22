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
* exactification through an irrelevant enclosing factor;
* repeated-root extraction over `ℚ(√2)`.

The parametric ladders carry the Phase-4 asymptotic evidence:

* `runQAdjoinAddLadder` / `runQAdjoinMulLadder` / `runQAdjoinInvLadder`:
  fixed-field arithmetic in `ℚ(2^{1/n})` at growing modulus degree `n`;
* `runAddEliminantLadder`: Brown-resultant sum-eliminant construction at
  growing first-operand degree;
* `runLazyAddLadder`: end-to-end lazy `AlgebraicRoot.add?` at growing
  degree product (capped at the SPEC's merge-facing ceiling `20`);
* `runExactLadder`: exactification through an enclosing polynomial with an
  irrelevant linear factor at growing degree;
* `runQAdjoinRootsLadder` / `runAlgebraicRootsLadder`: the two root APIs on
  non-degenerate inputs with a repeated factor (fixed field) and a
  `√2`-dependent coefficient (canonical coefficients);
* `runCommonPresentationLadder`: the public common-field construction
  behind `AlgebraicPoly.roots?`, separated per the Attribution rule.

Informational PARI comparator (`SPEC/benchmarking.md` §External comparators
§Process call): PARI's `t_POLMOD` arithmetic (`Mod(a, m) * Mod(b, m)` and
`Mod(a, m)^(-1)`) is the callable PARI surface matching `QAdjoin`
multiplication and inversion. The `runQAdjoinMulPair*` / `runPariPolmodMul*`
and `runQAdjoinInvPair*` / `runPariPolmodInv*` fixed rungs consume identical
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

/-! # Parametric ladder fixtures -/

/-- `X^m - 2`, Eisenstein-irreducible at `2` for every `m ≥ 1`. -/
private def xPowSubTwo (m : Nat) : ZPoly :=
  DensePoly.ofList ((-2 : Int) :: List.replicate (m - 1) 0 ++ [1])

/-- Deterministic dense all-nonzero rational coefficients keyed by length
and salt: alternating signs, growing numerators, denominator `i + 2`. -/
private def denseRatCoeffs (len salt : Nat) : Array Rat :=
  (Array.range len).map fun i =>
    let sign : Int := if (i + salt) % 2 == 0 then 1 else -1
    mkRat (sign * Int.ofNat (i + salt + 1)) (i + 2)

/-- Deterministic refined isolation for a squarefree polynomial: run the
bounded isolator at separation depth and take the first returned atom. -/
private def refinedOf? (p : ZPoly) (h : HasOnlySimpleRoots p) :
    Option (RefinedIsolation p) := do
  let isolations ← isolate p h (separationDepth p : Int)
  let iso ← isolations[0]?
  iso.toRefined?

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

/-- Prepared degree-`m` fixed-field arithmetic fixture: the field
`ℚ(2^{1/m})` with two dense all-nonzero-coordinate elements. -/
private structure FieldInput where
  p : ZPoly
  x : SimpleRoot p
  a : QAdjoin p x
  b : QAdjoin p x

private instance : Hashable FieldInput where
  hash input :=
    mixHash (hash input.p.toArray)
      (mixHash (fixedChecksum input.a) (fixedChecksum input.b))

private instance : Inhabited FieldInput :=
  ⟨{ p := sqrtTwoPoly, x := sqrtTwoRoot, a := fixedSqrtTwo, b := fixedSqrtTwo }⟩

def prepFieldInput (n : Nat) : FieldInput :=
  let m := max n 2
  let p := xPowSubTwo m
  if hsf : HasOnlySimpleRoots p then
    match refinedOf? p hsf with
    | some rep =>
      let x := SimpleRoot.mk rep
      { p := p, x := x
        a := QAdjoin.reduce p x (DensePoly.ofCoeffs (denseRatCoeffs m 3))
        b := QAdjoin.reduce p x (DensePoly.ofCoeffs (denseRatCoeffs m 7)) }
    | none => panic! "prepFieldInput: isolation failed"
  else panic! "prepFieldInput: squarefree check failed"

/-- Prepared inversion fixture: `FieldInput` data plus the runtime-checked
irreducibility instance, decided in prep so no factorization work leaks
into the timed extended-gcd region. -/
private structure InvInput where
  p : ZPoly
  x : SimpleRoot p
  a : QAdjoin p x
  checked : Option (PLift (ZPoly.CheckedIrreducible p))

private instance : Hashable InvInput where
  hash input := mixHash (hash input.p.toArray) (fixedChecksum input.a)

private instance : Inhabited InvInput :=
  ⟨{ p := sqrtTwoPoly, x := sqrtTwoRoot, a := fixedSqrtTwo, checked := none }⟩

def prepInvInput (n : Nat) : InvInput :=
  let m := max n 2
  let p := xPowSubTwo m
  if hirr : ZPoly.isIrreducible p = true then
    if hdeg : 0 < p.degree?.getD 0 then
      if hsf : HasOnlySimpleRoots p then
        match refinedOf? p hsf with
        | some rep =>
          let x := SimpleRoot.mk rep
          { p := p, x := x
            a := QAdjoin.reduce p x (DensePoly.ofCoeffs (denseRatCoeffs m 5))
            checked := some ⟨⟨hirr, hdeg⟩⟩ }
        | none => panic! "prepInvInput: isolation failed"
      else panic! "prepInvInput: squarefree check failed"
    else panic! "prepInvInput: degree check failed"
  else panic! "prepInvInput: irreducibility check failed"

def runQAdjoinAddLadder (input : FieldInput) : UInt64 :=
  fixedChecksum (input.a + input.b)

def runQAdjoinMulLadder (input : FieldInput) : UInt64 :=
  fixedChecksum (input.a * input.b)

def runQAdjoinInvLadder (input : InvInput) : UInt64 :=
  match input.checked with
  | some ⟨inst⟩ =>
    letI : ZPoly.CheckedIrreducible input.p := inst
    fixedChecksum input.a⁻¹
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
    paramFloor := 4
    paramCeiling := 32
    paramSchedule := .custom #[4, 6, 8, 12, 16, 24, 32]
    maxSecondsPerCall := 10.0
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
    paramFloor := 4
    paramCeiling := 32
    paramSchedule := .custom #[4, 6, 8, 12, 16, 24, 32]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Cost model. Inversion runs the polynomial extended gcd of the degree-`(n-1)`
element against the degree-`n` modulus over `ℚ`: the Euclidean remainder
sequence performs a quadratic number of rational coefficient operations (SPEC
§Complexity: "extended gcd ... quadratic number of coefficient operations with
coefficient-size growth"). Intermediate numerator/denominator growth across the
chain is modelled with the same logarithmic limb-growth proxy the HexResultant
Brown-chain registrations use, giving `n^2 * log n` rather than declaring every
arbitrary-precision operation constant-cost. -/
setup_benchmark runQAdjoinInvLadder n => n * n * (Nat.log2 (n + 2) + 1)
  with prep := prepInvInput
  where {
    paramFloor := 3
    paramCeiling := 12
    paramSchedule := .custom #[3, 4, 6, 8, 12]
    maxSecondsPerCall := 10.0
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

def runLazyAddLadder (input : LazyAddInput) : UInt64 :=
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
    paramFloor := 4
    paramCeiling := 64
    paramSchedule := .custom #[4, 8, 16, 32, 64]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Cost model. Per SPEC §Complexity the lazy binary ceiling is the eliminant
resultant cost plus the HexRoots isolation cost at the eliminant degree
`d = deg(a.p) * deg(b.p) = 2n`, and isolation at separation depth dominates.
State-of-practice real/complex isolation for a degree-`d` integer polynomial
is `~O(d^3 + d^2 * tau)` bit operations with working precision `B`; here the
separation-depth target and the resultant Hadamard coefficient bound give
`tau, B = O(d log d)`, so the HexRoots heuristic `O(d^3 * B^2)` yields the
declared `n^5 log^2 n` wall shape (constants in `d = 2n` drop out). The
schedule stops at degree product 20, the SPEC's largest merge-facing lazy
class. -/
setup_benchmark runLazyAddLadder n => n ^ 5 * (Nat.log2 (n + 2)) ^ 2
  with prep := prepLazyAddInput
  where {
    paramFloor := 2
    paramCeiling := 10
    paramSchedule := .custom #[2, 3, 4, 6, 8, 10]
    maxSecondsPerCall := 60.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/-! # Exactification ladder -/

/-- Prepared exactification fixture: the first isolated root of
`(X^m - 2)(X + 3)`, so factor selection always faces at least two
irreducible candidate factors. -/
private structure ExactInput where
  root : Option AlgebraicRoot

private instance : Hashable ExactInput where
  hash input := (input.root.map rootChecksum).getD 0

private instance : Inhabited ExactInput := ⟨⟨none⟩⟩

def prepExactInput (n : Nat) : ExactInput :=
  ⟨mkLadderRoot? (xPowSubTwo (max n 2) * DensePoly.ofList [3, 1])⟩

def runExactLadder (input : ExactInput) : UInt64 :=
  match input.root with
  | some root =>
    match root.exact? with
    | some a => polyChecksum a.p
    | none => 1
  | none => 0

/- Cost model. Per SPEC §Complexity, exactification adds one
Berlekamp-Zassenhaus factorization of the degree-`(n+1)` enclosing polynomial
plus factor-root selection. The declared model is the classical BHKS
polynomial bound in the enclosing degree, `n^9 + n^7 log^2 n` (the same shape
the HexBerlekampZassenhaus registrations declare); the subsequent candidate
re-isolation and canonicalization are lower order against it. -/
setup_benchmark runExactLadder n => n ^ 9 + n ^ 7 * (Nat.log2 (n + 2)) ^ 2
  with prep := prepExactInput
  where {
    paramFloor := 2
    paramCeiling := 8
    paramSchedule := .custom #[2, 3, 4, 6, 8]
    maxSecondsPerCall := 30.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/-! # Root-API ladders -/

/-- Prepared fixed-field roots fixture over `ℚ(√2)`: `f = g^2 * (X - 1)` with
`g` dense of degree `m` and every coefficient `√2`-dependent, so Yun
produces a genuine multiplicity-2 component and the norm eliminant has
degree `2m`. -/
private structure FieldRootsInput where
  f : DensePoly (QAdjoin sqrtTwoPoly sqrtTwoRoot)
  checked : Option (PLift (ZPoly.CheckedIrreducible sqrtTwoPoly))

private instance : Hashable FieldRootsInput where
  hash input :=
    input.f.toArray.foldl
      (fun checksum coefficient => mixHash checksum (fixedChecksum coefficient))
      (hash input.f.size)

private instance : Inhabited FieldRootsInput :=
  ⟨⟨DensePoly.ofCoeffs #[], none⟩⟩

def prepFieldRootsInput (n : Nat) : FieldRootsInput :=
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

def runQAdjoinRootsLadder (input : FieldRootsInput) : UInt64 :=
  match input.checked with
  | some ⟨inst⟩ =>
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly := inst
    match QAdjoin.roots? input.f sqrtTwoRep rfl with
    | some result => rootSetChecksum result
    | none => 1
  | none => 0

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
      else AlgebraicNumber.ofRat (mkRat (Int.ofNat (i + 1)) (i + 2))⟩
  | none => panic! "prepAlgPolyInput: √2 fixture failed"

def runAlgebraicRootsLadder (input : AlgPolyInput) : UInt64 :=
  match input.f.roots? with
  | some result => rootSetChecksum result
  | none => 1

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
    paramFloor := 2
    paramCeiling := 16
    paramSchedule := .custom #[2, 4, 8, 16]
    maxSecondsPerCall := 60.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/- Cost model. Per SPEC §Complexity the root API runs Yun decomposition
(`O(n^2)` field operations, lower order here) and one norm eliminant per
squarefree component, then isolates and disambiguates. For the degree-`n`
squarefree component over the fixed quadratic field the norm eliminant has
degree `d = 2n`, and its separation-depth isolation dominates exactly as in
the lazy-addition derivation above (`O(d^3 * B^2)` with
`tau, B = O(d log d)`), so the declared wall model is the same
`n^5 log^2 n` shape. -/
setup_benchmark runQAdjoinRootsLadder n => n ^ 5 * (Nat.log2 (n + 2)) ^ 2
  with prep := prepFieldRootsInput
  where {
    paramFloor := 1
    paramCeiling := 6
    paramSchedule := .custom #[1, 2, 3, 4, 6]
    maxSecondsPerCall := 180.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/- Cost model. `AlgebraicPoly.roots?` first embeds the coefficients into one
primitive field — for this family the bounded primitive-element search
stabilises on the fixed quadratic generator `√2` after `O(n)` cheap checked
combinations — and then invokes the fixed-field algorithm, whose degree-`2n`
norm-eliminant isolation dominates per the derivation on
`runQAdjoinRootsLadder`. Declared model: the same `n^5 log^2 n` isolation
shape. -/
setup_benchmark runAlgebraicRootsLadder n => n ^ 5 * (Nat.log2 (n + 2)) ^ 2
  with prep := prepAlgPolyInput
  where {
    paramFloor := 2
    paramCeiling := 6
    paramSchedule := .custom #[2, 3, 4, 6]
    maxSecondsPerCall := 60.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
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
initialize mulPairRef8 : IO.Ref (Option FieldInput) ← IO.mkRef none
initialize mulPairRef16 : IO.Ref (Option FieldInput) ← IO.mkRef none
initialize invPairRef4 : IO.Ref (Option InvInput) ← IO.mkRef none
initialize invPairRef8 : IO.Ref (Option InvInput) ← IO.mkRef none
initialize invPairRef12 : IO.Ref (Option InvInput) ← IO.mkRef none

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
def runQAdjoinMulPair8 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinMulLadder (← getMulPair mulPairRef8 8)
def runPariPolmodMul8 : Unit → IO UInt64 := fun _ => do
  pariPolmodMul (← getMulPair mulPairRef8 8)
def runQAdjoinMulPair16 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinMulLadder (← getMulPair mulPairRef16 16)
def runPariPolmodMul16 : Unit → IO UInt64 := fun _ => do
  pariPolmodMul (← getMulPair mulPairRef16 16)

def runQAdjoinInvPair4 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinInvLadder (← getInvPair invPairRef4 4)
def runPariPolmodInv4 : Unit → IO UInt64 := fun _ => do
  pariPolmodInv (← getInvPair invPairRef4 4)
def runQAdjoinInvPair8 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinInvLadder (← getInvPair invPairRef8 8)
def runPariPolmodInv8 : Unit → IO UInt64 := fun _ => do
  pariPolmodInv (← getInvPair invPairRef8 8)
def runQAdjoinInvPair12 : Unit → IO UInt64 := fun _ => do
  return runQAdjoinInvLadder (← getInvPair invPairRef12 12)
def runPariPolmodInv12 : Unit → IO UInt64 := fun _ => do
  pariPolmodInv (← getInvPair invPairRef12 12)

/-- Timing shape shared by both sides of every PARI pair: the discarded
`warmupFirstIter` call builds the lazily cached rung fixture (and, on the
PARI side, spawns the persistent driver) outside the timed region, and the
raised `minTotalSeconds` floor amortises steady-state work across the
auto-tuned inner-repeat batch so per-rung ratios compare like with like. -/
def pariCompareConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 30.0, warmupFirstIter := true,
    minTotalSeconds := 0.2 }

/- Fixed per-rung process-call comparator registrations for PARI t_POLMOD
multiplication against `QAdjoin` multiplication (quadratic-cost surface; see
the `runQAdjoinMulLadder` derivation). Identical inputs, identical reduced
rational coefficient hash on both sides. -/
setup_fixed_benchmark runQAdjoinMulPair4 where pariCompareConfig
setup_fixed_benchmark runPariPolmodMul4 where pariCompareConfig
setup_fixed_benchmark runQAdjoinMulPair8 where pariCompareConfig
setup_fixed_benchmark runPariPolmodMul8 where pariCompareConfig
setup_fixed_benchmark runQAdjoinMulPair16 where pariCompareConfig
setup_fixed_benchmark runPariPolmodMul16 where pariCompareConfig

/- Fixed per-rung process-call comparator registrations for PARI t_POLMOD
inversion against `QAdjoin` extended-gcd inversion (quadratic
coefficient-operation surface; see the `runQAdjoinInvLadder` derivation). -/
setup_fixed_benchmark runQAdjoinInvPair4 where pariCompareConfig
setup_fixed_benchmark runPariPolmodInv4 where pariCompareConfig
setup_fixed_benchmark runQAdjoinInvPair8 where pariCompareConfig
setup_fixed_benchmark runPariPolmodInv8 where pariCompareConfig
setup_fixed_benchmark runQAdjoinInvPair12 where pariCompareConfig
setup_fixed_benchmark runPariPolmodInv12 where pariCompareConfig

end Hex.NumberFieldBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
