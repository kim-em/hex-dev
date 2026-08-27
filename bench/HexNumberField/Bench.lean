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
* `runExactFactorLadder` / `runCanonicalRepLadder`: the two separable
  certification phases exposed by exactification;
* `runExactLadder`: end-to-end exactification through a growing product of
  quadratic factors whose modular factorization requires recombination;
* `runMergeRootListLadder`: the duplicate-removal fold across the two Yun
  components of the repeated-factor fixed-field family;
* `runQAdjoinRootsLadder` / `runAlgebraicRootsLadder`: the two root APIs on
  non-degenerate inputs with a repeated factor (fixed field) and a
  `√2`-dependent coefficient (canonical coefficients);
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
  match positiveBinomialRoot? p m with
  | some rep =>
    let x := SimpleRoot.mk rep
    { p := p, x := x
      a := QAdjoin.reduce p x (DensePoly.ofCoeffs (denseRatCoeffs m 3))
      b := QAdjoin.reduce p x (DensePoly.ofCoeffs (denseRatCoeffs m 7)) }
  | none => panic! "prepFieldInput: isolation failed"

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
      match positiveBinomialRoot? p m with
      | some rep =>
        let x := SimpleRoot.mk rep
        { p := p, x := x
          a := QAdjoin.reduce p x (DensePoly.ofCoeffs (denseRatCoeffs m 5))
          checked := some ⟨⟨hirr, hdeg⟩⟩ }
      | none => panic! "prepInvInput: isolation failed"
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
    -- The degree-96 ceiling is set by the timed extended-gcd operation: its
    -- measured call is about 3.0 s there, supplying an upper asymptotic rung
    -- while remaining practical. The denser upper schedule exposes
    -- coefficient growth beyond the small-degree regime.
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
    -- The top rung costs about 92 s per call; a 60 s cap truncated the ladder
    -- there and left the verdict resting on the `C`-spread fallback instead of
    -- a fitted slope.
    maxSecondsPerCall := 300.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
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

def runExactFactorLadder (input : SelectionInput) : UInt64 :=
  match input.root with
  | some root =>
    match root.exactFactor? input.candidate with
    | some a => polyChecksum a.p
    | none => panic! "runExactFactorLadder: exactFactor? failed"
  | none => panic! "runExactFactorLadder: fixture preparation failed"

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

def runCanonicalRepLadder (input : Option CanonicalInput) : UInt64 :=
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

private def coefficientBits (p : ZPoly) : Nat :=
  p.toArray.foldl
    (fun bits coefficient =>
      max bits (if coefficient = 0 then 0 else Nat.log2 coefficient.natAbs + 1)) 0

def exactFamilyComplexity (count : Nat) : Nat :=
  let p := exactFactorFamily count
  let degree := p.degree?.getD 0
  let height := coefficientBits p
  degree ^ 9 + degree ^ 7 * height ^ 2

def exactFactorComplexity (n : Nat) : Nat :=
  let log := Nat.log2 (n + 2)
  n ^ 9 + n ^ 7 * log ^ 2 + n ^ 5 * log ^ 2

private structure ExactInput where
  root : Option AlgebraicRoot

private instance : Hashable ExactInput where
  hash input := (input.root.map rootChecksum).getD 0

private instance : Inhabited ExactInput := ⟨⟨none⟩⟩

def prepExactInput (n : Nat) : ExactInput :=
  let p := exactFactorFamily n
  ⟨mkLadderRoot? p⟩

def runExactLadder (input : ExactInput) : UInt64 :=
  match input.root with
  | some root =>
    match root.exact? with
    | some a => polyChecksum a.p
    | none => 1
  | none => 0

/- Cost model. Per SPEC §Complexity, exactification adds one
Berlekamp-Zassenhaus factorization of an enclosing polynomial of degree `2n`
plus factor-root selection. This family extends the BZ adversarial fixture
`(X^2 - 2)(X^2 - 3)` with further irreducible quadratic factors, so modular
factorization and Hensel lifting must feed a nontrivial combination search
rather than take the irreducible or linear-factor fast paths. The declared
model is the classical BHKS polynomial bound `d^9 + d^7 h^2` (the same shape
the HexBerlekampZassenhaus registrations declare), evaluated at the enclosing
polynomial's actual degree `d` and coefficient bit height `h`. -/
setup_benchmark runExactLadder n => (exactFamilyComplexity n)
  with prep := prepExactInput
  where {
    paramFloor := 2
    paramCeiling := 6
    paramSchedule := .custom #[2, 3, 4, 5, 6]
    maxSecondsPerCall := 30.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/- Cost model. `exactFactor?` certifies one degree-`n`, constant-height
candidate. Its irreducibility guard invokes the public BZ factorization API,
so the declaration includes the classical BHKS `n^9 + n^7 log^2 n` envelope.
It then isolates to separation depth, refines against the enclosing
polynomial, selects the matching root, and performs canonical re-isolation.
Applying the HexRoots state-of-practice isolation bound `~O(d^3 + d^2 tau)`
with the implementation's working-precision proxy `O(d^3 B^2)` and
`B = O(n log n)` adds `n^5 log^2 n`. -/
setup_benchmark runExactFactorLadder n => (exactFactorComplexity n)
  with prep := prepExactSelectionInput
  where {
    paramFloor := 2
    paramCeiling := 8
    paramSchedule := .custom #[2, 3, 4, 6, 8]
    maxSecondsPerCall := 30.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/- Cost model. `canonicalRep?` isolates a degree-`n`, constant-height
irreducible polynomial at separation depth, refines every isolation, and finds
the canonical disc matching the supplied root. With `B = O(n log n)`, the same
HexRoots isolation proxy `O(n^3 B^2)` gives `n^5 log^2 n`; refinement and the
linear selection scan are lower order. -/
setup_benchmark runCanonicalRepLadder n => (n ^ 5 * (Nat.log2 (n + 2)) ^ 2)
  with prep := prepCanonicalInput
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
      | [first, second] =>
        if first.size ≤ second.size then ⟨first.toList, second⟩
        else ⟨second.toList, first⟩
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
rational coefficient operations, while the same-polynomial comparisons are
constant-time square intersection tests. Summed over all candidates, both
parts are `O(n²)` coefficient/square operations. The fixture computes Yun,
norm eliminants, isolation, and disambiguation before timing begins. -/
setup_benchmark runMergeRootListLadder n => n * n
  with prep := prepMergeRootsInput
  where {
    paramFloor := 2
    paramCeiling := 8
    paramSchedule := .custom #[2, 3, 4, 6, 8]
    -- The timed merge is sub-millisecond, but preparing its isolated component
    -- roots is the same expensive prelude as the end-to-end ladder and reaches
    -- about one minute at n = 8.
    maxSecondsPerCall := 120.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/- Cost model. Per SPEC §Complexity the root API runs Yun decomposition
(`O(n²)` field operations, lower order here) and one norm eliminant per
squarefree component, then isolates and disambiguates. The earlier profile of
this exact family found only 7.61% of the call in `componentRoots?`, because
cross-component duplicate removal repeatedly exactified the same roots. The
rational-gcd guard measured by `runMergeRootListLadder` makes those coprime
comparisons quadratic lower-order work. The repaired profile puts 92.94% in
`componentRoots?` and 85.01% in `isolate`, so the degree-`d = 2n` norm
eliminant's separation-depth isolation supplies the ceiling again. Following
the HexRoots wall-model convention, its `d⁵` degree shape suppresses
polylogarithms; this registration retains one conservative
`log₂(d) + 1` limb-growth proxy. Constants in `d = 2n` drop out, giving
`n⁵ (log₂(n + 2) + 1)`. The shared double-resultant evaluation eliminant
remains unisolated and was below profile resolution. -/
setup_benchmark runQAdjoinRootsLadder n =>
    n ^ 5 * (Nat.log2 (n + 2) + 1)
  with prep := prepFieldRootsInput
  where {
    -- Degree 1 leaves the norm eliminant linear, so that rung measures the
    -- Yun and embedding prelude rather than the degree-`2n` isolation the
    -- model declares; the ladder starts at 2 and reaches 8.
    paramFloor := 2
    paramCeiling := 8
    paramSchedule := .custom #[2, 3, 4, 6, 8]
    maxSecondsPerCall := 900.0
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
    -- The common-field embedding is linear in the coefficient count and costs
    -- tens of milliseconds; below three coefficients it is comparable to the
    -- root work the model declares, so the ladder starts at 3 and reaches 8.
    paramFloor := 3
    paramCeiling := 8
    paramSchedule := .custom #[3, 4, 5, 6, 8]
    maxSecondsPerCall := 300.0
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

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
