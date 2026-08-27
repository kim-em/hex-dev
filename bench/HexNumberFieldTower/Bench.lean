/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexNumberFieldTower
import Hex.BenchOracle.Pari
import Lean.Data.Json
import LeanBench

/-!
Benchmark registrations for `HexNumberFieldTower`.

The fixed cases expose the Phase-4 components named by the library SPEC:

* addition, subtraction, negation, multiplication, recursive inversion,
  division, and rational scalar action in the dimension-four tower
  `Q(sqrt(2), sqrt(3))`;
* adjoining a fourth root of two to `Q(sqrt(2))`;
* rational, one-level Trager-retry, and recursive two-level factorization;
* splitting a quartic through two genuine extensions;
* flattening a two-level tower to a primitive-element presentation.

Every fixed case stays within tower dimension four and input degree four;
the isolated recovery adversary uses absolute degree six.

The parametric ladders carry the Phase-4 asymptotic evidence:

* `runTowerAddLadder` / `runTowerMulLadder` / `runTowerInvLadder`:
  coordinate arithmetic in the height-two tower `Q(sqrt(2), 3^{1/m})` at
  growing dimension `D = 2m`;
* `runTowerFactorLadder`: Trager factorization over `Q(sqrt(2))` of the
  degree-`n` Selmer trinomial `X^n - X - 1`, whose rational coefficients
  force the shift-zero norm to repeat, exercising the bounded shift search,
  a genuine one-level norm retry, the recursive rational factorization of
  the accepted degree-`2n` norm, and gcd recovery.

Informational PARI comparator (`SPEC/benchmarking.md` §External comparators
§Process call): `nffactor` is the callable PARI surface matching tower
polynomial factorization at one level. The `runTowerFactorPair*` /
`runPariNfFactor*` fixed rungs consume the same deterministic Selmer input
over `Q(sqrt(2))` and hash the identical sorted factor
degree/multiplicity multiset — the representation-free observable both
implementations share — so `compare` joins on result hashes. The PARI side
runs through the persistent-subprocess driver
`scripts/oracle/pari_bench_driver.py` (one JSON request per line; started by
a `warmupFirstIter` call outside the timed region and reused across the
child's auto-tuned inner-repeat batch — see `Hex/BenchOracle/Pari.lean`).
Both sides of every pair use `warmupFirstIter` and the same
`minTotalSeconds` floor so per-rung ratios compare steady-state medians on
the same basis. Tower element arithmetic, adjoining, splitting, and
flattening have no comparable PARI unit surface; see the SPEC's External
comparators section. The driver is Mathlib-free.
-/

namespace Hex.NumberTowerBench

open Hex
open Hex.NumberTower

private def requireSome (case : String) : Option α → IO α
  | some value => pure value
  | none => throw <| IO.userError (case ++ ": benchmark fixture failed")

private def ratChecksum (q : Rat) : UInt64 :=
  mixHash (hash q.num) (hash (q.den : Int))

private def elemChecksum {T : NumberTower} (a : Elem T) : UInt64 :=
  (coeffs a).foldl
    (fun checksum q => mixHash checksum (ratChecksum q))
    (hash T.dim)

private def polyChecksum {T : NumberTower} (p : Poly T) : UInt64 :=
  p.toArray.foldl
    (fun checksum coefficient => mixHash checksum (elemChecksum coefficient))
    (hash p.toArray.size)

private def zpolyChecksum (p : ZPoly) : UInt64 :=
  hash p.toArray

private def rawPolyChecksum (p : Array (Array Rat)) : UInt64 :=
  p.foldl
    (fun checksum coefficient => coefficient.foldl
      (fun checksum q => mixHash checksum (ratChecksum q)) checksum)
    (hash p.size)

private def qAdjoinChecksum {p : ZPoly} {x : SimpleRoot p}
    (a : QAdjoin p x) : UInt64 :=
  a.coeffs.toArray.foldl
    (fun checksum q => mixHash checksum (ratChecksum q))
    (hash a.coeffs.size)

private def extensionChecksum {T : NumberTower}
    (extension : Extension T) : UInt64 :=
  mixHash (hash extension.tower.dim) <|
    mixHash (elemChecksum extension.gen) (zpolyChecksum extension.root.p)

private def factorChecksum {T : NumberTower} {f : Poly T}
    (result : Hex.NumberTower.Factorization T f) : UInt64 :=
  result.factors.foldl
    (fun checksum entry =>
      mixHash checksum <| mixHash (polyChecksum entry.1) (hash entry.2))
    (elemChecksum result.scalar)

private def splitChecksum {T : NumberTower} {f : Poly T}
    (result : Splitting T f) : UInt64 :=
  let initial := mixHash (hash result.extension.tower.dim)
    (hash result.extension.tower.height)
  match result.roots with
  | .all => mixHash initial 1
  | .finite roots => roots.foldl
      (fun checksum entry =>
        mixHash checksum <| mixHash (elemChecksum entry.1) (hash entry.2))
      initial

private def flattenChecksum {T : NumberTower}
    (result : Flattening T) : UInt64 :=
  (List.range T.dim).foldl
    (fun checksum i =>
      let basis := ofCoeffs T (Flatten.unitCoords T.dim i)
      let primitive := result.toPrimitive basis
      let roundTrip := result.fromPrimitive primitive
      mixHash checksum <|
        mixHash (qAdjoinChecksum primitive) (elemChecksum roundTrip))
    (mixHash (zpolyChecksum result.root.p) (hash T.dim))

private def recoveredChecksum (result : Flatten.Recovered) : UInt64 :=
  mixHash (hash result.shift) <| mixHash (zpolyChecksum result.root.p) <|
    mixHash (qAdjoinChecksum result.thetaCoordinate)
      (qAdjoinChecksum result.alphaCoordinate)

/-! # Shared fixed-embedding fixtures -/

private def sqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def sqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def sqrtTwoRep : RefinedIsolation sqrtTwoPoly :=
  ⟨⟨sqrtTwoSquare, .ofWitness (by decide)⟩, by decide⟩

private def sqrtTwo? (_ : Unit) : Option (Extension rat) :=
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly :=
      ⟨hirred, by decide⟩
    if hsimple : HasOnlySimpleRoots sqrtTwoPoly then
      some (ofQAdjoin (x := SimpleRoot.mk sqrtTwoRep)
        hsimple sqrtTwoRep rfl)
    else
      none
  else
    none

private def sqrtThreePoly : ZPoly := DensePoly.ofList [-3, 0, 1]

private def sqrtThreeSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 222 7, 0, 8⟩

private def sqrtThreeRep : RefinedIsolation sqrtThreePoly :=
  ⟨⟨sqrtThreeSquare, .ofWitness (by decide)⟩, by decide⟩

private def sqrtThree? (_ : Unit) : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots sqrtThreePoly then
    some
      { p := sqrtThreePoly, prim := by rfl, pos_lc := by decide
        pos_degree := by decide, squarefree := hsimple
        x := SimpleRoot.mk sqrtThreeRep, rep := sqrtThreeRep, rep_mk := rfl }
  else
    none

private def fourthRootTwoPoly : ZPoly :=
  DensePoly.ofList [-2, 0, 0, 0, 1]

private def fourthRootTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 77936 16, 0, 17⟩

private def fourthRootTwoRep : RefinedIsolation fourthRootTwoPoly :=
  ⟨⟨fourthRootTwoSquare, .ofWitness (by decide)⟩, by decide⟩

private def fourthRootTwo? (_ : Unit) : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots fourthRootTwoPoly then
    some
      { p := fourthRootTwoPoly, prim := by rfl, pos_lc := by decide
        pos_degree := by decide, squarefree := hsimple
        x := SimpleRoot.mk fourthRootTwoRep, rep := fourthRootTwoRep
        rep_mk := rfl }
  else
    none

/- This cyclotomic pair has a full-degree candidate at shift `+1` whose
recovery gcd is nonlinear; shift `-1` is the first recoverable candidate. -/
private def retryThetaPoly : ZPoly :=
  DensePoly.ofList [-1, -2, 1, 1]

private def retryThetaSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 1371068573887 40, 0, 16⟩

private def retryThetaRep : RefinedIsolation retryThetaPoly :=
  ⟨⟨retryThetaSquare, .ofWitness (by decide)⟩, by decide⟩

private def retryTheta? (_ : Unit) : Option AlgebraicNumber :=
  if hsimple : HasOnlySimpleRoots retryThetaPoly then
    let root : AlgebraicRoot :=
      { p := retryThetaPoly, prim := by rfl, pos_lc := by decide
        pos_degree := by decide, squarefree := hsimple
        x := SimpleRoot.mk retryThetaRep, rep := retryThetaRep, rep_mk := rfl }
    root.exact?
  else
    none

private def retryAlphaPoly : ZPoly :=
  DensePoly.ofList [29, -1, 15, -1, 1, -1, 1]

private def retryAlphaSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec (-1501032013268545746) 60,
    Dyadic.ofIntWithPrec 1525171791184062904 60, 52⟩

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 1000 in
private def retryAlphaRep : RefinedIsolation retryAlphaPoly :=
  ⟨⟨retryAlphaSquare, .ofWitness (by decide)⟩, by decide⟩

private def retryAlpha? (_ : Unit) : Option AlgebraicNumber :=
  if hsimple : HasOnlySimpleRoots retryAlphaPoly then
    let root : AlgebraicRoot :=
      { p := retryAlphaPoly, prim := by rfl, pos_lc := by decide
        pos_degree := by decide, squarefree := hsimple
        x := SimpleRoot.mk retryAlphaRep, rep := retryAlphaRep, rep_mk := rfl }
    root.exact?
  else
    none

private structure RetryPair where
  theta : AlgebraicNumber
  alpha : AlgebraicNumber

private def retryPair? (_ : Unit) : Option RetryPair := do
  some ⟨← retryTheta? (), ← retryAlpha? ()⟩

private structure RecoveryInput where
  theta : AlgebraicNumber
  alpha : AlgebraicNumber
  gamma : AlgebraicNumber
  shift : Int

private def recoveryInput? (_ : Unit) : Option RecoveryInput := do
  let pair ← retryPair? ()
  let (shift, gamma) ← Flatten.candidateAt? pair.theta pair.alpha 6 1
  some ⟨pair.theta, pair.alpha, gamma, shift⟩

private structure TwoLevel where
  base : Extension rat
  extension : Extension base.tower

private def twoLevel? (_ : Unit) : Option TwoLevel := do
  let base ← sqrtTwo? ()
  let root ← sqrtThree? ()
  let extension ← adjoin? base.tower root
  some ⟨base, extension⟩

private structure CandidateInput where
  tower : TwoLevel
  generators : Array (Flatten.Generator tower.extension.tower)
  candidate : Flatten.Candidate tower.extension.tower

private structure CertifyInput where
  tower : TwoLevel
  candidate : Flatten.Candidate tower.extension.tower
  images : Array (QAdjoin candidate.root.p candidate.root.x)

private structure MapInput where
  tower : TwoLevel
  result : Flattening tower.extension.tower

private structure QAdjoinInput where
  rep : RefinedIsolation sqrtTwoPoly
  irreducible : ZPoly.isIrreducible sqrtTwoPoly = true
  simple : HasOnlySimpleRoots sqrtTwoPoly

private def qAdjoinInput? (_ : Unit) : Option QAdjoinInput :=
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    if hsimple : HasOnlySimpleRoots sqrtTwoPoly then
      some ⟨sqrtTwoRep, hirred, hsimple⟩
    else
      none
  else
    none

private def rationalPoly (coefficients : List Rat) : Poly rat :=
  DensePoly.ofCoeffs (coefficients.toArray.map (ofRat rat))

initialize sqrtTwoRef : IO.Ref (Option (Extension rat)) ← IO.mkRef none

initialize qAdjoinInputRef : IO.Ref (Option QAdjoinInput) ← IO.mkRef none

initialize fourthRootRef : IO.Ref (Option AlgebraicRoot) ← IO.mkRef none

initialize twoLevelRef : IO.Ref (Option TwoLevel) ← IO.mkRef none

private def getSqrtTwo : IO (Extension rat) := do
  if let some extension ← sqrtTwoRef.get then
    return extension
  let extension ← requireSome "sqrt-two-fixture" (sqrtTwo? ())
  sqrtTwoRef.set (some extension)
  return extension

private def getQAdjoinInput : IO QAdjoinInput := do
  if let some input ← qAdjoinInputRef.get then
    return input
  let input ← requireSome "of-qadjoin preparation" (qAdjoinInput? ())
  qAdjoinInputRef.set (some input)
  return input

private def getFourthRoot : IO AlgebraicRoot := do
  if let some root ← fourthRootRef.get then
    return root
  let root ← requireSome "fourth-root-fixture" (fourthRootTwo? ())
  fourthRootRef.set (some root)
  return root

private def getTwoLevel : IO TwoLevel := do
  match ← twoLevelRef.get with
  | some tower => pure tower
  | none =>
      let tower ← requireSome "two-level-fixture" (twoLevel? ())
      twoLevelRef.set (some tower)
      pure tower

initialize candidateInputRef : IO.Ref (Option CandidateInput) ←
  IO.mkRef none

initialize certifyInputRef : IO.Ref (Option CertifyInput) ←
  IO.mkRef none

initialize mapInputRef : IO.Ref (Option MapInput) ← IO.mkRef none

private def getCandidateInput : IO CandidateInput := do
  match ← candidateInputRef.get with
  | some input => pure input
  | none =>
      let tower ← getTwoLevel
      let generators ← requireSome "flatten/candidate-fixture"
        (Flatten.generators? tower.extension.tower)
      let candidate ← requireSome "flatten/candidate-fixture"
        (Flatten.candidate? tower.extension.tower generators)
      let input : CandidateInput := ⟨tower, generators, candidate⟩
      candidateInputRef.set (some input)
      pure input

private def getCertifyInput : IO CertifyInput := do
  match ← certifyInputRef.get with
  | some input => pure input
  | none =>
      let candidate ← getCandidateInput
      let images := Flatten.basisImages
        candidate.generators candidate.candidate.coordinates
      let input : CertifyInput :=
        ⟨candidate.tower, candidate.candidate, images⟩
      certifyInputRef.set (some input)
      pure input

private def getMapInput : IO MapInput := do
  match ← mapInputRef.get with
  | some input => pure input
  | none =>
      let tower ← getTwoLevel
      let result ← requireSome "flatten/map-fixture"
        (flatten? tower.extension.tower)
      let input : MapInput := ⟨tower, result⟩
      mapInputRef.set (some input)
      pure input

initialize recoveryInputRef : IO.Ref (Option RecoveryInput) ←
  IO.mkRef none

/- Exactifying the degree-six cyclotomic fixture is deliberately lazy. The
fixed harness's first warmup call populates this process-local cache, so fixture
construction is neither timed nor paid by unrelated benchmark child processes. -/
private def getRecoveryInput : IO RecoveryInput := do
  match ← recoveryInputRef.get with
  | some input => pure input
  | none =>
      let input ← requireSome "flatten/recovery-fixture" (recoveryInput? ())
      recoveryInputRef.set (some input)
      pure input

/-! # Arithmetic and adjoining -/

def runOfQAdjoin : Unit → IO UInt64 := fun _ => do
  let input ← getQAdjoinInput
  letI : ZPoly.CheckedIrreducible sqrtTwoPoly :=
    ⟨input.irreducible, by decide⟩
  return extensionChecksum
    (ofQAdjoin (x := SimpleRoot.mk input.rep) input.simple input.rep rfl)

def runAdd : Unit → IO UInt64 := fun _ => do
  let tower ← getTwoLevel
  let sqrtTwo := tower.extension.embed tower.base.gen
  return elemChecksum (sqrtTwo + tower.extension.gen)

def runMul : Unit → IO UInt64 := fun _ => do
  let tower ← getTwoLevel
  let sqrtTwo := tower.extension.embed tower.base.gen
  let value := sqrtTwo + tower.extension.gen
  return elemChecksum (value * value)

def runInv : Unit → IO UInt64 := fun _ => do
  let tower ← getTwoLevel
  let sqrtTwo := tower.extension.embed tower.base.gen
  let value := sqrtTwo + tower.extension.gen
  return elemChecksum value⁻¹

def runAdjoin : Unit → IO UInt64 := fun _ => do
  let base ← getSqrtTwo
  let root ← getFourthRoot
  return extensionChecksum
    (← requireSome "adjoin/fourth-root" (adjoin? base.tower root))

def runAdjoinIdentity : Unit → IO UInt64 := fun _ => do
  let base ← getSqrtTwo
  return extensionChecksum
    (← requireSome "adjoin/identity" (adjoin? base.tower base.root))

/- Constructing the canonical one-level presentation normalizes the defining
relation, installs the selected embedding, and certifies the tower boundary.
Irreducibility and simple-root decisions are hoisted outside the timed body. -/
setup_fixed_benchmark runOfQAdjoin where {
  repeats := 5, maxSecondsPerCall := 2.0,
  expectedHash := some 0x51ddf5878af8a696
}

/- Coordinate addition visits exactly `D` rational coordinates. This fixed
`D = 4` case isolates that linear operation from multiplication and inversion. -/
setup_fixed_benchmark runAdd where {
  repeats := 5, maxSecondsPerCall := 2.0,
  expectedHash := some 0xd381defc58f22934
}

/- Schoolbook multiplication and recursive reduction visit `O(D^2)` pairs of
coordinates before coefficient-size growth. -/
setup_fixed_benchmark runMul where {
  repeats := 5, maxSecondsPerCall := 2.0,
  expectedHash := some 0xca888473e6359390
}

/- Top-level extended gcd recursively invokes lower-tower division; unlike
multiplication, its cost depends on both tower dimension and height. This fixed
`D = 4`, height-two case attributes recursive inversion separately. -/
setup_fixed_benchmark runInv where {
  repeats := 5, maxSecondsPerCall := 2.0,
  expectedHash := some 0xfdfda24536fdd084
}

/- Adjoining the fourth root factors a degree-four absolute presentation over
a dimension-two base, selects the quadratic relative factor using the fixed
embedding, and validates the new level. This fixed case attributes that whole
smart-constructor boundary. -/
setup_fixed_benchmark runAdjoin where {
  repeats := 3, maxSecondsPerCall := 10.0,
  expectedHash := some 0xde9179e4f67a3948
}

/- Adjoining a root already represented in the base selects a linear factor
and returns an identity extension instead of appending a redundant level. -/
setup_fixed_benchmark runAdjoinIdentity where {
  repeats := 3, maxSecondsPerCall := 10.0,
  expectedHash := some 0x51ddf5878af8a696
}

/-! # Trager factorization -/

private def repeatedNormInput : Array (Array Rat) :=
  #[#[-3, 0], #[0, 0], #[1, 0]]

initialize repeatedNormRef : IO.Ref (Option (Array (Array Rat))) ←
  IO.mkRef (some repeatedNormInput)

def runOneLevelNorm : Unit → IO UInt64 := fun _ => do
  let base ← getSqrtTwo
  let level ← requireSome "norm/one-level" base.tower.levels[0]?
  let input ← requireSome "norm/one-level" (← repeatedNormRef.get)
  return rawPolyChecksum (Norm.oneLevel level [] input 0)

def runShiftSearch : Unit → IO UInt64 := fun _ => do
  let base ← getSqrtTwo
  let level ← requireSome "norm/shift-search" base.tower.levels[0]?
  let input ← requireSome "norm/shift-search" (← repeatedNormRef.get)
  let (shift, norm) ← requireSome "norm/shift-search"
    (Norm.findSquarefreeShift level [] input)
  return mixHash (hash shift) (rawPolyChecksum norm)

private def repeatedInput : Poly rat :=
  rationalPoly [4, 0, -4, 0, 1]

initialize repeatedRef : IO.Ref (Option (Poly rat)) ←
  IO.mkRef (some repeatedInput)

private def repeatedFactor? (_ : Unit) :
    Option (Hex.NumberTower.Factorization rat repeatedInput) :=
  factor? rat repeatedInput

initialize repeatedFactorRef : IO.Ref
    (Option (Hex.NumberTower.Factorization rat repeatedInput)) ←
  IO.mkRef none

private def getRepeatedFactor : IO (Hex.NumberTower.Factorization rat repeatedInput) := do
  if let some result ← repeatedFactorRef.get then
    return result
  let result ← requireSome "factor/check preparation" (repeatedFactor? ())
  repeatedFactorRef.set (some result)
  return result

def runFactorRat : Unit → IO UInt64 := fun _ => do
  let input ← requireSome "factor/rational" (← repeatedRef.get)
  return factorChecksum
    (← requireSome "factor/rational" (factor? rat input))

def runFactorRetry : Unit → IO UInt64 := fun _ => do
  let base ← getSqrtTwo
  let T := base.tower
  let input : Poly T := DensePoly.ofCoeffs #[ofRat T (-3), 0, 1]
  return factorChecksum
    (← requireSome "factor/retry" (factor? T input))

def runFactorRecursive : Unit → IO UInt64 := fun _ => do
  let tower ← getTwoLevel
  let T := tower.extension.tower
  let input : Poly T := DensePoly.ofCoeffs #[ofRat T (-3), 0, 1]
  return factorChecksum
    (← requireSome "factor/recursive" (factor? T input))

def runCheckFactorization : Unit → IO UInt64 := fun _ => do
  let result ← getRepeatedFactor
  return hash (checkFactorization repeatedInput result.scalar result.factors)

/- One Trager norm constructs the shifted outer polynomial and computes one
Brown resultant over the lower rational tower. This is the retry loop's
separable dominant inner operation. -/
setup_fixed_benchmark runOneLevelNorm where {
  repeats := 5, maxSecondsPerCall := 5.0,
  expectedHash := some 0x98a9884aa98ddd32
}

/- The canonical retry input has a repeated shift-zero norm, so the bounded
search computes another one-level norm at shift one and checks squarefreeness. -/
setup_fixed_benchmark runShiftSearch where {
  repeats := 5, maxSecondsPerCall := 5.0,
  expectedHash := some 0x0bb795ff2f22014a
}

/- Rational factorization separates Yun multiplicity for the degree-four
square `(X^2 - 2)^2` and then performs one integer factorization. The fixed
case is the base-case reference for the two Trager registrations below. -/
setup_fixed_benchmark runFactorRat where {
  repeats := 3, maxSecondsPerCall := 5.0,
  expectedHash := some 0x90fa5a1ee979f50c
}

/- Over `Q(sqrt(2))`, the shift-zero norm of `X^2 - 3` is repeated, so the
bounded Trager search advances to a square-free one-level norm before gcd
recovery. This isolates retry cost at base dimension two and input degree two. -/
setup_fixed_benchmark runFactorRetry where {
  repeats := 3, maxSecondsPerCall := 10.0,
  expectedHash := some 0xf830f035fb69256e
}

/- Over `Q(sqrt(2), sqrt(3))`, `X^2 - 3` factors through the intermediate
field. The fixed dimension-four case measures recursive one-level norms and
lower-field factorization instead of an invalid absolute-norm shortcut. -/
setup_fixed_benchmark runFactorRecursive where {
  repeats := 3, maxSecondsPerCall := 10.0,
  expectedHash := some 0xd13bbfca65f65898
}

/- Replay reconstruction, multiplicities, canonical order, and recursive
irreducibility for a precomputed rational factorization. -/
setup_fixed_benchmark runCheckFactorization where {
  repeats := 5, maxSecondsPerCall := 5.0,
  expectedHash := some 0x000000000000000b
}

/-! # Splitting and flattening -/

private def quarticInput : Poly rat :=
  rationalPoly [6, 0, -5, 0, 1]

initialize quarticRef : IO.Ref (Option (Poly rat)) ←
  IO.mkRef (some quarticInput)

def runSplit : Unit → IO UInt64 := fun _ => do
  let input ← requireSome "split/quartic" (← quarticRef.get)
  return splitChecksum (← requireSome "split/quartic" (split? rat input))

def runFlatten : Unit → IO UInt64 := fun _ => do
  let tower ← getTwoLevel
  return flattenChecksum
    (← requireSome "flatten/two-level" (flatten? tower.extension.tower))

def runBasisImages : Unit → IO UInt64 := fun _ => do
  let input ← getCandidateInput
  let images := Flatten.basisImages
    input.generators input.candidate.coordinates
  return images.foldl
    (fun checksum image => mixHash checksum (qAdjoinChecksum image))
    (hash images.size)

def runCertifies : Unit → IO UInt64 := fun _ => do
  let input ← getCertifyInput
  return hash (Flatten.certifies input.candidate input.images)

def runCoordinateMaps : Unit → IO UInt64 := fun _ => do
  let input ← getMapInput
  return flattenChecksum input.result

def runRecoverPair : Unit → IO UInt64 := fun _ => do
  let input ← getRecoveryInput
  match Flatten.recoverPairFast?
      input.theta input.alpha input.gamma input.shift with
  | none => return mixHash (hash input.shift) (hash true)
  | some coordinates =>
      return mixHash (qAdjoinChecksum coordinates.1)
        (qAdjoinChecksum coordinates.2)

def runRecoverSearch : Unit → IO UInt64 := fun _ => do
  let input ← getRecoveryInput
  return recoveredChecksum (← requireSome "flatten/recover-search"
    (Flatten.searchRecoveredAux input.theta input.alpha 6 1 2))

/- Splitting `(X^2 - 2)(X^2 - 3)` factors and performs two genuine adjoining
steps before collecting four simple roots. Dimension and input degree are both
four, so this fixed case measures the complete degree-reducing outer loop. -/
setup_fixed_benchmark runSplit where {
  repeats := 2, maxSecondsPerCall := 20.0,
  expectedHash := some 0xd863bc339d467bf8
}

/- The shift-`+1` full-degree candidate performs the exact Euclidean gcd over
its degree-six primitive field and rejects the resulting nonlinear recovery.
This isolates the fast flattening scan without invoking trace recovery. -/
setup_fixed_benchmark runRecoverPair where {
  repeats := 2, maxSecondsPerCall := 20.0,
  expectedHash := some 0x190011a8e6411c8e
}

/- The two-candidate search first pays the rejected recovery gcd at shift
`+1`, then repeats candidate formation and accepts the linear gcd at `-1`. -/
setup_fixed_benchmark runRecoverSearch where {
  repeats := 1, maxSecondsPerCall := 60.0,
  expectedHash := some 0xf696f44e1e1e7ef7
}

/- `basisImages` expands recovered generator coordinates into the complete
mixed-radix tower basis. The candidate search is precomputed for attribution. -/
setup_fixed_benchmark runBasisImages where {
  repeats := 5, maxSecondsPerCall := 5.0,
  expectedHash := some 0xb5d54195958fb61e
}

/- Certification checks the primitive relation and both coordinate maps on
every tower basis vector for precomputed candidate images. -/
setup_fixed_benchmark runCertifies where {
  repeats := 5, maxSecondsPerCall := 5.0,
  expectedHash := some 0x000000000000000b
}

/- The public conversion closures are timed from a precomputed flattening;
the checksum applies both directions to every dimension-four basis vector. -/
setup_fixed_benchmark runCoordinateMaps where {
  repeats := 5, maxSecondsPerCall := 5.0,
  expectedHash := some 0xcc1b7720bfe3fc24
}

/- Flattening the dimension-four two-level tower searches signed primitive
shifts, constructs a degree-four eliminant, performs exact linear recovery,
and verifies both coordinate maps. This covers the complete primitive-element
path at the CI size bound. -/
setup_fixed_benchmark runFlatten where {
  repeats := 2, maxSecondsPerCall := 20.0,
  expectedHash := some 0xcc1b7720bfe3fc24
}


/-! # Fixed registrations completing the arithmetic surface -/

def runSub : Unit → IO UInt64 := fun _ => do
  let tower ← getTwoLevel
  let sqrtTwo := tower.extension.embed tower.base.gen
  return elemChecksum (sqrtTwo - tower.extension.gen)

def runNeg : Unit → IO UInt64 := fun _ => do
  let tower ← getTwoLevel
  let sqrtTwo := tower.extension.embed tower.base.gen
  let value := sqrtTwo + tower.extension.gen
  return elemChecksum (-value)

def runDiv : Unit → IO UInt64 := fun _ => do
  let tower ← getTwoLevel
  let sqrtTwo := tower.extension.embed tower.base.gen
  let value := sqrtTwo + tower.extension.gen
  return elemChecksum (sqrtTwo / value)

def runSMul : Unit → IO UInt64 := fun _ => do
  let tower ← getTwoLevel
  let sqrtTwo := tower.extension.embed tower.base.gen
  let value := sqrtTwo + tower.extension.gen
  return elemChecksum ((mkRat 3 7) • value)

/- Coordinate subtraction, like addition, visits exactly `D` rational
coordinates; this fixed `D = 4` case completes the linear-cost surface. -/
setup_fixed_benchmark runSub where {
  repeats := 5, maxSecondsPerCall := 2.0
}

/- Negation visits `D` coordinates with one rational negation each; the
linear cost model matches addition. -/
setup_fixed_benchmark runNeg where {
  repeats := 5, maxSecondsPerCall := 2.0
}

/- Division composes recursive extended-gcd inversion with one `O(D^2)`
multiplication/reduction; the inversion term dominates as in `runInv`. -/
setup_fixed_benchmark runDiv where {
  repeats := 5, maxSecondsPerCall := 2.0
}

/- Rational scalar action multiplies each of the `D` coordinates by one
rational, a linear-cost surface like addition. -/
setup_fixed_benchmark runSMul where {
  repeats := 5, maxSecondsPerCall := 2.0
}

/-! # Parametric dimension ladders -/

/-- `X^m - 3`, Eisenstein-irreducible at `3` for every `m ≥ 1`; its degree
over `ℚ(√2)` is still `m` (the only quadratic subfield a pure cube/fourth/…
root field of `3` can contain is `ℚ(√3)`), so adjoining its first root to
`ℚ(√2)` yields a height-two tower of dimension `2m`. -/
private def xPowSubThree (m : Nat) : ZPoly :=
  DensePoly.ofList ((-3 : Int) :: List.replicate (m - 1) 0 ++ [1])

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

/-- The height-two ladder tower `ℚ(√2, 3^{1/m})` (just `ℚ(√2)` at `m = 1`). -/
private def ladderTower? (m : Nat) : Option NumberTower := do
  let base ← sqrtTwo? ()
  if m ≤ 1 then
    pure base.tower
  else do
    let root ← mkLadderRoot? (xPowSubThree m)
    let extension ← adjoin? base.tower root
    pure extension.tower

/-- Prepared dimension-`2m` coordinate-arithmetic fixture with two
all-nonzero-coordinate elements. -/
private structure ElemInput where
  tower : NumberTower
  a : Elem tower
  b : Elem tower

private instance : Hashable ElemInput where
  hash input :=
    mixHash (hash input.tower.dim)
      (mixHash (elemChecksum input.a) (elemChecksum input.b))

private instance : Inhabited ElemInput :=
  ⟨⟨rat, ofRat rat 1, ofRat rat 2⟩⟩

/-- Deterministic dense all-nonzero mixed-radix coordinates with bounded
height: numerators cycle modulo 11 and denominators modulo 6, so every
reduced common denominator divides `lcm(1, ..., 6) = 60` at every
dimension. The previous denominator shape `i + 3` varied with the
coordinate index, so the lcm of the vector's denominators had `Θ(D)` bit
length and the ladders varied coefficient height together with dimension
instead of holding it fixed as their one-parameter cost models require
(the same correction `denseRatCoeff` records in the HexNumberField
bench). -/
private def ladderCoords (d salt : Nat) : Array Rat :=
  (Array.range d).map fun i =>
    let sign : Int := if (i + salt) % 2 == 0 then 1 else -1
    mkRat (sign * Int.ofNat ((i * 7 + salt * 3) % 11 + 1)) ((i * 5 + salt) % 6 + 1)

def prepElemInput (n : Nat) : ElemInput :=
  let m := max n 1
  match ladderTower? m with
  | some tower =>
    let d := tower.dim
    { tower := tower
      a := ofCoeffs tower (ladderCoords d 3)
      b := ofCoeffs tower (ladderCoords d 7) }
  | none => panic! "prepElemInput: tower fixture failed"

def runTowerAddLadder (input : ElemInput) : UInt64 :=
  elemChecksum (input.a + input.b)

def runTowerMulLadder (input : ElemInput) : UInt64 :=
  elemChecksum (input.a * input.b)

def runTowerInvLadder (input : ElemInput) : UInt64 :=
  elemChecksum input.a⁻¹

/- Cost model. Coordinate addition adds the two mixed-radix coordinate
vectors pointwise: exactly `D = 2n` rational additions for the
dimension-`2n` ladder tower (SPEC §Complexity: "Coordinate addition costs
O(D) rational operations"). Fixture coordinate heights are bounded, so each
rational operation is `O(1)` words and the declared wall model is linear in
the parameter. -/
setup_benchmark runTowerAddLadder n => n
  with prep := prepElemInput
  where {
    paramFloor := 1
    paramCeiling := 6
    paramSchedule := .custom #[1, 2, 3, 4, 6]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Cost model. Schoolbook tower multiplication convolves the mixed-radix
coordinates and reduces from the top generator downward, `O(D^2)` rational
operations at dimension `D = 2n` (SPEC §Complexity: "Schoolbook
multiplication and reduction cost O(D²)"). Bounded fixture heights make each
rational operation `O(1)` words, so the declared wall model is quadratic.
The schedule extends through `n = 12` because the normalized cost has a
small-dimension transient (per-element construction and the `O(D)` checksum
walk weigh more against `D²` work at dimension four) that flattens from
`n = 6` on; the raised per-call cap accommodates the untimed tower-fixture
construction at `m = 8` and `m = 12`, whose `adjoin?` factors `X^m - 3`
over `ℚ(√2)` outside the timed region. -/
setup_benchmark runTowerMulLadder n => n * n
  with prep := prepElemInput
  where {
    paramFloor := 1
    paramCeiling := 12
    paramSchedule := .custom #[1, 2, 3, 4, 6, 8, 12]
    maxSecondsPerCall := 300.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Cost model. Inversion runs the extended gcd in the top quotient
`K[y]/(m_top)` with `deg m_top = n` over the fixed quadratic base `K`:
`O(n^2)` coefficient operations in `K`, each `O(1)` base-field operations
at the fixed base dimension, so `O(n^2) = O(D^2)` rational operations
overall. Rational coefficient growth along the Euclidean chain is modelled
with the same logarithmic limb-growth proxy the HexResultant Brown-chain
registrations use, giving the declared `n^2 log n` wall model. -/
setup_benchmark runTowerInvLadder n => n * n * (Nat.log2 (n + 2) + 1)
  with prep := prepElemInput
  where {
    paramFloor := 1
    paramCeiling := 6
    paramSchedule := .custom #[1, 2, 3, 4, 6]
    maxSecondsPerCall := 30.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/-! # Trager factorization ladder -/

/-- Ascending rational coefficients of the Selmer trinomial `X^m - X - 1`
(irreducible over `ℚ` for every `m ≥ 2`, and over `ℚ(√2)` because its
Galois group `S_m` leaves `ℚ(root)` without quadratic subfields). Shared by
the Lean fixture and the PARI comparator request so both sides factor the
same input. -/
private def selmerRatCoeffs (m : Nat) : Array Rat :=
  (Array.range (m + 1)).map fun i =>
    if i == 0 || i == 1 then (-1 : Rat) else if i == m then 1 else 0

/-- The Selmer trinomial as a polynomial over a tower. -/
private def selmerPoly (m : Nat) (T : NumberTower) : Poly T :=
  DensePoly.ofCoeffs ((selmerRatCoeffs m).map (ofRat T))

/-- Prepared Trager-ladder fixture: the degree-`m` Selmer trinomial over the
fixed base `ℚ(√2)`. Rational coefficients make the shift-zero one-level
norm the square `f^2`, so the bounded search always performs a genuine
retry before accepting a squarefree norm. -/
private structure FactorInput where
  tower : NumberTower
  f : Poly tower

private instance : Hashable FactorInput where
  hash input := mixHash (hash input.tower.dim) (polyChecksum input.f)

private instance : Inhabited FactorInput :=
  ⟨⟨rat, DensePoly.ofCoeffs #[]⟩⟩

def prepFactorInput (n : Nat) : FactorInput :=
  let m := max n 2
  match sqrtTwo? () with
  | some base => { tower := base.tower, f := selmerPoly m base.tower }
  | none => panic! "prepFactorInput: base tower fixture failed"

def runTowerFactorLadder (input : FactorInput) : UInt64 :=
  match factor? input.tower input.f with
  | some result => factorChecksum result
  | none => 1

/-- Worst-case textbook cost model for one Trager step over the quadratic
base at input degree `n`: the SPEC's shift recurrence tries at most
`choose(d * m, 2) + 1 = choose(2n, 2) + 1 = O(n^2)` one-level norms, each a
Brown resultant against the fixed quadratic level relation costing `O(n^2)`
coefficient operations, and then recursively factors one accepted norm of
degree `2n` over `ℚ`, whose classical BHKS bound `(2n)^9 + (2n)^7 log^2 (2n)`
dominates the total. -/
def tragerLadderModel (n : Nat) : Nat :=
  let bigN := 2 * n
  (bigN * (bigN - 1) / 2 + 1) * (n * n)
    + bigN ^ 9 + bigN ^ 7 * (Nat.log2 (bigN + 2)) ^ 2

/- Cost model. Declared per the SPEC's Trager recurrence, worst case: at
`K(α)/K` with `d = deg m_α = 2` and component degree `m = n`, at most
`choose(2n, 2) + 1` one-level norms (each an `O(n^2)`-operation Brown
resultant against the quadratic relation), plus the recursive rational
factorization of the accepted degree-`2n` norm at its classical BHKS bound —
the dominant term. `tragerLadderModel` writes out exactly this sum. The
deterministic Selmer family realises the retry (repeated shift-zero norm),
the accepted squarefree norm, the base factorization, and gcd recovery. -/
setup_benchmark runTowerFactorLadder n => tragerLadderModel n
  with prep := prepFactorInput
  where {
    paramFloor := 2
    paramCeiling := 6
    paramSchedule := .custom #[2, 3, 4, 6]
    maxSecondsPerCall := 60.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/-! # PARI `nffactor` comparator pairs -/

/-- Sorted factor degree/multiplicity multiset checksum: the
representation-free observable shared by the Lean and PARI factorizations. -/
private def degreeMultChecksum (pairs : Array (Nat × Nat)) : UInt64 :=
  let sorted := pairs.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
  sorted.foldl
    (fun checksum pair => mixHash checksum (mixHash (hash pair.1) (hash pair.2)))
    (hash pairs.size)

private def towerFactorDegrees (input : FactorInput) : UInt64 :=
  match factor? input.tower input.f with
  | some result =>
    degreeMultChecksum <| result.factors.map fun entry =>
      (entry.1.degree?.getD 0, entry.2)
  | none => 1

private def pariNfFactorDegrees (m : Nat) : IO UInt64 := do
  let result ← Hex.BenchOracle.Pari.runOp "nf" "factor_degrees"
    #[("field", Hex.BenchOracle.Flint.intsToJson [-2, 0, 1]),
      ("poly", Hex.BenchOracle.Pari.ratsToJson (selmerRatCoeffs m))]
  return degreeMultChecksum (← Hex.BenchOracle.Pari.jsonToNatPairs result)

initialize factorPairRef2 : IO.Ref (Option FactorInput) ← IO.mkRef none
initialize factorPairRef3 : IO.Ref (Option FactorInput) ← IO.mkRef none
initialize factorPairRef4 : IO.Ref (Option FactorInput) ← IO.mkRef none
initialize factorPairRef6 : IO.Ref (Option FactorInput) ← IO.mkRef none

private def getFactorPair (ref : IO.Ref (Option FactorInput)) (n : Nat) :
    IO FactorInput := do
  match ← ref.get with
  | some input => pure input
  | none =>
    let input := prepFactorInput n
    ref.set (some input)
    pure input

def runTowerFactorPair2 : Unit → IO UInt64 := fun _ => do
  return towerFactorDegrees (← getFactorPair factorPairRef2 2)
def runPariNfFactor2 : Unit → IO UInt64 := fun _ => pariNfFactorDegrees 2
def runTowerFactorPair3 : Unit → IO UInt64 := fun _ => do
  return towerFactorDegrees (← getFactorPair factorPairRef3 3)
def runPariNfFactor3 : Unit → IO UInt64 := fun _ => pariNfFactorDegrees 3
def runTowerFactorPair4 : Unit → IO UInt64 := fun _ => do
  return towerFactorDegrees (← getFactorPair factorPairRef4 4)
def runPariNfFactor4 : Unit → IO UInt64 := fun _ => pariNfFactorDegrees 4
def runTowerFactorPair6 : Unit → IO UInt64 := fun _ => do
  return towerFactorDegrees (← getFactorPair factorPairRef6 6)
def runPariNfFactor6 : Unit → IO UInt64 := fun _ => pariNfFactorDegrees 6

/-- Timing shape shared by both sides of every PARI pair: the discarded
`warmupFirstIter` call builds the lazily cached rung fixture (and, on the
PARI side, spawns the persistent driver) outside the timed region, and the
raised `minTotalSeconds` floor amortises steady-state work across the
auto-tuned inner-repeat batch so per-rung ratios compare like with like. -/
def pariCompareConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 3, maxSecondsPerCall := 60.0, warmupFirstIter := true,
    minTotalSeconds := 0.2 }

/- Fixed per-rung process-call comparator registrations for PARI `nffactor`
against `factor?` over `ℚ(√2)` (worst-case cost model per the
`runTowerFactorLadder` derivation). Identical Selmer inputs, identical sorted
degree/multiplicity multiset hash on both sides. -/
setup_fixed_benchmark runTowerFactorPair2 where pariCompareConfig
setup_fixed_benchmark runPariNfFactor2 where pariCompareConfig
setup_fixed_benchmark runTowerFactorPair3 where pariCompareConfig
setup_fixed_benchmark runPariNfFactor3 where pariCompareConfig
setup_fixed_benchmark runTowerFactorPair4 where pariCompareConfig
setup_fixed_benchmark runPariNfFactor4 where pariCompareConfig
setup_fixed_benchmark runTowerFactorPair6 where pariCompareConfig
setup_fixed_benchmark runPariNfFactor6 where pariCompareConfig

/-- Per-call driver overhead for the PARI comparator: one `nf`-family
request whose PARI-side work is a constant `0`, so the measured time is the
JSON request/reply round trip alone. `SPEC/benchmarking.md` §External
comparators §Process call requires this figure so the headline report can
quote overhead-adjusted ratios. -/
def runPariNfFactorOverhead : Unit → IO UInt64 := fun _ => do
  let result ← Hex.BenchOracle.Pari.runOp "nf" "overhead" #[]
  match result.getInt? with
  | .ok value => return UInt64.ofNat value.toNat
  | .error error =>
    throw <| IO.userError s!"invalid PARI overhead reply: {error}"

/- Driver round-trip floor for the PARI comparator: no algorithmic work on
either side, so this registration measures only the per-call request/reply
cost that the headline report subtracts from the PARI wall times. -/
setup_fixed_benchmark runPariNfFactorOverhead where
  { pariCompareConfig with expectedHash := some 0x0 }

end Hex.NumberTowerBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
