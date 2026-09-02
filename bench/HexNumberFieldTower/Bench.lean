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

The component cases stay within tower dimension four and input degree four;
the isolated recovery adversary uses absolute degree six, and the canonical
mode-3 factorization case uses input degree 24 over the quadratic base.

The parametric ladders carry the Phase-4 arithmetic evidence:

* `runTower{Add,Sub,Neg,SMul,Mul}Ladder`: coordinate arithmetic at growing
  dimension with bounded coordinate height;
* `runTower{Inv,Div}Ladder`: genuine recursive arithmetic in the height-two
  family `Q(3^{1/m}, sqrt(2))`, with checked fixtures outside the timed body;
* the completed `toPrimitive` and `fromPrimitive` basis maps.

Negation, inversion, and division retain failed mode-1 registrations as
binding diagnostics. They have no admissible fixed substitute, so the library
remains at Phase 3 while those cost models are unresolved.

The degree-24 Selmer factor case is a mode-3 fixed registration because its
realised Trager route mixes coefficient-growth gcd, resultant, certificate,
and integer-factorization phases without a stable independently derived
one-parameter wall model.

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

/- Expected-hash anchor only. `runOfQAdjoinLadder` supplies mode-1 performance
coverage for the public constructor. -/
setup_fixed_benchmark runOfQAdjoin where {
  repeats := 5, maxSecondsPerCall := 2.0,
  expectedHash := some 0x51ddf5878af8a696
}

/- Expected-hash anchor only. `runTowerAddLadder` supplies mode-1 performance
coverage for this operation. -/
setup_fixed_benchmark runAdd where {
  repeats := 5, maxSecondsPerCall := 2.0,
  expectedHash := some 0xd381defc58f22934,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/- Expected-hash anchor only. `runTowerMulLadder` supplies mode-1 performance
coverage for this operation. -/
setup_fixed_benchmark runMul where {
  repeats := 5, maxSecondsPerCall := 2.0,
  expectedHash := some 0xca888473e6359390,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/- Expected-hash anchor only. `runTowerInvLadder` supplies mode-1 performance
coverage for this operation. -/
setup_fixed_benchmark runInv where {
  repeats := 5, maxSecondsPerCall := 2.0,
  expectedHash := some 0xfdfda24536fdd084,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/- Mode 3. The attempted root-degree schedule `2,3,4,6,8,12` measured
13.7 ms, 35.5 ms, 98.1 ms, 804.5 ms, 4.71 s, then hit a 30 s cap: embedding
selection, factorization, isolation, and validation change dominance, so no
stable independently derived wall model is reachable, and no published bound
covers the dominant isolation phase. The canonical fourth-root extension of
`Q(sqrt(2))` has a 311.405 ms per-call and whole-batch median. Its 3 s
zero-grace whole-child budget includes startup and certified fixtures. -/
setup_fixed_benchmark runAdjoin where {
  repeats := 3, maxSecondsPerCall := 3.0, killGraceMs := 0,
  expectedHash := some 0xde9179e4f67a3948,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/- Mode 3 for the distinct identity branch. The attempted presentation-degree
schedule `2,3,4,6,8,12` measured 18.0 ms, 2.37 s, 1.68 s, then hit a 30 s cap
at degree 6: branch-sensitive embedding recovery is nonmonotone and supplies no
stable independently derived model; no complete published bound applies.
Re-adjoining `sqrt(2)` is canonical. Its 18.084 ms per-call median and
289.345 ms batch median fit a 1 s zero-grace whole-child ceiling. -/
setup_fixed_benchmark runAdjoinIdentity where {
  repeats := 3, maxSecondsPerCall := 1.0, killGraceMs := 0,
  expectedHash := some 0x51ddf5878af8a696,
  warmupFirstIter := true, minTotalSeconds := 0.2
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
  let input : Poly T := DensePoly.ofCoeffs #[ofRat T (-1), ofRat T (-1), 1]
  return factorChecksum
    (← requireSome "factor/recursive" (factor? T input))

def runCheckFactorization : Unit → IO UInt64 := fun _ => do
  let result ← getRepeatedFactor
  return hash (checkFactorization repeatedInput result.scalar result.factors)

/- Attribution anchor for the separable one-level norm phase. It does not
discharge public-operation performance coverage. -/
setup_fixed_benchmark runOneLevelNorm where {
  repeats := 5, maxSecondsPerCall := 5.0,
  expectedHash := some 0x98a9884aa98ddd32
}

/- Branch and attribution anchor: the canonical repeated shift-zero norm
forces a real retry. It does not discharge public-operation performance
coverage. -/
setup_fixed_benchmark runShiftSearch where {
  repeats := 5, maxSecondsPerCall := 5.0,
  expectedHash := some 0x0bb795ff2f22014a
}

/- Branch and expected-hash anchor for the rational Trager base case. It does
not discharge the public `factor?` performance surface. -/
setup_fixed_benchmark runFactorRat where {
  repeats := 3, maxSecondsPerCall := 5.0,
  expectedHash := some 0x90fa5a1ee979f50c
}

/- Branch and expected-hash anchor. It forces a real bad first shift, while the
canonical degree-24 registration supplies public `factor?` performance
coverage. -/
setup_fixed_benchmark runFactorRetry where {
  repeats := 3, maxSecondsPerCall := 5.0,
  expectedHash := some 0xf830f035fb69256e,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/- Mode 3 for genuine height-two relative factorization. The degree schedule
`2,3,4,6` measures 7.598, 12.320, 18.591, and 46.578 ms and rejects a linear
candidate with residual `+0.636`: recursive norms, gcd, rational factorization,
and replay change shares, and no published bound covers all phases. The
irreducible `X² - X - 1` input over `ℚ(√2, √3)` is the smallest
non-short-circuit canonical case. Its 7.919 ms per-call and 253.393 ms batch
medians fit the 2 s zero-grace whole-child ceiling. -/
setup_fixed_benchmark runFactorRecursive where {
  repeats := 3, maxSecondsPerCall := 2.0, killGraceMs := 0,
  expectedHash := some 0xa0c08a951ecca91a,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/- Expected-hash and attribution anchor for checked replay. It does not
discharge public-operation performance coverage. -/
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

def runToPrimitive : Unit → IO UInt64 := fun _ => do
  let input ← getMapInput
  let T := input.tower.extension.tower
  return (List.range T.dim).foldl (fun checksum i =>
    let basis := ofCoeffs T (Flatten.unitCoords T.dim i)
    mixHash checksum (qAdjoinChecksum (input.result.toPrimitive basis)))
    (hash T.dim)

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

/- Mode 3. The attempted factor-count schedule `1,2,3` (degrees `2,4,6`)
measured 19.5 ms, 68.3 ms, and 1.89 s as repeated factorization, isolation,
adjoining, and root collection change dominance. No tight independent wall
model or published dominant-isolation bound applies. The canonical quartic
performs two genuine extensions; its 68.203 ms per-call and 272.813 ms batch
medians fit a 1 s zero-grace whole-child ceiling. -/
setup_fixed_benchmark runSplit where {
  repeats := 2, maxSecondsPerCall := 1.0, killGraceMs := 0,
  expectedHash := some 0xd863bc339d467bf8,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/- Branch and attribution anchor for a rejected exact-recovery gcd. It does
not discharge public `flatten?` performance coverage. -/
setup_fixed_benchmark runRecoverPair where {
  repeats := 2, maxSecondsPerCall := 20.0,
  expectedHash := some 0x190011a8e6411c8e,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/- Branch and attribution anchor for a rejected then accepted recovery search.
It does not discharge public `flatten?` performance coverage. -/
setup_fixed_benchmark runRecoverSearch where {
  repeats := 1, maxSecondsPerCall := 60.0,
  expectedHash := some 0xf696f44e1e1e7ef7,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/- Attribution anchor for basis expansion from precomputed recovery data. It
does not discharge public `flatten?` performance coverage. -/
setup_fixed_benchmark runBasisImages where {
  repeats := 5, maxSecondsPerCall := 5.0,
  expectedHash := some 0xb5d54195958fb61e,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/- Correctness and attribution anchor for primitive-relation and coordinate-map
certification. It does not discharge public `flatten?` performance coverage. -/
setup_fixed_benchmark runCertifies where {
  repeats := 5, maxSecondsPerCall := 5.0,
  expectedHash := some 0x000000000000000b,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/- Expected-hash anchor for both conversion closures produced by `flatten?`.
It does not independently discharge their performance coverage. -/
setup_fixed_benchmark runCoordinateMaps where {
  repeats := 5, maxSecondsPerCall := 5.0,
  expectedHash := some 0xcc1b7720bfe3fc24,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/- Expected-hash anchor only. `runToPrimitiveLadder` supplies mode-1
performance coverage for the public closure. -/
setup_fixed_benchmark runToPrimitive where {
  repeats := 5, maxSecondsPerCall := 5.0,
  expectedHash := some 0xb5d54195958fb61e,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/- Mode 3. The attempted top-degree schedule `1,2,3,4` (tower dimensions
`2,4,6,8`) measured 0.96 ms, 21.0 ms, 107.7 ms, and 460.4 ms while candidate
enumeration, eliminants, isolation, recovery, and certification change
dominance. No stable independent wall model or published dominant-isolation
bound applies. The canonical dimension-four tower has a 20.819 ms per-call and
333.110 ms batch median; inclusive work fits a 1 s zero-grace ceiling. -/
setup_fixed_benchmark runFlatten where {
  repeats := 2, maxSecondsPerCall := 1.0, killGraceMs := 0,
  expectedHash := some 0xcc1b7720bfe3fc24,
  warmupFirstIter := true, minTotalSeconds := 0.2
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

/- Expected-hash anchor only. `runTowerSubLadder` supplies mode-1 performance
coverage for this operation. -/
setup_fixed_benchmark runSub where {
  repeats := 5, maxSecondsPerCall := 2.0,
  expectedHash := some 0x098874a34dd4ec44,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/- Expected-hash anchor only. The linear ladder is retained as a failed
mode-1 diagnostic; no canonical hard negation input gives this cheap operation
a meaningful mode-3 ceiling. -/
setup_fixed_benchmark runNeg where {
  repeats := 5, maxSecondsPerCall := 2.0,
  expectedHash := some 0x2e1510498ed9e174,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/- Expected-hash anchor only. The checked height-two ladder is retained as a
failed mode-1 diagnostic; this dimension-four case is not a canonical hard
input and therefore supplies no mode-3 evidence. -/
setup_fixed_benchmark runDiv where {
  repeats := 5, maxSecondsPerCall := 2.0,
  expectedHash := some 0xe534ce65592907a8,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/- Expected-hash anchor only. `runTowerSMulLadder` supplies mode-1 performance
coverage for this operation. -/
setup_fixed_benchmark runSMul where {
  repeats := 5, maxSecondsPerCall := 2.0,
  expectedHash := some 0xcea4d21168dc712c,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

/-! # Parametric dimension ladders -/

/-- `X^m - 3`, Eisenstein-irreducible at `3` for every `m ≥ 1`; its degree
over `ℚ(√2)` is still `m` (the only quadratic subfield a pure cube/fourth/…
root field of `3` can contain is `ℚ(√3)`), so adjoining its first root to
`ℚ(√2)` yields a height-two tower of dimension `2m`. -/
private def xPowSubThree (m : Nat) : ZPoly :=
  DensePoly.ofList ((-3 : Int) :: List.replicate (m - 1) 0 ++ [1])

/-- Floor the positive `n`th root of `a` by integer Newton iteration. -/
private def nthRootFloor (a n : Nat) : Nat :=
  if n = 0 then 0 else
    let rec go : Nat → Nat → Nat
      | 0, x => x
      | fuel + 1, x =>
        let y := ((n - 1) * x + a / x ^ (n - 1)) / n
        if x ≤ y then x else go fuel y
    go (a.log2 + 2) (2 ^ ((a.log2 + n) / n))

/-- Mahler-precision untrusted approximation to the positive real root of
`X^n - 3`. The local atom checker supplies the certificate. -/
private def ladderRootSeed (p : ZPoly) (n : Nat) : DyadicSquare :=
  let q := mahlerPrec p
  let scaled := 3 * 2 ^ (q * n)
  let center := nthRootFloor scaled n
  ⟨Dyadic.ofIntWithPrec (Int.ofNat center) q, 0, q⟩

/-- Certify one simple binomial root from a seed near the positive real root.
`isolateOne?` does not promise that the returned atom lies inside the seed, but
the choice does not affect the presentation degree or timed arithmetic. This
avoids refining and pairwise separating every other root merely to build an
untimed fixture. -/
private def positiveBinomialRoot? (p : ZPoly) (n : Nat) :
    Option (RefinedIsolation p) :=
  isolateOne? p (mahlerPrec p : Int) (ladderRootSeed p n)

/-- Deterministic factorization-lazy root of a primitive positive-leading
squarefree binomial (the certified positive root). -/
private def mkLadderRoot? (p : ZPoly) (n : Nat) : Option AlgebraicRoot :=
  if hprim : ZPoly.content p = 1 then
    if hlc : 0 < p.leadingCoeff then
      if hdeg : 0 < p.degree?.getD 0 then
        if hsf : HasOnlySimpleRoots p then
          match positiveBinomialRoot? p n with
          | some rep =>
            some { p := p, prim := hprim, pos_lc := hlc, pos_degree := hdeg
                   squarefree := hsf, x := SimpleRoot.mk rep, rep := rep
                   rep_mk := rfl }
          | none => none
        else none
      else none
    else none
  else none

/-- A checked rational presentation whose selected root remains runtime data. -/
private structure PresentationInput where
  root : AlgebraicRoot
  checked : Option (PLift (ZPoly.CheckedIrreducible root.p))

private instance : Hashable PresentationInput where
  hash input := zpolyChecksum input.root.p

private instance : Inhabited PresentationInput :=
  ⟨⟨AlgebraicNumber.zero.toRoot, none⟩⟩

def prepPresentationInput (n : Nat) : PresentationInput :=
  let m := max n 2
  let p := xPowSubThree m
  match mkLadderRoot? p m with
  | some root =>
      if hirred : ZPoly.isIrreducible root.p = true then
        ⟨root, some ⟨⟨hirred, root.pos_degree⟩⟩⟩
      else
        panic! "prepPresentationInput: irreducibility check failed"
  | none => panic! "prepPresentationInput: root fixture failed"

def runOfQAdjoinLadder (input : PresentationInput) : UInt64 :=
  let root := input.root
  match input.checked with
  | some ⟨checked⟩ =>
      letI : ZPoly.CheckedIrreducible root.p := checked
      extensionChecksum
        (ofQAdjoin (x := root.x) root.squarefree root.rep root.rep_mk)
  | none => 0

/- Cost model. `ofQAdjoin` normalizes the degree-`n` integer polynomial and
builds its length-`n` rational defining-coefficient array; the result checksum
then walks the generator coordinates and root polynomial once. The fixture's
certificate and selected root are prepared outside the timed region, so the
runtime constructor performs `Θ(n)` bounded-height array work. The extended
schedule makes the fixed constructor term lower order without changing the
declared model. -/
setup_benchmark runOfQAdjoinLadder n => n
  with prep := prepPresentationInput
  where {
    paramFloor := 2
    paramCeiling := 24
    paramSchedule := .custom #[2, 3, 4, 6, 8, 12, 16, 24]
    maxSecondsPerCall := 300.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-- The height-two ladder tower `ℚ(√2, 3^{1/m})` (just `ℚ(√2)` at `m = 1`). -/
private def ladderTower? (m : Nat) : Option NumberTower := do
  let base ← sqrtTwo? ()
  if m ≤ 1 then
    pure base.tower
  else do
    let root ← mkLadderRoot? (xPowSubThree m) m
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

/-- A dense one-level fixture for coordinatewise operations. Its timed
operation depends only on the coordinate-array length, so this preserves the
same linear family while avoiding relative-extension work in the untimed
fixture at the larger calibration rungs. -/
def prepLinearElemInput (n : Nat) : ElemInput :=
  let presentation := prepPresentationInput (max n 2)
  let root := presentation.root
  match presentation.checked with
  | some ⟨checked⟩ =>
      letI : ZPoly.CheckedIrreducible root.p := checked
      let extension := ofQAdjoin (x := root.x) root.squarefree root.rep root.rep_mk
      let tower := extension.tower
      let d := tower.dim
      { tower := tower
        a := ofCoeffs tower (ladderCoords d 3)
        b := ofCoeffs tower (ladderCoords d 7) }
  | none => panic! "prepLinearElemInput: tower fixture failed"

/-- A height-two arithmetic fixture `ℚ(3^(1/n), √2)` whose varying lower
presentation is constructed directly and whose fixed quadratic top level is
admitted through the public checked extension path. Inversion in the top
quotient therefore performs genuine recursive inversion in the degree-`n`
lower field without making degree-`n` relative factorization the fixture
bottleneck. -/
def prepRecursiveElemInput (n : Nat) : ElemInput :=
  let presentation := prepPresentationInput (max n 2)
  let root := presentation.root
  match presentation.checked, sqrtTwo? () with
  | some ⟨checked⟩, some sqrtTwo =>
      letI : ZPoly.CheckedIrreducible root.p := checked
      let base := ofQAdjoin (x := root.x) root.squarefree root.rep root.rep_mk
      match adjoin? base.tower sqrtTwo.root with
      | some extension =>
          let tower := extension.tower
          let d := tower.dim
          { tower := tower
            a := ofCoeffs tower (ladderCoords d 3)
            b := ofCoeffs tower (ladderCoords d 7) }
      | none => panic! "prepRecursiveElemInput: quadratic extension failed"
  | _, _ => panic! "prepRecursiveElemInput: base fixture failed"

def runTowerAddLadder (input : ElemInput) : UInt64 :=
  elemChecksum (input.a + input.b)

def runTowerSubLadder (input : ElemInput) : UInt64 :=
  elemChecksum (input.a - input.b)

def runTowerNegLadder (input : ElemInput) : UInt64 :=
  elemChecksum (-input.a)

def runTowerSMulLadder (input : ElemInput) : UInt64 :=
  elemChecksum (mkRat 3 5 • input.a)

def runTowerMulLadder (input : ElemInput) : UInt64 :=
  elemChecksum (input.a * input.b)

def runTowerInvLadder (input : ElemInput) : UInt64 :=
  elemChecksum input.a⁻¹

def runTowerDivLadder (input : ElemInput) : UInt64 :=
  elemChecksum (input.a / input.b)

/- Cost model. Negation maps rational negation over the `D = n` dense
coordinate array. The one-level presentation changes only untimed fixture
construction: the timed implementation sees the same fixed-height coordinate
representation and performs exactly `Θ(n)` work. -/
setup_benchmark runTowerNegLadder n => n
  with prep := prepLinearElemInput
  where {
    paramSchedule := .custom #[4, 6, 8, 12, 16, 24, 32, 48]
    maxSecondsPerCall := 300.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Cost model. Coordinate addition adds the two mixed-radix coordinate
vectors pointwise: exactly `D = 2n` bounded-height rational additions for the
dimension-`2n` ladder tower, hence `Θ(n)` work. -/
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

/- Cost model. Subtraction visits the two length-`D = 2n` bounded-height
coordinate vectors pointwise, hence performs `Θ(n)` work. -/
setup_benchmark runTowerSubLadder n => n
  with prep := prepElemInput
  where {
    paramFloor := 1
    paramCeiling := 6
    paramSchedule := .custom #[1, 2, 3, 4, 6]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Cost model. Rational scalar action multiplies each of the `D = 2n`
bounded-height coordinates by the fixed scalar `3/5`, hence performs
`Θ(n)` work. -/
setup_benchmark runTowerSMulLadder n => n
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

/- Cost model. Inversion runs extended gcd in the fixed quadratic top quotient
over a degree-`n` lower field. Its coefficient operations invoke genuine
recursive lower-field inversion, whose degree-`n` polynomial xgcd costs
`O(n²)` rational operations; the same logarithmic limb-growth proxy used by
the HexResultant Brown-chain registrations gives the declared `n² log n`
wall model. The registration is retained even though its clean verdict is
inconclusive: changing the tower order removed certification from the limiting
path but did not make the intended model pass. -/
setup_benchmark runTowerInvLadder n => n * n * (Nat.log2 (n + 2) + 1)
  with prep := prepRecursiveElemInput
  where {
    paramFloor := 2
    paramCeiling := 12
    paramSchedule := .custom #[2, 3, 4, 6, 8, 12]
    maxSecondsPerCall := 30.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Cost model. Division performs the recursive inversion above followed by
one `O(D²)` tower multiplication. The `n² log n` inversion term dominates on
the same bounded-height `ℚ(3^(1/n), √2)` family; both operations consume the
already checked height-two fixture outside the timed region. -/
setup_benchmark runTowerDivLadder n => n * n * (Nat.log2 (n + 2) + 1)
  with prep := prepRecursiveElemInput
  where {
    paramFloor := 2
    paramCeiling := 12
    paramSchedule := .custom #[2, 3, 4, 6, 8, 12]
    maxSecondsPerCall := 30.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
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

initialize factorCanonicalRef : IO.Ref (Option FactorInput) ← IO.mkRef none

private def getFactorCanonicalInput : IO FactorInput := do
  match ← factorCanonicalRef.get with
  | some input => pure input
  | none =>
    let input := prepFactorInput 24
    factorCanonicalRef.set (some input)
    pure input

def runTowerFactorLadder : Unit → IO UInt64 := fun _ => do
  let input ← getFactorCanonicalInput
  return match factor? input.tower input.f with
  | some result => factorChecksum result
  | none => 1

/- Mode 3. The historical degree sweep `2,3,4,6,8,12,16,24` tried the
SPEC's Trager/BHKS envelope, but its local exponents rose from 0.80 to 4.48
as the dominant rational-polynomial gcd, resultant, and checked-replay shares
changed with coefficient growth. That is not a stable independently derived
family model. Integer factorization is 1.42% of the whole-thread capture, while
gcd alone is 47.28%; the target frame is 58.24%. Non-uniform GMP stack-unwind
loss makes renormalized within-target ratios only qualitative, but the direct
whole-capture shares already exclude a BHKS-only mode-2 bound for the dominant
inclusive work.

The degree-24 Selmer trinomial over `Q(sqrt(2))` is the top completed rung and
the canonical hard input. Rational coefficients force a repeated shift-zero
norm, followed by a genuine retry, recursive rational factorization of the
accepted degree-48 norm, gcd recovery, and checked replay. Its 249.758 ms
per-call and whole-batch median, plus startup and fixture construction, fits a
2 s zero-grace whole-child budget. -/
setup_fixed_benchmark runTowerFactorLadder where {
  repeats := 5
  maxSecondsPerCall := 2.0
  killGraceMs := 0
  warmupFirstIter := true
  expectedHash := some 0x3a7f4c606ce48b1b
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
initialize factorPairRef8 : IO.Ref (Option FactorInput) ← IO.mkRef none
initialize factorPairRef12 : IO.Ref (Option FactorInput) ← IO.mkRef none

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
def runTowerFactorPair8 : Unit → IO UInt64 := fun _ => do
  return towerFactorDegrees (← getFactorPair factorPairRef8 8)
def runPariNfFactor8 : Unit → IO UInt64 := fun _ => pariNfFactorDegrees 8
def runTowerFactorPair12 : Unit → IO UInt64 := fun _ => do
  return towerFactorDegrees (← getFactorPair factorPairRef12 12)
def runPariNfFactor12 : Unit → IO UInt64 := fun _ => pariNfFactorDegrees 12

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
setup_fixed_benchmark runTowerFactorPair8 where pariCompareConfig
setup_fixed_benchmark runPariNfFactor8 where pariCompareConfig
setup_fixed_benchmark runTowerFactorPair12 where pariCompareConfig
setup_fixed_benchmark runPariNfFactor12 where pariCompareConfig

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

/-! # Checked replay and coordinate-map performance surfaces -/

private structure CheckInput where
  tower : NumberTower
  f : Poly tower
  scalar : Elem tower
  factors : Array (Poly tower × Nat)

private instance : Hashable CheckInput where
  hash input := mixHash (polyChecksum input.f) (elemChecksum input.scalar)

private instance : Inhabited CheckInput :=
  ⟨⟨rat, DensePoly.ofCoeffs #[], 0, #[]⟩⟩

private def prepCheckInput (n : Nat) : CheckInput :=
  let input := prepFactorInput n
  match factor? input.tower input.f with
  | some result => ⟨input.tower, input.f, result.scalar, result.factors⟩
  | none => panic! "prepCheckInput: factorization failed"

initialize checkCanonicalRef : IO.Ref (Option CheckInput) ← IO.mkRef none

private def getCheckCanonicalInput : IO CheckInput := do
  match ← checkCanonicalRef.get with
  | some input => pure input
  | none =>
      let input := prepCheckInput 24
      checkCanonicalRef.set (some input)
      pure input

def runTowerCheckFactorization : Unit → IO UInt64 := fun _ => do
  let input ← getCheckCanonicalInput
  return hash (checkFactorization input.f input.scalar input.factors)

/- Mode 3. The diagnostic degree schedule `2,3,4,6,8,12,16,24` rose from
0.404 ms to 126.3 ms with a `+1.485` residual even against a linear candidate;
its changing squarefree, Trager, gcd, and replay phases admit no independent
tight wall model, and no published bound covers the dominant gcd/replay work.
The degree-24 checked Selmer factorization is canonical. Its 124.730 ms
per-call and 249.460 ms batch medians fit the independently chosen 2 s
zero-grace whole-child ceiling. -/
setup_fixed_benchmark runTowerCheckFactorization where {
  repeats := 3, maxSecondsPerCall := 2.0, killGraceMs := 0,
  expectedHash := some 0x000000000000000b,
  warmupFirstIter := true, minTotalSeconds := 0.2
}

private structure MapLadderInput where
  tower : NumberTower
  result : Option (Flattening tower)

private instance : Hashable MapLadderInput where
  hash input := hash input.tower.dim

private instance : Inhabited MapLadderInput := ⟨⟨rat, none⟩⟩

def prepMapLadderInput (n : Nat) : MapLadderInput :=
  match ladderTower? (max n 1) with
  | some tower => ⟨tower, flatten? tower⟩
  | none => panic! "prepMapLadderInput: tower fixture failed"

def runToPrimitiveLadder (input : MapLadderInput) : UInt64 :=
  match input.result with
  | some result =>
      (List.range input.tower.dim).foldl (fun checksum i =>
        let basis := ofCoeffs input.tower
          (Flatten.unitCoords input.tower.dim i)
        mixHash checksum (qAdjoinChecksum (result.toPrimitive basis)))
        (hash input.tower.dim)
  | none => 0

/- Diagnostic only. One dense `toPrimitive` call has the public `O(D²)`
rational-operation bound from a length-`D` linear combination of degree-`D`
primitive coordinates. This basis family becomes sparse after the executable
zero-coordinate optimization, so its statistical cubic verdict cannot
discharge mode 1; the registration is retained to expose that behavior and
the structural checksum cost. -/
setup_benchmark runToPrimitiveLadder n => n * n * n
  with prep := prepMapLadderInput
  where {
    paramSchedule := .custom #[2, 3, 4, 5, 6, 9]
    maxSecondsPerCall := 300.0, targetInnerNanos := 100000000,
    signalFloorMultiplier := 1.0
  }

def runFromPrimitiveLadder (input : MapLadderInput) : UInt64 :=
  match input.result with
  | some result =>
      (List.range input.tower.dim).foldl (fun checksum i =>
        let primitive := QAdjoin.reduce result.root.p result.root.x
          (DensePoly.ofCoeffs (Flatten.unitCoords input.tower.dim i))
        mixHash checksum (elemChecksum (result.fromPrimitive primitive)))
        (hash input.tower.dim)
  | none => 0

/- Cost model. The benchmark applies `fromPrimitive` to all `D = 2n`
primitive basis vectors. Horner evaluation takes `D` tower
multiplication/addition steps, with `Θ(D²)` coordinate multiplication per
step, hence `Θ(D³)` per vector and `Θ(D⁴)` for the full basis. -/
setup_benchmark runFromPrimitiveLadder n => n * n * n * n
  with prep := prepMapLadderInput
  where {
    paramSchedule := .custom #[2, 3, 4, 5, 6, 9]
    maxSecondsPerCall := 300.0, targetInnerNanos := 100000000,
    signalFloorMultiplier := 1.0
  }

end Hex.NumberTowerBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
