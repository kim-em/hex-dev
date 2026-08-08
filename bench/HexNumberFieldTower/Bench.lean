/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexNumberFieldTower
import LeanBench

/-!
Benchmark registrations for `HexNumberFieldTower`.

The fixed cases expose the Phase-4 components named by the library SPEC:

* addition, multiplication, and recursive inversion in the dimension-four tower
  `Q(sqrt(2), sqrt(3))`;
* adjoining a fourth root of two to `Q(sqrt(2))`;
* rational, one-level Trager-retry, and recursive two-level factorization;
* splitting a quartic through two genuine extensions;
* flattening a two-level tower to a primitive-element presentation.

Every case stays within tower dimension four and input degree four; the
isolated recovery adversary uses absolute degree six. The driver is
Mathlib-free; external PARI comparison belongs to conformance, not timing.
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


end Hex.NumberTowerBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
