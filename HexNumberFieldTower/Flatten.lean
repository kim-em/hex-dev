/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTower.Split
public meta import HexNumberFieldTower.Split

public section

/-!
# Primitive-element flattening for number-field towers

The fixed absolute generators are combined in deterministic signed-shift order.
A candidate is admitted only when its canonical minimal-polynomial degree is the
full accumulated tower dimension. Exact polynomial gcds then recover every old
generator in the primitive power basis. A tower-basis coordinate round trip and
the primitive polynomial relation are checked before the maps are returned.
-/
namespace Hex.NumberTower

/-- A one-generator presentation of a tower together with checked executable
coordinate conversions in both directions. -/
structure Flattening (T : NumberTower) where
  root : AlgebraicNumber
  toPrimitive : Elem T → QAdjoin root.p root.x
  fromPrimitive : QAdjoin root.p root.x → Elem T

/-- The finite combined bound for primitive-element and coordinate-recovery
collisions in a field of dimension `dimension`. -/
@[expose]
def flattenShiftCount (dimension : Nat) : Nat :=
  Nat.choose dimension 2 + 1

namespace Flatten

/-- One exact absolute generator and its mixed-radix coordinate in the final
tower. -/
structure Generator (T : NumberTower) where
  degree : Nat
  root : AlgebraicNumber
  value : Elem T

/-- A primitive generator accumulated through the lower part of the tower. -/
structure Candidate (T : NumberTower) where
  dimension : Nat
  root : AlgebraicNumber
  value : Elem T
  coordinates : Array (QAdjoin root.p root.x)

/-- Standard coordinate vector of length `dimension`. -/
def unitCoords (dimension index : Nat) : Array Rat :=
  (Array.replicate dimension 0).set! index 1

/-- Exactify the stored roots from the oldest level upward and pair them with
their canonical mixed-radix generator coordinates in the final tower. -/
@[expose]
def generators? (T : NumberTower) : Option (Array (Generator T)) := do
  let state ← T.levels.toList.reverse.foldlM
    (fun state level => do
      let root ← level.root.exact?
      let value := ofCoeffs T (unitCoords T.dim state.2)
      some (state.1.push ⟨level.degree, root, value⟩,
        state.2 * level.degree))
    (#[], 1)
  if state.2 = T.dim then some state.1 else none

/-- Try one deterministic signed shift for a candidate of the full required
degree. -/
@[expose]
def candidateAt? (theta alpha : AlgebraicNumber) (target index : Nat) :
    Option (Int × AlgebraicNumber) :=
  let shift := Norm.signedShift index
  match AlgebraicPoly.Common.shift? theta alpha shift with
  | some candidate =>
      if AlgebraicPoly.Common.degree candidate = target then
        some (shift, candidate)
      else
        none
  | none => none

/-- Lift an integer polynomial coefficientwise into a fixed primitive
presentation. -/
@[expose]
def liftZPoly {p : ZPoly} {x : SimpleRoot p}
    (f : ZPoly) : DensePoly (QAdjoin p x) :=
  DensePoly.ofCoeffs <| f.toArray.map fun (coefficient : Int) =>
    (coefficient : Rat) • (1 : QAdjoin p x)

/-- Evaluate a rational coordinate polynomial in another fixed presentation. -/
@[expose]
def evalRatPoly {p : ZPoly} {x : SimpleRoot p}
    (f : DensePoly Rat) (a : QAdjoin p x) : QAdjoin p x :=
  f.toArray.foldr
    (fun coefficient value =>
      value * a + coefficient • (1 : QAdjoin p x))
    0

/-- Recover `theta` and `alpha` in a candidate presentation
`gamma = theta + shift * alpha`. A full-degree candidate can still have a
non-linear gcd because incompatible conjugate pairs need not be field
embeddings, so failure here is a reason to try another shift. -/
@[expose]
def recoverPair? (theta alpha gamma : AlgebraicNumber) (shift : Int) :
    Option (QAdjoin gamma.p gamma.x × QAdjoin gamma.p gamma.x) := do
  if shift = 0 then
    none
  else
    letI : ZPoly.CheckedIrreducible gamma.p := gamma.checked
    let gammaCoordinate := gamma.toQAdjoin
    let affine : DensePoly (QAdjoin gamma.p gamma.x) :=
      DensePoly.ofList
        [gammaCoordinate, (-(shift : Rat)) • (1 : QAdjoin gamma.p gamma.x)]
    let thetaRelation :=
      DensePoly.composeImpl (liftZPoly theta.p) affine
    let alphaRelation : DensePoly (QAdjoin gamma.p gamma.x) :=
      liftZPoly alpha.p
    let common := DensePoly.gcd thetaRelation alphaRelation
    if common.degree?.getD 0 = 1 && common.leadingCoeff != 0 then
      let alphaCoordinate := -(common.coeff 0) / common.leadingCoeff
      let thetaCoordinate :=
        gammaCoordinate - (shift : Rat) • alphaCoordinate
      some (thetaCoordinate, alphaCoordinate)
    else
      none

/-- A full-degree primitive candidate together with its recovered old and new
generator coordinates. -/
structure Recovered where
  shift : Int
  root : AlgebraicNumber
  thetaCoordinate : QAdjoin root.p root.x
  alphaCoordinate : QAdjoin root.p root.x

/-- Search a prescribed shift suffix, rejecting both degree collisions and
full-degree candidates whose exact recovery gcd is not linear. -/
@[expose]
def searchRecoveredAux (theta alpha : AlgebraicNumber)
    (target start : Nat) : Nat → Option Recovered
  | 0 => none
  | fuel + 1 =>
      match candidateAt? theta alpha target start with
      | none =>
          searchRecoveredAux theta alpha target (start + 1) fuel
      | some (shift, root) =>
          match recoverPair? theta alpha root shift with
          | some (thetaCoordinate, alphaCoordinate) =>
              some ⟨shift, root, thetaCoordinate, alphaCoordinate⟩
          | none =>
              searchRecoveredAux theta alpha target (start + 1) fuel

/-- Search the combined finite bound for a primitive candidate with exact
linear coordinate recovery. -/
@[expose]
def searchRecovered? (theta alpha : AlgebraicNumber) (target : Nat) :
    Option Recovered :=
  searchRecoveredAux theta alpha target 1 (flattenShiftCount target)

/-- Combine the fixed generators one level at a time, retaining a tower
coordinate for each accepted canonical primitive element. -/
@[expose]
def candidate? (T : NumberTower) (generators : Array (Generator T)) :
    Option (Candidate T) := do
  match generators[0]? with
  | none =>
      some ⟨1, AlgebraicNumber.zero, 0, #[]⟩
  | some first => do
      if AlgebraicPoly.Common.degree first.root = first.degree then
        generators.toList.drop 1 |>.foldlM
          (fun current generator => do
            let target := current.dimension * generator.degree
            let recovered ←
              searchRecovered? current.root generator.root target
            let value := current.value +
              (recovered.shift : Rat) • generator.value
            let coordinates := current.coordinates.map fun coordinate =>
              evalRatPoly coordinate.coeffs recovered.thetaCoordinate
            some ⟨target, recovered.root, value,
              coordinates.push recovered.alphaCoordinate⟩)
          ⟨first.degree, first.root, first.value, #[first.root.toQAdjoin]⟩
      else
        none

/-- Extend lower mixed-radix basis images by powers of one newly recovered
generator. The lower basis remains the fastest-varying coordinate block. -/
@[expose]
def extendBasis {p : ZPoly} {x : SimpleRoot p}
    (basis : Array (QAdjoin p x)) (generator : QAdjoin p x)
    (degree : Nat) : Array (QAdjoin p x) :=
  let state := (List.range degree).foldl
    (fun state _ =>
      (state.1 ++ basis.map fun b => b * state.2,
        state.2 * generator))
    (#[], 1)
  state.1

/-- Images of the full tower mixed-radix basis in the primitive
presentation. -/
@[expose]
def basisImages {T : NumberTower} {p : ZPoly} {x : SimpleRoot p}
    (generators : Array (Generator T))
    (coordinates : Array (QAdjoin p x)) : Array (QAdjoin p x) :=
  (generators.zip coordinates).foldl
    (fun basis entry => extendBasis basis entry.2 entry.1.degree)
    #[1]

/-- Apply a rational coordinate vector to precomputed primitive-basis images. -/
@[expose]
def toPrimitiveWith {T : NumberTower} {p : ZPoly} {x : SimpleRoot p}
    (images : Array (QAdjoin p x)) (a : Elem T) : QAdjoin p x :=
  (images.zip (coeffs a)).foldl
    (fun value entry => value + entry.2 • entry.1) 0

/-- Evaluate a reduced primitive coordinate polynomial at its tower element. -/
@[expose]
def fromPrimitiveWith {T : NumberTower} {p : ZPoly} {x : SimpleRoot p}
    (generator : Elem T) (a : QAdjoin p x) : Elem T :=
  a.coeffs.toArray.reverse.foldl
    (fun value coefficient => value * generator + ofRat T coefficient) 0

/-- Evaluate an integer polynomial at a tower element. -/
@[expose]
def evalZPoly {T : NumberTower} (f : ZPoly) (a : Elem T) : Elem T :=
  f.toArray.foldr
    (fun (coefficient : Int) value =>
      value * a + ofRat T (coefficient : Rat)) 0

/-- Verify the coordinate composite on the tower basis and check that the
candidate tower element satisfies its claimed primitive minimal polynomial.
The first condition makes the rational-linear coordinate maps inverse; the
root relation and irreducibility make evaluation through the primitive
quotient an injective ring map. The resulting dimension squeeze makes the
linear inverse multiplicative as well. -/
@[expose]
def certifies {T : NumberTower} (candidate : Candidate T)
    (images : Array (QAdjoin candidate.root.p candidate.root.x)) : Bool :=
  let toPrimitive := toPrimitiveWith images
  let fromPrimitive := fromPrimitiveWith candidate.value
  images.size = T.dim && candidate.dimension = T.dim &&
    (List.range T.dim).all (fun i =>
      let basis := ofCoeffs T (unitCoords T.dim i)
      fromPrimitive (toPrimitive basis) == basis) &&
    evalZPoly candidate.root.p candidate.value == 0

end Flatten

/-- Replace a checked tower by one canonical primitive-element presentation.
The result is returned only after exact generator recovery, a tower-basis
round trip, and the primitive polynomial relation succeed. -/
def flatten? (T : NumberTower) : Option (Flattening T) := do
  let generators ← Flatten.generators? T
  let candidate ← Flatten.candidate? T generators
  let images := Flatten.basisImages generators candidate.coordinates
  if Flatten.certifies candidate images then
    some
      { root := candidate.root
        toPrimitive := Flatten.toPrimitiveWith images
        fromPrimitive := Flatten.fromPrimitiveWith candidate.value }
  else
    none

/-! Compiled primitive-element and coordinate round-trip regressions. -/

#guard
    match flatten? rat with
    | some flattened =>
        let value := ofRat rat (7 / 3)
        flattened.root.p = ZPoly.X &&
          (flattened.toPrimitive value).coeffs = DensePoly.C (7 / 3) &&
          flattened.fromPrimitive (flattened.toPrimitive value) == value
    | none => false

private def flattenSqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def flattenSqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def flattenSqrtTwoRep : RefinedIsolation flattenSqrtTwoPoly :=
  ⟨⟨flattenSqrtTwoSquare, .ofWitness (by decide)⟩, by decide⟩

private def flattenSqrtTwoRoot : SimpleRoot flattenSqrtTwoPoly :=
  SimpleRoot.mk flattenSqrtTwoRep

#guard
    if hirred : ZPoly.isIrreducible flattenSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible flattenSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      if hsimple : HasOnlySimpleRoots flattenSqrtTwoPoly then
        let base := ofQAdjoin (x := flattenSqrtTwoRoot)
          hsimple flattenSqrtTwoRep rfl
        match flatten? base.tower with
        | some flattened =>
            flattened.root.p = flattenSqrtTwoPoly &&
              (flattened.toPrimitive base.gen).coeffs =
                DensePoly.ofList [0, 1] &&
              flattened.fromPrimitive
                (flattened.toPrimitive base.gen) == base.gen
        | none => false
      else
        false
    else
      false

private def flattenSqrtThreePoly : ZPoly := DensePoly.ofList [-3, 0, 1]

private def flattenSqrtThreeSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 222 7, 0, 8⟩

private def flattenSqrtThreeRep : RefinedIsolation flattenSqrtThreePoly :=
  ⟨⟨flattenSqrtThreeSquare, .ofWitness (by decide)⟩, by decide⟩

private def flattenSumPoly : ZPoly :=
  DensePoly.ofList [1, 0, -10, 0, 1]

private def flattenFourthRootTwoPoly : ZPoly :=
  DensePoly.ofList [-2, 0, 0, 0, 1]

private def flattenFourthRootTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 77936 16, 0, 17⟩

private def flattenFourthRootTwoRep :
    RefinedIsolation flattenFourthRootTwoPoly :=
  ⟨⟨flattenFourthRootTwoSquare, .ofWitness (by decide)⟩, by decide⟩

#guard
    if hirred : ZPoly.isIrreducible flattenSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible flattenSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      if htwo : HasOnlySimpleRoots flattenSqrtTwoPoly then
        let base := ofQAdjoin (x := flattenSqrtTwoRoot)
          htwo flattenSqrtTwoRep rfl
        if hthree : HasOnlySimpleRoots flattenSqrtThreePoly then
          let root : AlgebraicRoot :=
            { p := flattenSqrtThreePoly
              prim := by rfl
              pos_lc := by decide
              pos_degree := by decide
              squarefree := hthree
              x := SimpleRoot.mk flattenSqrtThreeRep
              rep := flattenSqrtThreeRep
              rep_mk := rfl }
          match adjoin? base.tower root with
          | some extension =>
              match flatten? extension.tower with
              | some flattened =>
                  let sqrtTwo := extension.embed base.gen
                  let sqrtThree := extension.gen
                  let twoCoordinate := flattened.toPrimitive sqrtTwo
                  let threeCoordinate := flattened.toPrimitive sqrtThree
                  flattened.root.p = flattenSumPoly &&
                    twoCoordinate.coeffs =
                      DensePoly.ofList [0, -9 / 2, 0, 1 / 2] &&
                    threeCoordinate.coeffs =
                      DensePoly.ofList [0, 11 / 2, 0, -1 / 2] &&
                    flattened.fromPrimitive twoCoordinate == sqrtTwo &&
                    flattened.fromPrimitive threeCoordinate == sqrtThree
              | none => false
          | none => false
        else
          false
      else
        false
    else
      false

-- The newest absolute generator has degree four but relative degree two. This
-- distinguishes the accumulated relative-dimension target from the naive
-- product of the two absolute minimal-polynomial degrees.
#guard
    if hirred : ZPoly.isIrreducible flattenSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible flattenSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      if htwo : HasOnlySimpleRoots flattenSqrtTwoPoly then
        let base := ofQAdjoin (x := flattenSqrtTwoRoot)
          htwo flattenSqrtTwoRep rfl
        if hfourth : HasOnlySimpleRoots flattenFourthRootTwoPoly then
          let root : AlgebraicRoot :=
            { p := flattenFourthRootTwoPoly
              prim := by rfl
              pos_lc := by decide
              pos_degree := by decide
              squarefree := hfourth
              x := SimpleRoot.mk flattenFourthRootTwoRep
              rep := flattenFourthRootTwoRep
              rep_mk := rfl }
          match adjoin? base.tower root with
          | some extension =>
              match flatten? extension.tower with
              | some flattened =>
                  let sqrtTwo := extension.embed base.gen
                  let fourthRoot := extension.gen
                  let fourthCoordinate :=
                    flattened.toPrimitive fourthRoot
                  flattened.root.p =
                      DensePoly.ofList [2, -8, -4, 0, 1] &&
                    fourthCoordinate.coeffs =
                      DensePoly.ofList [-10 / 9, -1 / 3, -1 / 9, 2 / 9] &&
                    fourthCoordinate * fourthCoordinate ==
                      flattened.toPrimitive sqrtTwo &&
                    flattened.fromPrimitive
                      (flattened.toPrimitive sqrtTwo) == sqrtTwo &&
                    flattened.fromPrimitive fourthCoordinate == fourthRoot
              | none => false
          | none => false
        else
          false
      else
        false
    else
      false

end Hex.NumberTower
