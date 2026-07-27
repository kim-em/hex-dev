/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTower.Split
public import HexRowReduce
public meta import HexNumberFieldTower.Split
public meta import HexRowReduce

public section

/-!
# Primitive-element flattening for number-field towers

The fixed absolute generators are combined in deterministic signed-shift order.
A candidate is admitted only when its canonical minimal-polynomial degree is the
full accumulated tower dimension. Exact trace-pairing row reduction then
recovers every old generator in the primitive power basis. Both coordinate
maps are checked on their respective rational bases before they are returned.
-/
namespace Hex.NumberTower

/-- A one-generator presentation of a tower together with checked executable
coordinate conversions in both directions. -/
structure Flattening (T : NumberTower) where
  root : AlgebraicNumber
  toPrimitive : Elem T → QAdjoin root.p root.x
  fromPrimitive : QAdjoin root.p root.x → Elem T

/-- The finite primitive-element collision bound for a field of dimension
`dimension`. -/
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

/-- Standard coordinate vector of length `dimension`. -/
@[expose]
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

/-- Search a prescribed suffix of the deterministic signed shifts for a
candidate of the full required degree. -/
@[expose]
def searchAux (theta alpha : AlgebraicNumber) (target start : Nat) : Nat →
    Option (Int × AlgebraicNumber)
  | 0 => none
  | fuel + 1 => do
      let shift := Norm.signedShift start
      let candidate ← AlgebraicPoly.Common.shift? theta alpha shift
      if AlgebraicPoly.Common.degree candidate = target then
        some (shift, candidate)
      else
        searchAux theta alpha target (start + 1) fuel

/-- Search exactly the primitive-element collision bound. -/
@[expose]
def search? (theta alpha : AlgebraicNumber) (target : Nat) :
    Option (Int × AlgebraicNumber) :=
  searchAux theta alpha target 0 (flattenShiftCount target)

/-- Combine the fixed generators one level at a time, retaining a tower
coordinate for each accepted canonical primitive element. -/
@[expose]
def candidate? (T : NumberTower) (generators : Array (Generator T)) :
    Option (Candidate T) := do
  match generators[0]? with
  | none =>
      some ⟨1, AlgebraicNumber.zero, 0⟩
  | some first => do
      if AlgebraicPoly.Common.degree first.root = first.degree then
        generators.toList.drop 1 |>.foldlM
          (fun current generator => do
            let target := current.dimension * generator.degree
            let (shift, root) ← search? current.root generator.root target
            let value := current.value + (shift : Rat) • generator.value
            some ⟨target, root, value⟩)
          ⟨first.degree, first.root, first.value⟩
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

/-- Verify both coordinate composites on the mixed-radix and primitive power
bases. -/
@[expose]
def roundTrips {T : NumberTower} (candidate : Candidate T)
    (images : Array (QAdjoin candidate.root.p candidate.root.x)) : Bool :=
  let toPrimitive := toPrimitiveWith images
  let fromPrimitive := fromPrimitiveWith candidate.value
  images.size = T.dim && candidate.dimension = T.dim &&
    (List.range T.dim).all (fun i =>
      let basis := ofCoeffs T (unitCoords T.dim i)
      fromPrimitive (toPrimitive basis) == basis) &&
    (List.range T.dim).all (fun i =>
      let basis := QAdjoin.reduce candidate.root.p candidate.root.x
        (DensePoly.monomial i 1)
      toPrimitive (fromPrimitive basis) == basis)

end Flatten

/-- Replace a checked tower by one canonical primitive-element presentation.
The result is returned only after exact generator recovery and both basis
round-trip checks succeed. -/
def flatten? (T : NumberTower) : Option (Flattening T) := do
  let generators ← Flatten.generators? T
  let candidate ← Flatten.candidate? T generators
  let powers ← AlgebraicPoly.Common.powers? candidate.root
    (2 * candidate.dimension - 2)
  let coordinates ← generators.mapM fun generator =>
    AlgebraicPoly.Common.coordinates? candidate.root generator.root powers
  let images := Flatten.basisImages generators coordinates
  if Flatten.roundTrips candidate images then
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
  ⟨⟨flattenSqrtTwoSquare, by decide⟩, by decide⟩

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
  ⟨⟨flattenSqrtThreeSquare, by decide⟩, by decide⟩

private def flattenSumPoly : ZPoly :=
  DensePoly.ofList [1, 0, -10, 0, 1]

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

end Hex.NumberTower
