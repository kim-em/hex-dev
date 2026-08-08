/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTower.Factor
public meta import HexNumberFieldTower.Factor

public section

/-!
# Adjoining roots and splitting tower polynomials

The fixed embedding of a tower is evaluated recursively in mixed-radix order.
Factor selection uses the bounded evaluation-disambiguation machinery from
`HexNumberField`: a wrong conjugate factor is rejected by a certified ball,
while exactly one factor of the candidate's enclosing polynomial is retained.
-/
namespace Hex.NumberTower

namespace Evaluation

/-- Evaluate a fixed tower element in its chosen absolute embedding. -/
@[expose]
def evalElem? (T : NumberTower) (a : Elem T) : Option AlgebraicRoot :=
  RawEvaluation.evalCoords? T.levels.toList (coeffs a)

/-- Exact lazy Horner evaluation of a tower polynomial at an absolute
candidate root. -/
@[expose]
def evalPoly? (T : NumberTower) (f : Poly T) (candidate : AlgebraicRoot) :
    Option AlgebraicRoot :=
  RawEvaluation.evalPoly? T.levels.toList (f.toArray.map coeffs) candidate

/-- Integer magnitude majorant for a fixed tower element. -/
@[expose]
def elemMajorant (T : NumberTower) (a : Elem T) : Nat :=
  RawEvaluation.coordsMajorant T.levels.toList (coeffs a)

/-- Certified ball Horner evaluation at the tower's fixed embedding and one
absolute candidate root. Each exact coefficient is refined far enough to
supply the common `2^-prec` input-error unit consumed by
{name}`Hex.Disambiguation.evalMajorant`. -/
@[expose]
def evalBall? (T : NumberTower) (f : Poly T) (candidate : AlgebraicRoot)
    (prec : Nat) : Option DyadicComplexBall :=
  RawEvaluation.evalBall? T.levels.toList (f.toArray.map coeffs)
    candidate prec

/-- Decide, with the prescribed finite precision endpoint, whether a tower
polynomial vanishes at an absolute candidate root. -/
@[expose]
def vanishesAt? (T : NumberTower) (f : Poly T)
    (candidate : AlgebraicRoot) : Option Bool :=
  RawEvaluation.vanishesAt? T.levels.toList (f.toArray.map coeffs) candidate

end Evaluation

/-- Lift an integer polynomial coefficientwise to a tower polynomial. -/
@[expose]
def liftZPoly (T : NumberTower) (p : ZPoly) : Poly T :=
  DensePoly.ofCoeffs <| p.toArray.map fun (coefficient : Int) =>
    ofRat T (coefficient : Rat)

/-- Retain the unique multiplicity-one irreducible factor that vanishes at the
specified absolute root under the tower's fixed embedding. -/
@[expose]
def selectFactor? (T : NumberTower) (candidate : AlgebraicRoot)
    (factors : Array (Poly T × Nat)) : Option (Poly T) := do
  let selected ← factors.foldlM (fun selected entry => do
    if entry.2 = 1 then
      let keep ← Evaluation.vanishesAt? T entry.1 candidate
      if keep then some (selected.push entry.1) else some selected
    else
      none) #[]
  match selected.toList with
  | [factor] => some factor
  | _ => none

/-- Encode a selected monic relative factor as one raw extension level. -/
@[expose]
def levelOfFactor (candidate : AlgebraicRoot) (selected : Poly T) : Level :=
  let d := selected.degree?.getD 0
  let defining := ((List.range d).map fun i =>
    coeffs (selected.coeff i)).toArray
  ⟨d, defining, candidate⟩

/-- Root data for a polynomial over a completed splitting tower. -/
inductive Roots (T : NumberTower) where
  | all
  | finite (roots : Array (Elem T × Nat))

/-- A checked extension together with all roots of the original polynomial in
that extension. -/
structure Splitting (T : NumberTower) (f : Poly T) where
  extension : Extension T
  roots : Roots extension.tower

/-- Map polynomial coefficients through an explicitly supplied tower
embedding. -/
@[expose]
def mapPoly {T U : NumberTower} (embed : Elem T → Elem U)
    (f : Poly T) : Poly U :=
  DensePoly.ofCoeffs (f.toArray.map embed)

/-- The identity extension, used when no generator needs to be adjoined. -/
@[expose]
def Extension.identity (T : NumberTower) : Extension T :=
  { tower := T
    embed := id
    gen := 0
    root := AlgebraicNumber.zero.toRoot }

/-- Compose dependent tower extensions while retaining the most recently
adjoined generator. -/
@[expose]
def Extension.trans {T : NumberTower} (outer : Extension T)
    (inner : Extension outer.tower) : Extension T :=
  { tower := inner.tower
    embed := fun a => inner.embed (outer.embed a)
    gen := inner.gen
    root := inner.root }

/-- The carrier of a composed extension is the carrier of its inner step. -/
theorem Extension.trans_tower {T : NumberTower} (outer : Extension T)
    (inner : Extension outer.tower) :
    (outer.trans inner).tower = inner.tower := rfl

/-- A composed extension embeds by applying the outer and then inner map. -/
theorem Extension.trans_embed {T : NumberTower} (outer : Extension T)
    (inner : Extension outer.tower) (a : Elem T) :
    (outer.trans inner).embed a = inner.embed (outer.embed a) := rfl

/-- Record-level normal form for a composed extension. -/
theorem Extension.trans_eq {T : NumberTower} (outer : Extension T)
    (inner : Extension outer.tower) :
    outer.trans inner =
      { tower := inner.tower
        embed := fun a => inner.embed (outer.embed a)
        gen := inner.gen
        root := inner.root } := rfl

/-- Whole-record normal form for pulling an inner splitting back through an
extension.  Stating the equality at this level keeps the dependent root
carrier aligned while clients reason about the explicit composite. -/
theorem Splitting.trans_eq {T : NumberTower} {f : Poly T}
    (outer : Extension T)
    (inner : Splitting outer.tower (mapPoly outer.embed f)) :
    ({ extension := outer.trans inner.extension
       roots := inner.roots } : Splitting T f) =
      { extension :=
          { tower := inner.extension.tower
            embed := fun a => inner.extension.embed (outer.embed a)
            gen := inner.extension.gen
            root := inner.extension.root }
        roots := inner.roots } := rfl

/-- Adjoin the specified absolute algebraic root. A selected linear factor
produces the identity extension; a nonlinear factor is admitted only through
{name}`Hex.NumberTower.Internal.extend?`, which reruns structural,
relative-irreducibility, and fixed-
embedding checks before constructing the new carrier index. -/
@[expose]
def adjoin? (T : NumberTower) (candidate : AlgebraicRoot) :
    Option (Extension T) := do
  let input := liftZPoly T candidate.p
  let factorization ← factor? T input
  let selected ← selectFactor? T candidate factorization.factors
  let d := selected.degree?.getD 0
  if d = 0 then
    none
  else if d = 1 then
    some
      { tower := T
        embed := id
        gen := -(selected.coeff 0) / selected.leadingCoeff
        root := candidate }
  else
    let level := levelOfFactor candidate selected
    let tower ← Internal.extend? T level
    some
      { tower
        embed := fun a => ofCoeffs tower (coeffs a)
        gen := ofCoeffs tower ((Array.replicate T.dim 0).push 1)
        root := candidate }

/-- Squarefree primitive integer eliminant obtained by taking the selected
factor's norm through every tower level. -/
@[expose]
def factorEliminant (T : NumberTower) (f : Poly T) : ZPoly :=
  let absolute := Norm.iterated T.levels.toList (f.toArray.map coeffs)
  ZPoly.squareFreeCore <|
    ZPoly.ratPolyPrimitivePart (Factor.toRatPoly absolute)

/-- Retain exactly the absolute candidates at which the relative factor
vanishes, preserving isolation order. -/
@[expose]
def retainRoots? (T : NumberTower) (f : Poly T) :
    List AlgebraicRoot → Option (List AlgebraicRoot)
  | [] => some []
  | candidate :: candidates => do
      let keep ← Evaluation.vanishesAt? T f candidate
      let retained ← retainRoots? T f candidates
      if keep then some (candidate :: retained) else some retained

/-- Isolate the absolute eliminant and retain the first root that zeros the
relative factor under the current fixed embedding. -/
@[expose]
def factorRoot? (T : NumberTower) (f : Poly T) : Option AlgebraicRoot := do
  let p := factorEliminant T f
  if hprim : ZPoly.content p = 1 then
    if hpos : 0 < p.leadingCoeff then
      if hdegree : 0 < p.degree?.getD 0 then
        if hsimple : HasOnlySimpleRoots p then do
          let isolations ← isolate p hsimple (separationDepth p : Int)
          let refined ← isolations.mapM DyadicRootIsolation.toRefined?
          let candidates := refined.toList.map fun rep : RefinedIsolation p =>
            ({ p
               prim := hprim
               pos_lc := hpos
               pos_degree := hdegree
               squarefree := hsimple
               x := SimpleRoot.mk rep
               rep
               rep_mk := rfl } : AlgebraicRoot)
          let retained ← retainRoots? T f candidates
          retained.head?
        else
          none
      else
        none
    else
      none
  else
    none

/-- Recover all roots once a checked factorization is entirely linear. -/
@[expose]
def linearRoots? {T : NumberTower} (factors : Array (Poly T × Nat)) :
    Option (Array (Elem T × Nat)) :=
  factors.mapM fun entry =>
    if entry.1.degree?.getD 0 = 1 && 0 < entry.2 then
      some (-(entry.1.coeff 0) / entry.1.leadingCoeff, entry.2)
    else
      none

/-- Fuel-bounded split/refactor loop. Each recursive call works over the local
tower and composes its checked extension on return, retaining the intermediate
embedding needed by proof-facing consumers. Every successful nonlinear
iteration consumes one fuel unit and must strictly increase the tower
dimension. -/
@[expose]
def splitAux (T : NumberTower) (f : Poly T) (fuel : Nat) :
    Option (Splitting T f) := do
  let factorization ← factor? T f
  match linearRoots? factorization.factors with
  | some roots =>
      some { extension := Extension.identity T
             roots := .finite roots }
  | none =>
      match fuel with
      | 0 => none
      | fuel + 1 => do
          let nonlinear ← factorization.factors.toList.find? fun entry =>
            decide (1 < entry.1.degree?.getD 0)
          let candidate ← factorRoot? T nonlinear.1
          let step ← adjoin? T candidate
          if step.tower.dim ≤ T.dim then
            none
          else
            let inner ← splitAux step.tower (mapPoly step.embed f) fuel
            some
              { extension := step.trans inner.extension
                roots := inner.roots }

/-- Construct an extension in which the input polynomial splits into linear
factors, retaining multiplicities from checked factorization. -/
@[expose]
def split? (T : NumberTower) (f : Poly T) : Option (Splitting T f) :=
  if f.isZero then
    some { extension := Extension.identity T
           roots := .all }
  else if f.degree?.getD 0 = 0 then
    some { extension := Extension.identity T
           roots := .finite #[] }
  else
    splitAux T f (f.degree?.getD 0)

/-! Compiled fixed-embedding selection regression. -/

private def selectSqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def selectSqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def selectSqrtTwoRep : RefinedIsolation selectSqrtTwoPoly :=
  ⟨⟨selectSqrtTwoSquare, .ofWitness (by decide)⟩, by decide⟩

private def selectSqrtTwoRoot : SimpleRoot selectSqrtTwoPoly :=
  SimpleRoot.mk selectSqrtTwoRep

-- The quotient alone admits both conjugate linear factors. Evaluation at the
-- stored positive root must retain `X - sqrt(2)` and reject `X + sqrt(2)`.
#guard
    if hirred : ZPoly.isIrreducible selectSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible selectSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      if hsimple : HasOnlySimpleRoots selectSqrtTwoPoly then
        let extension := ofQAdjoin (x := selectSqrtTwoRoot)
          hsimple selectSqrtTwoRep rfl
        let input := liftZPoly extension.tower selectSqrtTwoPoly
        match Evaluation.evalElem? extension.tower extension.gen,
            factor? extension.tower input with
        | some evaluated, some factorization =>
            match QAdjoin.Roots.sameValue? evaluated extension.root,
                selectFactor? extension.tower extension.root
                  factorization.factors with
            | some true, some selected =>
                factorization.factors.size = 2 &&
                  selected.degree?.getD 0 = 1 &&
                  coeffs (selected.coeff 0) = #[0, -1] &&
                  Evaluation.vanishesAt? extension.tower selected
                    extension.root = some true
            | _, _ => false
        | _, _ => false
      else
        false
    else
      false

-- Adjoining a root already present in the fixed embedding returns the
-- identity tower and recovers the existing element from its linear factor.
#guard
    if hirred : ZPoly.isIrreducible selectSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible selectSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      if hsimple : HasOnlySimpleRoots selectSqrtTwoPoly then
        let base := ofQAdjoin (x := selectSqrtTwoRoot)
          hsimple selectSqrtTwoRep rfl
        match adjoin? base.tower base.root with
        | some identity =>
            identity.tower.height = base.tower.height &&
              identity.tower.dim = base.tower.dim &&
              coeffs identity.gen = coeffs base.gen &&
              coeffs (identity.embed base.gen) = coeffs base.gen
        | none => false
      else
        false
    else
      false

private def selectSqrtThreePoly : ZPoly := DensePoly.ofList [-3, 0, 1]

private def selectSqrtThreeSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 222 7, 0, 8⟩

private def selectSqrtThreeRep : RefinedIsolation selectSqrtThreePoly :=
  ⟨⟨selectSqrtThreeSquare, .ofWitness (by decide)⟩, by decide⟩

private def selectFourthRootTwoPoly : ZPoly :=
  DensePoly.ofList [-2, 0, 0, 0, 1]

private def selectFourthRootTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 77936 16, 0, 17⟩

private def selectFourthRootTwoRep :
    RefinedIsolation selectFourthRootTwoPoly :=
  ⟨⟨selectFourthRootTwoSquare, .ofWitness (by decide)⟩, by decide⟩

-- A genuinely new root is admitted through the checked relative-level
-- constructor. The old generator occupies the first lower block and the new
-- generator satisfies the selected relation.
#guard
    if hirred : ZPoly.isIrreducible selectSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible selectSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      if hsimple : HasOnlySimpleRoots selectSqrtTwoPoly then
        let base := ofQAdjoin (x := selectSqrtTwoRoot)
          hsimple selectSqrtTwoRep rfl
        if hthree : HasOnlySimpleRoots selectSqrtThreePoly then
          let candidate : AlgebraicRoot :=
            { p := selectSqrtThreePoly
              prim := by rfl
              pos_lc := by decide
              pos_degree := by decide
              squarefree := hthree
              x := SimpleRoot.mk selectSqrtThreeRep
              rep := selectSqrtThreeRep
              rep_mk := rfl }
          match adjoin? base.tower candidate with
          | some extension =>
              extension.tower.height = 2 && extension.tower.dim = 4 &&
                coeffs (extension.embed base.gen) = #[0, 1, 0, 0] &&
                coeffs (extension.gen * extension.gen) = #[3, 0, 0, 0]
          | none => false
        else
          false
      else
        false
    else
      false

-- The fourth-root polynomial splits over `Q(sqrt(2))` into two nonlinear
-- conjugate factors. Fixed-embedding selection must retain the factor with
-- the negative non-rational constant and use it as the new relation.
#guard
    if hirred : ZPoly.isIrreducible selectSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible selectSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      if hsimple : HasOnlySimpleRoots selectSqrtTwoPoly then
        let base := ofQAdjoin (x := selectSqrtTwoRoot)
          hsimple selectSqrtTwoRep rfl
        if hfourth : HasOnlySimpleRoots selectFourthRootTwoPoly then
          let fourth : AlgebraicRoot :=
            { p := selectFourthRootTwoPoly
              prim := by rfl
              pos_lc := by decide
              pos_degree := by decide
              squarefree := hfourth
              x := SimpleRoot.mk selectFourthRootTwoRep
              rep := selectFourthRootTwoRep
              rep_mk := rfl }
          let minus : Poly base.tower := DensePoly.ofCoeffs
            #[-base.gen, 0, 1]
          let plus : Poly base.tower := DensePoly.ofCoeffs
            #[base.gen, 0, 1]
          match selectFactor? base.tower fourth
              #[(minus, 1), (plus, 1)] with
          | some selected =>
              let level := levelOfFactor fourth selected
              selected.degree?.getD 0 = 2 &&
                coeffs (selected.coeff 0) = #[0, -1] &&
                level.defining = #[#[0, -1], #[0, 0]]
          | none => false
        else
          false
      else
        false
    else
      false

-- An otherwise irreducible relative relation is rejected when it does not
-- vanish at the absolute root recorded for the new level.
#guard
    if hirred : ZPoly.isIrreducible selectSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible selectSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      if hsimple : HasOnlySimpleRoots selectSqrtTwoPoly then
        let base := ofQAdjoin (x := selectSqrtTwoRoot)
          hsimple selectSqrtTwoRep rfl
        let mismatched : Level :=
          ⟨2, #[#[-3, 0], #[0, 0]], base.root⟩
        if Factor.isIrreducible base.tower.levels.toList
            (mismatched.polynomial base.tower.levels.toList) then
          if RawEvaluation.vanishesAt? base.tower.levels.toList
              (mismatched.polynomial base.tower.levels.toList)
              mismatched.root = some false then
            match Internal.extend? base.tower mismatched with
            | none => true
            | some _ => false
          else
            false
        else
          false
      else
        false
    else
      false

-- Zero and nonzero constants split in the identity tower without inventing
-- roots.
#guard
    let constant : Poly rat := DensePoly.C (ofRat rat 5)
    match split? rat 0, split? rat constant with
    | some zeroResult, some constantResult =>
        zeroResult.extension.tower.dim = 1 &&
          constantResult.extension.tower.dim = 1 &&
          match zeroResult.roots, constantResult.roots with
          | .all, .finite roots => roots.isEmpty
          | _, _ => false
    | _, _ => false

-- Splitting one rational quadratic adjoins one root and recovers both linear
-- factors with multiplicity one.
#guard
    let quadratic : Poly rat := DensePoly.ofCoeffs
      #[ofRat rat (-2), 0, 1]
    match split? rat quadratic with
    | some result =>
        result.extension.tower.height = 1 &&
          result.extension.tower.dim = 2 &&
          match result.roots with
          | .finite roots =>
              roots.size = 2 && roots.all fun entry =>
                entry.2 = 1 &&
                  coeffs (entry.1 * entry.1) = #[2, 0]
          | .all => false
    | none => false

-- Multiplicities survive the adjoin/refactor loop rather than being recovered
-- from a squarefree absolute eliminant.
#guard
    let repeated : Poly rat := DensePoly.ofCoeffs
      #[ofRat rat 4, 0, ofRat rat (-4), 0, 1]
    match split? rat repeated with
    | some result =>
        match result.roots with
        | .finite roots =>
            result.extension.tower.dim = 2 && roots.size = 2 &&
              roots.all fun entry =>
                entry.2 = 2 &&
                  coeffs (entry.1 * entry.1) = #[2, 0]
        | .all => false
    | none => false

-- The quartic `(X² - 2)(X² - 3)` requires two genuine adjoining steps and
-- ends in `Q(sqrt(2), sqrt(3))` with all four simple roots.
#guard
    let quartic : Poly rat := DensePoly.ofCoeffs
      #[ofRat rat 6, 0, ofRat rat (-5), 0, 1]
    match split? rat quartic with
    | some result =>
        result.extension.tower.height = 2 &&
          result.extension.tower.dim = 4 &&
          match result.roots with
          | .finite roots =>
              roots.size = 4 && roots.all fun entry =>
                let square := coeffs (entry.1 * entry.1)
                entry.2 = 1 &&
                  (square = #[2, 0, 0, 0] ||
                    square = #[3, 0, 0, 0])
          | .all => false
    | none => false

end Hex.NumberTower
