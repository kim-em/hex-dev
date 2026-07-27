/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField.AlgebraicPoly
public import HexResultant
public meta import HexNumberField.AlgebraicPoly
public meta import HexResultant

public section

/-!
Roots of polynomials over a fixed algebraic number field.

The fixed-field driver first separates multiplicities by Yun decomposition,
then takes one integer norm resultant for each square-free component. Candidate
roots of that norm are retained only when bounded ball evaluation at the
selected embedding cannot refute zero.
-/
namespace Hex.QAdjoin.Roots

variable {p : ZPoly} {x : SimpleRoot p}

/-- Monic normalization over a checked fixed field. -/
@[expose]
def monic [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) : DensePoly (QAdjoin p x) :=
  if f.isZero then 0 else DensePoly.scale f.leadingCoeff⁻¹ f

/-- Formal derivative using the existing rational scalar action, avoiding any
law-bearing cast instance on the computational fixed-field carrier. -/
@[expose]
def derivative (f : DensePoly (QAdjoin p x)) : DensePoly (QAdjoin p x) :=
  DensePoly.ofCoeffs <| ((List.range (f.size - 1)).map fun i =>
    ((i + 1 : Nat) : Rat) • f.coeff (i + 1)).toArray

/-- Fuel-bounded characteristic-zero Yun loop. Each returned pair is a monic
square-free component and its positive multiplicity index. -/
@[expose]
def yunAux [ZPoly.CheckedIrreducible p]
    (w repeated : DensePoly (QAdjoin p x)) (multiplicity fuel : Nat)
    (out : Array (DensePoly (QAdjoin p x) × Nat)) :
    Array (DensePoly (QAdjoin p x) × Nat) :=
  match fuel with
  | 0 => out
  | fuel + 1 =>
      if w = 1 then
        out
      else
        let shared := monic (DensePoly.gcd w repeated)
        let component := monic (w / shared)
        let out := if 0 < component.degree?.getD 0 then
          out.push (component, multiplicity)
        else
          out
        let nextRepeated := monic (repeated / shared)
        yunAux shared nextRepeated (multiplicity + 1) fuel out

/-- Yun square-free decomposition over a checked fixed field. The zero and
constant polynomials have no finite components; the public root driver handles
their distinct root-set conventions. -/
@[expose]
def yun [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) :
    Array (DensePoly (QAdjoin p x) × Nat) :=
  if f.degree?.getD 0 = 0 then
    #[]
  else
    let normalized := monic f
    let repeated := monic (DensePoly.gcd normalized (derivative normalized))
    let distinct := monic (normalized / repeated)
    yunAux distinct repeated 1 (f.size + 1) #[]

/-- Common positive denominator of every rational coordinate occurring among
the coefficients of `f`. -/
@[expose]
def commonDen (f : DensePoly (QAdjoin p x)) : Nat :=
  f.toArray.foldl
    (fun den a => a.coeffs.toArray.foldl
      (fun den q => Nat.lcm den q.den) den)
    1

/-- Clear a rational coefficient against a common denominator. -/
@[expose]
def clearRat (den : Nat) (q : Rat) : Int :=
  q.num * Int.ofNat (den / q.den)

/-- Regard a fixed-field polynomial as a polynomial in the generator `y`,
with coefficients in `Int[t]`, after clearing all rational denominators at
once. -/
@[expose]
def clearedOuter (f : DensePoly (QAdjoin p x)) : DensePoly ZPoly :=
  let den := commonDen f
  let generatorDegree := p.degree?.getD 0
  DensePoly.ofCoeffs <| ((List.range generatorDegree).map fun j =>
    DensePoly.ofCoeffs <| ((List.range f.size).map fun i =>
      clearRat den ((f.coeff i).coeffs.coeff j)).toArray).toArray

/-- Integer norm eliminant `Res_y(p(y), F(y,t))` of a fixed-field
polynomial. -/
@[expose]
def normEliminant (f : DensePoly (QAdjoin p x)) : ZPoly :=
  DensePoly.resultant p.liftOuter (clearedOuter f)

/-- A canonical coefficient as a lazy root, propagating any checked
conversion failure. -/
@[expose]
def coeffRoot? [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) : Option AlgebraicRoot :=
  if a.isZero then
    some AlgebraicNumber.zero.toRoot
  else do
    let exact ← a.toAlgebraicNumber? rep h
    some exact.toRoot

/-- Exact lazy Horner evaluation. Its enclosing polynomial is the evaluation
eliminant used for the reciprocal-Cauchy zero bound. -/
@[expose]
def evalRoot? [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (candidate : AlgebraicRoot) :
    Option AlgebraicRoot := do
  f.toArray.reverse.toList.foldlM
    (fun acc coeff => do
      let product ← acc.mul? candidate
      let coefficient ← coeffRoot? coeff rep h
      product.add? coefficient)
    AlgebraicNumber.zero.toRoot

/-- Certified ball Horner evaluation at the selected fixed-field embedding and
one absolute candidate root. Coefficient approximation retains its sound
fallback; candidate refinement is checked because the bounded selector must
observe the requested shrinking radius. -/
@[expose]
def evalBall? [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (candidate : AlgebraicRoot)
    (prec : Nat) : Option DyadicComplexBall := do
  -- A square at precision `prec + 1` has circumscribed-disc radius below
  -- `2^-prec`; this is the common input-error unit used by `evalMajorant`.
  let candidate' ← candidate.rep.refineTo? ((prec : Int) + 1)
  let z := candidate'.1.1.square.toBall
  let coeffs := f.toArray
  match coeffs.back? with
  | none => some DyadicComplexBall.zero
  | some top =>
      let topBall := (top.approx rep h (prec : Int)).2
      some <| coeffs.foldr
        (fun coeff acc =>
          ((coeff.approx rep h (prec : Int)).2).add (z.mul acc))
        topBall (start := coeffs.size - 1)

/-- Isolate a component's norm roots and retain exactly the roots belonging to
the selected embedding. -/
@[expose]
def componentRoots? [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (multiplicity : Nat)
    (hMultiplicity : 0 < multiplicity) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) : Option (Array RootCount) := do
  let eliminant := ZPoly.squareFreeCore (normEliminant f)
  if hprim : ZPoly.content eliminant = 1 then
    if hpos : 0 < eliminant.leadingCoeff then
      if hdegree : 0 < eliminant.degree?.getD 0 then
        if hsimple : HasOnlySimpleRoots eliminant then do
          let isolations ← isolate eliminant hsimple (separationDepth eliminant : Int)
          let refined ← isolations.mapM DyadicRootIsolation.toRefined?
          refined.foldlM
            (fun out candidateRep => do
              let candidate : AlgebraicRoot :=
                { p := eliminant
                  prim := hprim
                  pos_lc := hpos
                  pos_degree := hdegree
                  squarefree := hsimple
                  x := SimpleRoot.mk candidateRep
                  rep := candidateRep
                  rep_mk := rfl }
              let evaluation ← evalRoot? f rep h candidate
              let keep ← retainZero? evaluation.p (evalMajorant f candidate.p)
                (evalBall? f rep h candidate)
              if keep then
                some (out.push
                  { root := candidate
                    multiplicity
                    multiplicity_pos := hMultiplicity })
              else
                some out)
            #[]
        else
          none
      else
        none
    else
      none
  else
    none

/-- Semantic equality of two lazy roots, using the fast common-polynomial path
and exactifying only when their enclosing polynomials differ. -/
@[expose]
def sameValue? (a b : AlgebraicRoot) : Option Bool :=
  if hp : a.p = b.p then
    some ((hp ▸ a.rep).sameRoot b.rep)
  else do
    let a' ← a.exact?
    let b' ← b.exact?
    some (a' == b')

/-- Merge one root into a duplicate-free multiplicity array. -/
@[expose]
def mergeRootAux (candidate : RootCount) (index : Nat) :
    Nat → Array RootCount → Option (Array RootCount)
  | 0, roots => some (roots.push candidate)
  | fuel + 1, roots =>
      if hi : index < roots.size then do
        let current := roots[index]
        let same ← sameValue? current.root candidate.root
        if same then
          let merged : RootCount :=
            { root := current.root
              multiplicity := current.multiplicity + candidate.multiplicity
              multiplicity_pos := by
                have hc : 0 < current.multiplicity := current.multiplicity_pos
                omega }
          some ((roots.eraseIdx index).push merged)
        else
          mergeRootAux candidate (index + 1) fuel roots
      else
        some (roots.push candidate)

/-- Merge one root using a complete scan of the current array. -/
@[expose]
def mergeRoot (roots : Array RootCount) (candidate : RootCount) :
    Option (Array RootCount) :=
  mergeRootAux candidate 0 (roots.size + 1) roots

/-- Lexicographic non-strict order on integer coefficient lists. -/
@[expose]
def intListLe : List Int → List Int → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a < b then true
      else if b < a then false
      else intListLe as bs

/-- Stable root order: enclosing polynomial coefficients, then isolation
centre and precision. -/
@[expose]
def rootLe (a b : RootCount) : Bool :=
  if a.root.p != b.root.p then
    intListLe a.root.p.toArray.toList b.root.p.toArray.toList
  else if a.root.rep.1.square.re != b.root.rep.1.square.re then
    decide (a.root.rep.1.square.re < b.root.rep.1.square.re)
  else if a.root.rep.1.square.im != b.root.rep.1.square.im then
    decide (a.root.rep.1.square.im < b.root.rep.1.square.im)
  else
    decide (a.root.rep.1.square.prec ≤ b.root.rep.1.square.prec)

end Hex.QAdjoin.Roots

namespace Hex.QAdjoin

variable {p : ZPoly} {x : SimpleRoot p}

/-- Checked roots of a fixed-field polynomial. `none` is reserved for a
certificate that did not appear within its prescribed finite bound. -/
@[expose]
def roots? [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) : Option RootSet :=
  if f.isZero then
    some .all
  else if f.degree?.getD 0 = 0 then
    some (.finite #[])
  else do
    let roots ← (Roots.yun f).foldlM
      (fun out component =>
        if hm : 0 < component.2 then do
          let found ← Roots.componentRoots? component.1 component.2 hm rep h
          found.foldlM Roots.mergeRoot out
        else
          none)
      #[]
    some (.finite (roots.qsort Roots.rootLe))

/-- Total fixed-field root API. The loud `.all` fallback is unreachable once
the companion discharges `roots?_isSome`. -/
@[expose]
def roots [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) : RootSet :=
  (roots? f rep h).getD
    (Hex.panicWith .all "QAdjoin.roots: certification failed")

end Hex.QAdjoin

namespace Hex

/-! Compiled fixed-field root regressions. -/

private def rootsSqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def rootsSqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def rootsSqrtTwoRep : RefinedIsolation rootsSqrtTwoPoly :=
  ⟨⟨rootsSqrtTwoSquare, by decide⟩, by decide⟩

private def rootsSqrtTwoRoot : SimpleRoot rootsSqrtTwoPoly :=
  SimpleRoot.mk rootsSqrtTwoRep

private def rootsSqrtTwo : QAdjoin rootsSqrtTwoPoly rootsSqrtTwoRoot :=
  QAdjoin.reduce rootsSqrtTwoPoly rootsSqrtTwoRoot
    (DensePoly.ofList ([0, 1] : List Rat))

private def rootsLinear : DensePoly (QAdjoin rootsSqrtTwoPoly rootsSqrtTwoRoot) :=
  DensePoly.ofList [-rootsSqrtTwo, 1]

#guard QAdjoin.Roots.normEliminant rootsLinear = rootsSqrtTwoPoly

#guard
    if hirred : ZPoly.isIrreducible rootsSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible rootsSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      let factors := QAdjoin.Roots.yun (rootsLinear * rootsLinear)
      factors.size = 1 &&
        (factors[0]?).map (fun factor => factor.2) = some 2
    else
      false

#guard
    if hirred : ZPoly.isIrreducible rootsSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible rootsSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      match QAdjoin.roots? (rootsLinear * rootsLinear) rootsSqrtTwoRep rfl with
      | some (.finite roots) =>
          roots.size = 1 &&
            (roots[0]?).map (fun root => root.multiplicity) = some 2 &&
            (roots[0]?).any fun root => decide (0 < root.root.rep.1.square.re)
      | _ => false
    else
      false

#guard
    if hirred : ZPoly.isIrreducible rootsSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible rootsSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      match
          QAdjoin.roots?
            (0 : DensePoly (QAdjoin rootsSqrtTwoPoly rootsSqrtTwoRoot))
            rootsSqrtTwoRep rfl,
          QAdjoin.roots? 1 rootsSqrtTwoRep rfl with
      | some .all, some (.finite roots) => roots.isEmpty
      | _, _ => false
    else
      false

end Hex
