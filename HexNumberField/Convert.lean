/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField.QAdjoin
public import HexRowReduce
public meta import HexNumberField.QAdjoin
public meta import HexRowReduce

public section

/-!
Canonical fixed-presentation conversion and exactification of lazy roots.

Exactification factors the enclosing squarefree polynomial, rechecks each
factor's executable normalization certificates, isolates its roots, and keeps
the unique factor isolation whose disc meets the input representative. The
selected factor is finally passed through
{name}`Hex.AlgebraicNumber.ofNormalized?`, so
the stored representative follows the library's deterministic canonical
isolation strategy.
-/
namespace Hex

namespace AlgebraicNumber

/-- The canonical algebraic number as the fixed-field generator in its own
minimal-polynomial presentation. -/
@[expose]
def toQAdjoin (a : AlgebraicNumber) : QAdjoin a.p a.x :=
  QAdjoin.reduce a.p a.x (DensePoly.ofList ([0, 1] : List Rat))

/-- Forget minimality while retaining every checked root certificate. -/
@[expose]
def toRoot (a : AlgebraicNumber) : AlgebraicRoot where
  p := a.p
  prim := a.prim
  pos_lc := a.pos_lc
  pos_degree := a.pos_degree
  squarefree := a.squarefree
  x := a.x
  rep := a.rep
  rep_mk := a.rep_mk

end AlgebraicNumber

namespace AlgebraicRoot

/-- Try one normalized factor of a lazy root's enclosing polynomial. Candidate
isolations are refined to the enclosing polynomial's separation precision
before their discs are compared. -/
@[expose]
def exactFactor? (a : AlgebraicRoot) (q : ZPoly) : Option AlgebraicNumber :=
  if hprim : ZPoly.content q = 1 then
    if hpos : 0 < q.leadingCoeff then
      if hdegree : 0 < q.degree?.getD 0 then
        if hirred : ZPoly.isIrreducible q = true then
          if hsquarefree : HasOnlySimpleRoots q then do
            let isolations ← isolate q hsquarefree (separationDepth q : Int)
            let refined ← isolations.mapM DyadicRootIsolation.toRefined?
            let comparable ← refined.mapM fun r =>
              (r.refineTo? (mahlerPrec a.p : Int)).unattach
            let matching ← comparable.toList.find? fun r =>
              decide ((mahlerPrec a.p : Int) ≤ r.1.square.prec) &&
                r.1.square.discsMeet a.rep.1.square
            AlgebraicNumber.ofNormalized? q hprim hpos hdegree
              ⟨hirred, hdegree⟩ hsquarefree matching
          else
            none
        else
          none
      else
        none
    else
      none
  else
    none

/-- Factor a lazy root's enclosing polynomial and select the normalized
irreducible factor containing its chosen root. -/
@[expose]
def exact? (a : AlgebraicRoot) : Option AlgebraicNumber :=
  (ZPoly.factorize a.p).factors.foldl
    (fun found entry =>
      match found with
      | some b => some b
      | none => exactFactor? a entry.1)
    none

/-- Canonicalize a lazy root. Failure is a checked implementation branch whose
unreachability is proved by the Mathlib companion. -/
@[expose]
def exact (a : AlgebraicRoot) : AlgebraicNumber :=
  a.exact?.getD (Hex.panicWith 0 "AlgebraicRoot.exact: certification failed")

/-! Compiled canonicalization regressions. -/

private def sqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def sqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def sqrtTwoRep : RefinedIsolation sqrtTwoPoly :=
  ⟨⟨sqrtTwoSquare, by decide⟩, by decide⟩

private def sqrtTwoRoot (hsquarefree : HasOnlySimpleRoots sqrtTwoPoly) : AlgebraicRoot where
  p := sqrtTwoPoly
  prim := by rfl
  pos_lc := by decide
  pos_degree := by decide
  squarefree := hsquarefree
  x := SimpleRoot.mk sqrtTwoRep
  rep := sqrtTwoRep
  rep_mk := rfl

#guard
    if hsquarefree : HasOnlySimpleRoots sqrtTwoPoly then
      (sqrtTwoRoot hsquarefree).exact?.isSome
    else
      false

private def enclosingPoly : ZPoly :=
  sqrtTwoPoly * DensePoly.ofList [-3, 1]

private def enclosingSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 6074001000 32, 0, 32⟩

private def enclosingRep : RefinedIsolation enclosingPoly :=
  ⟨⟨enclosingSquare, by decide⟩, by decide⟩

private def reducibleRoot (hsquarefree : HasOnlySimpleRoots enclosingPoly) :
    AlgebraicRoot where
  p := enclosingPoly
  prim := by rfl
  pos_lc := by decide
  pos_degree := by decide
  squarefree := hsquarefree
  x := SimpleRoot.mk enclosingRep
  rep := enclosingRep
  rep_mk := rfl

-- Exactification discards the irrelevant linear factor and returns `X² - 2`.
#guard
    if hsquarefree : HasOnlySimpleRoots enclosingPoly then
      match (reducibleRoot hsquarefree).exact? with
      | some b => b.p = sqrtTwoPoly
      | none => false
    else
      false

-- A nearby rational root lies inside the linear factor's own coarse
-- separation disc. Cross-factor matching must nevertheless retain `X² - 2`
-- by refining candidates to the enclosing polynomial's precision.
private def nearEnclosingPoly : ZPoly :=
  sqrtTwoPoly * DensePoly.ofList [-99, 70]

private def nearEnclosingRep : RefinedIsolation nearEnclosingPoly :=
  ⟨⟨enclosingSquare, by decide⟩, by decide⟩

private def nearReducibleRoot
    (hsquarefree : HasOnlySimpleRoots nearEnclosingPoly) : AlgebraicRoot where
  p := nearEnclosingPoly
  prim := by rfl
  pos_lc := by decide
  pos_degree := by decide
  squarefree := hsquarefree
  x := SimpleRoot.mk nearEnclosingRep
  rep := nearEnclosingRep
  rep_mk := rfl

#guard
    if hsquarefree : HasOnlySimpleRoots nearEnclosingPoly then
      match (nearReducibleRoot hsquarefree).exact? with
      | some b => b.p = sqrtTwoPoly
      | none => false
    else
      false

#guard
    let q := AlgebraicNumber.zero.toQAdjoin
    q.coeffs = 0 && AlgebraicNumber.zero.toRoot.isZero

end AlgebraicRoot

namespace QAdjoin

variable {p : ZPoly} {x : SimpleRoot p}

/-! # Fixed-presentation minimal polynomials -/

/-- Matrix of multiplication by `a` in the power basis
`1, X, ..., X^(degree p - 1)`. -/
@[expose]
def mulMatrix (a : QAdjoin p x) :
    Matrix Rat (p.degree?.getD 0) (p.degree?.getD 0) :=
  let n := p.degree?.getD 0
  let products : Vector (QAdjoin p x) n := Vector.ofFn fun j =>
    a * reduce p x (DensePoly.monomial j.val 1)
  Matrix.ofFn fun i j =>
    products[j].coeffs.coeff i.val

/-- The first `n + 1` Krylov powers, built with one multiplication per step. -/
@[expose]
def krylovPowers (a : QAdjoin p x) :
    (n : Nat) → Vector (QAdjoin p x) (n + 1)
  | 0 => #v[1]
  | n + 1 =>
      let previous := krylovPowers a n
      previous.push (previous.get (Fin.last n) * a)

/-- Krylov orbit `1, a, a², ...` through the defining-field dimension. -/
@[expose]
def krylovOrbit [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) :
    Vector (QAdjoin p x) (p.degree?.getD 0 + 1) :=
  krylovPowers a (p.degree?.getD 0)

/-- The monic polynomial encoded by a Krylov dependence vector. -/
@[expose]
def relationPoly {k : Nat} (coeffs : Vector Rat k) : DensePoly Rat :=
  DensePoly.ofCoeffs ((coeffs.toArray.map fun c => -c).push 1)

/-- The monic relation at one Krylov-orbit index, when the new power is in
the span of its predecessors. -/
@[expose]
def relationAt? [ZPoly.CheckedIrreducible p]
    (_a : QAdjoin p x)
    (orbit : Vector (QAdjoin p x) (p.degree?.getD 0 + 1))
    (k : Nat) : Option ZPoly :=
  let n := p.degree?.getD 0
  if hk : k ≤ n then
    let previous : Matrix Rat k n := Matrix.ofFn fun i j =>
      (orbit.get ⟨i.val, by omega⟩).coeffs.coeff j
    let target : Vector Rat n := Vector.ofFn fun j =>
      (orbit.get ⟨k, Nat.lt_succ_of_le hk⟩).coeffs.coeff j
    (Matrix.spanCoeffs previous target).map fun coeffs =>
      ZPoly.ratPolyPrimitivePart (relationPoly coeffs)
  else
    none

/-- First monic relation in the Krylov orbit of the multiplication operator,
normalized as a primitive positive-leading integer polynomial. -/
@[expose]
def minpoly? [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) : Option ZPoly :=
  let n := p.degree?.getD 0
  let orbit := a.krylovOrbit
  (List.range n).findSome? fun i => a.relationAt? orbit (i + 1)

/-- Convert a fixed-presentation value to its canonical irreducible
representation. Every stored certificate and every precision-sensitive step
is checked before construction. -/
@[expose]
def toAlgebraicNumber? [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (_h : SimpleRoot.mk rep = x) : Option AlgebraicNumber := do
  let q ← a.minpoly?
  if hprim : ZPoly.content q = 1 then
    if hpos : 0 < q.leadingCoeff then
      if hdegree : 0 < q.degree?.getD 0 then
        if hirred : ZPoly.isIrreducible q = true then
          if hsquarefree : HasOnlySimpleRoots q then do
            let isolations ← isolate q hsquarefree (separationDepth q : Int)
            let refined ← isolations.mapM DyadicRootIsolation.toRefined?
            let requested : Int := mahlerPrec q
            let target := requested + (approxGuardBits rep.1.square a.coeffs : Int)
            -- This checked bind is deliberate: `QAdjoin.approx` has a sound
            -- but potentially coarse fallback when refinement fails, while
            -- root selection must fail rather than compare that wide ball.
            let threaded ← rep.refineTo? target
            let valueBall := evalRatBall a.coeffs threaded.1.1.square target
            -- Candidate discs have radius below `sep(q)/4`; the guarded value
            -- ball requested at `mahlerPrec q` has radius below
            -- `sep(q)/(4*sqrt 2)`. Hence two candidates meeting it would put
            -- distinct roots less than `2r + 2R < sep(q)` apart. The first
            -- match is therefore unique. The precision here must follow `q`,
            -- not the defining polynomial `p`.
            let matching ← refined.toList.find? fun r =>
              r.1.square.meetsBall valueBall
            AlgebraicNumber.ofNormalized? q hprim hpos hdegree
              ⟨hirred, hdegree⟩ hsquarefree matching
          else
            none
        else
          none
      else
        none
    else
      none
  else
    none

/-- Total fixed-presentation conversion. The checked failure branch is proved
unreachable by the Mathlib companion. -/
@[expose]
def toAlgebraicNumber [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) : AlgebraicNumber :=
  (a.toAlgebraicNumber? rep h).getD
    (Hex.panicWith 0 "QAdjoin.toAlgebraicNumber: certification failed")

/-! Compiled fixed-field conversion regressions. -/

private def sqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def sqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def sqrtTwoRep : RefinedIsolation sqrtTwoPoly :=
  ⟨⟨sqrtTwoSquare, by decide⟩, by decide⟩

private def sqrtTwoRoot : SimpleRoot sqrtTwoPoly :=
  SimpleRoot.mk sqrtTwoRep

private def sqrtTwo : QAdjoin sqrtTwoPoly sqrtTwoRoot :=
  reduce sqrtTwoPoly sqrtTwoRoot (DensePoly.ofList [0, 1])

private def oneAddSqrtTwo : QAdjoin sqrtTwoPoly sqrtTwoRoot :=
  1 + sqrtTwo

private def three : QAdjoin sqrtTwoPoly sqrtTwoRoot :=
  reduce sqrtTwoPoly sqrtTwoRoot (DensePoly.C 3)

#guard
    if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible sqrtTwoPoly := ⟨hirred, by decide⟩
      let shiftedPoly : ZPoly := DensePoly.ofList [-1, -2, 1]
      let sqrtTwoTotal := sqrtTwo.toAlgebraicNumber sqrtTwoRep rfl
      sqrtTwo.minpoly? = some sqrtTwoPoly &&
        three.minpoly? = some (DensePoly.ofList [-3, 1]) &&
        oneAddSqrtTwo.minpoly? = some shiftedPoly &&
        sqrtTwoTotal.p = sqrtTwoPoly &&
        sqrtTwoTotal.rep.1.square.discsMeet sqrtTwoSquare &&
        (match sqrtTwo.toAlgebraicNumber? sqrtTwoRep rfl with
        | some a => a.p = sqrtTwoPoly && a.rep.1.square.discsMeet sqrtTwoSquare
        | none => false) &&
        (match (-sqrtTwo).toAlgebraicNumber? sqrtTwoRep rfl with
        | some a => a.p = sqrtTwoPoly && !a.rep.1.square.discsMeet sqrtTwoSquare
        | none => false) &&
        (match oneAddSqrtTwo.toAlgebraicNumber? sqrtTwoRep rfl with
        | some a => a.p = shiftedPoly && decide (0 < a.rep.1.square.re)
        | none => false)
    else
      false

end QAdjoin
end Hex
