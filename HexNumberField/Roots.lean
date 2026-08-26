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

/-- Constant trivariate lift of a candidate eliminant: regard `e(z)` as a
polynomial in the candidate variable `z` whose coefficients are constant in
both the generator variable `y` and the evaluation variable `S`. -/
@[expose]
def candidateLift (e : ZPoly) : DensePoly (DensePoly ZPoly) :=
  DensePoly.ofCoeffs (e.toArray.map fun c => DensePoly.C (DensePoly.C c))

/-- The trivariate polynomial `S - G(y, z)` with `G = clearedOuter f`,
regarded as a polynomial in the candidate variable `z` whose coefficients are
polynomials in the generator `y` over `Int[S]`. The evaluation variable `S`
enters only the constant coordinate of the constant `z`-coefficient. -/
@[expose]
def evalShifted (f : DensePoly (QAdjoin p x)) : DensePoly (DensePoly ZPoly) :=
  let den := commonDen f
  let generatorDegree := p.degree?.getD 0
  DensePoly.ofCoeffs <| ((List.range (Nat.max f.size 1)).map fun i =>
    DensePoly.ofCoeffs <| ((List.range generatorDegree).map fun j =>
      let c := clearRat den ((f.coeff i).coeffs.coeff j)
      if i = 0 && j = 0 then DensePoly.ofCoeffs #[-c, 1]
      else DensePoly.C (-c)).toArray).toArray

/-- Integer evaluation eliminant for one component and candidate eliminant:
the double resultant `Res_y(p(y), Res_z(e(z), S - G(y, z)))` with
`G = clearedOuter f`, dilated by the common denominator so that its roots are
the candidate evaluations themselves rather than their denominator-cleared
multiples. Zero-root removal and primitive normalization happen inside the
bounded disambiguation search, per the SPEC. -/
@[expose]
def evalEliminant (f : DensePoly (QAdjoin p x)) (e : ZPoly) : ZPoly :=
  ZPoly.dilate (Int.ofNat (commonDen f))
    (DensePoly.resultant p.liftOuter
      (DensePoly.resultant (candidateLift e) (evalShifted f)))

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
          let evaluationEliminant := evalEliminant f eliminant
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
              let keep ← retainZero? evaluationEliminant
                (evalMajorant f candidate.p)
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

/-- Merge one root into a list, retaining the first representative of an
existing semantic value and the incoming certified multiplicity. -/
@[expose]
def mergeRootList (candidate : RootCount) :
    List RootCount → Option (List RootCount)
  | [] => some [candidate]
  | current :: rest => do
      let same ← sameValue? current.root candidate.root
      if same then
        let merged : RootCount :=
          { root := current.root
            multiplicity := candidate.multiplicity
            multiplicity_pos := candidate.multiplicity_pos }
        some (merged :: rest)
      else
        let tail ← mergeRootList candidate rest
        some (current :: tail)

/-- Merge one root using a complete scan of the current array. -/
@[expose]
def mergeRoot (roots : Array RootCount) (candidate : RootCount) :
    Option (Array RootCount) := do
  let merged ← mergeRootList candidate roots.toList
  some merged.toArray

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
    some (.finite (roots.mergeSort Roots.rootLe))

/-- Total fixed-field root API. The loud `.all` fallback is unreachable once
the companion discharges `roots?_isSome`. -/
@[expose]
def roots [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) : RootSet :=
  (roots? f rep h).getD
    (Hex.panicWith .all "QAdjoin.roots: certification failed")

end Hex.QAdjoin

namespace Hex.AlgebraicPoly.Common

/-- A primitive fixed-field presentation of an algebraic coefficient array. -/
structure Presentation where
  /-- The canonical primitive element of the common field. -/
  generator : AlgebraicNumber
  /-- The input coefficients rewritten in the generator's fixed field. -/
  coefficients : Array (QAdjoin generator.p generator.x)

/-- Deterministic signed shift order `0, 1, -1, 2, -2, ...`. -/
@[expose]
def signedShift : Nat → Int
  | 0 => 0
  | k + 1 =>
      if k % 2 = 0 then Int.ofNat (k / 2 + 1)
      else -Int.ofNat (k / 2 + 1)

/-- Checked canonical embedding of a rational number. -/
@[expose]
def rational? (q : Rat) : Option AlgebraicNumber :=
  if q = 0 then
    some 0
  else do
    let p := ZPoly.ratPolyPrimitivePart (DensePoly.ofList [-q, 1])
    let root ← AlgebraicRoot.ofEliminant? p fun prec =>
      some (DyadicComplexBall.ofRat q prec)
    root.exact?

/-- Checked canonical sum. -/
@[expose]
def add? (a b : AlgebraicNumber) : Option AlgebraicNumber := do
  let root ← a.toRoot.add? b.toRoot
  root.exact?

/-- Checked canonical product. -/
@[expose]
def mul? (a b : AlgebraicNumber) : Option AlgebraicNumber := do
  let root ← a.toRoot.mul? b.toRoot
  root.exact?

/-- Checked multiplication by an integer shift. -/
@[expose]
def scale? (c : Int) (a : AlgebraicNumber) : Option AlgebraicNumber := do
  let scalar ← rational? c
  mul? scalar a

/-- One primitive-element shift candidate `theta + c * alpha`. -/
@[expose]
def shift? (theta alpha : AlgebraicNumber) (c : Int) : Option AlgebraicNumber :=
  if c = 0 then
    some theta
  else do
    let scaled ← scale? c alpha
    add? theta scaled

/-- Degree of a canonical algebraic number. -/
@[expose]
def degree (a : AlgebraicNumber) : Nat :=
  a.p.degree?.getD 0

/-- A primitive-search candidate together with the signed shift that produced
it. -/
structure ShiftCandidate where
  /-- The signed integer shift that produced this candidate. -/
  shift : Int
  /-- The candidate primitive element `theta + shift * alpha`. -/
  value : AlgebraicNumber

/-- One maximum-degree update that retains the producing signed shift. -/
@[expose]
def extendShiftStep (theta alpha : AlgebraicNumber) :
    Option ShiftCandidate → Nat → Option (Option ShiftCandidate) :=
  fun best k => do
    let shift := signedShift k
    let candidate ← shift? theta alpha shift
    let shifted := ShiftCandidate.mk shift candidate
    some <| match best with
    | none => some shifted
    | some current =>
        if degree current.value < degree candidate then some shifted
        else some current

/-- Maximum-degree primitive candidate together with its producing shift. -/
@[expose]
def extendShift? (theta alpha : AlgebraicNumber) : Option ShiftCandidate := do
  let upper := degree theta * degree alpha
  let count := Nat.choose upper 2 + 1
  let best ← (List.range count).foldlM
    (extendShiftStep theta alpha) none
  best

/-- Extend a primitive presentation by one algebraic number. Testing
`choose(deg(theta) * deg(alpha), 2) + 1` shifts is a conservative bounded
primitive-element search. The maximum-degree candidate generates the
compositum even when the two fields overlap. -/
@[expose]
def extend? (theta alpha : AlgebraicNumber) : Option AlgebraicNumber :=
  (extendShift? theta alpha).map ShiftCandidate.value

/-- Bounded primitive element for all nonzero coefficients. -/
@[expose]
def primitive? (coefficients : Array AlgebraicNumber) : Option AlgebraicNumber := do
  let nonzero := coefficients.filter fun a => !a.isZero
  let first ← nonzero[0]?
  nonzero.toList.drop 1 |>.foldlM extend? first

/-- Checked canonical powers `1, gamma, ..., gamma^last`. -/
@[expose]
def powers? (gamma : AlgebraicNumber) (last : Nat) :
    Option (Array AlgebraicNumber) := do
  let one ← rational? 1
  (List.range last).foldlM
    (fun powers _ => do
      let previous ← powers.back?
      let next ← mul? previous gamma
      some (powers.push next))
    #[one]

/-- Field trace of `a` from a known ambient field degree. If `m` is the
minimal-polynomial degree of `a`, this is `(ambient / m)` times the sum of its
`m` conjugates. -/
@[expose]
def trace? (ambient : Nat) (a : AlgebraicNumber) : Option Rat :=
  let m := degree a
  if m = 0 || ambient % m != 0 then
    none
  else
    let conjugateSum : Rat :=
      -(a.p.coeff (m - 1) : Rat) / (a.p.leadingCoeff : Rat)
    some (((ambient / m : Nat) : Rat) * conjugateSum)

/-- Recover one coefficient in the power basis of `gamma` through the
nondegenerate trace pairing, then validate the recovered coordinate by
canonical algebraic equality. -/
@[expose]
def coordinates? (gamma a : AlgebraicNumber)
    (powers : Array AlgebraicNumber) :
    Option (QAdjoin gamma.p gamma.x) :=
  if a.isZero then
    some 0
  else do
    let d := degree gamma
    let powerTraces ← powers.mapM (trace? d)
    let gram : Matrix Rat d d := Matrix.ofFn fun i j =>
      powerTraces[i.val + j.val]!
    let indices : Vector Nat d :=
      ⟨(List.range d).toArray, by simp⟩
    let products ← indices.mapM fun k => mul? a powers[k]!
    let rhs ← products.mapM (trace? d)
    let coeffs ← Matrix.spanCoeffs gram rhs
    let coordinate := QAdjoin.reduce gamma.p gamma.x
      (DensePoly.ofCoeffs coeffs.toArray)
    let recovered ← @QAdjoin.toAlgebraicNumber? gamma.p gamma.x gamma.checked
      coordinate gamma.rep gamma.rep_mk
    if recovered == a then some coordinate else none

/-- Construct and validate one primitive fixed-field presentation for an
algebraic coefficient array. -/
@[expose]
def presentation? (coefficients : Array AlgebraicNumber) :
    Option Presentation := do
  let generator ← primitive? coefficients
  let d := degree generator
  let powers ← powers? generator (2 * d - 2)
  let embedded ← coefficients.mapM fun a => coordinates? generator a powers
  some ⟨generator, embedded⟩

end Hex.AlgebraicPoly.Common

namespace Hex.AlgebraicNumber

/-- Total executable embedding of a rational number into canonical algebraic
numbers. The companion proves that the checked constructor cannot fail. -/
@[expose]
def ofRat (q : Rat) : AlgebraicNumber :=
  (AlgebraicPoly.Common.rational? q).getD
    (Hex.panicWith 0 "AlgebraicNumber.ofRat: certification failed")

instance : One AlgebraicNumber := ⟨ofRat 1⟩
instance : NatCast AlgebraicNumber := ⟨fun n => ofRat (n : Rat)⟩
instance : IntCast AlgebraicNumber := ⟨fun n => ofRat (n : Rat)⟩
-- Mathlib's generic `OfNat` from `NatCast` has priority 100. Keep this
-- Mathlib-free fallback below it so importing the companion yields one normal
-- form for numerals while the executable library still supports literals.
instance (priority := 90) (n : Nat) : OfNat AlgebraicNumber (n + 2) :=
  ⟨ofRat (n + 2 : Nat)⟩

/-- Executable scalar multiplication through the canonical rational
embedding. -/
@[expose]
def smul (q : Rat) (a : AlgebraicNumber) : AlgebraicNumber :=
  ofRat q * a

instance : SMul Rat AlgebraicNumber := ⟨smul⟩
instance : SMul Nat AlgebraicNumber :=
  ⟨fun n a => smul (n : Rat) a⟩
instance : SMul Int AlgebraicNumber :=
  ⟨fun n a => smul (n : Rat) a⟩

/-- Natural powers by repeated squaring using executable canonical
multiplication. -/
@[expose]
def natPow (a : AlgebraicNumber) : Nat → AlgebraicNumber
  | 0 => 1
  | n + 1 =>
      let q := natPow a ((n + 1) / 2)
      let q2 := q * q
      if (n + 1) % 2 = 0 then q2 else q2 * a
termination_by n => n
decreasing_by omega

instance : Pow AlgebraicNumber Nat := ⟨natPow⟩

/-- Integer powers assembled from executable multiplication and inversion. -/
@[expose]
def intPow (a : AlgebraicNumber) : Int → AlgebraicNumber
  | .ofNat n => natPow a n
  | .negSucc n => (natPow a (n + 1))⁻¹

instance : Pow AlgebraicNumber Int := ⟨intPow⟩

end Hex.AlgebraicNumber

namespace Hex.AlgebraicPoly

/-- Checked roots of a polynomial with canonical algebraic coefficients. All
nonzero coefficients are first embedded in one bounded deterministic primitive
presentation, then the fixed-field root driver is reused. -/
@[expose]
def roots? (f : AlgebraicPoly) : Option RootSet :=
  if f.isZero then
    some .all
  else do
    let common ← Common.presentation? f.coeffs
    letI : ZPoly.CheckedIrreducible common.generator.p := common.generator.checked
    let polynomial := DensePoly.ofCoeffs common.coefficients
    QAdjoin.roots? polynomial common.generator.rep common.generator.rep_mk

/-- Total roots of a polynomial with canonical algebraic coefficients. -/
@[expose]
def roots (f : AlgebraicPoly) : RootSet :=
  f.roots?.getD
    (Hex.panicWith .all "AlgebraicPoly.roots: certification failed")

end Hex.AlgebraicPoly

namespace Hex

/-! Compiled fixed-field root regressions. -/

private def rootsSqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def rootsSqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def rootsSqrtTwoRep : RefinedIsolation rootsSqrtTwoPoly :=
  ⟨⟨rootsSqrtTwoSquare, .ofWitness (by decide)⟩, by decide⟩

private def rootsSqrtTwoRoot : SimpleRoot rootsSqrtTwoPoly :=
  SimpleRoot.mk rootsSqrtTwoRep

private def rootsSqrtTwo : QAdjoin rootsSqrtTwoPoly rootsSqrtTwoRoot :=
  QAdjoin.reduce rootsSqrtTwoPoly rootsSqrtTwoRoot
    (DensePoly.ofList ([0, 1] : List Rat))

private def rootsLinear : DensePoly (QAdjoin rootsSqrtTwoPoly rootsSqrtTwoRoot) :=
  DensePoly.ofList [-rootsSqrtTwo, 1]

private def rootsHalfSqrtTwo : QAdjoin rootsSqrtTwoPoly rootsSqrtTwoRoot :=
  QAdjoin.reduce rootsSqrtTwoPoly rootsSqrtTwoRoot
    (DensePoly.ofList ([0, (1 : Rat) / 2] : List Rat))

private def rootsHalfLinear : DensePoly (QAdjoin rootsSqrtTwoPoly rootsSqrtTwoRoot) :=
  DensePoly.ofList [-rootsHalfSqrtTwo, 1]

private def rootsSqrtTwoExact? : Option AlgebraicNumber :=
  if hirred : ZPoly.isIrreducible rootsSqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible rootsSqrtTwoPoly :=
      ⟨hirred, by decide⟩
    rootsSqrtTwo.toAlgebraicNumber? rootsSqrtTwoRep rfl
  else
    none

private def algebraicLinearRoots? : Option RootSet := do
  let sqrtTwo ← rootsSqrtTwoExact?
  let negSqrtTwo ← AlgebraicPoly.Common.scale? (-1) sqrtTwo
  let one ← AlgebraicPoly.Common.rational? 1
  AlgebraicPoly.roots? (AlgebraicPoly.ofArray #[negSqrtTwo, one])

#guard QAdjoin.Roots.normEliminant rootsLinear = rootsSqrtTwoPoly

-- The double-resultant evaluation eliminant for `X - √2` over `ℚ(√2)` with
-- candidate eliminant `X² - 2`: its roots are the four differences
-- `z - y` over conjugate pairs, i.e. `S²(S² - 8)`.
#guard
    QAdjoin.Roots.evalEliminant rootsLinear
      (ZPoly.squareFreeCore (QAdjoin.Roots.normEliminant rootsLinear)) =
    DensePoly.ofList [0, 0, -8, 0, 1]

-- A non-unit common denominator exercises the dilation direction: before
-- dilation the nonzero evaluation roots are `±2√2`; substituting `2S`
-- moves them to the actual values `±√2`.
#guard QAdjoin.Roots.commonDen rootsHalfLinear = 2

#guard
    QAdjoin.Roots.evalEliminant rootsHalfLinear
      (ZPoly.squareFreeCore (QAdjoin.Roots.normEliminant rootsHalfLinear)) =
    DensePoly.ofList [0, 0, -128, 0, 64]

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

-- The algebraic-coefficient driver finds the positive root of `T - sqrt 2`
-- after constructing and validating a common primitive presentation.
#guard
    match algebraicLinearRoots? with
    | some (.finite roots) =>
        roots.size = 1 &&
          (roots[0]?).any fun root =>
            root.multiplicity = 1 &&
              decide (0 < root.root.rep.1.square.re)
    | _ => false

-- The public zero/constant conventions survive the common-field conversion.
#guard
    match
        AlgebraicPoly.roots? (AlgebraicPoly.ofArray #[]),
        rootsSqrtTwoExact? >>= fun one =>
          AlgebraicPoly.roots? (AlgebraicPoly.ofArray #[one]) with
    | some .all, some (.finite roots) => roots.isEmpty
    | _, _ => false

end Hex
