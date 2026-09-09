/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField.Convert
public import HexNumberField.Roots

public section

/-!
Roots of integer polynomials as canonical algebraic numbers, the reality
test on stored isolations, and display.

`ZPoly.algebraicRoots` is the entry point a user reaches for first: it turns
an integer polynomial into its distinct complex roots, each a canonical
`AlgebraicNumber`, real roots first by centre order and conjugate pairs adjacent.
The reality test reads the orientation tag. Construction establishes that tag
by comparing the isolation centre with its rounded disc radius; separation
precision makes this exact, as the companion proves.
-/

namespace Hex

namespace AlgebraicRoot

/-- The selected root is real. Exact at the stored separation precision. -/
@[expose]
def isReal (a : AlgebraicRoot) : Bool :=
  a.rep.1.square.meetsRealAxis

end AlgebraicRoot

namespace AlgebraicNumber

/-- The represented number is real. Exact at the stored separation precision. -/
@[expose]
def isReal (a : AlgebraicNumber) : Bool :=
  decide (a.side = .real)

/-- A successful reality test makes conjugation the identity. -/
@[simp] theorem conj_of_isReal (a : AlgebraicNumber) (h : a.isReal = true) : a.conj = a :=
  conj_of_side_real a (of_decide_eq_true h)

/-- Deterministic root enumeration: real roots first by their isolation centres;
then adjacent conjugate pairs, ordered by the upper base's height and real
coordinate. Precision and minimal polynomial distinguish pairs before the
negative-imaginary member is placed first. This is an order of stored data,
not exact lexicographic comparison of the complex coordinates. -/
@[expose]
def rootLe (a b : AlgebraicNumber) : Bool :=
  match a.isReal, b.isReal with
  | true, false => true
  | false, true => false
  | true, true =>
    let s := a.isolation.base.1.square
    let t := b.isolation.base.1.square
    if s.re = t.re then
      if s.im = t.im then decide (s.prec ≤ t.prec) else decide (s.im < t.im)
    else decide (s.re < t.re)
  | false, false =>
    let s := a.isolation.base.1.square
    let t := b.isolation.base.1.square
    if s.im ≠ t.im then decide (s.im < t.im)
    else if s.re ≠ t.re then decide (s.re < t.re)
    else if s.prec ≠ t.prec then decide (s.prec < t.prec)
    else if a.p ≠ b.p then PolyQuot.Roots.intListLe a.p.toArray.toList b.p.toArray.toList
    else decide (a.side = .lower) || decide (b.side ≠ .lower)

/-- A dyadic complex ball of radius at most `2^(-prec)` around the value,
evaluated on the stored representative. -/
@[expose]
def approx (a : AlgebraicNumber) (prec : Int := 64) : DyadicComplexBall :=
  (a.toQAdjoin.approx a.rep a.rep_mk prec).2

end AlgebraicNumber

namespace AlgebraicRoot

/-- The lazy root selected by one refined isolation of a normalized squarefree
polynomial. -/
@[expose]
def ofRefined (q : ZPoly) (prim : ZPoly.content q = 1) (pos_lc : 0 < q.leadingCoeff)
    (pos_degree : 0 < q.natDegree) (squarefree : HasOnlySimpleRoots q)
    (rep : RefinedIsolation q) : AlgebraicRoot :=
  { p := q
    prim := prim
    pos_lc := pos_lc
    pos_degree := pos_degree
    squarefree := squarefree
    x := SimpleRoot.mk rep
    rep := rep
    rep_mk := rfl }

end AlgebraicRoot

namespace ZPoly

/-- Every distinct complex root of `p` as a canonical algebraic number, or
`none` if a certificate could not be produced. See `algebraicRoots`.

Irreducible, like `algebraicRoots`, so that a type such as `PolyQuot a.p a.x`
for a root `a` found here is cheap to reduce: `#eval` reduces the type of a
value while looking for a printing instance, and must not run the root
isolation symbolically. Proofs unfold it explicitly. -/
@[expose, irreducible]
def algebraicRoots? (p : ZPoly) : Option (Array AlgebraicNumber) :=
  if p.natDegree = 0 then
    some #[]
  else
    let q := ZPoly.squareFreeCore p
    if hprim : ZPoly.content q = 1 then
      if hpos : 0 < q.leadingCoeff then
        if hdeg : 0 < q.natDegree then
          if hsimple : HasOnlySimpleRoots q then do
            let isolations ← ZPoly.isolateComplexRoots? q hsimple (separationDepth q : Int)
            let refined ← isolations.mapM DyadicRootIsolation.toRefined?
            let roots ← refined.mapM fun rep =>
              (AlgebraicRoot.ofRefined q hprim hpos hdeg hsimple rep).exact?
            some (roots.toList.mergeSort AlgebraicNumber.rootLe).toArray
          else
            none
        else
          none
      else
        none
    else
      none

/-- Every distinct complex root of `p` as a canonical algebraic number: the
squarefree primitive part of `p` is isolated, and each isolated root is
exactified. Real roots come first by isolation centre, then adjacent nonreal
conjugate pairs with the lower member first. For exact value ordering of real
roots use `ZPoly.realAlgebraicRoots` from `HexRealAlgebraic`. Multiplicities are
not returned; use `AlgebraicPoly.roots` for them. A constant polynomial,
including zero, has no roots here. Irreducible for the reason given at
`algebraicRoots?`. -/
@[expose, irreducible]
def algebraicRoots (p : ZPoly) : Array AlgebraicNumber :=
  p.algebraicRoots?.getD (Hex.panicWith #[] "ZPoly.algebraicRoots: certification failed")

end ZPoly


namespace Display

/-- A dyadic as the expression that rebuilds it. `Dyadic` is a core inductive
with no `Repr`; `ofOdd n k` denotes `n · 2⁻ᵏ`, which is `ofIntWithPrec n k`. -/
def dyadic : Dyadic → String
  | .zero => "0"
  | .ofOdd n k _ =>
      -- Core's `>>>` on `Dyadic` is exact division by `2ᵏ`. The ascription is
      -- load-bearing: without it the mantissa elaborates as `Nat`, takes
      -- `Nat`'s truncating shift, and is coerced -- a silently wrong value.
      if k ≥ 0 then s!"(({n} : Dyadic) >>> {k})"
      else s!"(({n} : Dyadic) >>> ({k} : Int))"

/-- A square as the anonymous constructor its three fields rebuild. -/
def square (s : DyadicSquare) : String :=
  s!"⟨{dyadic s.re}, {dyadic s.im}, {s.prec}⟩"

/-- Replay a certificate's actual constructors; transported certificates need
not pass a fresh numerical check at their final square. -/
def certificate {p : ZPoly} {s : DyadicSquare} : AtomCertificate p s → String
  | @AtomCertificate.nk p s _ =>
    s!"(@Hex.AtomCertificate.nk ({repr p}) ({square s}) (by decide))"
  | @AtomCertificate.pellet p s _ =>
    s!"(@Hex.AtomCertificate.pellet ({repr p}) ({square s}) (by decide))"
  | @AtomCertificate.neg p s _ c =>
    s!"(@Hex.AtomCertificate.neg ({repr p}) ({square s}) (by decide) {certificate c})"
  | @AtomCertificate.normalize p s c =>
    s!"(@Hex.AtomCertificate.normalize ({repr p}) ({square s}) {certificate c})"
  | @AtomCertificate.conj p s c =>
    s!"(@Hex.AtomCertificate.conj ({repr p}) ({square s}) {certificate c})"

end Display

/-- A fixed-field element prints as the expression that rebuilds it:
`PolyQuot.ofSquare` replays a direct NK/Pellet certificate;
`PolyQuot.ofIsolation` replays the actual certificate constructors when the
representative was transported. Both include the reduced coordinates and
select the same root. A transported square need not pass a fresh checker.

The representative comes out of the `Quot` by `unquot`, as Mathlib's `Multiset`
and `Finset` instances do, so the instance is `unsafe` and the printed square is
whichever representative the value happens to carry. That choice is invisible in
the result: `Intersects` compares stored squares, so every representative of the
root rebuilds the same element. -/
unsafe instance {p : ZPoly} {x : SimpleRoot p} : Repr (PolyQuot p x) where
  reprPrec a _ :=
    let r := (unsafeCast x : RefinedIsolation p)
    let s := r.1.square
    Std.Format.text <| match r.1.witness with
      | .nk _ | .pellet _ =>
        s!"PolyQuot.ofSquare {repr p} {Display.square s} {repr a.coeffs}"
      | _ =>
        s!"PolyQuot.ofIsolation (p := {repr p}) ⟨⟨{Display.square s}, {Display.certificate r.1.witness}⟩, by decide⟩ {repr a.coeffs}"

end Hex
