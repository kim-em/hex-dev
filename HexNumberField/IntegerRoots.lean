/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField.Convert

public section

/-!
Roots of integer polynomials as canonical algebraic numbers, the reality
test on stored isolations, and display.

`ZPoly.algebraicRoots` is the entry point a user reaches for first: it turns
an integer polynomial into its distinct complex roots, each a canonical
`AlgebraicNumber`, real roots first in increasing order. The reality test
compares the centre of a stored isolation with the dyadic upper bound of its
disc radius; at separation precision that decides reality exactly, as the
companion proves.
-/

namespace Hex

namespace DyadicSquare

/-- The closed circumscribed disc, with its radius rounded up to `radiusHi`,
meets the real axis. -/
@[expose]
def meetsRealAxis (s : DyadicSquare) : Bool :=
  -s.radiusHi ≤ s.im && s.im ≤ s.radiusHi

end DyadicSquare

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
  a.rep.1.square.meetsRealAxis

/-- The output order of `ZPoly.algebraicRoots`: real roots first, in
increasing order of their isolation centres (which is their order as real
numbers), then nonreal roots by isolation centre and precision. -/
@[expose]
def rootLe (a b : AlgebraicNumber) : Bool :=
  match a.isReal, b.isReal with
  | true, false => true
  | false, true => false
  | _, _ =>
    let s := a.rep.1.square
    let t := b.rep.1.square
    if s.re = t.re then
      if s.im = t.im then decide (s.prec ≤ t.prec) else decide (s.im < t.im)
    else
      decide (s.re < t.re)

/-- A dyadic complex ball of radius at most `2^(-prec)` around the value,
evaluated on the stored representative. -/
@[expose]
def approx (a : AlgebraicNumber) (prec : Int := 64) : DyadicComplexBall :=
  (a.toQAdjoin.approx a.rep a.rep_mk prec).2

end AlgebraicNumber

namespace ZPoly

/-- Every distinct complex root of `p` as a canonical algebraic number, or
`none` if a certificate could not be produced. See `algebraicRoots`. -/
@[expose]
def algebraicRoots? (p : ZPoly) : Option (Array AlgebraicNumber) :=
  if p.degree?.getD 0 = 0 then
    some #[]
  else
    let q := ZPoly.squareFreeCore p
    if hprim : ZPoly.content q = 1 then
      if hpos : 0 < q.leadingCoeff then
        if hdeg : 0 < q.degree?.getD 0 then
          if hsimple : HasOnlySimpleRoots q then do
            let isolations ← isolate q hsimple (separationDepth q : Int)
            let refined ← isolations.mapM DyadicRootIsolation.toRefined?
            let roots ← refined.mapM fun rep =>
              ({ p := q
                 prim := hprim
                 pos_lc := hpos
                 pos_degree := hdeg
                 squarefree := hsimple
                 x := SimpleRoot.mk rep
                 rep := rep
                 rep_mk := rfl } : AlgebraicRoot).exact?
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
exactified. Real roots come first, in increasing order, then the nonreal
roots in a deterministic order set by their isolations. Multiplicities are
not returned; use `AlgebraicPoly.roots` for them. A constant polynomial,
including zero, has no roots here. -/
@[expose]
def algebraicRoots (p : ZPoly) : Array AlgebraicNumber :=
  p.algebraicRoots?.getD (Hex.panicWith #[] "ZPoly.algebraicRoots: certification failed")

end ZPoly

namespace AlgebraicNumber

namespace Display

/-- `q` truncated toward zero to `digits` decimal places. A display helper
for the `Repr` instance; it carries no contract. -/
def decimal (q : Rat) (digits : Nat) : String :=
  let scale := 10 ^ digits
  let n := q.num.natAbs * scale / q.den
  let whole := n / scale
  let frac := n % scale
  let fracDigits := toString frac
  let padded := String.mk (List.replicate (digits - fracDigits.length) '0') ++ fracDigits
  (if q.num < 0 && n ≠ 0 then "-" else "") ++ s!"{whole}.{padded}"

/-- `p` written with descending powers of `X`. A display helper for the
`Repr` instance; it carries no contract. -/
def polynomial (p : ZPoly) : String :=
  let coeffs := p.coeffs
  let terms := (List.range coeffs.size).reverse.filterMap fun i =>
    let c := coeffs.getD i 0
    if c = 0 then none
    else
      let magnitude := c.natAbs
      let body :=
        if i = 0 then s!"{magnitude}"
        else
          (if magnitude = 1 then "" else s!"{magnitude}*") ++
            (if i = 1 then "X" else s!"X^{i}")
      some (decide (c < 0), body)
  match terms with
  | [] => "0"
  | (negative, body) :: rest =>
      rest.foldl (fun acc (neg, term) => acc ++ (if neg then " - " else " + ") ++ term)
        ((if negative then "-" else "") ++ body)

end Display

instance : Repr AlgebraicNumber where
  reprPrec a _ :=
    let ball := a.approx 64
    let re := Display.decimal ball.re.toRat 12
    let value :=
      if a.isReal then re
      else
        let im := Display.decimal ball.im.toRat 12
        re ++ (if im.startsWith "-" then " - " ++ im.drop 1 else " + " ++ im) ++ "i"
    Std.Format.text s!"root of {Display.polynomial a.p} near {value}"

end AlgebraicNumber

end Hex
