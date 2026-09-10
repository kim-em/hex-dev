/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexNumberField
import HexRealAlgebraic

/-! Compiled checks for complex algebraic operations and common fields. -/
namespace Hex.ComplexAlgebraicChecks

private def conjugation (_ : Unit) : Bool :=
  let s := ZPoly.rootNear #p[-2, 0, 1] 1.4
  let i := AlgebraicNumber.I
  let z := s + i
  (#[0, 1, s, i, z, -z]).all (fun a => a.conj.conj == a) &&
    i.conj == -i && s.conj == s && z.conj == s - i &&
    z.re.toAlgebraic == s && z.im == 1 &&
    z.re.toAlgebraic + z.im.toAlgebraic * i == z &&
    (z * z).re == z.re * z.re - z.im * z.im &&
    (z * z).im == 2 * z.re * z.im &&
    RealAlgebraicNumber.ofAlgebraic? i == none &&
    decide ((0 : AlgebraicNumber) ≤ 0) && !decide ((0 : AlgebraicNumber) < 0) &&
    decide (i < z) && decide (i ≤ z) && !decide (z ≤ i) &&
    !decide (i ≤ 2 * i) && !decide (2 * i ≤ i) && !decide (i < 2 * i) &&
    !decide (i ≤ 0) && !decide ((0 : AlgebraicNumber) ≤ i) &&
    decide (s ≤ (s + 1) - 1) && !decide (s < (s + 1) - 1)

private def pairs (_ : Unit) : Bool :=
  let p : ZPoly := #p[1, 0, 1] * #p[4, 0, 1] * #p[-2, 0, 1] * #p[-3, 0, 1]
  let rs := p.algebraicRoots
  let cubic := (ZPoly.algebraicRoots #p[-2, 0, 0, 1])
  let near := (ZPoly.algebraicRoots #p[1048577, -2097152, 1048576])
  rs.size == 8 && (rs.extract 0 4).all (·.isReal) &&
    (#[rs.extract 4 6, rs.extract 6 8, cubic.extract 1 3, near]).all (fun pair =>
      match pair[0]?, pair[1]? with
      | some a, some b => decide (a.side = .lower) && a.conj == b && b.conj == a
      | _, _ => false)

private def radicals (_ : Unit) : Bool :=
  let i := AlgebraicNumber.I
  let s := ZPoly.rootNear #p[-2, 0, 1] 1.4
  let c := (-8 : AlgebraicNumber).nthRoot 3
  let above := (1 + i) * (1 + i)
  let below := (1 - i) * (1 - i)
  (0 : AlgebraicNumber).nthRoot 0 == 1 && (0 : AlgebraicNumber).sqrt == 0 &&
    (1 : AlgebraicNumber).nthRoot 7 == 1 && i.nthRoot 1 == i &&
    (2 : AlgebraicNumber).sqrt == s && (s * s).sqrt == s &&
    (-1 : AlgebraicNumber).sqrt == i && (-1 : AlgebraicNumber).nthRoot 4 ^ 4 == -1 &&
    c ^ 3 == -8 && !c.isReal && decide (c.side = .upper) &&
    above.sqrt == 1 + i && below.sqrt == 1 - i &&
    i.sqrt ^ 2 == i && (-i).sqrt == i.sqrt.conj

private def fields (_ : Unit) : Bool :=
  let s := ZPoly.rootNear #p[-2, 0, 1] 1.4
  let t := ZPoly.rootNear #p[-3, 0, 1] 1.7
  let a := s + t
  let cubic := ZPoly.algebraicRoots #p[-2, 0, 0, 1]
  let chosen := QAdjoin.ofAlgebraics? a #[s, t, s]
  let common := QAdjoin.common #[s, t, s]
  let zs := QAdjoin.common #[0, 0]
  (QAdjoin.ofAlgebraic? cubic[0]! cubic[1]!).isNone &&
    (QAdjoin.ofAlgebraic? s (-s)).isSome && (QAdjoin.ofAlgebraic? s t).isNone &&
    chosen.all Option.isSome &&
    chosen.map (fun v => v.map (·.toAlgebraicNumber)) == #[some s, some t, some s] &&
    common.entries.map (·.toAlgebraicNumber) == #[s, t, s] &&
    zs.entries.map (·.toAlgebraicNumber) == #[0, 0] &&
    (QAdjoin.common #[]).entries.isEmpty &&
    (QAdjoin.ofAlgebraic? a s).map (·.coeffs) == some (#p[0, -9/2, 0, 1/2] : DensePoly Rat)

private def fastPaths (_ : Unit) : Bool :=
  let s := ZPoly.rootNear #p[-2, 0, 1] 1.4
  let t := ZPoly.rootNear #p[-3, 0, 1] 1.7
  let i := AlgebraicNumber.I
  let a := s.rep.1.square
  let touch := { a with re := a.re + 2 * a.radiusHi }
  let pairs := #[(s, t), (t, s), (s, s), (0, s), (s, 0)]
  let roots := [i.toRoot, (-i).toRoot]
  (pairs.all fun (a, b) => a.realCompare b == a.realCompareExact b) &&
    Interval.realOrder? a touch == none && Interval.notLt touch a &&
    !Interval.notLe touch a &&
    (Interval.search Interval.realOrder? [] s.rep s.rep).isNone &&
    (RootSelection.select? roots).isNone && RootSelection.maximum? roots == some i &&
    (#[i, s + i, 2 * i, t + i]).all (fun a =>
      (#[i, s + i, 2 * i, t + i]).all (fun b =>
        a.partialCompare b == a.partialCompareExact b &&
        decide (a < b) == AlgebraicNumber.ordered true (a.partialCompareExact b) &&
        decide (a ≤ b) == AlgebraicNumber.ordered false (a.partialCompareExact b)))

private def unityAndNorms (_ : Unit) : Bool :=
  let i := AlgebraicNumber.I
  let z := 3 + 4 * i
  let angles : Array Rat := #[0, 1/2, 1/4, -1/4, 1/3, 2/5, -1/6, 7/6, 1/8]
  angles.all (fun q =>
    let a := AlgebraicNumber.rootOfUnity q
    a ^ q.den == 1 && a.conj == AlgebraicNumber.rootOfUnity (-q) &&
      a == AlgebraicNumber.rootOfUnity (q + 1)) &&
    i.nthRoot 4 == AlgebraicNumber.rootOfUnity (1/16) &&
    (-i).nthRoot 4 == AlgebraicNumber.rootOfUnity (-1/16) &&
    z.normSq == 25 && z.abs == 5 && z.conj.abs == z.abs &&
    (z * z).normSq == z.normSq * z.normSq &&
    (0 : AlgebraicNumber).abs == 0 && (-3 : AlgebraicNumber).abs == 3

/-- Run the complex API regressions, naming each completed case. -/
def run : IO Unit := do
  for (name, check) in [("conjugation/order/projections", conjugation),
      ("conjugate pairs", pairs), ("principal radicals", radicals), ("common fields", fields),
      ("interval paths and fallback", fastPaths), ("unity and norms", unityAndNorms)] do
    unless check () do throw (IO.userError s!"complex algebraic check failed: {name}")
    IO.eprintln s!"complex algebraic check passed: {name}"

end Hex.ComplexAlgebraicChecks
